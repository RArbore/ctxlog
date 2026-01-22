use core::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::io::{Result, Write};

use string_interner::Symbol as _;

use crate::ast::{ExpressionAST, FunctionAST, StatementAST, Symbol};

pub type BlockId = u32;
pub type TermId = u32;

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum Term {
    Constant(i32),
    Param(i32),
    Phi(BlockId, TermId, TermId),
    Unary(UnaryOp, TermId),
    Binary(BinaryOp, TermId, TermId),
    Tombstone,
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum UnaryOp {
    Negate,
    Not,
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    EE,
    NE,
    LT,
    LE,
    GT,
    GE,
}

#[derive(Debug, Clone)]
struct Context<'a> {
    vars: BTreeMap<Symbol, TermId>,
    num_blocks: &'a RefCell<BlockId>,
    last_block: BlockId,
}

pub type CFG = BTreeMap<BlockId, Vec<(BlockId, TermId)>>;

#[derive(Debug, Clone)]
pub struct SSA {
    pub name: Symbol,
    pub terms: Vec<Term>,
    pub intern: BTreeMap<Term, TermId>,
    pub cfg: CFG,
    pub roots: BTreeSet<TermId>,
}

impl Term {
    fn symbol(&self) -> String {
        match self {
            Term::Constant(val) => format!("{}", val),
            Term::Param(idx) => format!("#{}", idx),
            Term::Phi(_, _, _) => "Φ".to_string(),
            Term::Unary(op, _) => format!("{:?}", op),
            Term::Binary(op, _, _) => format!("{:?}", op),
            Term::Tombstone => panic!(),
        }
    }
}

impl SSA {
    fn add_term(&mut self, term: Term) -> TermId {
        if let Some(id) = self.intern.get(&term) {
            *id
        } else {
            let id = self.alloc_term();
            self.set_term(id, term);
            id
        }
    }

    fn alloc_term(&mut self) -> TermId {
        let id = self.terms.len() as TermId;
        self.terms.push(Term::Tombstone);
        id
    }

    fn set_term(&mut self, id: TermId, term: Term) {
        self.terms[id as usize] = term;
        self.intern.insert(term, id);
    }

    pub fn terms(&self) -> impl Iterator<Item = (TermId, Term)> + '_ {
        self.terms
            .iter()
            .enumerate()
            .map(|(idx, term)| (idx as TermId, *term))
    }
}

pub fn naive_ssa_translation(func: &FunctionAST) -> SSA {
    let mut ssa = SSA {
        name: func.name,
        terms: vec![],
        intern: BTreeMap::new(),
        cfg: BTreeMap::new(),
        roots: BTreeSet::new(),
    };
    let num_blocks = RefCell::new(1);
    let mut ctx = Context {
        vars: BTreeMap::new(),
        num_blocks: &num_blocks,
        last_block: 0,
    };
    for (idx, sym) in func.params.iter().enumerate() {
        ctx.vars.insert(*sym, ssa.add_term(Term::Param(idx as i32)));
    }
    ctx.handle_stmt(&mut ssa, &func.body);
    ssa
}

impl<'a> Context<'a> {
    fn new_block(&self) -> BlockId {
        let mut num = self.num_blocks.borrow_mut();
        let id = *num;
        *num += 1;
        id
    }

    fn handle_stmt(&mut self, ssa: &mut SSA, stmt: &StatementAST) {
        use StatementAST::*;
        match stmt {
            Block(stmts) => stmts.iter().for_each(|stmt| self.handle_stmt(ssa, stmt)),
            Assign(sym, expr) => {
                let term = self.handle_expr(ssa, expr);
                self.vars.insert(*sym, term);
            }
            IfElse(cond_expr, then_stmt, else_stmt) => {
                let true_cond = self.handle_expr(ssa, cond_expr);
                let false_cond = ssa.add_term(Term::Unary(UnaryOp::Not, true_cond));
                let true_term = ssa.add_term(Term::Constant(1));

                let mut then_ctx = self.clone();
                let true_block = self.new_block();
                ssa.cfg
                    .insert(true_block, vec![(self.last_block, true_cond)]);
                then_ctx.last_block = true_block;
                then_ctx.handle_stmt(ssa, then_stmt);

                let mut else_ctx = self.clone();
                if let Some(else_stmt) = else_stmt {
                    let false_block = self.new_block();
                    ssa.cfg
                        .insert(false_block, vec![(self.last_block, false_cond)]);
                    else_ctx.last_block = false_block;
                    else_ctx.handle_stmt(ssa, else_stmt);
                }

                let merge_block = self.new_block();
                ssa.cfg.insert(
                    merge_block,
                    vec![
                        (then_ctx.last_block, true_term),
                        (
                            else_ctx.last_block,
                            if else_stmt.is_some() {
                                true_term
                            } else {
                                false_cond
                            },
                        ),
                    ],
                );
                for (sym, then_term) in &then_ctx.vars {
                    let Some(else_term) = else_ctx.vars.get(sym) else {
                        continue;
                    };
                    self.vars.insert(
                        *sym,
                        ssa.add_term(Term::Phi(merge_block, *then_term, *else_term)),
                    );
                }
                self.last_block = merge_block;
            }
            While(cond_expr, body_stmt) => {
                let mut sym_entry_phi_tuples = vec![];
                for (sym, entry) in self.vars.iter_mut() {
                    let old_entry = *entry;
                    let phi = ssa.alloc_term();
                    *entry = phi;
                    sym_entry_phi_tuples.push((*sym, old_entry, phi));
                }

                let entry_block = self.last_block;
                let header_block = self.new_block();
                self.last_block = header_block;

                let true_cond = self.handle_expr(ssa, cond_expr);
                let false_cond = ssa.add_term(Term::Unary(UnaryOp::Not, true_cond));
                let true_term = ssa.add_term(Term::Constant(1));

                let body_block = self.new_block();
                let mut body_ctx = self.clone();
                body_ctx.last_block = body_block;
                body_ctx.handle_stmt(ssa, body_stmt);
                for (sym, entry, phi) in sym_entry_phi_tuples {
                    let bottom = body_ctx.vars[&sym];
                    ssa.set_term(phi, Term::Phi(header_block, entry, bottom));
                }
                ssa.cfg.insert(
                    header_block,
                    vec![(entry_block, true_term), (body_ctx.last_block, true_term)],
                );
                ssa.cfg.insert(body_block, vec![(header_block, true_cond)]);

                let exit_block = self.new_block();
                ssa.cfg.insert(exit_block, vec![(header_block, false_cond)]);
                self.last_block = exit_block;
            }
            Return(expr) => {
                let returned = self.handle_expr(ssa, expr);
                ssa.roots.insert(returned);
            }
        }
    }

    fn handle_expr(&self, ssa: &mut SSA, expr: &ExpressionAST) -> TermId {
        use ExpressionAST::*;
        match expr {
            NumberLiteral(val) => ssa.add_term(Term::Constant(*val)),
            Variable(sym) => self.vars[sym],
            Call(_, _) => todo!(),
            Add(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::Add, lhs, rhs))
            }
            Subtract(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::Sub, lhs, rhs))
            }
            Multiply(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::Mul, lhs, rhs))
            }
            Divide(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::Div, lhs, rhs))
            }
            Modulo(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::Rem, lhs, rhs))
            }
            EqualsEquals(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::EE, lhs, rhs))
            }
            NotEquals(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::NE, lhs, rhs))
            }
            Less(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::LT, lhs, rhs))
            }
            LessEquals(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::LE, lhs, rhs))
            }
            Greater(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::GT, lhs, rhs))
            }
            GreaterEquals(lhs, rhs) => {
                let lhs = self.handle_expr(ssa, lhs);
                let rhs = self.handle_expr(ssa, rhs);
                ssa.add_term(Term::Binary(BinaryOp::GE, lhs, rhs))
            }
            Not(value) => {
                let value = self.handle_expr(ssa, value);
                ssa.add_term(Term::Unary(UnaryOp::Not, value))
            }
            Negate(value) => {
                let value = self.handle_expr(ssa, value);
                ssa.add_term(Term::Unary(UnaryOp::Negate, value))
            }
        }
    }
}

pub fn dce(ssa: &mut SSA) {
    let mut alive = BTreeSet::new();
    let mut worklist = Vec::from_iter(ssa.roots.iter().cloned());
    worklist.extend(
        ssa.cfg
            .iter()
            .map(|(_, preds)| preds.iter().map(|(_, term)| *term))
            .flatten(),
    );

    while let Some(term) = worklist.pop() {
        if !alive.contains(&term) {
            alive.insert(term);
            match ssa.terms[term as usize] {
                Term::Constant(_) | Term::Param(_) => {}
                Term::Phi(_, lhs, rhs) | Term::Binary(_, lhs, rhs) => {
                    worklist.push(lhs);
                    worklist.push(rhs);
                }
                Term::Unary(_, input) => worklist.push(input),
                Term::Tombstone => panic!(),
            }
        }
    }

    for idx in 0..ssa.terms.len() {
        if !alive.contains(&(idx as TermId)) {
            ssa.terms[idx] = Term::Tombstone;
        }
    }
}

pub fn ssa_to_dot<W: Write>(ssa: &SSA, w: &mut W) -> Result<()> {
    writeln!(w, "digraph F{} {{", ssa.name.to_usize())?;
    writeln!(w, "B0[label=\"0\", shape=\"box\", style=\"rounded\"];")?;
    for (block, cfg) in &ssa.cfg {
        writeln!(
            w,
            "B{}[label=\"{}\", shape=\"box\", style=\"rounded\"];",
            block, block
        )?;
        for (pred, cond) in cfg {
            writeln!(w, "B{} -> B{};", pred, block)?;
            if ssa.terms[*cond as usize] != Term::Constant(1) {
                writeln!(
                    w,
                    "N{} -> B{} [style=\"dotted\", constraint=false];",
                    cond, block
                )?;
            }
        }
    }
    for (term_id, term) in ssa.terms() {
        if term != Term::Tombstone {
            writeln!(
                w,
                "N{}[label=\"{}\", color=\"{}\"];",
                term_id,
                term.symbol(),
                if ssa.roots.contains(&term_id) {
                    "blue"
                } else {
                    "black"
                }
            )?;
        }
        match term {
            Term::Constant(_) | Term::Param(_) => {}
            Term::Unary(_, input) => writeln!(w, "N{} -> N{};", input, term_id)?,
            Term::Binary(_, lhs, rhs) => {
                writeln!(w, "N{} -> N{};", lhs, term_id)?;
                writeln!(w, "N{} -> N{};", rhs, term_id)?;
            }
            Term::Phi(block, lhs, rhs) => {
                writeln!(w, "N{} -> N{};", lhs, term_id)?;
                writeln!(w, "N{} -> N{};", rhs, term_id)?;
                writeln!(
                    w,
                    "B{} -> N{} [style=\"dashed\", constraint=false];",
                    block, term_id
                )?;
            }
            Term::Tombstone => {}
        }
    }
    writeln!(w, "}}")
}
