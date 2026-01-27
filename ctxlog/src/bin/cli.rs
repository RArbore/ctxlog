use std::io::{Read, Result, stdin};
use std::process::Command;

use tempfile::NamedTempFile;

use ctxlog::ast::NameInterner;
use ctxlog::cfg::dominator;
use ctxlog::grammar::ProgramParser;
use ctxlog::interner::Interner;
use ctxlog::lattice::{Interval, IsZero};
use ctxlog::provenance::{
    FlowContexts, factor, flow_contexts, joint_use, leq, mk_prov, propagate, root_prov,
};
use ctxlog::ssa::{BinaryOp, SSA, SSAValue, dce, naive_ssa_translation, ssa_to_dot};
use ctxlog::table::{Table, Value};

pub fn main() -> Result<()> {
    let mut interner = NameInterner::new();

    let mut imp_program = String::new();
    stdin().read_to_string(&mut imp_program)?;
    let ast = ProgramParser::new()
        .parse(&mut interner, &imp_program)
        .unwrap();

    let mut ssas = vec![];
    let mut flows = vec![];
    for func in &ast.funcs {
        let mut terms = naive_ssa_translation(func);
        dce(&mut terms);
        let dom = dominator(&terms.cfg);
        let flow = flow_contexts(&terms, &dom);
        ssas.push(terms);
        flows.push(flow);
    }

    let mut tmp = NamedTempFile::new().unwrap();
    ssa_to_dot(&ssas, &mut tmp)?;
    println!("Drawing {}", tmp.path().display());
    Command::new("xdot").arg(tmp.path()).status().unwrap();

    Ok(())
}

fn analysis(ssa: &SSA, ctxs: &FlowContexts) {
    let int_intern = Interner::new();
    let mut iz = Table::new(2);
    let mut int = Table::new(2);
    let mut iz_merge = |iz1, iz2| Value::from(IsZero::from(iz1).meet(&IsZero::from(iz2)));
    let mut int_merge = int_intern.intersect();

    for (idx, cond) in ctxs.contexts.iter().enumerate() {
        iz.insert(
            &[*cond, mk_prov(idx as u32), IsZero::NotZero.into()],
            &mut iz_merge,
        );
    }

    for _ in 0..100 {
        for (term_id, term) in ssa.terms() {
            use SSAValue::*;
            match term {
                Constant(0) => {
                    iz.insert(&[term_id, root_prov(), IsZero::Zero.into()], &mut iz_merge);
                    int.insert(
                        &[
                            term_id,
                            root_prov(),
                            int_intern.intern(Interval::from(0)).into(),
                        ],
                        &mut int_merge,
                    );
                }
                Constant(c) => {
                    iz.insert(
                        &[term_id, root_prov(), IsZero::NotZero.into()],
                        &mut iz_merge,
                    );
                    int.insert(
                        &[
                            term_id,
                            root_prov(),
                            int_intern.intern(Interval::from(c)).into(),
                        ],
                        &mut int_merge,
                    );
                }
                Param(_) => {
                    iz.insert(&[term_id, root_prov(), IsZero::Top.into()], &mut iz_merge);
                    int.insert(
                        &[
                            term_id,
                            root_prov(),
                            int_intern.intern(Interval::top()).into(),
                        ],
                        &mut int_merge,
                    );
                }
                Phi(block, lhs, rhs) => {
                    let factors = &ctxs.phi_factors[&block];
                    let lhs_factor = factors[0];
                    let rhs_factor = factors[1];

                    let mut new = vec![];
                    for (row1, _) in iz.rows() {
                        if row1[0] == lhs {
                            for (row2, _) in iz.rows() {
                                if row2[0] == rhs {
                                    let join_iz =
                                        IsZero::from(row1[2]).join(&IsZero::from(row2[2]));
                                    let prov = joint_use(
                                        factor(lhs_factor, row1[1]),
                                        factor(rhs_factor, row2[1]),
                                    );
                                    new.push([term_id, prov, join_iz.into()]);
                                }
                            }
                        }
                    }

                    for new_row in new {
                        iz.insert(&new_row, &mut iz_merge);
                    }

                    let mut new = vec![];
                    for (row1, _) in int.rows() {
                        if row1[0] == lhs {
                            for (row2, _) in int.rows() {
                                if row2[0] == rhs {
                                    let join_int = int_intern.union()(row1[2], row2[2]);
                                    let prov = joint_use(
                                        factor(lhs_factor, row1[1]),
                                        factor(rhs_factor, row2[1]),
                                    );
                                    new.push([term_id, prov, join_int.into()]);
                                }
                            }
                        }
                    }

                    for new_row in new {
                        int.insert(&new_row, &mut int_merge);
                    }
                }
                Unary(op, input) => {
                    let mut new = vec![];
                    for (row, _) in iz.rows() {
                        if row[0] == input {
                            new.push([
                                term_id,
                                row[1],
                                IsZero::from(row[2]).forward_unary(op).into(),
                            ])
                        } else if row[0] == term_id {
                            new.push([
                                input,
                                row[1],
                                IsZero::from(row[2]).backward_unary(op).into(),
                            ]);
                        }
                    }

                    for new_row in new {
                        iz.insert(&new_row, &mut iz_merge);
                    }

                    let mut new = vec![];
                    for (row, _) in int.rows() {
                        if row[0] == input {
                            new.push([term_id, row[1], int_intern.forward_unary()(row[2], op)])
                        }
                    }

                    for new_row in new {
                        int.insert(&new_row, &mut int_merge);
                    }
                }
                Binary(op, lhs, rhs) => {
                    let mut new = vec![];
                    for (row1, _) in iz.rows() {
                        if row1[0] == lhs {
                            for (row2, _) in iz.rows() {
                                if row2[0] == rhs {
                                    new.push([
                                        term_id,
                                        joint_use(row1[1], row2[1]),
                                        IsZero::from(row1[2])
                                            .forward_binary(&IsZero::from(row2[2]), op)
                                            .into(),
                                    ])
                                }
                            }
                        }
                    }

                    for new_row in new {
                        iz.insert(&new_row, &mut iz_merge);
                    }

                    let mut new = vec![];
                    for (row1, _) in int.rows() {
                        if row1[0] == lhs {
                            for (row2, _) in int.rows() {
                                if row2[0] == rhs {
                                    new.push([
                                        term_id,
                                        joint_use(row1[1], row2[1]),
                                        int_intern.forward_binary()(row1[2], row2[2], op),
                                    ])
                                }
                            }
                        }
                    }

                    for new_row in new {
                        int.insert(&new_row, &mut int_merge);
                    }

                    let mut new = vec![];
                    if op == BinaryOp::LT {
                        for (iz_row, _) in iz.rows() {
                            if iz_row[0] == term_id && IsZero::from(iz_row[2]).leq(&IsZero::NotZero)
                            {
                                for (rhs_row, _) in int.rows() {
                                    if rhs_row[0] == rhs {
                                        let high = int_intern.get(rhs_row[2].into()).high;
                                        new.push([
                                            lhs,
                                            joint_use(iz_row[1], rhs_row[1]),
                                            int_intern.intern(Interval::high(high - 1)).into(),
                                        ]);
                                    }
                                }
                            } else if iz_row[0] == term_id
                                && IsZero::from(iz_row[2]).leq(&IsZero::Zero)
                            {
                                for (rhs_row, _) in int.rows() {
                                    if rhs_row[0] == rhs {
                                        let low = int_intern.get(rhs_row[2].into()).low;
                                        new.push([
                                            lhs,
                                            joint_use(iz_row[1], rhs_row[1]),
                                            int_intern.intern(Interval::low(low)).into(),
                                        ]);
                                    }
                                }
                            }
                        }
                    }

                    for new_row in new {
                        int.insert(&new_row, &mut int_merge);
                    }
                }
                Call(sym, args) => {}
                Tombstone => {}
            }
        }

        for (row, _) in iz.rows() {
            if IsZero::from(row[2]) == IsZero::Zero {
                int.insert(
                    &[row[0], row[1], int_intern.intern(Interval::from(0)).into()],
                    &mut int_merge,
                );
            }
        }

        propagate(&mut iz, &mut iz_merge);
        propagate(&mut int, &mut int_merge);
    }

    for (row, _) in iz.rows() {
        let Some(block_id) = ctxs
            .block_provs
            .iter()
            .filter(|(_, prov)| **prov == row[1])
            .map(|(block, _)| *block)
            .min()
        else {
            continue;
        };

        println!("{}: {:?} @ {}", row[0], IsZero::from(row[2]), block_id);
    }

    for (row, _) in int.rows() {
        let Some(block_id) = ctxs
            .block_provs
            .iter()
            .filter(|(_, prov)| **prov == row[1])
            .map(|(block, _)| *block)
            .min()
        else {
            continue;
        };

        println!(
            "{}: {:?} @ {}",
            row[0],
            int_intern.get(row[2].into()),
            block_id
        );
    }

    for (exit, root) in &ssa.roots {
        let prov = ctxs.block_provs[exit];
        let mut agg = IsZero::Top;
        for (row, _) in iz.rows() {
            if row[0] == *root && leq(prov, row[1]) {
                agg = agg.meet(&IsZero::from(row[2]));
            }
        }
        println!("Root {} at exit {}: {:?}", root, exit, agg);
    }

    for (exit, root) in &ssa.roots {
        let prov = ctxs.block_provs[exit];
        let mut agg = Interval::top();
        for (row, _) in int.rows() {
            if row[0] == *root && leq(prov, row[1]) {
                agg = agg.intersect(&int_intern.get(row[2].into()));
            }
        }
        println!("Root {} at exit {}: {:?}", root, exit, agg);
    }
}
