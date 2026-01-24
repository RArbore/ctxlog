use std::io::{Read, Result, stdin};
use std::process::Command;

use tempfile::NamedTempFile;

use ctxlog::ast::Interner;
use ctxlog::cfg::{DomContexts, compute_contexts, dominator};
use ctxlog::grammar::ProgramParser;
use ctxlog::lattice::IsZero;
use ctxlog::provenance::{factor, joint_use, mk_prov, propagate, root_prov};
use ctxlog::ssa::{SSA, SSAValue, dce, naive_ssa_translation, ssa_to_dot};
use ctxlog::table::{Table, Value};

pub fn main() -> Result<()> {
    let mut interner = Interner::new();

    let mut imp_program = String::new();
    stdin().read_to_string(&mut imp_program)?;
    let ast = ProgramParser::new()
        .parse(&mut interner, &imp_program)
        .unwrap();

    for func in &ast.funcs {
        let mut terms = naive_ssa_translation(func);
        dce(&mut terms);
        let dom = dominator(&terms.cfg);
        let ctxs = compute_contexts(&terms, &dom);
        analysis(&terms, &ctxs);
        let mut tmp = NamedTempFile::new().unwrap();
        ssa_to_dot(&terms, &mut tmp)?;
        Command::new("xdot").arg(tmp.path()).status().unwrap();
    }

    Ok(())
}

fn analysis(ssa: &SSA, ctxs: &DomContexts) {
    let mut iz = Table::new(2);
    let mut merge = |iz1, iz2| Value::from(IsZero::from(iz1).meet(&IsZero::from(iz2)));

    for (idx, cond) in ctxs.contexts.iter().enumerate() {
        iz.insert(
            &[*cond, mk_prov(idx as u32), IsZero::NotZero.into()],
            &mut merge,
        );
    }

    for _ in 0..100 {
        for (term_id, term) in ssa.terms() {
            use SSAValue::*;
            match term {
                Constant(0) => {
                    iz.insert(&[term_id, root_prov(), IsZero::Zero.into()], &mut merge);
                }
                Constant(_) => {
                    iz.insert(&[term_id, root_prov(), IsZero::NotZero.into()], &mut merge);
                }
                Param(_) => {
                    iz.insert(&[term_id, root_prov(), IsZero::Top.into()], &mut merge);
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
                        iz.insert(&new_row, &mut merge);
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
                        iz.insert(&new_row, &mut merge);
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
                        iz.insert(&new_row, &mut merge);
                    }
                }
                Tombstone => {}
            }
        }

        propagate(&mut iz, &mut merge);
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
}
