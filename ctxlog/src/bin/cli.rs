use std::io::{Read, Result, stdin};
use std::process::Command;

use string_interner::symbol::Symbol as _;
use tempfile::NamedTempFile;

use ctxlog::ast::NameInterner;
use ctxlog::cfg::dominator;
use ctxlog::grammar::ProgramParser;
use ctxlog::interner::Interner;
use ctxlog::lattice::{Interval, IsZero};
use ctxlog::provenance::{
    CallContexts, FlowContexts, call_contexts, factor, flow_contexts, joint_use, leq, mk_prov,
    propagate, root_prov,
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
    let call = call_contexts(&ssas);

    analysis(&ssas, &flows, &call);

    let mut tmp = NamedTempFile::new().unwrap();
    ssa_to_dot(&ssas, &mut tmp)?;
    println!("Drawing {}", tmp.path().display());
    Command::new("xdot").arg(tmp.path()).status().unwrap();

    Ok(())
}

fn analysis(ssas: &[SSA], flows: &[FlowContexts], call: &CallContexts) {
    assert_eq!(ssas.len(), flows.len());
    let num_funcs = ssas.len();

    let int_intern = Interner::new();
    let mut iz = Table::new(3);
    let mut int = Table::new(3);
    let mut iz_merge = |iz1, iz2| Value::from(IsZero::from(iz1).meet(&IsZero::from(iz2)));
    let mut int_merge = int_intern.intersect();

    for func in 0..num_funcs {
        let name = ssas[func].name;
        let flow = &flows[func];
        for (idx, cond) in flow.contexts.iter().enumerate() {
            iz.insert(
                &[
                    name.into(),
                    (*cond).into(),
                    mk_prov(idx as u32).into(),
                    IsZero::NotZero.into(),
                ],
                &mut iz_merge,
            );
        }
    }

    for _ in 0..100 {
        for func in 0..num_funcs {
            let name = ssas[func].name;
            let ssa = &ssas[func];
            let flow = &flows[func];
            for (term_id, term) in ssa.terms() {
                use SSAValue::*;
                match term {
                    Constant(0) => {
                        iz.insert(
                            &[
                                name.into(),
                                term_id.into(),
                                root_prov().into(),
                                IsZero::Zero.into(),
                            ],
                            &mut iz_merge,
                        );
                        int.insert(
                            &[
                                name.into(),
                                term_id.into(),
                                root_prov().into(),
                                int_intern.intern(Interval::from(0)).into(),
                            ],
                            &mut int_merge,
                        );
                    }
                    Constant(c) => {
                        iz.insert(
                            &[
                                name.into(),
                                term_id.into(),
                                root_prov().into(),
                                IsZero::NotZero.into(),
                            ],
                            &mut iz_merge,
                        );
                        int.insert(
                            &[
                                name.into(),
                                term_id.into(),
                                root_prov().into(),
                                int_intern.intern(Interval::from(c)).into(),
                            ],
                            &mut int_merge,
                        );
                    }
                    Param(_) => {
                        iz.insert(
                            &[
                                name.into(),
                                term_id.into(),
                                root_prov().into(),
                                IsZero::Top.into(),
                            ],
                            &mut iz_merge,
                        );
                        int.insert(
                            &[
                                name.into(),
                                term_id.into(),
                                root_prov().into(),
                                int_intern.intern(Interval::top()).into(),
                            ],
                            &mut int_merge,
                        );
                    }
                    Phi(block, lhs, rhs) => {
                        let factors = &flow.phi_factors[&block];
                        let lhs_factor = factors[0];
                        let rhs_factor = factors[1];

                        let mut new = vec![];
                        for (row1, _) in iz.rows() {
                            if row1[1] == lhs.into() && row1[0] == name.into() {
                                for (row2, _) in iz.rows() {
                                    if row2[1] == rhs.into() && row2[0] == name.into() {
                                        let join_iz =
                                            IsZero::from(row1[3]).join(&IsZero::from(row2[3]));
                                        let prov = joint_use(
                                            factor(lhs_factor, row1[2].into()),
                                            factor(rhs_factor, row2[2].into()),
                                        );
                                        new.push([
                                            name.into(),
                                            term_id.into(),
                                            prov.into(),
                                            join_iz.into(),
                                        ]);
                                    }
                                }
                            }
                        }

                        for new_row in new {
                            iz.insert(&new_row, &mut iz_merge);
                        }

                        let mut new = vec![];
                        for (row1, _) in int.rows() {
                            if row1[1] == lhs.into() && row1[0] == name.into() {
                                for (row2, _) in int.rows() {
                                    if row2[1] == rhs.into() && row2[0] == name.into() {
                                        let join_int = int_intern.union()(row1[3], row2[3]);
                                        let prov = joint_use(
                                            factor(lhs_factor, row1[2].into()),
                                            factor(rhs_factor, row2[2].into()),
                                        );
                                        new.push([
                                            name.into(),
                                            term_id.into(),
                                            prov.into(),
                                            join_int.into(),
                                        ]);
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
                            if row[1] == input.into() && row[0] == name.into() {
                                new.push([
                                    name.into(),
                                    term_id.into(),
                                    row[2],
                                    IsZero::from(row[3]).forward_unary(op).into(),
                                ])
                            } else if row[1] == term_id.into() && row[0] == name.into() {
                                new.push([
                                    name.into(),
                                    input.into(),
                                    row[2],
                                    IsZero::from(row[3]).backward_unary(op).into(),
                                ]);
                            }
                        }

                        for new_row in new {
                            iz.insert(&new_row, &mut iz_merge);
                        }

                        let mut new = vec![];
                        for (row, _) in int.rows() {
                            if row[1] == input.into() && row[0] == name.into() {
                                new.push([
                                    name.into(),
                                    term_id.into(),
                                    row[2],
                                    int_intern.forward_unary()(row[3], op),
                                ])
                            }
                        }

                        for new_row in new {
                            int.insert(&new_row, &mut int_merge);
                        }
                    }
                    Binary(op, lhs, rhs) => {
                        let mut new = vec![];
                        for (row1, _) in iz.rows() {
                            if row1[1] == lhs.into() && row1[0] == name.into() {
                                for (row2, _) in iz.rows() {
                                    if row2[1] == rhs.into() && row2[0] == name.into() {
                                        new.push([
                                            name.into(),
                                            term_id.into(),
                                            joint_use(row1[2].into(), row2[2].into()).into(),
                                            IsZero::from(row1[3])
                                                .forward_binary(&IsZero::from(row2[3]), op)
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
                            if row1[1] == lhs.into() && row1[0] == name.into() {
                                for (row2, _) in int.rows() {
                                    if row2[1] == rhs.into() && row2[0] == name.into() {
                                        new.push([
                                            name.into(),
                                            term_id.into(),
                                            joint_use(row1[2].into(), row2[2].into()).into(),
                                            int_intern.forward_binary()(row1[3], row2[3], op),
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
                                if iz_row[1] == term_id.into()
                                    && IsZero::from(iz_row[3]).leq(&IsZero::NotZero)
                                    && iz_row[0] == name.into()
                                {
                                    for (rhs_row, _) in int.rows() {
                                        if rhs_row[1] == rhs.into() && rhs_row[0] == name.into() {
                                            let high = int_intern.get(rhs_row[3].into()).high;
                                            new.push([
                                                name.into(),
                                                lhs.into(),
                                                joint_use(iz_row[2].into(), rhs_row[2].into())
                                                    .into(),
                                                int_intern.intern(Interval::high(high - 1)).into(),
                                            ]);
                                        }
                                    }
                                } else if iz_row[1] == term_id.into()
                                    && IsZero::from(iz_row[3]).leq(&IsZero::Zero)
                                    && iz_row[0] == name.into()
                                {
                                    for (rhs_row, _) in int.rows() {
                                        if rhs_row[1] == rhs.into() && rhs_row[0] == name.into() {
                                            let low = int_intern.get(rhs_row[3].into()).low;
                                            new.push([
                                                name.into(),
                                                lhs.into(),
                                                joint_use(iz_row[2].into(), rhs_row[2].into())
                                                    .into(),
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
                if IsZero::from(row[3]) == IsZero::Zero {
                    int.insert(
                        &[
                            row[0],
                            row[1],
                            row[2],
                            int_intern.intern(Interval::from(0)).into(),
                        ],
                        &mut int_merge,
                    );
                }
            }
        }

        propagate(&mut iz, &mut iz_merge);
        propagate(&mut int, &mut int_merge);
    }

    for func in 0..num_funcs {
        let name = ssas[func].name;
        let ssa = &ssas[func];
        let flow = &flows[func];
        println!("Function {}", name.to_usize());

        for (row, _) in iz.rows() {
            if row[0] == name.into() {
                let Some(block_id) = flow
                    .block_provs
                    .iter()
                    .filter(|(_, prov)| **prov == row[2].into())
                    .map(|(block, _)| *block)
                    .min()
                else {
                    continue;
                };

                println!("{}: {:?} @ {}", row[1].0, IsZero::from(row[3]), block_id);
            }
        }

        for (row, _) in int.rows() {
            if row[0] == name.into() {
                let Some(block_id) = flow
                    .block_provs
                    .iter()
                    .filter(|(_, prov)| **prov == row[2].into())
                    .map(|(block, _)| *block)
                    .min()
                else {
                    continue;
                };

                println!(
                    "{}: {:?} @ {}",
                    row[1].0,
                    int_intern.get(row[3].into()),
                    block_id
                );
            }
        }

        for (exit, root) in &ssa.roots {
            let prov = flow.block_provs[exit];
            let mut agg = IsZero::Top;
            for (row, _) in iz.rows() {
                if row[1] == (*root).into() && leq(prov, row[2].into()) && row[0] == name.into() {
                    agg = agg.meet(&IsZero::from(row[3]));
                }
            }
            println!("Root {} at exit {}: {:?}", root, exit, agg);
        }

        for (exit, root) in &ssa.roots {
            let prov = flow.block_provs[exit];
            let mut agg = Interval::top();
            for (row, _) in int.rows() {
                if row[1] == (*root).into() && leq(prov, row[2].into()) && row[0] == name.into() {
                    agg = agg.intersect(&int_intern.get(row[3].into()));
                }
            }
            println!("Root {} at exit {}: {:?}", root, exit, agg);
        }
    }
}
