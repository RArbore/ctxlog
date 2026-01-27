use std::collections::HashMap;

use crate::ast::Symbol;
use crate::cfg::{BlockId, DomTree};
use crate::ssa::{SSA, SSAValue, SSAValueId};
use crate::table::{Table, Value};

pub type Provenance = Value;

pub fn mk_prov(id: u32) -> Provenance {
    assert!((id as usize) < size_of::<Provenance>() * 8);
    1 << id
}

pub fn root_prov() -> Provenance {
    0
}

pub fn joint_use(a: Provenance, b: Provenance) -> Provenance {
    a | b
}

pub fn leq(a: Provenance, b: Provenance) -> bool {
    factor(a, b) == 0
}

pub fn factor(a: Provenance, b: Provenance) -> Provenance {
    !a & b
}

pub fn propagate<M>(table: &mut Table, merge: &mut M)
where
    M: FnMut(Value, Value) -> Value,
{
    let prov_column = table.num_determinant() - 1;
    let lat_column = table.num_determinant();

    let mut to_modify = HashMap::new();
    loop {
        for (row1, id) in table.rows() {
            let prov1 = row1[prov_column];
            let lat1 = row1[lat_column];
            let mut total_merged = lat1;
            for (row2, _) in table.rows() {
                let prov2 = row2[prov_column];
                if &row1[0..prov_column] == &row2[0..prov_column] && leq(prov1, prov2) {
                    let lat2 = row2[lat_column];
                    total_merged = merge(total_merged, lat2);
                }
            }

            let mut action = if total_merged != lat1 {
                Some(Some(total_merged))
            } else {
                None
            };
            for (row2, _) in table.rows() {
                let prov2 = row2[prov_column];
                if &row1[0..prov_column] == &row2[0..prov_column]
                    && leq(prov1, prov2)
                    && prov1 != prov2
                {
                    let lat2 = row2[lat_column];
                    if lat2 == merge(lat2, total_merged) {
                        action = Some(None);
                        break;
                    }
                }
            }

            if let Some(action) = action {
                to_modify.insert(id, action);
            }
        }

        if to_modify.is_empty() {
            break;
        } else {
            for (id, action) in to_modify.drain() {
                if let Some(new) = action {
                    table.write_dependent(id, new);
                } else {
                    table.delete(id);
                }
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct FlowContexts {
    pub contexts: Vec<SSAValueId>,
    pub block_provs: HashMap<BlockId, Provenance>,
    pub phi_factors: HashMap<BlockId, Vec<Provenance>>,
}

pub fn flow_contexts(ssa: &SSA, dom: &DomTree) -> FlowContexts {
    let mut ctx = FlowContexts::default();
    let mut value_to_prov = HashMap::new();
    for (_, preds) in &ssa.cfg {
        for (_, cond) in preds {
            if ssa.terms[*cond as usize] == SSAValue::Constant(1) {
                value_to_prov.insert(*cond, root_prov());
            } else {
                let prov = mk_prov(ctx.contexts.len() as u32);
                ctx.contexts.push(*cond);
                value_to_prov.insert(*cond, prov);
            }
        }
    }

    ctx.block_provs.insert(0, root_prov());
    for (block, _) in &ssa.cfg {
        let mut prov = root_prov();
        let mut cursor = block;
        while let Some(pred) = dom.idom.get(&cursor) {
            let preds = &ssa.cfg[&cursor];
            if preds.len() == 1 && preds[0].0 == *pred {
                let cond = preds[0].1;
                prov = joint_use(prov, value_to_prov[&cond]);
            }

            if let Some(pred_prov) = ctx.block_provs.get(pred) {
                prov = joint_use(prov, *pred_prov);
                break;
            }

            cursor = pred;
        }
        ctx.block_provs.insert(*block, prov);
    }

    for (block, preds) in &ssa.cfg {
        if preds.len() > 1 {
            assert_eq!(preds.len(), 2);
            let phi_factors = ctx.phi_factors.entry(*block).or_default();
            for (pred, cond) in preds {
                let prov = joint_use(ctx.block_provs[pred], value_to_prov[cond]);
                phi_factors.push(prov);
            }
        }
    }

    ctx
}

#[derive(Debug, Default)]
pub struct CallContexts {
    pub contexts: HashMap<(Symbol, SSAValueId), Provenance>,
}

pub fn call_contexts(ssa: &SSA) -> CallContexts {
    todo!()
}
