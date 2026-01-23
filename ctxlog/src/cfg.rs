use core::cmp::min;
use std::collections::{BTreeMap, BTreeSet};

use crate::provenance::{Provenance, joint_use, mk_prov, root_prov};
use crate::ssa::{SSA, SSAValue, SSAValueId};

pub type BlockId = u32;
pub type CFG = BTreeMap<BlockId, Vec<(BlockId, SSAValueId)>>;

fn po(cfg: &CFG) -> Vec<BlockId> {
    let mut succs: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();

    succs.entry(0).or_default();
    for (block, preds) in cfg {
        succs.entry(*block).or_default();
        for (pred, _) in preds {
            succs.entry(*pred).or_default().push(*block);
        }
    }

    let mut po = vec![];
    let mut visited = BTreeSet::new();
    po_helper(0, &succs, &mut visited, &mut po);
    po
}

pub fn rpo(cfg: &CFG) -> Vec<BlockId> {
    let mut rpo = po(cfg);
    rpo.reverse();
    rpo
}

fn po_helper(
    block: BlockId,
    succs: &BTreeMap<BlockId, Vec<BlockId>>,
    visited: &mut BTreeSet<BlockId>,
    po: &mut Vec<BlockId>,
) {
    visited.insert(block);

    for succ in &succs[&block] {
        if !visited.contains(succ) {
            po_helper(*succ, succs, visited, po);
        }
    }

    po.push(block);
}

pub fn back_edges(rpo: &[BlockId], cfg: &CFG) -> BTreeSet<(BlockId, BlockId)> {
    let mut visited = BTreeSet::new();
    let mut back_edges = BTreeSet::new();

    visited.insert(0);
    for block in &rpo[1..] {
        visited.insert(*block);
        for (pred, _) in &cfg[block] {
            if !visited.contains(pred) {
                back_edges.insert((*pred, *block));
            }
        }
    }

    back_edges
}

#[derive(Debug)]
pub struct DomTree {
    pub idom: BTreeMap<BlockId, BlockId>,
    pub level: BTreeMap<BlockId, u32>,
}

pub fn dominator(cfg: &CFG) -> DomTree {
    let mut succs: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    succs.entry(0).or_default();
    for (block, preds) in cfg {
        succs.entry(*block).or_default();
        for (pred, _) in preds {
            succs.entry(*pred).or_default().push(*block);
        }
    }

    let mut preorder = vec![];
    let mut parents: BTreeMap<BlockId, BlockId> = BTreeMap::new();
    let mut stack = vec![(0, None)];
    while let Some((block, parent)) = stack.pop() {
        if parents.contains_key(&block) {
            continue;
        }

        if let Some(parent) = parent {
            parents.insert(block, parent);
        }

        preorder.push(block);

        stack.extend(succs[&block].iter().map(|succ| (*succ, Some(block))));
    }
    let block_nums: BTreeMap<_, _> = preorder
        .iter()
        .enumerate()
        .map(|(num, block)| (*block, num))
        .collect();

    let mut sdom = vec![0; preorder.len()];
    let mut ancestors = vec![0; preorder.len()];
    let mut labels: Vec<_> = (0..preorder.len()).collect();
    let mut idom = BTreeMap::new();
    for block in preorder[1..].iter() {
        idom.insert(*block, parents[block]);
    }

    for block_num in (1..preorder.len()).rev() {
        sdom[block_num] = block_num;
        for (pred, _) in &cfg[&preorder[block_num]] {
            let pred_num = block_nums[pred];
            semi_nca_compress(pred_num, &mut ancestors, &mut labels);
            sdom[block_num] = min(sdom[block_num], labels[pred_num]);
        }
        labels[block_num] = sdom[block_num];
        ancestors[block_num] = block_nums[&parents[&preorder[block_num]]];
    }

    for (block_num, block) in preorder.iter().enumerate().skip(1) {
        while block_nums[&idom[block]] > sdom[block_num] {
            idom.insert(*block, idom[&idom[block]]);
        }
    }

    let mut level = BTreeMap::new();
    level.insert(0, 0);
    while level.len() != preorder.len() {
        for (block, idom) in &idom {
            if let Some(idom_level) = level.get(idom) {
                level.insert(*block, idom_level + 1);
            }
        }
    }

    DomTree { idom, level }
}

fn semi_nca_compress(block_num: usize, ancestors: &mut Vec<usize>, labels: &mut Vec<usize>) {
    let ancestor = ancestors[block_num];
    if ancestor != 0 {
        semi_nca_compress(ancestor, ancestors, labels);
        if labels[ancestor] < labels[block_num] {
            labels[block_num] = labels[ancestor];
        }
        ancestors[block_num] = ancestors[ancestor];
    }
}

#[derive(Debug, Default)]
pub struct DomContexts {
    pub contexts: Vec<SSAValueId>,
    pub phi_factors: BTreeMap<BlockId, Vec<Provenance>>,
}

pub fn compute_contexts(ssa: &SSA, dom: &DomTree) -> DomContexts {
    let mut ctx = DomContexts::default();
    let mut value_to_prov = BTreeMap::new();
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

    for (block, preds) in &ssa.cfg {
        if preds.len() > 1 {
            let phi_factors = ctx.phi_factors.entry(*block).or_default();
            for (pred, cond) in preds {
                let mut prov = value_to_prov[cond];
                let mut cursor = pred;
                while let Some(pred) = dom.idom.get(&cursor) {
                    let preds = &ssa.cfg[&cursor];
                    if preds.len() == 1 && preds[0].0 == *pred {
                        let cond = preds[0].1;
                        prov = joint_use(prov, value_to_prov[&cond]);
                    }
                    cursor = pred;
                }
                phi_factors.push(prov);
            }
        }
    }

    ctx
}
