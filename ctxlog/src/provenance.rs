use std::collections::HashMap;

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
