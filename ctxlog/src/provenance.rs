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
