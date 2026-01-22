#[cfg(test)]
mod tests {
    use crate::lattice::IsZero;
    use crate::provenance::*;
    use crate::table::{Table, Value};
    use crate::ssa::UnaryOp;

    #[test]
    fn flow_example() {
        // Consider the following SSA program:
        //
        // v1 = Top                  entry
        // v2 = Not(v1)            v1 / \ v2
        // v3 = Phi_J(v1, v2)         \ /
        //                             J
        // A flow sensitive analysis in the is-zero lattice could be expressed like:
        //
        // IZ(1, Top) :-
        // IZ(2, forward_not(iz)) :- IZ(1, iz)
        // IZ(1, backward_not(iz)) :- IZ(2, iz)
        // IZ(3, join(iz1, iz2)) :- (IZ(1, NotZero) -> IZ(2, iz1)), (IZ(2, NotZero) -> IZ(1, iz2))
        //
        // We want the user to explicitly give contexts to reason under, so make labels explicit like:
        //
        // IZ(1, Top) :-
        // IZ(2, not(iz)) :- IZ(1, iz)
        // IZ(1, not(iz)) :- IZ(2, iz)
        // IZ(3, join(iz1, iz2)) :- (x -> IZ(2, iz1)), (y -> IZ(1, iz2))
        // where IZ(1, NotZero) :- x and IZ(2, NotZero) :- y

        let mut iz = Table::new(2);
        let mut merge = |iz1, iz2| Value::from(IsZero::from(iz1).meet(&IsZero::from(iz2)));

        let x = mk_prov(0);
        let y = mk_prov(1);
        iz.insert(&[1, root_prov(), IsZero::Top.into()], &mut merge);
        iz.insert(&[1, x, IsZero::NotZero.into()], &mut merge);
        iz.insert(&[2, y, IsZero::NotZero.into()], &mut merge);

        let mut new = vec![];
        for (row, _) in iz.rows() {
            let not = IsZero::from(row[2]).forward_unary(UnaryOp::Not);
            let dst = if row[0] == 1 { 2 } else { 1 };
            new.push([dst, row[1], not.into()]);
        }
        for new_row in new {
            iz.insert(&new_row, &mut merge);
        }

        let mut new = vec![];
        for (row1, _) in iz.rows() {
            for (row2, _) in iz.rows() {
                if row1[0] == 2 && row2[0] == 1 {
                    let join_iz = IsZero::from(row1[2]).join(&IsZero::from(row2[2]));
                    let prov = joint_use(factor(x, row1[1]), factor(y, row2[1]));
                    new.push([3, prov, join_iz.into()]);
                }
            }
        }
        for new_row in new {
            iz.insert(&new_row, &mut merge);
        }
        assert_eq!(iz.get(&[3, root_prov()]), Some(IsZero::Zero.into()));

        propagate(&mut iz, &mut merge);
        assert_eq!(iz.get(&[3, root_prov()]), Some(IsZero::Zero.into()));
        assert_eq!(iz.get(&[3, joint_use(x, y)]), Some(IsZero::Bottom.into()));
    }
}
