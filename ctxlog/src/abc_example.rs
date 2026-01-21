#[cfg(test)]
mod tests {
    use crate::provenance::*;
    use crate::table::Table;

    #[test]
    fn abc_example() {
        let mut a = Table::new(2);
        let mut b = Table::new(3);
        let mut c = Table::new(3);
        let mut merge = |_, _| 0;

        a.insert(&[1, make_provenance(0), 0], &mut merge);
        a.insert(&[2, make_provenance(1), 0], &mut merge);
        a.insert(&[3, make_provenance(2), 0], &mut merge);

        for (row1, _) in a.rows() {
            b.insert(&[row1[0], row1[0], row1[1], 0], &mut merge);
            for (row2, _) in a.rows() {
                c.insert(
                    &[row1[0], row2[0], joint_use(row1[1], row2[1]), 0],
                    &mut merge,
                );
            }
        }
        assert_eq!(b.num_rows(), 3);
        assert_eq!(c.num_rows(), 9);

        for (row, _) in c.rows() {
            b.insert(
                &[row[0], row[1], factor(make_provenance(1), row[2]), 0],
                &mut merge,
            );
        }
        assert_eq!(b.num_rows(), 10);

        assert!(b.get(&[3, 2, make_provenance(2)]).is_some());

        assert!(b.get(&[2, 2, 0]).is_some());
        assert!(b.get(&[2, 2, make_provenance(0)]).is_none());
        assert!(b.get(&[2, 2, make_provenance(1)]).is_some());
        assert!(b.get(&[2, 2, make_provenance(2)]).is_none());

        assert!(b.get(&[1, 3, joint_use(make_provenance(0), make_provenance(2))]).is_some());
        assert!(b.get(&[3, 1, joint_use(make_provenance(0), make_provenance(2))]).is_some());
    }
}
