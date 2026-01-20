#[cfg(test)]
mod tests {
    use crate::provenance::*;
    use crate::table::Table;

    #[test]
    fn abc_example() {
        let mut a = Table::new(2);
        let mut b = Table::new(3);
        let mut c = Table::new(3);

        a.insert(&[1, make_provenance(0)]);
        a.insert(&[2, make_provenance(1)]);
        a.insert(&[3, make_provenance(2)]);

        for row1 in a.rows() {
            b.insert(&[row1[0], row1[0], row1[1]]);
            for row2 in a.rows() {
                c.insert(&[row1[0], row2[0], joint_use(row1[1], row2[1])]);
            }
        }
        assert_eq!(b.num_rows(), 3);
        assert_eq!(c.num_rows(), 9);

        for row in c.rows() {
            if let Some(factor) = factor(make_provenance(1), row[2]) {
                b.insert(&[row[0], row[1], factor]);
            }
        }
        assert_eq!(b.num_rows(), 8);

        assert!(b.probe(&[3, 2, make_provenance(2)]).is_some());

        assert!(b.probe(&[2, 2, 0]).is_some());
        assert!(b.probe(&[2, 2, make_provenance(0)]).is_none());
        assert!(b.probe(&[2, 2, make_provenance(1)]).is_some());
        assert!(b.probe(&[2, 2, make_provenance(2)]).is_none());
    }
}
