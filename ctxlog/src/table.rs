use core::hash::Hasher;
use core::mem::replace;
use std::collections::BTreeSet;
use std::collections::btree_set::Iter;
use std::iter::Peekable;

use hashbrown::HashTable;
use hashbrown::hash_table::Entry;
use rustc_hash::FxHasher;

pub type Value = u32;
type RowId = u64;
type HashCode = u64;

#[derive(Debug)]
struct TableEntry {
    hash: HashCode,
    row: RowId,
}

#[derive(Debug)]
struct Rows {
    buffer: Vec<Value>,
    num_columns: usize,
}

#[derive(Debug)]
pub struct Table {
    rows: Rows,
    table: HashTable<TableEntry>,
    deleted_rows: BTreeSet<RowId>,
    changed: bool,
}

#[derive(Debug)]
struct TableRows<'a> {
    table: &'a Table,
    row: RowId,
    deleted_iter: Peekable<Iter<'a, RowId>>,
}

fn hash(row: &[Value]) -> HashCode {
    let mut hasher = FxHasher::default();
    for val in row {
        hasher.write_u32(*val);
    }
    hasher.finish()
}

impl Rows {
    fn num_rows(&self) -> RowId {
        (self.buffer.len() / self.num_columns) as RowId
    }

    fn get_row(&self, row: RowId) -> &[Value] {
        let start = (row as usize) * self.num_columns;
        &self.buffer[start..start + self.num_columns]
    }

    fn add_row(&mut self, row: &[Value]) -> RowId {
        let row_id = self.num_rows();
        self.buffer.extend(row);
        row_id
    }
}

impl Table {
    pub fn new(num_columns: usize) -> Self {
        Self {
            rows: Rows {
                buffer: vec![],
                num_columns,
            },
            table: HashTable::new(),
            deleted_rows: BTreeSet::new(),
            changed: false,
        }
    }

    pub fn num_columns(&self) -> usize {
        self.rows.num_columns
    }

    pub fn check_changed(&mut self) -> bool {
        replace(&mut self.changed, false)
    }

    pub fn insert(&mut self, row: &[Value]) -> RowId {
        let num_columns = self.rows.num_columns;
        assert_eq!(row.len(), num_columns);
        let hash = hash(row);
        let entry = self.table.entry(
            hash,
            |te| te.hash == hash && self.rows.get_row(te.row) == row,
            |te| te.hash,
        );
        match entry {
            Entry::Occupied(occupied) => {
                occupied.get().row
            }
            Entry::Vacant(vacant) => {
                let row_id = self.rows.add_row(row);
                vacant.insert(TableEntry { hash, row: row_id });
                self.changed = true;
                row_id
            }
        }
    }

    pub fn probe(&self, row: &[Value]) -> Option<RowId> {
        let num_columns = self.rows.num_columns;
        assert_eq!(row.len(), num_columns);
        let hash = hash(row);
        let te = self.table
            .find(hash, |te| {
                te.hash == hash && self.rows.get_row(te.row) == row
            });
        te.map(|te| te.row)
    }

    pub fn delete(&mut self, row_id: RowId) -> &[Value] {
        let row = self.rows.get_row(row_id);
        let hash = hash(row);
        let entry = self
            .table
            .entry(hash, |te| te.hash == hash && te.row == row_id, |te| te.hash);
        let Entry::Occupied(occupied) = entry else {
            panic!();
        };
        occupied.remove();
        self.deleted_rows.insert(row_id);
        self.changed = true;
        row
    }

    pub fn rows(&self) -> impl Iterator<Item = (&[Value], RowId)> + '_ {
        TableRows {
            table: self,
            row: 0,
            deleted_iter: self.deleted_rows.iter().peekable(),
        }
    }

    pub fn num_rows(&self) -> RowId {
        self.rows.num_rows() - self.deleted_rows.len() as RowId
    }
}

impl<'a> Iterator for TableRows<'a> {
    type Item = (&'a [Value], RowId);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(recent_deleted) = self.deleted_iter.peek() {
            if **recent_deleted > self.row {
                break;
            } else if **recent_deleted == self.row {
                self.row += 1;
            }
            self.deleted_iter.next();
        }

        if self.row >= self.table.rows.num_rows() {
            None
        } else {
            let row = self.row;
            self.row += 1;
            Some((self.table.rows.get_row(row), row))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_table() {
        let mut table = Table::new(2);
        let id1 = table.insert(&[1, 2]);
        let id2 = table.insert(&[1, 3]);
        assert!(table.probe(&[1, 2]) == Some(id1));
        assert!(table.probe(&[1, 3]) == Some(id2));
        assert!(table.probe(&[1, 4]).is_none());
        assert_eq!(table.delete(id2), &[1, 3]);
        let id3 = table.insert(&[1, 4]);
        assert!(table.probe(&[1, 2]) == Some(id1));
        assert!(table.probe(&[1, 3]).is_none());
        assert!(table.probe(&[1, 4]) == Some(id3));
    }
}
