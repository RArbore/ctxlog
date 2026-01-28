use core::hash::Hasher;
use core::mem::replace;
use std::collections::BTreeSet;
use std::collections::btree_set::Iter;
use std::iter::Peekable;

use hashbrown::HashTable;
use hashbrown::hash_table::Entry;
use rustc_hash::FxHasher;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Value(pub u32);
pub type RowId = u64;
type HashCode = u64;

impl From<Value> for u32 {
    fn from(value: Value) -> Self {
        value.0
    }
}

impl From<u32> for Value {
    fn from(value: u32) -> Self {
        Value(value)
    }
}

#[derive(Debug)]
struct TableEntry {
    hash: HashCode,
    row: RowId,
}

#[derive(Debug)]
struct Rows {
    buffer: Vec<Value>,
    num_determinant: usize,
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

fn hash(determinant: &[Value]) -> HashCode {
    let mut hasher = FxHasher::default();
    for val in determinant {
        hasher.write_u32(val.0);
    }
    hasher.finish()
}

impl Rows {
    fn num_rows(&self) -> RowId {
        let num_columns = self.num_determinant + 1;
        (self.buffer.len() / num_columns) as RowId
    }

    fn get_row(&self, row: RowId) -> &[Value] {
        let num_columns = self.num_determinant + 1;
        let start = (row as usize) * num_columns;
        &self.buffer[start..start + num_columns]
    }

    fn get_row_mut(&mut self, row: RowId) -> &mut [Value] {
        let num_columns = self.num_determinant + 1;
        let start = (row as usize) * num_columns;
        &mut self.buffer[start..start + num_columns]
    }

    fn add_row(&mut self, row: &[Value]) -> RowId {
        let row_id = self.num_rows();
        self.buffer.extend(row);
        row_id
    }
}

impl Table {
    pub fn new(num_determinant: usize) -> Self {
        Self {
            rows: Rows {
                buffer: vec![],
                num_determinant,
            },
            table: HashTable::new(),
            deleted_rows: BTreeSet::new(),
            changed: false,
        }
    }

    pub fn num_determinant(&self) -> usize {
        self.rows.num_determinant
    }

    pub fn check_changed(&mut self) -> bool {
        replace(&mut self.changed, false)
    }

    pub fn insert<'a, M>(&'a mut self, row: &[Value], merge: &mut M) -> (&'a [Value], RowId)
    where
        M: FnMut(Value, Value) -> Value,
    {
        let num_determinant = self.num_determinant();
        assert_eq!(row.len(), num_determinant + 1);
        let determinant = &row[0..num_determinant];
        let hash = hash(determinant);
        let entry = self.table.entry(
            hash,
            |te| te.hash == hash && &self.rows.get_row(te.row)[0..num_determinant] == determinant,
            |te| te.hash,
        );
        match entry {
            Entry::Occupied(occupied) => {
                let row_id = occupied.get().row;
                let old = self.rows.get_row(row_id)[num_determinant];
                let new = row[num_determinant];
                let merged = merge(old, new);
                if merged != old {
                    self.changed = true;
                }
                self.rows.get_row_mut(row_id)[num_determinant] = merged;
                (self.rows.get_row(row_id), row_id)
            }
            Entry::Vacant(vacant) => {
                let row_id = self.rows.add_row(row);
                vacant.insert(TableEntry { hash, row: row_id });
                self.changed = true;
                (self.rows.get_row(row_id), row_id)
            }
        }
    }

    pub fn write_dependent(&mut self, id: RowId, new: Value) {
        let num_determinant = self.num_determinant();
        let old = self.rows.get_row(id)[num_determinant];
        if new != old {
            self.changed = true;
        }
        self.rows.get_row_mut(id)[num_determinant] = new;
    }

    pub fn get(&self, determinant: &[Value]) -> Option<Value> {
        let num_determinant = self.num_determinant();
        assert_eq!(determinant.len(), num_determinant);
        let hash = hash(determinant);
        let te = self.table.find(hash, |te| {
            te.hash == hash && &self.rows.get_row(te.row)[0..num_determinant] == determinant
        });
        te.map(|te| self.rows.get_row(te.row)[num_determinant])
    }

    pub fn delete(&mut self, row_id: RowId) -> &[Value] {
        let row = self.rows.get_row(row_id);
        let determinant = &row[0..self.num_determinant()];
        let hash = hash(determinant);
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

    pub fn split_rows(&self) -> impl Iterator<Item = (&[Value], Value, RowId)> + '_ {
        self.rows()
            .map(|(row, id)| (&row[0..row.len() - 1], row[row.len() - 1], id))
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
