use lalrpop_util::lalrpop_mod;

pub mod abc_example;
pub mod ast;
pub mod cfg;
pub mod flow_example;
pub mod interner;
pub mod lattice;
pub mod provenance;
pub mod ssa;
pub mod table;

lalrpop_mod!(pub grammar);
