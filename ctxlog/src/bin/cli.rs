use std::io::{Read, Result, stdin};
use std::process::Command;

use tempfile::NamedTempFile;

use ctxlog::ast::Interner;
use ctxlog::grammar::ProgramParser;
use ctxlog::term::{dce, naive_ssa_translation, ssa_to_dot};

pub fn main() -> Result<()> {
    let mut interner = Interner::new();

    let mut imp_program = String::new();
    stdin().read_to_string(&mut imp_program)?;
    let ast = ProgramParser::new()
        .parse(&mut interner, &imp_program)
        .unwrap();

    for func in &ast.funcs {
        let mut terms = naive_ssa_translation(func);
        dce(&mut terms);
        let mut tmp = NamedTempFile::new().unwrap();
        ssa_to_dot(&terms, &mut tmp)?;
        Command::new("xdot").arg(tmp.path()).status().unwrap();
    }

    Ok(())
}
