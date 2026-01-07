// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use chumsky::error::Rich;
use intcode::asm::{AssemblyError, assemble_ast, build_ast};

use std::process::ExitCode;

#[cfg(not(feature = "ariadne"))]
fn report_ast_build_err(err: Rich<'_, char>, file: &str) {
    eprintln!("error parsing {file}: {err}");
}

#[cfg(feature = "ariadne")]
fn report_ast_build_err(err: Rich<'_, char>, file: &str) {
    todo!("#[cfg(feature = \"ariadne\")]\treport_ast_build_err(err={err:?}, file={file:?});");
}

#[cfg(not(feature = "ariadne"))]
fn report_ast_assembly_err(err: AssemblyError<'_>, file: &str) {
    eprintln!("error assembling {file}: {err}");
}

#[cfg(feature = "ariadne")]
fn report_ast_assembly_err(err: AssemblyError<'_>, file: &str) {
    todo!("#[cfg(feature = \"ariadne\")]\treport_ast_assembly_err(err={err:?}, file={file:?});");
}

fn main() -> ExitCode {
    use std::env::args_os;
    use std::fs::read_to_string;
    let input_file = args_os().nth(1).expect("must provide filename");
    let input = read_to_string(&input_file).expect("must be able to read");

    let ast = match build_ast(&input) {
        Ok(ast) => ast,
        Err(errs) => {
            let escaped_filename = input_file.to_string_lossy();
            for err in errs {
                report_ast_build_err(err, &escaped_filename);
            }
            return ExitCode::FAILURE;
        }
    };

    let intcode = match assemble_ast(ast) {
        Ok(code) => code,
        Err(e) => {
            report_ast_assembly_err(e, &input_file.to_string_lossy());
            return ExitCode::FAILURE;
        }
    };
    let intcode: Vec<String> = intcode.into_iter().map(|i| i.to_string()).collect();
    println!("{}", intcode.join(","));
    ExitCode::SUCCESS
}
