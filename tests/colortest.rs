// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! A handful of tests involving the [colortest](https://github.com/eliminmax/colortest) IAL
//! implementation.

use ial::asm::ast::{Directive, Instr, Line};
use ial::asm::{assemble_with_debug, build_ast};
use ial::debug_info::DebugInfo;
use ial::{Interpreter, State};
use itertools::Itertools;
use std::sync::OnceLock;

const COLORTEST_ASM: &str = include_str!("colortest/ial/colortest.ial");

fn parsed_ast() -> &'static (Vec<i64>, DebugInfo) {
    static PARSED: OnceLock<(Vec<i64>, DebugInfo)> = OnceLock::new();
    PARSED.get_or_init(|| assemble_with_debug(ast().to_vec()).unwrap())
}

fn code() -> &'static [i64] {
    &parsed_ast().0
}

fn ast() -> &'static [Line<'static>] {
    static AST: OnceLock<Vec<Line<'static>>> = OnceLock::new();
    AST.get_or_init(|| build_ast(COLORTEST_ASM).unwrap())
}

/// Sanity check - do the number of directives of each kind match the number of directive keywords
/// of each kind?
#[test]
fn ast_instruction_counts() {
    let directives = COLORTEST_ASM
        .lines()
        .filter_map(|mut line| {
            // trim comment
            line = line.split_once(';').map_or(line, |l| l.0);
            // get directive - that'll be the first word that doesn't end in a colon
            line.split_ascii_whitespace().find(|word| !word.ends_with(':'))
                .map(str::to_ascii_uppercase)
                .map(|kw| match kw.as_str() {
                    "SLT" => String::from("LT"),
                    "SEQ" => String::from("EQ"),
                    "INCB" => String::from("RBO"),
                    _ => kw,
                })
        })
        .counts();

    let ast_matches = ast()
        .iter()
        .filter_map(|line| line.directive.as_ref())
        .map(|directive| match &directive.inner {
            Directive::Instruction(i) => match i.as_ref() {
                Instr::Add(..) => "ADD",
                Instr::Mul(..) => "MUL",
                Instr::In(..) => "IN",
                Instr::Out(..) => "OUT",
                Instr::Lt(..) => "LT",
                Instr::Eq(..) => "EQ",
                Instr::Jnz(..) => "JNZ",
                Instr::Jz(..) => "JZ",
                Instr::Rbo(..) => "RBO",
                Instr::Halt => "HALT",
            },
            Directive::Data(_) => "DATA",
            Directive::Ascii(_) => "ASCII",
            d => panic!("unaccounted-for directive {d}"),
        })
        .map(String::from)
        .counts();
    assert_eq!(directives, ast_matches);
    for s in ["MUL", "IN", "RBO"] {
        assert_eq!(ast_matches.get(s), None, "unexpected {s} instruction found");
    }
}

#[test]
fn expected_output() {
    let expected_output = include_bytes!("colortest/colortest_output")
        .iter()
        .map(|c| i64::from(*c))
        .collect_vec();
    let mut interp = Interpreter::new(code().iter().copied());
    let (output, State::Halted) = interp.run_through_inputs([]).unwrap() else {
        panic!("failed to run to completion");
    };
    assert_eq!(output, expected_output);
}
