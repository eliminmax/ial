// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use intcode::asm::{assemble_ast, build_ast};
use std::env::args_os;
use std::fs::read_to_string;

fn main() {
    let input = read_to_string(args_os().nth(1).expect("must provide filename"))
        .expect("must be able to read");

    let ast = build_ast(&input).unwrap();
    let intcode = assemble_ast(ast).unwrap();
    let intcode: Vec<String> = intcode.into_iter().map(|i| i.to_string()).collect();
    println!("{}", intcode.join(","));
}
