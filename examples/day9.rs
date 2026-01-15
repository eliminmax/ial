// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! A solution to Advent of Code 2019 Day 9 built using the `intcode` library.

use ial::prelude::*;

fn part1(mut i: Interpreter) -> i64 {
    let (output, state) = i.run_through_inputs([1]).unwrap();
    assert_eq!(state, State::Halted);
    assert_eq!(output.len(), 1, "{output:?}");
    output[0]
}

fn part2(mut i: Interpreter) -> i64 {
    let (output, state) = i.run_through_inputs([2]).unwrap();
    assert_eq!(state, State::Halted);
    assert_eq!(output.len(), 1, "{output:?}");
    output[0]
}

fn main() {
    use std::env::args_os;
    use std::fs::read_to_string;
    let input =
        read_to_string(args_os().nth(1).expect("missing file name")).expect("failed to read file");

    let code = input
        .trim()
        .split(",")
        .map(str::parse)
        .collect::<Result<Vec<i64>, _>>()
        .unwrap();
    let interpreter = Interpreter::new(code);
    println!("part 1: {}", part1(interpreter.clone()));
    println!("part 2: {}", part2(interpreter));
}
