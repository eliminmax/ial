// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! A solution to Advent of Code 2019 Day 5 built using the `ial` library.

use ial::prelude::*;

fn part1(mut i: Interpreter) -> i64 {
    let (mut outputs, State::Halted) = i.run_through_inputs([1]).unwrap() else {
        panic!();
    };
    let diagnostic = outputs.pop().unwrap();
    assert!(outputs.into_iter().all(|i| i == 0), "diagnostic failed");

    diagnostic
}
fn part2(mut i: Interpreter) -> i64 {
    let (mut outputs, State::Halted) = i.run_through_inputs([5]).unwrap() else {
        panic!();
    };
    let diagnostic = outputs.pop().unwrap();
    assert!(outputs.into_iter().all(|i| i == 0), "diagnostic failed");

    diagnostic
}

fn main() {
    use std::env::args_os;
    use std::fs::read_to_string;
    let input =
        read_to_string(args_os().nth(1).expect("missing file name")).expect("failed to read file");

    let code = input
        .trim()
        .split(',')
        .map(str::parse)
        .collect::<Result<Vec<i64>, _>>()
        .unwrap();
    let interpreter = Interpreter::new(code);
    println!("part 1: {}", part1(interpreter.clone()));
    println!("part 2: {}", part2(interpreter));
}
