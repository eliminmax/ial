// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! A solution to Advent of Code 2019 Day 2 built using the `ial` library.

use ial::prelude::*;

fn part1(mut i: Interpreter) -> i64 {
    i[1] = 12;
    i[2] = 2;
    let (output, state) = i.run_through_inputs(empty()).unwrap();
    assert_eq!(state, State::Halted, "intcode did not run to completion");
    assert!(output.is_empty(), "intcode had unexpected output");
    i[0]
}

fn part2(base_interp: &Interpreter) -> i64 {
    for noun in 0..=99 {
        for verb in 0..=99 {
            let mut i = base_interp.clone();
            i[1] = noun;
            i[2] = verb;
            let (output, state) = i.run_through_inputs(empty()).unwrap();
            assert_eq!(state, State::Halted, "intcode did not run to completion");
            assert!(output.is_empty(), "intcode had unexpected output");
            #[allow(clippy::unreadable_literal, reason = "from Advent of Code")]
            if i.mem_get(0).unwrap() == 19690720 {
                return 100 * noun + verb;
            }
        }
    }
    panic!("no answer found for part 2");
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
    println!("part 2: {}", part2(&interpreter));
}
