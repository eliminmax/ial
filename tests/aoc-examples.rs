//! Test that examples from Advent of Code problem descriptions behave as described.
// SPDX-FileCopyrightText: 2024 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use either::Either;
use ial::prelude::*;
use ial::trace::{Trace, TracedInstr};
use ial::{OpCode, ParamMode};
use itertools::Itertools;

// first, some groundwork for common elements of different tests

/// Construct a new interpreter with the given starting code
macro_rules! interp {
    [$($i:expr),*] => {{
        Interpreter::new([$($i),*])
    }}
}

/// Run an interpreter to end, returning its output.
/// Borrows the interpreter in case it's trace is useful
fn run_to_end(
    interp: &mut Interpreter,
    inputs: impl IntoIterator<Item = i64>,
) -> Result<Vec<i64>, Either<ial::ErrorState, Awaiting>> {
    let (output, state) = interp.run_through_inputs(inputs).map_err(Either::Left)?;
    if state == State::Halted {
        Ok(output)
    } else {
        Err(Either::Right(Awaiting { output }))
    }
}

/// A struct with the information about expected traced instruction
struct ExpectedOp {
    op_int: i64,
    instr_ptr: i64,
    stored_val: Option<i64>,
}

impl ExpectedOp {
    const fn new(op_int: i64, instr_ptr: i64, stored_val: Option<i64>) -> Self {
        Self {
            op_int,
            instr_ptr,
            stored_val,
        }
    }

    fn validate(self, traced: TracedInstr) {
        assert_eq!(self.op_int, traced.op_int());
        assert_eq!(self.instr_ptr, traced.instr_ptr());
        assert_eq!(self.stored_val, traced.stored_val());
    }
}

fn validate_trace(expected: impl IntoIterator<Item = ExpectedOp>, Trace(trace): Trace) {
    expected
        .into_iter()
        .zip_eq(trace)
        .for_each(|(op, instr)| op.validate(instr))
}

mod day2_examples {
    mod part1 {
        use crate::*;

        /// the extended example used to help illustrate the basics
        #[test]
        fn extended_example() {
            let mut interp = interp![1, 9, 10, 3, 2, 3, 11, 0, 99, 30, 40, 50];
            interp.start_trace();
            let output = run_to_end(&mut interp, empty()).unwrap();
            assert!(output.is_empty());
            const EXPECTED: [ExpectedOp; 3] = [
                ExpectedOp::new(1, 0, Some(70)),
                ExpectedOp::new(2, 4, Some(3500)),
                ExpectedOp::new(99, 8, None),
            ];
            validate_trace(EXPECTED, interp.end_trace().unwrap());
        }

        /// the extra, smaller examples that are listed after the extended example
        #[test]
        fn small_examples() {
            macro_rules! example {
            ($($code: literal),+ becomes $($output: literal),+) => {{
                let mut interp = interp![$($code),*];
                run_to_end(&mut interp, []).unwrap();
                for (i, val) in [$($output),+].into_iter().enumerate() {
                    assert_eq!(interp[i as i64], val);
                }
            }}
        }
            example!(1,0,0,0,99 becomes 2,0,0,0,99);
            example!(2,3,0,3,99 becomes 2,3,0,6,99);
            example!(2,4,4,5,99,0 becomes 2,4,4,5,99,9801);
            example!(1,1,1,4,99,5,6,0,99 becomes 30,1,1,4,2,5,6,0,99);
        }
    }
}

mod day5_examples {
    mod part1 {
        use crate::*;

        #[test]
        fn echo_input() {
            let template = interp![3, 0, 4, 0, 99];
            for i in -128..128 {
                assert_eq!(run_to_end(&mut template.clone(), [i]).unwrap(), vec![i]);
            }
        }

        #[test]
        fn immediate_mode_example() {
            let mut interp = interp![1002, 4, 3, 4, 33];
            interp.start_trace();
            let output = run_to_end(&mut interp, []).unwrap();
            assert!(output.is_empty());
            const EXPECTED: [ExpectedOp; 2] = [
                ExpectedOp::new(1002, 0, Some(99)),
                ExpectedOp::new(99, 4, None),
            ];
            let trace = interp.end_trace().unwrap();
            assert_eq!(
                trace.0[0].param_modes(),
                [
                    ParamMode::Positional,
                    ParamMode::Immediate,
                    ParamMode::Positional
                ]
            );
            validate_trace(EXPECTED, trace);
        }
    }
    mod part2 {
        use crate::*;

        #[test]
        fn comparison_examples() {
            let templates = [
                interp![3, 9, 8, 9, 10, 9, 4, 9, 99, -1, 8],
                interp![3, 9, 7, 9, 10, 9, 4, 9, 99, -1, 8],
                interp![3, 3, 1108, -1, 8, 3, 4, 3, 99],
                interp![3, 3, 1107, -1, 8, 3, 4, 3, 99],
            ];

            let expected_builder = |mode, cmp_op, input| {
                let val = if cmp_op == OpCode::Lt {
                    input < 8
                } else {
                    input == 8
                } as i64;
                let expected = [
                    ExpectedOp::new(OpCode::In as i64, 0, Some(input)),
                    ExpectedOp::new(cmp_op as i64 + (mode as i64 * 1100), 2, Some(val)),
                    ExpectedOp::new(OpCode::Out as i64, 6, None),
                    ExpectedOp::new(OpCode::Halt as i64, 8, None),
                ];
                (expected, val)
            };

            let expected = |i: i64| {
                [
                    expected_builder(ParamMode::Positional, OpCode::Eq, i),
                    expected_builder(ParamMode::Positional, OpCode::Lt, i),
                    expected_builder(ParamMode::Immediate, OpCode::Eq, i),
                    expected_builder(ParamMode::Immediate, OpCode::Lt, i),
                ]
            };

            for input in [7, 8, 9] {
                let mut interps = templates.clone();
                let expected_traces = expected(input);
                for (interp, (trace, out)) in interps.iter_mut().zip(expected_traces) {
                    interp.start_trace();
                    let output = run_to_end(interp, [input]).unwrap();
                    assert_eq!(output, vec![out]);
                    validate_trace(trace, interp.end_trace().unwrap());
                }
            }
        }

        #[test]
        fn part2_jump_examples() {
            let templates = [
                interp![3, 12, 6, 12, 15, 1, 13, 14, 13, 4, 13, 99, -1, 0, 1, 9],
                interp![3, 3, 1105, -1, 9, 1101, 0, 0, 12, 4, 12, 99, 1],
            ];

            for i in [0, 1] {
                let mut interps = templates.clone();
                let mut v = vec![];
                for interp in interps.iter_mut() {
                    interp
                        .exec_instruction(&mut std::iter::once(i), &mut v)
                        .unwrap();
                    interp.start_trace();
                    interp.exec_instruction(&mut empty(), &mut v).unwrap();
                    assert!(v.is_empty());
                }
                let modes: [[ParamMode; 3]; 2] = core::array::from_fn(|i| {
                    let Trace(trace) = interps[i].end_trace().unwrap();
                    assert_eq!(trace.len(), 1);
                    trace[0].param_modes()
                });
                for mut interp in interps {
                    assert_eq!(run_to_end(&mut interp, empty()).unwrap(), vec![i]);
                }
                assert_eq!(
                    modes,
                    [
                        [ParamMode::Positional; 3],
                        [
                            ParamMode::Immediate,
                            ParamMode::Immediate,
                            ParamMode::Positional
                        ]
                    ]
                );
            }
        }
    }
}

mod day9_examples {
    mod part1 {
        use crate::*;
        /// > takes no input and produces a copy of itself as output.
        #[test]
        fn quine() {
            let quine_code = [
                109, 1, 204, -1, 1001, 100, 1, 100, 1008, 100, 16, 101, 1006, 101, 0, 99,
            ];
            let mut interp = Interpreter::new(quine_code);
            let output = run_to_end(&mut interp, empty()).unwrap();
            assert_eq!(output.as_slice(), quine_code.as_slice());
        }

        /// > should output a 16-digit number
        #[test]
        fn output_sixteen_digit() {
            let mut interp = interp![1102, 34915192, 34915192, 7, 4, 7, 99, 0];
            let output = run_to_end(&mut interp, empty()).unwrap();
            assert_eq!(output.len(), 1, "{output:?}");
            assert_eq!(output[0].to_string().len(), 16, "{output:?}");
        }

        /// > should output the large number in the middle
        #[test]
        fn large_number() {
            let mut interp = interp![104, 1125899906842624, 99];
            let output = run_to_end(&mut interp, empty()).unwrap();
            assert_eq!(output, vec![1125899906842624]);
        }
    }
}

#[derive(Debug)]
struct Awaiting {
    #[allow(dead_code, reason = "for Debug impl")]
    output: Vec<i64>,
}
