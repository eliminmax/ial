// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use ial::InterpreterError;
use ial::asm::assemble;
use ial::prelude::*;
use std::fs::read_to_string;
use std::path::Path;

fn src(name: &str) -> String {
    let mut path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("ial_examples");
    path.push(name);
    path.add_extension("ial");
    read_to_string(path).unwrap()
}

macro_rules! test {
    {$name: ident, $expected: expr} => {
        #[test]
        fn $name() {
            let mut interp = Interpreter::new(assemble(&src(stringify!($name))).unwrap());
            let outcome = interp.run_through_inputs(empty());
            let expected = $expected;
            assert_eq!(outcome, expected, "expected {expected:?}, got {outcome:?}");
        }
    }
}

fn ascii_to_ints(ascii: impl IntoIterator<Item = u8>) -> Vec<i64> {
    ascii.into_iter().map(i64::from).collect()
}

test! { err, Err(InterpreterError::NegativeMemAccess(ial::NegativeMemAccess(-1))) }
test! { hello, Ok((ascii_to_ints(*b"Hello, world!\n"), State::Halted)) }
test! { param_label, Ok((ascii_to_ints([b'1']), State::Halted)) }
