// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

use ial::{Interpreter, State};
#[test]
fn missing_input_recoverable() {
    let mut interpreter = Interpreter::new(vec![3, 10, 4, 10, 99]);
    let old_state = interpreter.clone();

    let failed_run = interpreter.run_through_inputs([]);

    // make sure that the failure returned the right InterpreterError and left both `outputs` and
    // `interpreter` unchanged
    assert_eq!(failed_run, Ok((vec![], State::Awaiting)));
    assert_eq!(interpreter, old_state);

    // make sure that interpreter can still be used
    assert_eq!(
        interpreter.run_through_inputs([1]),
        Ok((vec![1], State::Halted))
    );
}
