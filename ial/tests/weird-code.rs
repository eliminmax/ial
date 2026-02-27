// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use ial::prelude::*;
use std::collections::HashMap;

use ial::asm::{assemble_with_debug, build_ast};

/// Macro to express a test of assembly
///
/// I can't decide if I'm proud or ashamed of this macro
///
/// It basically creates a DSL for expressing assembly tests, built around the idea of
/// mappings. A mapping is expressed as `a => b`.
///
/// It has 3 parts to its input:
///
/// First, a mapping of IAL into Intcode, expressed as the mapping `IAL => [INTCODE]`,
/// where IAL is a [`str`] literal and INTCODE is a comma-separated list of [`i64`]
/// literals.
///
/// Second, a mapping of label identifiers to addresses, using the syntax
/// `{ LABELS }`, where LABELS is a comma-separated sequence of `k => v` mappings.
///
/// Finally, any number of [input] => [output] mappings of input to the IAL interpreter to
/// the expected output.
macro_rules! test_code {
    {
        $ial:literal => [$($ic: literal),*]
        {$($k:literal => $v:literal),*}
        $([$($in:literal),*] => [$($out:literal),*]),+
    } => {{
        let ast = build_ast($ial).unwrap();
        let (code, dbg) = assemble_with_debug(ast).unwrap();
        assert_eq!(code, vec![$($ic),*]);
        let labels: HashMap<&str, i64> =
            dbg.labels.iter().map(|(l, a)| (&*l.inner, *a)).collect();
        assert_eq!(labels, HashMap::from([$(($k, $v)),*]));
        for (input, expected_out) in [$((vec![$($in),*], vec![$($out),*])),*] {
            let mut interpreter = Interpreter::new([$($ic),*]);
            let (output, state) = interpreter.run_through_inputs(input).unwrap();
            assert_eq!(state, State::Halted);
            assert_eq!(output, expected_out);
        }
    }};
}

#[test]
fn weird_code() {
    test_code! {
        "ADD #90, #9, _: _+1" => [1101, 90, 9, 4]
        {"_" => 3}
        [] => []
    }

    test_code! {
        "MUL #11, #9, end\na: b: c: d: end: DATA -250" => [1102, 11, 9, 4, -250]
        {"a" => 4, "b" => 4, "c" => 4, "d" => 4, "end" => 4}
        [] => []
    }

    test_code! {
        "OUT #_99: 99\nJZ #0, #_99" => [104, 99, 1106, 0, 1]
        {"_99" => 1}
        [] => [99]
    }

    // HALT embedded as a nonzero value in the middle of a JNZ instruction that jumps into
    // itself to execute the actual HALT instruction
    test_code! {
        "JNZ #halt: 99, #halt" => [1105, 99, 1]
        {"halt" => 1}
        [] => []
    }

    // HALT embedded as an index of a 0 value in the middle of a JZ instruction that jumps into
    // itself to execute the actual HALT instruction
    test_code! {
        "JZ halt: 99, #halt" => [1006, 99, 1]
        {"halt" => 1}
        [] => []
    }

    // HALT, expressed as an ASCII directive with a comment
    test_code! {
        r#"ASCII "c\n" ; ASCII 'c' is 99 "# => [99, 10]
        {}
        [] => []
    }

    // Write out "hi" in ASCII. Avoid using any capital letters, and encode the HALT enstruction
    // with a DATA directive that uses the ASCII character literal 'c'.
    test_code! {
        r#"rbo #hi
    loop:  out @0
           rbo #1
           jnz @0, #loop
           data 'c' ; ascii 'c' is 99
           hi: ascii "hi\0""# => [
                109,  10,       // 00: rbo #hi
    /* loop: */ 204,   0,       // 02: out @0
                109,   1,       // 04: rbo #1
               1205,   0, 2,    // 06: jnz @0, #loop
                 99,            // 09: data 'c'
      /* hi: */ 104, 105, 0]    // 10: ascii "hi\0"
        {"hi" => 10, "loop" => 2}
        [] => [104, 105]
    }

    // If the input is 99, execute it as a "HALT" instruction. Otherwise, echo it and halt
    // normally. Use alternating uppercase and lowercase letters for keywords, to be obnoxious.
    test_code! {
        r"In input
          Eq input, #99, cond
          JnZ #cond: 0, #input
          OuT #input: -1
          HaLt
        " => [
             3,           10,         // 00: In input
          1008,           10, 99, 7,  // 02: Eq input, #99, cond
          1105, /*cond*/   0, 10,     // 06: JnZ #cond: 0, #input
           104, /*input*/ -1,         // 09: OuT #input: -1
            99]                       // 11: HaLt
        {"cond" => 7, "input" => 10}
        [1] =>  [1], [0] => [0], [123] => [123], [-5_231_612] => [-5_231_612], [99] => []
    }
}
