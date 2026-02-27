// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD
use ial::asm::{assemble_with_debug, build_ast};
use ial::prelude::*;

const PROG: &str = r"
RBO #--z
JNZ #1, #halt
a:b:ADD #halt:z:99, #0, #0
end:";

#[test]
fn diagnostic() {
    let (code, dbg) = assemble_with_debug(build_ast(PROG).unwrap()).unwrap();
    let mut interp = Interpreter::new(code);
    let mut diagnostic = Vec::new();
    interp.write_diagnostic(&dbg, &mut diagnostic).unwrap();

    assert_eq!(
        str::from_utf8(&diagnostic).unwrap(),
        r"INTERPRETER STATE
    instruction pointer: 0
        directive #1
    relative base: 0


DISASSEMBLY
RBO #halt
JNZ #1, #halt
a: b: ADD #halt: z: 99, #0, #0
end:
"
    );

    interp
        .exec_instruction(&mut std::iter::empty(), &mut vec![])
        .unwrap();
    interp
        .exec_instruction(&mut std::iter::empty(), &mut vec![])
        .unwrap();
    let mut diagnostic = Vec::new();
    interp.write_diagnostic(&dbg, &mut diagnostic).unwrap();
    assert_eq!(
        str::from_utf8(&diagnostic).unwrap(),
        r"INTERPRETER STATE
    instruction pointer: 6 (halt, z)
        not a directive boundary
    relative base: 6 (halt, z)


DISASSEMBLY
RBO #halt
JNZ #1, #halt
a: b: ADD #halt: z: 99, #0, #0
end:
"
    );
}
