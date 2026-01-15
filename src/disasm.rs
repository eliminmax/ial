// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

#![cfg(feature = "disasm")]

use super::asm::ast_prelude::*;
use super::asm::ast_util::*;
use super::{Interpreter, OpCode};

/// Create disassembly from the memory
///
/// # Example
///
/// ```
/// use intcode::{prelude::*, asm::assemble, disassemble};
/// const HELLO_ASM: &str = r#"
/// ; A simple Hello World program
/// RBO #hello      ; set relative base to address of hello text
/// loop: OUT @0    ; output int at relative base
///       RBO #1    ; increment relative base
///       JNZ @0, #loop
/// HALT
///
/// hello: ASCII "Hello, world!\n\0" ; a classic greeting
/// "#;
/// let diassembled = disassemble(assemble(HELLO_ASM).unwrap());
///
/// const EXPECTED_DISASM: &str = r#"
/// RBO #10
/// OUT @0
/// RBO #1
/// JNZ @0, #2
/// HALT
/// DATA 72, 101, 108, 108, 111, 44, 32, 118, 111, 114, 108, 100, 33, 10, 0
/// "#.trim_ascii_start();
/// ```
///
/// # Caveats
///
/// ## Naïve Approach to Ambiguity
///
/// Due to the ability to jump to any index, it's ambiguous where an instruction begins.
/// Additionally, [`DATA` directives] can contain valid instructions, and there's no way to tell
/// whether [instruction] or [`DATA` directive] produced a given int in memory.
///
/// The approach this function uses is to start at the beginning of `mem_iter`, and treat the first
/// valid opcode that doesn't have [ignored opcode digits](#ignored-opcode-digits) as the start of an
/// instruction.
///
/// ### Example
///
/// ```
/// use intcode::{asm::assemble, disassemble};
/// // the following both produce the same output:
///
/// // how it's actually run
/// const A: &str = r#"
/// JNZ 1, #4 ; jump over garbage data
/// DATA 1101 ; garbage data that's jumped over
/// MUL 1, 4, 99
/// HALT
/// "#;
///
/// // matching the first possible valid instruction
/// const B: &str = r#"
/// JNZ 1, #4
/// ADD #2, #1, 4
/// HALT
/// HALT
/// "#.trim_ascii_start();
/// assert_eq!(disassemble(assemble(A).unwrap()), B);
/// ```
///
/// The 1st of these reflects what's actually executed, but this function would return the 2nd, as
/// it always goes with the first valid instruction it can, falling back to "DATA" directives for
/// anything that can't be matched.
///
/// ## Ignored Opcode Digits
///
/// If an integer's last 2 digits are a valid opcode, but it has more than 5 digits, invalid
/// parameter modes, or digits higher than the ten thousands' place, then this function will not
/// recognize it as a valid [instruction], as while it is accepted by this crate's [Interpreter]
/// without issue, the ignored digits might have an effect if it's not actually an opcode[^naive]
/// as being part of a [`DATA` directive], not an [instruction].
///
/// ### Example
///
/// ```
/// use intcode::{prelude::*, disassemble};
/// const HALT_WITH_MODES: i64 = 21299; // a HALT instruction with ignored parameter modes
/// let mut interp = Interpreter::new([HALT_WITH_MODES]);
/// assert_eq!(interp.run_through_inputs(empty()).unwrap(), (vec![], State::Halted));
/// assert_eq!(disassemble([HALT_WITH_MODES]), "DATA 21299\n");
/// ```
///
/// ## Self-modifying Code
///
/// Because Intcode programs can potentially modify themselves, disassembling them can only show
/// their code as it exists at a specific point in time, and not what an instruction will look like
/// at the time it's executed:
///
/// ```
/// use intcode::{prelude::*, disassemble, asm::assemble};
///
/// const CODE: &str = r#"
/// ADD #99, #0, halt
/// halt: DATA 12345 ; can be anything, as it will be overwritten
/// "#;
///
/// let code = assemble(CODE).unwrap();
///
/// // note that the disassembled code doesn't actually reflect what's executed:
/// let disasm = disassemble(code.iter().copied());
/// assert_eq!(disasm, "ADD #99, #0, 4\nDATA 12345\n");
///
/// let mut interp = Interpreter::new(code);
/// assert_eq!(interp[4], 12345);
/// let outcome = interp.exec_instruction(&mut empty(), &mut vec![]).unwrap();
/// assert_eq!(outcome, StepOutcome::Running);
/// assert_eq!(interp[4], 99);
/// let outcome = interp.exec_instruction(&mut empty(), &mut vec![]).unwrap();
/// assert_eq!(outcome, StepOutcome::Stopped(State::Halted));
/// ```
///
/// [`DATA` directive]: super::asm::Directive::Data
/// [`DATA` directives]: super::asm::Directive::Data
/// [instruction]: super::asm::Instr
/// [self-modifying]: <#self-modifying-code>
/// [Naïve Approach to Ambiguity]: <#naïve-approach-to-ambiguity>
/// [^naive]: See [Naïve Approach to Ambiguity] and [self-modifying]
pub fn disassemble(mem_iter: impl IntoIterator<Item = i64>) -> String {
    let mut mem_iter = mem_iter.into_iter().peekable();

    let mut lines = Vec::new();

    let parse_op_strict = |i: i64| -> Option<(OpCode, [ParamMode; 3])> {
        let (opcode, modes) = Interpreter::parse_op(i).ok()?;
        let rebuilt = match opcode {
            OpCode::Add | OpCode::Mul | OpCode::Lt | OpCode::Eq => {
                opcode as i64
                    + (modes[0] as i64 * 100)
                    + (modes[1] as i64 * 1000)
                    + (modes[2] as i64 * 10000)
            }
            OpCode::Jnz | OpCode::Jz => {
                opcode as i64 + (modes[0] as i64 * 100) + (modes[1] as i64 * 1000)
            }
            OpCode::In | OpCode::Out | OpCode::Rbo => opcode as i64 + (modes[0] as i64 * 100),
            OpCode::Halt => opcode as i64,
        };
        (rebuilt == i).then_some((opcode, modes))
    };

    while let Some(i) = mem_iter.next() {
        if let Some((opcode, modes)) = parse_op_strict(i) {
            macro_rules! param {
                ($mode_i: literal) => {{
                    Parameter(
                        modes[$mode_i],
                        boxed(span(
                            Expr::Number(mem_iter.next().unwrap_or_default()),
                            0..0,
                        )),
                    )
                }};
            }
            macro_rules! instr {
                ($type: ident, 3) => {{ Instr::$type(param!(0), param!(1), param!(2)) }};
                ($type: ident, 2) => {{ Instr::$type(param!(0), param!(1)) }};
                ($type: ident, 1) => {{ Instr::$type(param!(0)) }};
            }

            let instr = match opcode {
                OpCode::Add => instr!(Add, 3),
                OpCode::Mul => instr!(Mul, 3),
                OpCode::In => instr!(In, 1),
                OpCode::Out => instr!(Out, 1),
                OpCode::Jnz => instr!(Jnz, 2),
                OpCode::Jz => instr!(Jz, 2),
                OpCode::Lt => instr!(Lt, 3),
                OpCode::Eq => instr!(Eq, 3),
                OpCode::Rbo => instr!(Rbo, 1),
                OpCode::Halt => Instr::Halt,
            };
            lines.push(Line {
                labels: vec![],
                inner: Some(span(Directive::Instruction(boxed(instr)), 0..0)),
            });
        } else {
            let mut data = vec![span(Expr::Number(i), 0..0)];
            while mem_iter
                .peek()
                .is_some_and(|n| parse_op_strict(*n).is_none())
            {
                data.push(span(Expr::Number(mem_iter.next().unwrap()), 0..0));
            }
            lines.push(Line {
                labels: vec![],
                inner: Some(span(Directive::Data(data), 0..0)),
            });
        }
    }

    lines.into_iter().map(|line| format!("{line}\n")).collect()
}
