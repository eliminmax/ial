// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Disassembler-related functionality
//!
//! See [disassemble] for documentation

use super::OpCode;
use ial_ast::prelude::*;
use ial_ast::util::boxed;
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::{self, Display, Write};

fn parse_op_strict(i: i64) -> Option<(OpCode, [ParamMode; 3])> {
    let (opcode, modes) = parse_op(i).ok()?;
    let rebuilt = match opcode {
        op @ (OpCode::Add | OpCode::Mul | OpCode::Lt | OpCode::Eq) => {
            op as i64
                + (modes[0] as i64 * 100)
                + (modes[1] as i64 * 1000)
                + (modes[2] as i64 * 10000)
        }
        op @ (OpCode::Jnz | OpCode::Jz) => {
            op as i64 + (modes[0] as i64 * 100) + (modes[1] as i64 * 1000)
        }
        op @ (OpCode::In | OpCode::Out | OpCode::Rbo) => op as i64 + (modes[0] as i64 * 100),
        op @ OpCode::Halt => op as i64,
    };
    (rebuilt == i).then_some((opcode, modes))
}

/// Create disassembly from Intcode memory
///
/// # Example
///
/// ```
/// use ial::{prelude::*, asm::assemble, disasm::disassemble};
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
/// use ial::{asm::assemble, disasm::disassemble};
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
/// recognize it as a valid [instruction], as while it is accepted by this crate's [`Interpreter`]
/// without issue, the ignored digits might have an effect if it's not actually an opcode[^naive]
/// as being part of a [`DATA` directive], not an [instruction].
///
/// ### Example
///
/// ```
/// use ial::{prelude::*, disasm::disassemble};
/// const HALT_WITH_MODES: i64 = 21299; // a HALT instruction with ignored parameter modes
/// let mut interp = Interpreter::new([HALT_WITH_MODES]);
/// assert_eq!(interp.run_through_inputs([]).unwrap(), (vec![], State::Halted));
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
/// use ial::{prelude::*, disasm::disassemble, asm::assemble};
/// use std::iter::empty;
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
/// [`DATA` directive]: <https://github.com/eliminmax/ial/blob/main/IAL.md#data-directives>
/// [`DATA` directives]: <https://github.com/eliminmax/ial/blob/main/IAL.md#data-directives>
/// [instruction]: <https://github.com/eliminmax/ial/blob/main/IAL.md#instructions>
/// [`Interpreter`]: crate::Interpreter
/// [self-modifying]: <#self-modifying-code>
/// [Naïve Approach to Ambiguity]: <#naïve-approach-to-ambiguity>
/// [^naive]: See [Naïve Approach to Ambiguity] and [self-modifying]
pub fn disassemble(mem_iter: impl IntoIterator<Item = i64>) -> String {
    let mut mem_iter = mem_iter.into_iter().peekable();

    let mut lines = Vec::new();

    while let Some(i) = mem_iter.next() {
        if let Some((opcode, modes)) = parse_op_strict(i) {
            let mut param = |i: usize| {
                Parameter(
                    modes[i],
                    boxed(OuterExpr {
                        expr: spanned_expr(Expr::Number(mem_iter.next().unwrap_or_default())),
                        labels: vec![],
                    }),
                )
            };

            let instr = match opcode {
                OpCode::Add => Instr::Add(param(0), param(1), param(2)),
                OpCode::Mul => Instr::Mul(param(0), param(1), param(2)),
                OpCode::In => Instr::In(param(0)),
                OpCode::Out => Instr::Out(param(0)),
                OpCode::Jnz => Instr::Jnz(param(0), param(1)),
                OpCode::Jz => Instr::Jz(param(0), param(1)),
                OpCode::Lt => Instr::Lt(param(0), param(1), param(2)),
                OpCode::Eq => Instr::Eq(param(0), param(1), param(2)),
                OpCode::Rbo => Instr::Rbo(param(0)),
                OpCode::Halt => Instr::Halt,
            };

            lines.push(Line {
                labels: vec![],
                directive: Some(span_dis(Directive::Instruction(boxed(instr)))),
                comment: None,
            });
        } else {
            let mut data = vec![spanned_expr(Expr::Number(i))];
            while mem_iter
                .peek()
                .is_some_and(|n| parse_op_strict(*n).is_none())
            {
                data.push(spanned_expr(Expr::Number(
                    mem_iter
                        .next()
                        .unwrap_or_else(|| unreachable!("already confirmed `Some`")),
                )));
            }
            lines.push(Line {
                labels: vec![],
                directive: Some(span_dis(Directive::Data(data))),
                comment: None,
            });
        }
    }

    lines.into_iter().format("\n").to_string() + "\n"
}

use crate::debug_info::{DebugInfo, DirectiveDebug, DirectiveKind};
use crate::internals::parse_op;

macro_rules! write_string {
    ($($tok: tt)*) => {
        write!($($tok)*).expect("write!(&mut String, ...) can't fail")
    }
}

macro_rules! writeln_string {
    ($($tok: tt)*) => {
        writeln!($($tok)*).expect("writeln!(&mut String, ...) can't fail")
    }
}

fn span_dis<T>(inner: T) -> Spanned<T> {
    Spanned {
        inner,
        span: SimpleSpan {
            start: 0,
            end: 0,
            context: (),
        },
    }
}

fn spanned_expr(expr: Expr<'_>) -> SpannedExpr<'_> {
    SpannedExpr {
        expr,
        span: SimpleSpan::from(0..0),
    }
}

fn disasm_ascii(ints: &[i64], disasm: &mut String) {
    if let Ok(bytes) = ints
        .iter()
        .copied()
        .map(u8::try_from)
        .collect::<Result<Vec<_>, _>>()
    {
        disasm.push_str("ASCII \"");
        for b in bytes {
            match b {
                0x1b => disasm.push_str("\\e"),
                _ => write_string!(disasm, "{}", b.escape_ascii()),
            }
        }
        disasm.push_str("\"\n");
    } else {
        writeln_string!(disasm, "DATA {} ; expected ASCII", ints.iter().format(", "));
    }
}

fn disasm_instr<I: Iterator<Item = i64>>(
    mut ints: I,
    directive_size: usize,
    start_address: i64,
    label_lookups: &HashMap<i64, Vec<&str>>,
    disasm: &mut String,
) {
    let op_int = ints.next().unwrap();
    if let Some((op, modes)) = parse_op_strict(op_int) {
        match (op, directive_size) {
            (OpCode::Add | OpCode::Mul | OpCode::Lt | OpCode::Eq, 4)
            | (OpCode::Jnz | OpCode::Jz, 3)
            | (OpCode::In | OpCode::Out | OpCode::Rbo, 2) => {
                let param_fmt =
                    |((mode, num), addr), f: &mut dyn FnMut(&dyn Display) -> fmt::Result| {
                        if let Some(labels) = label_lookups.get(&addr) {
                            f(&format_args!("{mode}{}: {num}", labels.iter().format(": ")))
                        } else {
                            f(&format_args!("{mode}{num}"))
                        }
                    };
                let params = modes
                    .iter()
                    .zip(ints.map(|i| {
                        label_lookups
                            .get(&i)
                            .map_or_else(|| i.to_string(), |v| v[0].to_string())
                    }))
                    .zip(start_address + 1..)
                    .format_with(", ", |param, f| param_fmt(param, f));
                writeln_string!(disasm, "{op} {}", params);
            }
            (OpCode::Halt, 1) => writeln_string!(disasm, "HALT"),
            (op, 1) => {
                writeln_string!(disasm, "DATA {op_int} ; invalid length {op} instruction");
            }
            (op, _) => {
                write_string!(disasm, "DATA {op_int}, {}", ints.format(", "));
                writeln_string!(disasm, " ; invalid length {op} instruction");
            }
        }
    } else {
        writeln_string!(
            disasm,
            "DATA {} ; {}",
            std::iter::once(op_int).chain(ints).format(", "),
            "expected instruction"
        );
    }
}

fn disasm_directive_with_dbg<'a, I: Iterator<Item = i64>>(
    dbg: &'a DirectiveDebug,
    code: &mut I,
    start_address: i64,
    label_lookups: &HashMap<i64, Vec<&'a str>>,
    disasm: &mut String,
) -> i64 {
    let directive_size = dbg.output_span.end - dbg.output_span.start;
    if directive_size == 0 {
        writeln_string!(disasm, "; empty directive");
        return 0;
    }

    let ints = code
        .by_ref()
        .chain(std::iter::repeat(0))
        .take(directive_size);

    match dbg.kind {
        DirectiveKind::Instruction => {
            disasm_instr(ints, directive_size, start_address, label_lookups, disasm);
        }
        DirectiveKind::Data => {
            writeln_string!(disasm, "DATA {}", ints.format(", "));
        }
        DirectiveKind::Ascii => disasm_ascii(&ints.collect_vec(), disasm),
    }

    i64::try_from(directive_size).expect("directives must be smaller than i64::MAX")
}

/// Dissasmble `code`, using [`DebugInfo`] to avoid some of the limitations of [disassemble]
///
/// # Panics
///
/// Panics if a directive's size exceeds [`usize::MAX`]
///
/// [`self.labels`]: DebugInfo::labels
/// [`self.directives`]: DebugInfo::directives
pub fn disassemble_with_debug(
    mem_iter: impl IntoIterator<Item = i64>,
    debug_info: &DebugInfo,
) -> String {
    let mut code = mem_iter.into_iter();
    let label_lookups: HashMap<i64, Vec<&str>> = debug_info
        .labels
        .iter()
        .map(|(label, addr)| (*addr, label.inner.as_ref()))
        .into_group_map();

    let mut addr: i64 = 0;

    let mut disasm = String::new();
    for dir in &debug_info.directives {
        if let Some(labels) = label_lookups.get(&addr) {
            write_string!(&mut disasm, "{}: ", labels.iter().format(": "));
        }

        addr += disasm_directive_with_dbg(dir, &mut code, addr, &label_lookups, &mut disasm);
    }

    if let Some(labels) = label_lookups.get(&addr) {
        write_string!(&mut disasm, "{}:", labels.iter().format(": "));
    }
    disasm
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::asm::{assemble, assemble_with_debug, build_ast};

    #[test]
    fn disassemble_various() {
        const PROGS: [&str; 12] = [
            "ADD #1, @1, 1\n",
            "MUL 3, @20, 3\n",
            "IN 1\n",
            "OUT #5\n",
            "JNZ @1, @2\n",
            "JZ #0, @0\n",
            "LT 1, @1, 1032\n",
            "EQ #8086, @-500, 5\n",
            "RBO @0\n",
            "HALT\n",
            "ASCII \"\\e[48;5;\"\n",
            "DATA 123, 312, 123\n",
        ];

        for prog in PROGS {
            let (code, dbg) = assemble_with_debug(build_ast(prog).unwrap()).unwrap();
            let disasm = disassemble(code.iter().copied());
            // ensure that the original and disassembly result in the same intcode
            assert_eq!(assemble(&disasm).unwrap(), code);
            // ensure that dbg-informed disassembly matches the original
            assert_eq!(disassemble_with_debug(code, &dbg), prog);
        }
    }
}
