// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Disassembler-related functionality
//!
//! See [disassemble] for documentation

use super::{Interpreter, OpCode};
use ial_ast::prelude::*;
use ial_ast::util::boxed;
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Write;

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
/// recognize it as a valid [instruction], as while it is accepted by this crate's [Interpreter]
/// without issue, the ignored digits might have an effect if it's not actually an opcode[^naive]
/// as being part of a [`DATA` directive], not an [instruction].
///
/// ### Example
///
/// ```
/// use ial::{prelude::*, disasm::disassemble};
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
/// use ial::{prelude::*, disasm::disassemble, asm::assemble};
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
                        boxed(OuterExpr {
                            expr: span_dis(Expr::Number(mem_iter.next().unwrap_or_default())),
                            labels: vec![],
                        }),
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
                directive: Some(span_dis(Directive::Instruction(boxed(instr)))),
                comment: None,
            });
        } else {
            let mut data = vec![span_dis(Expr::Number(i))];
            while mem_iter
                .peek()
                .is_some_and(|n| parse_op_strict(*n).is_none())
            {
                data.push(span_dis(Expr::Number(
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

use crate::debug_info::{DebugInfo, DebugInfoError, DirectiveDebug};
use ial_ast::DirectiveKind;

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

fn disasm_outer_expr<'a>(
    addr: i64,
    value: i64,
    label_lookups: &HashMap<i64, Vec<&'a str>>,
) -> OuterExpr<'a> {
    OuterExpr {
        labels: label_lookups
            .get(&addr)
            .map(|labels| labels.iter().map(|id| Label(span_dis(*id))).collect())
            .unwrap_or_default(),
        expr: span_dis(
            label_lookups
                .get(&value)
                .map_or(Expr::Number(value), |ids| Expr::Ident(ids[0])),
        ),
    }
}

fn disasm_directive_with_dbg<'a, I: Iterator<Item = i64>>(
    dbg: &'a DirectiveDebug,
    code: &mut I,
    start_address: i64,
    label_lookups: &HashMap<i64, Vec<&'a str>>,
    disasm: &mut String,
) -> Result<i64, DebugInfoError> {
    let directive_size = dbg.output_span.end - dbg.output_span.start;
    let ints = code.by_ref().take(directive_size).collect_vec();

    if let Some(needed @ 1..) = directive_size.checked_sub(ints.len()) {
        return Err(DebugInfoError::MissingInts(needed));
    }

    macro_rules! fallback {
        ($msg: expr) => {{
            writeln_string!(disasm, "DATA {} ; {}", ints.into_iter().format(", "), $msg);
            return i64::try_from(directive_size)
                .map_err(|_| DebugInfoError::DirectiveTooLarge(directive_size));
        }};
    }

    match dbg.kind {
        DirectiveKind::Instruction => {
            if ints.is_empty() || ints.len() > 4 {
                return Err(DebugInfoError::CorruptDirectiveSize);
            }

            let Ok((op, modes)) = crate::Interpreter::parse_op(ints[0]) else {
                fallback!("expected instruction");
            };

            macro_rules! param {
                ($mode_i: literal) => {{
                    let int = ints[$mode_i + 1];
                    let outer_expr = boxed(disasm_outer_expr(
                        start_address + $mode_i + 1,
                        int,
                        label_lookups,
                    ));
                    Parameter(modes[$mode_i], outer_expr)
                }};
            }

            macro_rules! instr {
                ($type: ident, 3) => {{ Instr::$type(param!(0), param!(1), param!(2)) }};
                ($type: ident, 2) => {{ Instr::$type(param!(0), param!(1)) }};
                ($type: ident, 1) => {{ Instr::$type(param!(0)) }};
                ($type: ident, 0) => {{ Instr::$type }};
            }

            macro_rules! write_instr {
                ($type: ident, $n: tt) => {{
                    if $n + 1 > ints.len() {
                        fallback!(format_args!(
                            "insufficient parameters for {} instruction",
                            op
                        ))
                    }
                    writeln_string!(disasm, "{}", instr!($type, $n));
                    if ints.len() > $n + 1 {
                        writeln_string!(
                            disasm,
                            "DATA {}; leftover parameters from above instruction",
                            ints[$n + 1..].into_iter().format(", ")
                        );
                    }
                }};
            }

            match op {
                OpCode::Add => write_instr!(Add, 3),
                OpCode::Mul => write_instr!(Mul, 3),
                OpCode::In => write_instr!(In, 1),
                OpCode::Out => write_instr!(Out, 1),
                OpCode::Jnz => write_instr!(Jnz, 2),
                OpCode::Jz => write_instr!(Jz, 2),
                OpCode::Lt => write_instr!(Lt, 3),
                OpCode::Eq => write_instr!(Eq, 3),
                OpCode::Rbo => write_instr!(Rbo, 1),
                OpCode::Halt => write_instr!(Halt, 0),
            }
        }
        DirectiveKind::Data => {
            writeln_string!(disasm, "DATA {}", ints.into_iter().format(", "));
        }
        DirectiveKind::Ascii => {
            if ints.iter().all(|i| (0..=255).contains(i)) {
                disasm.push_str("ASCII \"");
                for i in ints {
                    #[allow(
                        clippy::cast_possible_truncation,
                        clippy::cast_sign_loss,
                        reason = "already known to be in range 0..=255"
                    )]
                    match i as u8 {
                        b'\x1b' => disasm.push_str("\\e"),
                        b => write_string!(disasm, "{}", b.escape_ascii()),
                    }
                }
                disasm.push_str("\"\n");
            } else {
                fallback!("expected ASCII");
            }
        }
    }

    i64::try_from(directive_size).map_err(|_| DebugInfoError::DirectiveTooLarge(directive_size))
}

/// Dissasmble `code`, using [`DebugInfo`] to avoid some of the limitations of [disassemble]
///
/// # Errors
///
/// * If `code` is shorter than expected for [`self.directives`], returns
///   [`DebugInfoError::MissingInts`].
/// * If an instruction directive's span is out of the range `1..=4`, returns a
///   [`DebugInfoError::CorruptDirectiveSize`].
/// * If a directive's size exceeds [`usize::MAX`], returns a
///   [`DebugInfoError::DirectiveTooLarge`].
///
/// [`self.labels`]: DebugInfo::labels
/// [`self.directives`]: DebugInfo::directives
pub fn disassemble_with_debug(
    mem_iter: impl IntoIterator<Item = i64>,
    debug_info: &DebugInfo,
) -> Result<String, DebugInfoError> {
    let mut code = mem_iter.into_iter();
    let label_lookups: HashMap<i64, Vec<&str>> = debug_info
        .labels
        .iter()
        .map(|(label, addr)| (*addr, label.inner.as_ref()))
        .into_group_map();

    let mut addr: i64 = 0;

    let mut disasm = String::new();
    for (i, dir) in debug_info.directives.iter().enumerate() {
        if let Some(labels) = label_lookups.get(&addr) {
            for label in &labels[..] {
                write_string!(&mut disasm, "{label}:\t");
            }
        }

        match disasm_directive_with_dbg(dir, &mut code, addr, &label_lookups, &mut disasm) {
            Ok(n) => addr += n,
            Err(DebugInfoError::MissingInts(mut missing)) => {
                for dir in &debug_info.directives[i + 1..] {
                    missing += dir.output_span.end - dir.output_span.start;
                }

                return Err(DebugInfoError::MissingInts(missing));
            }
            Err(e) => return Err(e),
        }
    }

    if let Some(labels) = label_lookups.get(&addr) {
        for label in &labels[..] {
            write_string!(&mut disasm, "{label}:\t");
        }
    }
    Ok(disasm)
}
