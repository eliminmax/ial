// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! module containing the [Trace] type and its related functionality
use std::fmt::{self, Debug, Display};

use super::{Interpreter, OpCode, ParamMode};

#[derive(Clone, Copy)]
struct PackedModes(u8);
impl PackedModes {
    const fn pack(modes: [ParamMode; 3]) -> Self {
        Self(modes[0] as u8 | ((modes[1] as u8) << 2) | ((modes[2] as u8) << 4))
    }
    const fn unpack(self) -> [ParamMode; 3] {
        const fn unpack_bit_pair(bit_pair: u8) -> ParamMode {
            match bit_pair {
                0b00 => ParamMode::Positional,
                0b01 => ParamMode::Immediate,
                0b10 => ParamMode::Relative,
                _ => unreachable!(),
            }
        }
        [
            unpack_bit_pair(self.0 & 0b11),
            unpack_bit_pair((self.0 & 0b1100) >> 2),
            unpack_bit_pair((self.0 & 0b110000) >> 4),
        ]
    }
}

#[derive(Clone, Copy)]
enum TracedOp {
    Add((i64, i64), (i64, i64), (i64, i64)),
    Mul((i64, i64), (i64, i64), (i64, i64)),
    In((i64, i64)),
    Out((i64, i64)),
    Jnz((i64, i64), (i64, i64)),
    Jz((i64, i64), (i64, i64)),
    Lt((i64, i64), (i64, i64), (i64, i64)),
    Eq((i64, i64), (i64, i64), (i64, i64)),
    Rbo((i64, i64)),
    Halt,
}

#[derive(Clone)]
/// An opaque type containing information about what instruction was executed, which can be queried
/// with its various methods, or converted into a [String] using its [Display] impl.
pub struct TracedInstr {
    op: TracedOp,
    op_int: i64,
    instr_ptr: i64,
    rel_base: i64,
    packed_modes: PackedModes,
    opcode: OpCode,
}

impl TracedInstr {
    /// Return the relative base at the time the traced instruction was excuted,
    pub fn rel_base(&self) -> i64 {
        self.rel_base
    }

    /// Return the instruction pointer's position when the traced instruction was executed
    pub fn instr_ptr(&self) -> i64 {
        self.instr_ptr
    }

    /// Return the actual integer of the traced instruction
    pub fn op_int(&self) -> i64 {
        self.op_int
    }

    /// Return the opcode of the traced instruction
    pub fn op_code(&self) -> OpCode {
        self.opcode
    }

    /// If the instruction stored a value, return that value
    pub fn stored_val(&self) -> Option<i64> {
        match self.op {
            TracedOp::Add(_, _, (_, stored))
            | TracedOp::Mul(_, _, (_, stored))
            | TracedOp::Lt(_, _, (_, stored))
            | TracedOp::Eq(_, _, (_, stored))
            | TracedOp::In((_, stored)) => Some(stored),
            _ => None,
        }
    }

    /// Return an array of the parameter modes of the traced instruction
    pub fn param_modes(&self) -> [ParamMode; 3] {
        self.packed_modes.unpack()
    }

    pub(super) fn build(
        op_int: i64,
        instr_ptr: i64,
        rel_base: i64,
        resolved_params: &[(i64, i64)],
    ) -> Self {
        let (opcode, modes) =
            Interpreter::parse_op(op_int).expect("previously parsed successfully");
        macro_rules! op {
            {$id: ident(_, _, _)} => {{
                debug_assert_eq!(resolved_params.len(), 3);
                TracedOp::$id(resolved_params[0], resolved_params[1], resolved_params[2])
            }};
            {$id: ident(_, _)} => {{
                debug_assert_eq!(resolved_params.len(), 2);
                TracedOp::$id(resolved_params[0], resolved_params[1])
            }};
            {$id: ident(_)} => {{
                debug_assert_eq!(resolved_params.len(), 1);
                TracedOp::$id(resolved_params[0])
            }};
            {$id: ident} => {{
                debug_assert_eq!(resolved_params.len(), 0);
                TracedOp::$id
            }}
        }

        let packed_modes = PackedModes::pack(modes);

        let op = match opcode {
            OpCode::Add => op! { Add(_, _, _) },
            OpCode::Mul => op! { Mul(_, _, _) },
            OpCode::In => op! { In(_) },
            OpCode::Out => op! { Out(_) },
            OpCode::Jnz => op! { Jnz(_, _) },
            OpCode::Jz => op! { Jz(_, _) },
            OpCode::Lt => op! { Lt(_, _, _) },
            OpCode::Eq => op! { Eq(_, _, _) },
            OpCode::Rbo => op! { Rbo(_) },
            OpCode::Halt => op! { Halt },
        };
        Self {
            op_int,
            instr_ptr,
            rel_base,
            op,
            packed_modes,
            opcode,
        }
    }
}

impl Interpreter {
    /// Begin a [Trace] of executed instructions. If a trace is already running, this replaces that
    /// trace and returns in a [`Some`], otherwise, it returns [`None`].
    ///
    /// # Example
    /// ```
    /// use ial::prelude::*;
    /// use ial::OpCode;
    /// let mut interp = Interpreter::new([1101, 90, 9, 4]);
    /// let prev_trace = interp.start_trace();
    /// assert!(prev_trace.is_none());
    /// let _out = interp.run_through_inputs(empty()).unwrap();
    ///# assert_eq!(_out, (vec![], State::Halted));
    /// let traced = interp.end_trace().unwrap().0;
    /// assert_eq!(traced[0].op_code(), OpCode::Add);
    /// assert_eq!(traced[0].instr_ptr(), 0);
    /// assert_eq!(traced[1].op_code(), OpCode::Halt);
    /// ```
    pub fn start_trace(&mut self) -> Option<Trace> {
        self.trace.replace(Trace::new())
    }

    /// Stop tracing executed instructions into a [Trace]. If no trace was active, returns [`None`]
    ///
    /// see [Interpreter::start_trace]
    pub fn end_trace(&mut self) -> Option<Trace> {
        self.trace.take()
    }

    /// Get a view of the current trace
    pub fn show_trace(&self) -> Option<&Trace> {
        self.trace.as_ref()
    }

    #[inline]
    pub(crate) fn trace<const N: usize>(&mut self, resolved_params: [(i64, i64); N]) {
        if let Some(trace) = self.trace.as_mut() {
            trace.push(
                self.code[self.index],
                self.index,
                self.rel_offset,
                &resolved_params,
            );
        }
    }
}

#[derive(Debug, Default, Clone)]
/// A log of instructions that an [Interpreter] has executed since a call to
/// [Interpreter::start_trace]
///
/// see [Interpreter::start_trace]
pub struct Trace(pub Vec<TracedInstr>);

impl Trace {
    pub(crate) fn push(
        &mut self,
        op_int: i64,
        instr_ptr: i64,
        rel_base: i64,
        resolved_params: &[(i64, i64)],
    ) {
        self.0.push(TracedInstr::build(
            op_int,
            instr_ptr,
            rel_base,
            resolved_params,
        ))
    }

    pub(crate) fn new() -> Self {
        Self(Vec::new())
    }
}
impl Debug for TracedOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        macro_rules! arg {
            ($arg: ident) => {
                format_args!("{} => {}", $arg.0, $arg.1)
            };
        }
        macro_rules! variant {
            ($name: literal, ($($arg: ident),*)) => {
                f.debug_tuple($name)
                $(.field(&arg!($arg) ))*
                .finish()
            }
        }
        match self {
            Self::Add(a0, a1, a2) => variant!("Add", (a0, a1, a2)),
            Self::Mul(a0, a1, a2) => variant!("Mul", (a0, a1, a2)),
            Self::In(a0) => variant!("In", (a0)),
            Self::Out(a0) => variant!("Out", (a0)),
            Self::Jnz(a0, a1) => variant!("Jnz", (a0, a1)),
            Self::Jz(a0, a1) => variant!("Jz", (a0, a1)),
            Self::Lt(a0, a1, a2) => variant!("Lt", (a0, a1, a2)),
            Self::Eq(a0, a1, a2) => variant!("Eq", (a0, a1, a2)),
            Self::Rbo(a0) => variant!("Rbo", (a0)),
            Self::Halt => write!(f, "Halt"),
        }
    }
}

impl Debug for TracedInstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TracedInstr")
            .field("op", &self.op)
            .field("op_int", &self.op_int)
            .field("instr_ptr", &self.instr_ptr)
            .field("rel_base", &self.rel_base)
            .field("modes", &self.packed_modes.unpack())
            .field("opcode", &self.opcode)
            .finish()
    }
}

impl Display for TracedInstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ran instruction at {:0>4}: op int {: <5} | ",
            self.instr_ptr, self.op_int
        )?;
        let modes = self.packed_modes.unpack();

        match self.op {
            TracedOp::Add((pa, va), (pb, vb), (dest, idx))
            | TracedOp::Mul((pa, va), (pb, vb), (dest, idx))
            | TracedOp::Lt((pa, va), (pb, vb), (dest, idx))
            | TracedOp::Eq((pa, va), (pb, vb), (dest, idx)) => {
                write!(
                    f,
                    "[{} {}{pa} (resolves to {va}), {}{pb} (resolves to {vb}), {}{dest} (stored {})]",
                    self.opcode,
                    modes[0],
                    modes[1],
                    modes[2],
                    idx.cast_unsigned()
                )
            }
            TracedOp::Jnz((p_base, v_base), (p_dest, v_dest)) => {
                write!(
                    f,
                    "[{} {}{p_base} (resolves to {v_base}), {}{p_dest} ({} to {v_dest})]",
                    self.opcode,
                    modes[0],
                    modes[1],
                    if v_base != 0 { "jumped" } else { "didn't jump" }
                )
            }
            TracedOp::Jz((p_base, v_base), (p_dest, v_dest)) => {
                write!(
                    f,
                    "[{} {}{p_base} (resolves to {v_base}), {}{p_dest} ({} to {v_dest})]",
                    self.opcode,
                    modes[0],
                    modes[1],
                    if v_base == 0 { "jumped" } else { "didn't jump" }
                )
            }
            TracedOp::In((p, v)) => {
                write!(f, "[{} {}{p} (stored {v})]", self.opcode, modes[0])
            }
            TracedOp::Out((p, v)) => {
                write!(f, "[{} {}{p} (resolves to {v})]", self.opcode, modes[0])
            }
            TracedOp::Rbo((p, v)) => write!(
                f,
                "[RBO {}{p} (resolved to {v}) (went from {} to {})]",
                modes[0],
                self.rel_base,
                self.rel_base + v,
            ),
            TracedOp::Halt => {
                write!(f, "[HALT]")
            }
        }
    }
}

#[cfg(test)]
#[test]
fn test_param_mode_packing() {
    const MODES: [ParamMode; 3] = [
        ParamMode::Positional,
        ParamMode::Immediate,
        ParamMode::Relative,
    ];

    for a in MODES {
        for b in MODES {
            for c in MODES {
                assert_eq!(PackedModes::pack([a, b, c]).unpack(), [a, b, c]);
            }
        }
    }
}
