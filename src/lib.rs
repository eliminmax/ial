// SPDX-FileCopyrightText: 2024 - 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD
#![warn(missing_docs)]

//! Library providing an Intcode interpreter and optional assembly language
//!
//! The interpreter is fully functional, with all of the [Opcodes] and [Parameter Modes] defined in
//! the completed Intcode computer for [Day 9].
//!
//! # Example
//!
//! ```rust
//! use intcode::prelude::*;
//! let mut interpreter = Interpreter::new(vec![104, 1024, 99]);
//!
//! assert_eq!(
//!     interpreter.run_through_inputs(std::iter::empty()).unwrap(),
//!     (vec![1024], State::Halted)
//! );
//! ```
//!
//! Additionally, if the `asm` feature is enabled, tools to work with a minimal assembly language
//! for Intcode are provided in the [asm] module:
//!
//! # Example
//!
//! ```rust
//! use intcode::{prelude::*, asm::assemble};
//! const ASM: &str = r#"
//! OUT #1024
//! HALT
//! "#;
//!
//!
//! let assembled = assemble(ASM).unwrap();
//! assert_eq!(assembled, vec![104, 1024, 99]);
//!
//! let mut interpreter = Interpreter::new(assembled);
//! assert_eq!(
//!     interpreter.run_through_inputs(std::iter::empty()).unwrap(),
//!     (vec![1024], State::Halted)
//! );
//!
//! ```
//!
//! See the docs for the [asm] module for more complex examples.
//!
//! [Opcodes]: https://esolangs.org/wiki/Intcode#Opcodes
//! [Parameter Modes]: https://esolangs.org/wiki/Intcode#Parameter_Modes
//! [Day 9]: https://adventofcode.com/2019/day/9

/// A module providing a sort of logical memory management unit, using a hashmap to split memory
/// into segments, which are each contiguous in memory.
mod mmu;

use std::error::Error;
use std::fmt::{self, Display};
use std::ops::{Index, IndexMut};
use std::io;
use std::num::TryFromIntError;
use std::sync::{Arc, Mutex};

/// A small module that re-exports items needed when working with the Intcode interpreter
pub mod prelude {
    pub use crate::{Interpreter, State};
}

#[cfg(feature = "asm")]
pub mod asm;

use mmu::IntcodeMem;

/// The state of the intcode system, returned whenever the intcode system has stopped.
///
/// [Awaiting](State::Awaiting) means that there are more instructions to execute, but all input
/// has been consumed and the next instruction requires input.
///
/// [Halted](State::Halted) means that a `HALT` instruction has been executed. Once it's been
/// returned, no more instructions will be executed.
#[derive(Debug, PartialEq)]
pub enum State {
    /// Execution is awaiting input
    Awaiting,
    /// Execution has halted
    Halted,
}

#[derive(Debug)]
/// An error occured when executing an intcode instruction
pub enum ErrorState {
    /// An invalid opcode was encountered
    UnrecognizedOpcode(i64),
    /// An unknown parameter mode was encountered
    UnknownMode(i64),
    /// A negative memory address was encountered
    NegativeMemAccess(TryFromIntError),
    /// An instruction tried to write to an immediate destination
    WriteToImmediate(i64),
    /// An error occured with the logger
    LoggerFailed(io::Error),
}

impl PartialEq for ErrorState {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::UnrecognizedOpcode(lhs), Self::UnrecognizedOpcode(rhs)) => lhs == rhs,
            (Self::UnknownMode(lhs), Self::UnknownMode(rhs)) => lhs == rhs,
            (Self::NegativeMemAccess(lhs), Self::NegativeMemAccess(rhs)) => lhs == rhs,
            (Self::WriteToImmediate(lhs), Self::WriteToImmediate(rhs)) => lhs == rhs,
            _ => false,
        }
    }
}

impl Display for ErrorState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorState::UnrecognizedOpcode(n) => write!(f, "encountered unrecognized opcode {n}"),
            ErrorState::UnknownMode(mode) => write!(f, "encountered unknown parameter mode {mode}"),
            ErrorState::NegativeMemAccess(e) => {
                write!(f, "could not convert index to unsigned address: {e}")
            }
            ErrorState::WriteToImmediate(i) => {
                write!(f, "code attempted to write to immediate {i}")
            }
            ErrorState::LoggerFailed(e) => write!(f, "logger encountered an error: {e}"),
        }
    }
}

impl Error for ErrorState {}

#[derive(Clone)]
/// An intcode interpreter, which provides optional logging of instructions encountered.
pub struct Interpreter<'a> {
    index: u64,
    rel_offset: i64,
    code: IntcodeMem,
    logger: Option<Arc<Mutex<&'a mut (dyn Send + Sync + io::Write)>>>,
}

// ignore the logger field
impl PartialEq for Interpreter<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.rel_offset == other.rel_offset && self.code == other.code
    }
}

impl fmt::Debug for Interpreter<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("Interpreter")
            .field("code", &self.code)
            .field("rbo", &self.rel_offset)
            .field("ip", &self.index)
            .field(
                "logger as *const _",
                &if let Some(ref logger) = self.logger {
                    logger as *const _
                } else {
                    std::ptr::null()
                },
            )
            .finish()
    }
}

impl Index<u64> for Interpreter<'_> {
    type Output = i64;

    fn index(&self, i: u64) -> &Self::Output {
        self.code.index(i)
    }
}

impl IndexMut<u64> for Interpreter<'_> {
    fn index_mut(&mut self, i: u64) -> &mut Self::Output {
        self.code.index_mut(i)
    }
}

/// Parameter mode for Intcode instruction
///
/// Intcode instruction parameters each have a mode:  [positional], [immediate], or [relative].
///
/// When executing an intcode instruction, the instruction's parameters are interpreted in
/// accordance with their associated modes.
///
/// [positional]: ParamMode::Positional
/// [immediate]: ParamMode::Immediate
/// [relative]: ParamMode::Relative
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum ParamMode {
    /// Positional Mode
    ///
    /// A parameter in positional mode evaluates to the value at the address specified by the
    /// parameter.
    Positional = 0,
    /// Immediate Mode
    ///
    /// A parameter in immediate mode evaluates directly to the value specified. Instructions which
    /// write to memory may not use immediate mode for their destinations.
    #[doc(alias = "#")]
    Immediate = 1,
    /// Relative Mode
    ///
    /// A parameter in positional mode evaluates to the value at the address specified by the
    /// parameter, added to the [Relative Base], which starts out as `0` but can be modified
    /// throughout the program's execution.
    ///
    /// [Relative Base]: https://adventofcode.com/2019/day/9
    #[doc(alias = "@")]
    Relative = 2,
}

impl Display for ParamMode {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamMode::Positional => Ok(()),
            ParamMode::Immediate => write!(fmt, "#"),
            ParamMode::Relative => write!(fmt, "@"),
        }
    }
}

impl From<TryFromIntError> for ErrorState {
    fn from(err: TryFromIntError) -> Self {
        Self::NegativeMemAccess(err)
    }
}

impl From<io::Error> for ErrorState {
    fn from(err: io::Error) -> Self {
        Self::LoggerFailed(err)
    }
}

impl TryFrom<i64> for ParamMode {
    type Error = ErrorState;
    fn try_from(i: i64) -> Result<Self, Self::Error> {
        match i {
            0 => Ok(ParamMode::Positional),
            1 => Ok(ParamMode::Immediate),
            2 => Ok(ParamMode::Relative),
            _ => Err(Self::Error::UnknownMode(i)),
        }
    }
}

impl<'a> Interpreter<'a> {
    /// Log with the provided item that implements [`io::Write`].
    pub fn log_with(&mut self, logger: &'a mut (dyn io::Write + Send + Sync)) {
        self.logger = Some(Arc::new(Mutex::new(logger)));
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum OpCode {
    Add = 1,
    Mul = 2,
    In = 3,
    Out = 4,
    Jnz = 5,
    Jz = 6,
    Lt = 7,
    Eq = 8,
    Rbo = 9,
    Halt = 99,
}

impl Interpreter<'_> {
    fn param_val(&mut self, param: u64, mode: ParamMode) -> Result<i64, ErrorState> {
        match mode {
            ParamMode::Positional => {
                let i = self.code[param].try_into()?;
                Ok(self.code[i])
            }
            ParamMode::Immediate => Ok(self.code[param]),
            ParamMode::Relative => {
                let i = (self.code[param] + self.rel_offset).try_into()?;
                Ok(self.code[i])
            }
        }
    }

    fn parse_op(op: i64) -> Result<(OpCode, [ParamMode; 3]), ErrorState> {
        let modes: [ParamMode; 3] = [
            ((op / 100) % 10).try_into()?,  // C (hundreds place)
            ((op / 1000) % 10).try_into()?, // B (thousands place)
            (op / 10000).try_into()?,       // A (ten thousands place)
        ];
        match op % 100 {
            ..-99 | 100.. => unreachable!("modulo makes this impossible"),
            -99..=0 | 10..99 => Err(ErrorState::UnrecognizedOpcode(op % 100)),
            1 => Ok((OpCode::Add, modes)),
            2 => Ok((OpCode::Mul, modes)),
            3 => Ok((OpCode::In, modes)),
            4 => Ok((OpCode::Out, modes)),
            5 => Ok((OpCode::Jnz, modes)),
            6 => Ok((OpCode::Jz, modes)),
            7 => Ok((OpCode::Lt, modes)),
            8 => Ok((OpCode::Eq, modes)),
            9 => Ok((OpCode::Rbo, modes)),
            99 => Ok((OpCode::Halt, modes)),
        }
    }

    /// Manually set a memory location
    #[doc(alias("poke", "write"))]
    pub fn mem_override(&mut self, location: u64, value: i64) {
        self.code[location] = value;
    }

    /// Get the memory at `address`
    #[doc(alias = "peek")]
    pub fn mem_get(&self, address: u64) -> i64 {
        self.code[address]
    }

    fn exec_instruction(
        &mut self,
        inputs: &mut Option<i64>,
        outputs: &mut Vec<i64>,
    ) -> Result<Option<State>, ErrorState> {
        // Given a 5 digit number, digits ABCDE are used as follows:
        // DE is the two-digit opcode
        // C is the 1st parameter's mode
        // B is the 2nd parameter's mode
        // A is the 3rd parameter's mode
        //
        // So *0*1202 would be parsed as follows:
        //
        // Opcode 02 is multiply
        // C=2: 1st parameter is in relative mode
        // B=1: 2nd parameter is in immediate mode
        // A=0: 3rd parameter is in positional mode

        let instruction = self.code[self.index];
        // Ensure that instruction is in range - not strictly needed, so only a debug_assert
        debug_assert!((0..100_000).contains(&instruction));

        let (opcode, modes) = Self::parse_op(instruction)?;

        /// Shorthand to get the `$n`th parameter's value
        macro_rules! select_by_mode {
            ($n: literal) => {{ self.param_val(self.index + $n, modes[$n - 1])? }};
        }

        /// Resolves to the destination address pointed to by the `$n`th parameter
        macro_rules! dest {
            ($n: literal) => {{
                match modes[$n - 1] {
                    ParamMode::Positional => u64::try_from(self.code[self.index + $n])?,
                    ParamMode::Immediate => {
                        return Err(ErrorState::WriteToImmediate(self.code[self.index + $n]));
                    }
                    ParamMode::Relative => {
                        u64::try_from(self.rel_offset + self.code[self.index + $n])?
                    }
                }
            }};
        }

        macro_rules! set_val {
            ($dest: expr, $new_val: expr) => {{
                let val: i64 = $new_val;
                let dest: u64 = $dest;
                self.code[dest] = val;
            }};
        }

        /// A comparison instruction
        macro_rules! comp {
            ($op: expr) => {{ if $op { 1 } else { 0 } }};
        }

        macro_rules! report_op {
            ($fmt: literal) => {
                if let Some(ref logger) = self.logger {
                    let mut logger = logger.lock().unwrap();
                    write!(logger, "ip: {:>8} | rbo: {:>5} | ", self.index, self.rel_offset)?;
                    writeln!(logger, $fmt)?;
                }
            };
            ($fmt: literal, $($args:tt)*) => {
                if let Some(ref logger) = self.logger {
                    let mut logger = logger.lock().unwrap();
                    write!(logger, "ip: {:>8} | rbo: {:>5} | ", self.index, self.rel_offset)?;
                    logger.write_fmt(format_args!($fmt, $($args)*))?;
                    writeln!(logger)?;
                }
            }
        }

        macro_rules! report_op4 {
            ($name: literal) => {
                report_op!(
                    "{instruction:05} [{}({}{}, {}{}, {}{})]",
                    $name,
                    modes[0],
                    self.code[self.index + 1],
                    modes[1],
                    self.code[self.index + 2],
                    modes[2],
                    self.code[self.index + 3]
                )
            };
        }

        macro_rules! report_op3 {
            ($name: literal) => {
                report_op!(
                    "{instruction:05} [{}({}{}, {}{})]",
                    $name,
                    modes[0],
                    self.code[self.index + 1],
                    modes[1],
                    self.code[self.index + 2],
                )
            };
        }

        macro_rules! report_op2 {
            ($name: literal) => {
                report_op!(
                    "{instruction:05} [{}({}{})]",
                    $name,
                    modes[0],
                    self.code[self.index + 1],
                )
            };
        }

        match opcode {
            OpCode::Add => {
                // add
                report_op4!("add");
                set_val!(dest!(3), select_by_mode!(1) + select_by_mode!(2));
                self.index += 4;
                Ok(None)
            }
            OpCode::Mul => {
                // multiply
                report_op4!("mul");
                set_val!(dest!(3), select_by_mode!(1) * select_by_mode!(2));
                self.index += 4;
                Ok(None)
            }
            OpCode::In => {
                // input
                if let Some(input) = inputs.take() {
                    report_op2!("input");
                    set_val!(dest!(1), input);
                    self.index += 2;
                    Ok(None)
                } else {
                    Ok(Some(State::Awaiting))
                }
            }
            OpCode::Out => {
                report_op2!("output");
                // output
                outputs.push(select_by_mode!(1));
                self.index += 2;
                Ok(None)
            }
            OpCode::Jnz => {
                report_op3!("jnz");
                // jump-if-true
                if select_by_mode!(1) == 0 {
                    self.index += 3;
                    Ok(None)
                } else {
                    self.index = select_by_mode!(2).try_into()?;
                    Ok(None)
                }
            }
            OpCode::Jz => {
                report_op3!("jz");
                // jump-if-false
                if select_by_mode!(1) != 0 {
                    self.index += 3;
                    Ok(None)
                } else {
                    self.index = select_by_mode!(2).try_into()?;
                    Ok(None)
                }
            }
            OpCode::Lt => {
                report_op4!("lt");
                // less than
                set_val!(dest!(3), comp!(select_by_mode!(1) < select_by_mode!(2)));
                self.index += 4;
                Ok(None)
            }
            OpCode::Eq => {
                // equals
                report_op4!("eq");
                set_val!(dest!(3), comp!(select_by_mode!(1) == select_by_mode!(2)));
                self.index += 4;
                Ok(None)
            }
            OpCode::Rbo => {
                report_op2!("rbo");
                // relative base offset
                self.rel_offset += select_by_mode!(1);
                self.index += 2;
                Ok(None)
            }
            OpCode::Halt => {
                report_op!("{instruction:05} [halt]");
                Ok(Some(State::Halted))
            }
        }
    }

    /// Create a new interpreter. Collects `code` into the starting memory state.
    ///
    /// Panics if the number of entries exceeds `u64::MAX`
    pub fn new(code: impl IntoIterator<Item = i64>) -> Self {
        Self {
            index: 0,
            rel_offset: 0,
            logger: None,
            code: code.into_iter().collect(),
        }
    }

    /// Execute until either the program halts, or it tries to read nonexistent input.
    /// If the interpreter halted, returns `Ok((v, s))`, where `v` is a [`Vec<i64>`] containing all
    /// outputs that it found, and `s` is the [`State`] at the time it stopped.
    ///
    /// On error, it will return an [`ErrorState`] that reflects the error.
    pub fn run_through_inputs(
        &mut self,
        inputs: impl IntoIterator<Item = i64>,
    ) -> Result<(Vec<i64>, State), ErrorState> {
        let mut outputs = Vec::new();
        let mut inputs = inputs.into_iter();
        let mut current_input = None;
        loop {
            if current_input.is_none() {
                current_input = inputs.next();
            }
            match self.exec_instruction(&mut current_input, &mut outputs) {
                Ok(None) => (),
                Ok(Some(State::Halted)) => break Ok((outputs, State::Halted)),
                Ok(Some(State::Awaiting)) => break Ok((outputs, State::Awaiting)),
                Err(e) => break Err(e),
            }
        }
    }

    /// Pre-compute as much as possible - that is, run every up to, but not including, the first
    /// `IN`, `OUT`, or `HALT` instruction, bubbling up any errors that occur.
    pub fn precompute(&mut self) -> Result<(), ErrorState> {
        while Self::parse_op(self.code[self.index])
            .is_ok_and(|(opcode, _)| !matches!(opcode, OpCode::In | OpCode::Out | OpCode::Halt))
        {
            self.exec_instruction(&mut None, &mut Vec::with_capacity(0))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter::empty;
    /// Example program from day 9, which takes no input and outputs its own code
    #[test]
    fn quine() {
        let quine_code = vec![
            109, 1, 204, -1, 1001, 100, 1, 100, 1008, 100, 16, 101, 1006, 101, 0, 99,
        ];
        let mut interpreter = Interpreter::new(quine_code.clone());
        let (outputs, State::Halted) = interpreter.run_through_inputs(empty()).unwrap() else {
            panic!("Did not halt");
        };
        assert_eq!(quine_code, outputs);
    }

    /// Example program from day 9, which "should output a 16-digit number"
    #[test]
    fn output_sixteen_digit() {
        let mut interpreter = Interpreter::new([1102, 34915192, 34915192, 7, 4, 7, 99, 0]);
        let (outputs, State::Halted) = interpreter.run_through_inputs(empty()).unwrap() else {
            panic!("Did not halt");
        };
        assert_eq!(outputs.len(), 1);
        assert_eq!(outputs[0].to_string().len(), 16);
    }

    /// Example program from day 9, which "should output the large number in the middle"
    #[test]
    fn large_number() {
        let mut interpreter = Interpreter::new([104, 1125899906842624, 99]);
        let (outputs, State::Halted) = interpreter.run_through_inputs(empty()).unwrap() else {
            panic!("Did not halt");
        };
        assert_eq!(outputs, vec![1125899906842624]);
    }

    /// Ensure that failure due to missing input leaves the interpreter in a sane state that can
    /// be recovered from
    #[test]
    fn missing_input_recoverable() {
        let mut interpreter = Interpreter::new(vec![3, 10, 4, 10, 99]);
        let old_state = interpreter.clone();

        let failed_run = interpreter.run_through_inputs(empty());

        // make sure that the failure returned the right ErrorState and left both `outputs` and
        // `interpreter` unchanged
        assert_eq!(failed_run, Ok((vec![], State::Awaiting)));
        assert_eq!(interpreter, old_state);

        // make sure that interpreter can still be used
        assert_eq!(
            interpreter.run_through_inputs(vec![1].into_iter()),
            Ok((vec![1], State::Halted))
        );
    }
}
