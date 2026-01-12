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
//!     interpreter.run_through_inputs(empty()).unwrap(),
//!     (vec![1024], State::Halted)
//! );
//! ```
//!
//! Additionally, if the `asm` feature is enabled, tools to work with a minimal assembly language
//! for Intcode are provided in the [asm] module, and if the `disasm` feature is enabled, then a
//! minimal [dissasemble][disasm::disassemble] function is provided.
//!
//! [Opcodes]: https://esolangs.org/wiki/Intcode#Opcodes
//! [Parameter Modes]: https://esolangs.org/wiki/Intcode#Parameter_Modes
//! [Day 9]: https://adventofcode.com/2019/day/9

/// A module providing a sort of logical memory management unit, using a hashmap to split memory
/// into segments, which are each contiguous in memory.
mod mmu;

use std::error::Error;
use std::fmt::{self, Display};
use std::iter::empty;
use std::ops::{Index, IndexMut};

/// A small module that re-exports items useful when working with the Intcode interpreter
pub mod prelude {
    pub use crate::{IntcodeAddress, Interpreter, State, StepOutcome};
    pub use std::iter::empty;
}

#[cfg(feature = "asm")]
pub mod asm;

mod disasm;
#[cfg(feature = "disasm")]
pub use disasm::disassemble;

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

#[derive(Debug, PartialEq)]
/// An error occured when executing an intcode instruction
pub enum ErrorState {
    /// An invalid opcode was encountered
    UnrecognizedOpcode(i64),
    /// An unknown parameter mode was encountered
    UnknownMode(i64),
    /// A negative memory address was encountered
    NegativeMemAccess(i64),
    /// An instruction tried to write to an immediate destination
    WriteToImmediate(i64),
    /// An interpreter was used after previously erroring out
    Poisoned,
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
            ErrorState::Poisoned => write!(f, "tried to reuse an interpreter after a fatal error"),
        }
    }
}

impl Error for ErrorState {}

// store IntcodeAddress within its own module so that visibility rules prevent accidentally
// creating an IntcodeAddress with a negative value
mod address {
    #[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Copy)]
    /// A non-negative i64, usable as an index into Intcode memory
    pub struct IntcodeAddress(i64);
    impl IntcodeAddress {
        /// Create a new [IntcodeAddress]. If `n` is negative, returns [None]
        #[inline]
        pub const fn new(n: i64) -> Option<Self> {
            if n < 0 { None } else { Some(Self(n)) }
        }

        /// get the inner [i64]
        #[inline]
        pub const fn get(&self) -> i64 {
            self.0
        }
    }
}

pub use address::IntcodeAddress;

#[derive(Clone)]
/// An intcode interpreter, which provides optional logging of executed instructions.
pub struct Interpreter {
    index: i64,
    rel_offset: i64,
    code: IntcodeMem,
    poisoned: bool,
    halted: bool,
    trace: Option<trace::Trace>,
}

// ignore the logger field
impl PartialEq for Interpreter {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.rel_offset == other.rel_offset && self.code == other.code
    }
}

impl fmt::Debug for Interpreter {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("Interpreter")
            .field("code", &self.code)
            .field("rbo", &self.rel_offset)
            .field("ip", &self.index)
            .field("tracing", &self.trace.is_some())
            .finish()
    }
}

impl Index<IntcodeAddress> for Interpreter {
    type Output = i64;

    fn index(&self, i: IntcodeAddress) -> &Self::Output {
        self.code.index(i.get())
    }
}

impl Index<i64> for Interpreter {
    type Output = i64;

    fn index(&self, i: i64) -> &Self::Output {
        assert!(i >= 0, "intcode memory cannot be at a negative index");
        self.code.index(i)
    }
}

impl IndexMut<IntcodeAddress> for Interpreter {
    fn index_mut(&mut self, i: IntcodeAddress) -> &mut Self::Output {
        self.code.index_mut(i.get())
    }
}

impl IndexMut<i64> for Interpreter {
    fn index_mut(&mut self, i: i64) -> &mut Self::Output {
        assert!(i >= 0, "intcode memory cannot be at a negative index");
        self.code.index_mut(i)
    }
}

pub mod trace;

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
#[derive(Debug, PartialEq, Clone, Copy)]
/// An Intcode OpCode
///
/// For explanations of the specific opcodes and their meaning, either go through Advent of Code
/// 2019, or see [asm::Instr].
#[allow(missing_docs, reason = "trivial")]
pub enum OpCode {
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

impl Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add => write!(f, "ADD"),
            Self::Mul => write!(f, "MUL"),
            Self::In => write!(f, "IN"),
            Self::Out => write!(f, "OUT"),
            Self::Jnz => write!(f, "JNZ"),
            Self::Jz => write!(f, "JZ"),
            Self::Lt => write!(f, "LT"),
            Self::Eq => write!(f, "EQ"),
            Self::Rbo => write!(f, "RBO"),
            Self::Halt => write!(f, "HALT"),
        }
    }
}

/// The outcome when an [Interpreter] tries to execute a single instruction
#[derive(Debug, PartialEq)]
pub enum StepOutcome {
    /// step ran successfully
    Running,
    /// Step could not run, with the [State] representing why
    Stopped(State),
}

#[repr(transparent)]
/// Attempted to access the contained negative memory index
#[derive(Debug, PartialEq)]
pub struct NegativeMemAccess(pub i64);

impl From<NegativeMemAccess> for ErrorState {
    fn from(NegativeMemAccess(i): NegativeMemAccess) -> Self {
        Self::NegativeMemAccess(i)
    }
}

impl Interpreter {
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
    #[inline]
    pub fn mem_override(&mut self, location: i64, value: i64) -> Result<(), NegativeMemAccess> {
        if location >= 0 {
            self.code[location] = value;
            Ok(())
        } else {
            Err(NegativeMemAccess(location))
        }
    }

    /// Get the memory at `address`
    #[doc(alias = "peek")]
    #[inline]
    pub fn mem_get(&self, address: i64) -> Result<i64, NegativeMemAccess> {
        if address >= 0 {
            Ok(self.code[address])
        } else {
            Err(NegativeMemAccess(address))
        }
    }

    /// Run a single instruction
    ///
    /// On an error, returns an [Err] containing the appropriate [ErrorState]
    /// Otherwise, returns an [Ok] containing the [StepOutcome]
    ///
    /// # Example
    ///
    /// ```
    /// use intcode::prelude::*;
    /// ```
    #[doc(alias("step", "run"))]
    pub fn exec_instruction(
        &mut self,
        input: &mut impl Iterator<Item = i64>,
        output: &mut Vec<i64>,
    ) -> Result<StepOutcome, ErrorState> {
        debug_assert!(self.index >= 0, "uncaught negative instruction index");
        if self.poisoned {
            return Err(ErrorState::Poisoned);
        }
        if self.halted {
            return Ok(StepOutcome::Stopped(State::Halted));
        }

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

        let (opcode, modes) = Self::parse_op(instruction)?;

        #[inline(always)]
        const fn i(n: i64) -> Result<i64, NegativeMemAccess> {
            if n >= 0 {
                Ok(n)
            } else {
                Err(NegativeMemAccess(n))
            }
        }

        macro_rules! trace {
            ($resolved: expr) => {
                if let Some(trace) = self.trace.as_mut() {
                    trace.push(instruction, self.index, self.rel_offset, &$resolved);
                }
            };
        }

        /// Shorthand to get the `$n`th parameter's value
        macro_rules! arg {
            ($n: literal) => {{
                const { assert!($n > 0) };
                match modes[$n - 1] {
                    ParamMode::Positional => {
                        let index = i(self.code[i(self.index + $n)?])?;
                        self.code[i(index)?]
                    }
                    ParamMode::Immediate => self.code[i(self.index + $n)?],
                    ParamMode::Relative => {
                        let index = i(self.code[i(self.index + $n)?] + self.rel_offset)?;
                        self.code[i(index)?]
                    }
                }
            }};
        }

        /// Resolves to the destination address pointed to by the `$n`th parameter
        macro_rules! dest {
            ($n: literal) => {{
                match modes[$n - 1] {
                    ParamMode::Positional => self.code[i(self.index + $n)?],
                    ParamMode::Immediate => {
                        self.poisoned = true;
                        return Err(ErrorState::WriteToImmediate(self.code[i(self.index + $n)?]));
                    }
                    ParamMode::Relative => self.rel_offset + self.code[i(self.index + $n)?],
                }
            }};
        }

        /// using a fake closure to pass in the expression that determines the value, this can
        /// implement all 4 instructions that take 2 inputs and an output
        macro_rules! a_b_out {
            (|$a: ident, $b: ident| $val: expr) => {{
                let $a = arg!(1);
                let $b = arg!(2);
                let (dest, val) = { (dest!(3), $val) };
                trace!([
                    (self.code[self.index + 1], $a),
                    (self.code[self.index + 2], $b),
                    (self.code[self.index + 3], dest),
                ]);
                self.code[i(dest)?] = val;
                self.index += 4;
                Ok(StepOutcome::Running)
            }};
        }

        macro_rules! jump_if {
            (|$n: ident| $expr: expr) => {{
                let $n = arg!(1);
                let dest = arg!(2);
                trace!([
                    (self.code[self.index + 1], $n),
                    (self.code[self.index + 2], dest),
                ]);
                if $expr {
                    self.index = i(dest)?;
                } else {
                    self.index += 3;
                }
                Ok(StepOutcome::Running)
            }};
        }

        match opcode {
            OpCode::Add => a_b_out!(|a, b| a + b),
            OpCode::Mul => a_b_out!(|a, b| a * b),
            OpCode::In => {
                let Some(input) = input.next() else {
                    return Ok(StepOutcome::Stopped(State::Awaiting));
                };
                let dest = dest!(1);
                trace!([(self.code[self.index + 1], input)]);
                self.code[i(dest)?] = input;
                self.index += 2;
                Ok(StepOutcome::Running)
            }
            OpCode::Out => {
                let out_val = arg!(1);
                trace!([(self.code[self.index + 1], out_val)]);
                output.push(out_val);
                self.index += 2;
                Ok(StepOutcome::Running)
            }
            OpCode::Jnz => jump_if!(|i| i != 0),
            OpCode::Jz => jump_if!(|i| i == 0),
            OpCode::Lt => a_b_out!(|a, b| if a < b { 1 } else { 0 }),
            OpCode::Eq => a_b_out!(|a, b| if a == b { 1 } else { 0 }),
            OpCode::Rbo => {
                let offset = arg!(1);
                trace!([(self.code[self.index + 1], offset)]);
                self.rel_offset += arg!(1);
                self.index += 2;
                Ok(StepOutcome::Running)
            }
            OpCode::Halt => {
                trace!([]);
                self.halted = true;
                Ok(StepOutcome::Stopped(State::Halted))
            }
        }
    }

    /// Create a new interpreter. Collects `code` into the starting memory state.
    ///
    /// Panics if the number of entries exceeds `i64::MAX`
    pub fn new(code: impl IntoIterator<Item = i64>) -> Self {
        Self {
            index: 0,
            rel_offset: 0,
            poisoned: false,
            halted: false,
            trace: None,
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
        loop {
            match self.exec_instruction(&mut inputs, &mut outputs) {
                Ok(StepOutcome::Running) => (),
                Ok(StepOutcome::Stopped(state)) => break Ok((outputs, state)),
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
            self.exec_instruction(&mut empty(), &mut Vec::with_capacity(0))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
            interpreter.run_through_inputs([1]),
            Ok((vec![1], State::Halted))
        );
    }
}
