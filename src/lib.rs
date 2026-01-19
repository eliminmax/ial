// SPDX-FileCopyrightText: 2024 - 2026 Eli Array Minkoff
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
//! use ial::prelude::*;
//! let mut interpreter = Interpreter::new(vec![104, 1024, 99]);
//!
//! assert_eq!(
//!     interpreter.run_through_inputs(empty()).unwrap(),
//!     (vec![1024], State::Halted)
//! );
//! ```
//!
//! Additionally, the [asm] module provides tools to work with a minimal assembly language for
//! Intcode, and the [disasm] module provides a disassembler function.
//!
//! [Opcodes]: https://esolangs.org/wiki/Intcode#Opcodes
//! [Parameter Modes]: https://esolangs.org/wiki/Intcode#Parameter_Modes
//! [Day 9]: https://adventofcode.com/2019/day/9

/// A module implementing the internals of the [Interpreter]
mod internals;
/// A module providing a sort of logical memory management unit, using a hashmap to split memory
/// into segments, which are each contiguous in memory.
mod mmu;

use std::error::Error;
use std::fmt::{self, Display};
use std::iter::empty;
use std::ops::{Index, IndexMut};

pub mod trace;

/// A small module that re-exports items useful when working with the Intcode interpreter
pub mod prelude {
    pub use crate::{IntcodeAddress, Interpreter, State, StepOutcome};
    pub use std::iter::empty;
}

pub mod asm;

pub mod debug_info;
pub mod disasm;

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
pub enum InterpreterError {
    /// An invalid opcode was encountered
    UnrecognizedOpcode(i64),
    /// An unknown parameter mode was encountered
    UnknownMode(i64),
    /// A parameter referenced a negative memory address
    NegativeMemAccess(i64),
    /// A jump resolved to a negative address
    JumpToNegative(i64),
    /// An instruction tried to write to an immediate destination
    WriteToImmediate(i64),
    /// An interpreter was used after previously erroring out
    Poisoned,
}

impl Display for InterpreterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InterpreterError::UnrecognizedOpcode(n) => {
                write!(f, "encountered unrecognized opcode {n}")
            }
            InterpreterError::UnknownMode(mode) => {
                write!(f, "encountered unknown parameter mode {mode}")
            }
            InterpreterError::NegativeMemAccess(e) => {
                write!(f, "could not convert index to unsigned address: {e}")
            }
            InterpreterError::JumpToNegative(n) => {
                write!(f, "jumpped to negative address {n}")
            }
            InterpreterError::WriteToImmediate(i) => {
                write!(f, "code attempted to write to immediate {i}")
            }
            InterpreterError::Poisoned => {
                write!(f, "tried to reuse an interpreter after a fatal error")
            }
        }
    }
}

impl Error for InterpreterError {}

impl Display for NegativeMemAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "could not convert index to unsigned address: {}", self.0)
    }
}

impl Error for NegativeMemAccess {}

// store IntcodeAddress within its own module so that visibility rules prevent accidentally
// creating an IntcodeAddress with a negative value
mod address {
    #[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Copy)]
    /// A non-negative i64, usable as an index into Intcode memory
    pub struct IntcodeAddress(i64);
    impl IntcodeAddress {
        /// Create a new [`IntcodeAddress`]. If `n` is negative, returns [None]
        #[inline]
        #[must_use]
        pub const fn new(n: i64) -> Option<Self> {
            if n < 0 { None } else { Some(Self(n)) }
        }

        /// get the inner [i64]
        #[inline]
        #[must_use]
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
            .field("poisoned", &self.poisoned)
            .field("halted", &self.halted)
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

impl ParamMode {
    /// Extract the parameter modes from the provided opcode [i64]
    ///
    /// Digits are read from the absolute value of `op_int`.
    ///
    /// # Examples
    ///
    /// ```
    ///# use ial::{ParamMode, UnknownMode};
    /// assert_eq!(
    ///     ParamMode::extract(21001).unwrap(),
    ///     [
    ///         ParamMode::Positional,
    ///         ParamMode::Immediate,
    ///         ParamMode::Relative,
    ///     ],
    /// );
    /// assert_eq!(
    ///     ParamMode::extract(-21001).unwrap(),
    ///     [
    ///         ParamMode::Positional,
    ///         ParamMode::Immediate,
    ///         ParamMode::Relative,
    ///     ],
    /// );
    /// assert!(ParamMode::extract(31001).is_err());
    /// ```
    /// # Errors
    ///
    /// If any of the hundred's, thousand's, or ten thousand's digits are not a valid mode defined
    /// in ether Advent Of Code day [5] or [9], returns an [`UnknownMode`] containing the mode
    /// digit.
    ///
    /// [5]: https://adventofcode.com/2019/day/5
    /// [9]: https://adventofcode.com/2019/day/9
    pub fn extract(op_int: i64) -> Result<[Self; 3], UnknownMode> {
        let op_int = op_int.abs();
        Ok([
            ((op_int / 100) % 10).try_into()?,
            ((op_int / 1000) % 10).try_into()?,
            ((op_int / 10000) % 10).try_into()?,
        ])
    }
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
    type Error = UnknownMode;
    fn try_from(i: i64) -> Result<Self, Self::Error> {
        match i {
            0 => Ok(ParamMode::Positional),
            1 => Ok(ParamMode::Immediate),
            2 => Ok(ParamMode::Relative),
            _ => Err(Self::Error {
                mode_digit: (i % 10) as i8,
            }),
        }
    }
}

#[derive(Debug)]
/// An unknown mode was specified in an instruction
pub struct UnknownMode {
    mode_digit: i8,
}

impl From<UnknownMode> for InterpreterError {
    fn from(UnknownMode { mode_digit: i }: UnknownMode) -> Self {
        Self::UnknownMode(i64::from(i))
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
/// An Intcode `OpCode`
///
/// For explanations of the specific opcodes and their meaning, either go through Advent of Code
/// 2019, or see [`asm::Instr`].
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

impl TryFrom<i64> for OpCode {
    type Error = i64;
    fn try_from(i: i64) -> Result<Self, Self::Error> {
        match i {
            1 => Ok(Self::Add),
            2 => Ok(Self::Mul),
            3 => Ok(Self::In),
            4 => Ok(Self::Out),
            5 => Ok(Self::Jnz),
            6 => Ok(Self::Jz),
            7 => Ok(Self::Lt),
            8 => Ok(Self::Eq),
            9 => Ok(Self::Rbo),
            99 => Ok(Self::Halt),
            _ => Err(i),
        }
    }
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

impl From<NegativeMemAccess> for InterpreterError {
    fn from(NegativeMemAccess(i): NegativeMemAccess) -> Self {
        Self::NegativeMemAccess(i)
    }
}

impl Interpreter {
    /// Manually set a memory location to a provided value
    ///
    /// # Errors
    ///
    /// if `location` is negative, returns a [`NegativeMemAccess`] error
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

    /// Get the memory at `address`.
    ///
    /// # Errors
    ///
    /// if `address` is negative, returns a [`NegativeMemAccess`] error
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
    /// On an error, returns an [Err] containing the appropriate [`InterpreterError`]
    /// Otherwise, returns an [Ok] containing the [`StepOutcome`]
    ///
    /// # Example
    ///
    /// ```
    /// use ial::prelude::*;
    /// let mut interp = Interpreter::new([1101, 90, 9, 8, 3, 7, 4, -1]);
    /// let mut out = Vec::new();
    ///
    /// // the first instruction is `ADD #90, #9, 8`
    /// assert_eq!(interp.exec_instruction(&mut empty(), &mut out), Ok(StepOutcome::Running));
    /// // the second instruction is `IN 7`, but no input was provided.
    /// assert_eq!(
    ///     interp.exec_instruction(&mut empty(), &mut out),
    ///     Ok(StepOutcome::Stopped(State::Awaiting)),
    /// );
    ///
    /// // now try again, but with input available
    /// assert_eq!(
    ///     interp.exec_instruction(&mut [8].into_iter(), &mut out),
    ///     Ok(StepOutcome::Running)
    /// );
    ///
    /// // the third instruction was originally OUT -1, but the address was overwritten by the
    /// // previous instruction, so it will now read from address 8, where the 1st instruction
    /// // inserted 99.
    /// assert!(out.is_empty());
    /// assert_eq!(interp.exec_instruction(&mut empty(), &mut out), Ok(StepOutcome::Running));
    /// assert_eq!(out.as_slice(), [99].as_slice());
    ///
    /// // finally, the halt instruction
    /// assert_eq!(
    ///     interp.exec_instruction(&mut empty(), &mut out),
    ///     Ok(StepOutcome::Stopped(State::Halted))
    /// );
    /// ```
    ///
    /// # Errors
    ///
    /// If the interpreter has previously marked itself as poisoned, returns
    /// [`InterpreterError::Poisoned`] before attempting to do anything.
    ///
    /// Otherwise, if any of the following conditions occur, it marks itself as poisoned and
    /// returns the listed [`InterpreterError`] variant:
    ///
    ///
    /// | Condition                                           | Error type             |
    /// |-----------------------------------------------------|------------------------|
    /// | Opcode is unrecognized                              | [`UnrecognizedOpcode`] |
    /// | Mode digit is unrecognized                          | [`UnknownMode`]        |
    /// | Instruction accesses a negative index               | [`NegativeMemAccess`]  |
    /// | Jump instruction would jump to negative index       | [`JumpToNegative`]     |
    /// | Add, Mul, In, Lt, or Eq output is in immediate mode | [`WriteToImmediate`]   |
    ///
    /// [`UnrecognizedOpcode`]: InterpreterError::UnrecognizedOpcode
    /// [`UnknownMode`]: InterpreterError::UnknownMode
    /// [`NegativeMemAccess`]: InterpreterError::NegativeMemAccess
    /// [`JumpToNegative`]: InterpreterError::JumpToNegative
    /// [`WriteToImmediate`]: InterpreterError::WriteToImmediate
    #[doc(alias("step", "run"))]
    pub fn exec_instruction(
        &mut self,
        input: &mut impl Iterator<Item = i64>,
        output: &mut Vec<i64>,
    ) -> Result<StepOutcome, InterpreterError> {
        if self.poisoned {
            return Err(InterpreterError::Poisoned);
        }

        if self.halted {
            return Ok(StepOutcome::Stopped(State::Halted));
        }

        debug_assert!(self.index >= 0, "uncaught negative instruction index");

        let (opcode, modes) = Self::parse_op(self.code[self.index])?;

        match opcode {
            OpCode::Add => self.op3(modes, |a, b| a + b),
            OpCode::Mul => self.op3(modes, |a, b| a * b),
            OpCode::In => {
                let Some(input) = input.next() else {
                    return Ok(StepOutcome::Stopped(State::Awaiting));
                };
                let dest = self.resolve_dest(modes[0], 1)?;
                self.trace([(self.code[self.index + 1], input)]);
                self.code[dest] = input;
                self.index += 2;
                Ok(StepOutcome::Running)
            }
            OpCode::Out => {
                let out_val = self.resolve_param(modes[0], 1)?;
                self.trace([(self.code[self.index + 1], out_val)]);
                output.push(out_val);
                self.index += 2;
                Ok(StepOutcome::Running)
            }
            OpCode::Jnz => self.jump(modes, |i| i != 0),
            OpCode::Jz => self.jump(modes, |i| i == 0),
            OpCode::Lt => self.op3(modes, |a, b| i64::from(a < b)),
            OpCode::Eq => self.op3(modes, |a, b| i64::from(a == b)),
            OpCode::Rbo => {
                let offset = self.resolve_param(modes[0], 1)?;
                self.trace([(self.code[self.index + 1], offset)]);
                self.rel_offset += offset;
                self.index += 2;
                Ok(StepOutcome::Running)
            }
            OpCode::Halt => {
                self.trace([]);
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
    /// # Errors
    ///
    /// If an internal call to [`self.exec_instruction`][Interpreter::exec_instruction] fails,
    /// returns the resulting [`InterpreterError`] unchanged.
    pub fn run_through_inputs(
        &mut self,
        inputs: impl IntoIterator<Item = i64>,
    ) -> Result<(Vec<i64>, State), InterpreterError> {
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
    ///
    /// # Errors
    ///
    /// If an internal call to [`self.exec_instruction`][Interpreter::exec_instruction] fails,
    /// returns the resulting [`InterpreterError`] unchanged.
    pub fn precompute(&mut self) -> Result<(), InterpreterError> {
        while Self::parse_op(self.code[self.index])
            .is_ok_and(|(opcode, _)| !matches!(opcode, OpCode::In | OpCode::Out | OpCode::Halt))
        {
            self.exec_instruction(&mut empty(), &mut Vec::with_capacity(0))?;
        }
        Ok(())
    }
}

/// Ensure that failure due to missing input leaves the interpreter in a sane state that can
/// be recovered from
#[test]
fn missing_input_recoverable() {
    let mut interpreter = Interpreter::new(vec![3, 10, 4, 10, 99]);
    let old_state = interpreter.clone();

    let failed_run = interpreter.run_through_inputs(empty());

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
