// SPDX-FileCopyrightText: 2024 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD
#![warn(missing_docs)]

//! Library for working with Intcode and an Intcode assembly language
//!
//! This library provides a few different parts to it:
//!
//! # Intcode Interpreter
//!
//! [`Interpreter`] is a fully-functional Intcode interpreter, with a design and API derived from
//! the author's [Advent of Code solutions](https://github.com/eliminmax/advent-of-code), cleaned
//! up and made more generally usable. It uses [`i64`] as the type of Intcode integers, and some
//! select Advent of Code solutions using it can be found in this crate's [examples], though the
//! actual Intcode programs are not included, to comply with the restrictions on sharing Advent of
//! Code inputs.
//!
//! ## Interpreter Example
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
//! # Intcode Assembly Language (IAL)
//!
//! The [`asm`] module provides functions for assembling IAL.
//!
//! ## Basic Assembler Example
//!
//! ```rust
//! use ial::asm::assemble;
//! let intcode = assemble("OUT #1024\nHALT").unwrap();
//! assert_eq!(intcode, vec![104, 1024, 99]);
//! ```
//!
//! # Intcode Disassembler
//!
//! The [`disasm`] module provides a function to disassemble intcode into IAL, though it has some
//! limits; see [`disasm::disassemble` § caveats] for details.
//!
//! ## Basic Disassembler Example
//!
//! ```rust
//! use ial::disasm::disassemble;
//! let disassembly = disassemble([104, 1024, 99]);
//! assert_eq!(&disassembly, "OUT #1024\nHALT\n");
//! ```
//!
//! # [`DebugInfo`]
//!
//! The [`debug_info`] module defines a [`DebugInfo`] struct that can be used with an
//! [`Interpreter`] to diagnose issues with [`Interpreter::write_diagnostic`], and can be used to
//! disassemble with more accuracy than [`disasm::disassemble`].
//!
//! ## Example: using [`DebugInfo`] for more accurate disassembly
//!
//! Comparsion between [`disasm::disassemble`] and [`disasm::disassemble_with_debug`]:
//!
//! ```rust
//! use ial::asm::{build_ast, assemble_with_debug};
//! use ial::disasm::{disassemble, disassemble_with_debug};
//! let ial = r#"; Just because you can write IAL like this, doesn't mean you should!
//! ASCII "h"  ; ASCII 'h' is 104
//! DATA 32 * ('!' / 8 * 2 * (2 + 2)), 999 / 10 ; ASCII '!' is 33; 999/10 truncates to 99"#;
//! let ast = build_ast(ial).unwrap();
//! let (intcode, debug_info) = assemble_with_debug(ast).unwrap();
//!
//! // Because `disassemble` doesn't have access to the debug info, it can't tell that it was
//! // actually an abomination, and because it sees valid instructions, it disassembles to them.
//! let default_disasm = disassemble(intcode.clone());
//! assert_eq!(&default_disasm, "OUT #1024\nHALT\n");
//!
//! // It isn't identical, but using the debug info at least matches directive types:
//! let debug_info_disasm = disassemble_with_debug(intcode, &debug_info).unwrap();
//! assert_eq!(&debug_info_disasm, "ASCII \"h\"\nDATA 1024, 99\n")
//! ```
//!
//! [examples]: <https://github.com/eliminmax/ial/tree/main/examples>
//! [`disasm::disassemble` § caveats]: disasm::disassemble#caveats
//! [`DebugInfo`]: debug_info::DebugInfo

#[doc(hidden)]
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// A module implementing internal logic that doesn't fit cleanly into the module hierarchy
mod internals;

pub use ial_core::{ParamMode, UnknownMode};

/// A module providing a sort of logical memory management unit, using a hashmap to split memory
/// into segments, which are each contiguous in memory.
mod mmu;

use disasm::disassemble_with_debug;
use debug_info::DebugInfo;
use itertools::Itertools;
use std::convert::AsRef;
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::io::{self, Write};
use std::iter::empty;
use std::ops::{Index, IndexMut, Range};

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
    NegativeMemAccess(NegativeMemAccess),
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
            InterpreterError::NegativeMemAccess(err) => Display::fmt(err, f),
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
        write!(f, "could not convert {} to unsigned index", self.0)
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

impl Debug for Interpreter {
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

impl From<UnknownMode> for InterpreterError {
    fn from(mode: UnknownMode) -> Self {
        Self::UnknownMode(i64::from(mode.digit()))
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
/// An Intcode `OpCode`
///
/// For explanations of the specific opcodes and their meaning, either go through Advent of Code
/// 2019, or see [the IAL docs](https://github.com/eliminmax/ial/blob/main/IAL.md#instructions).
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
    fn from(i: NegativeMemAccess) -> Self {
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

    /// Get a range of memory addresses
    ///
    /// # Examples
    ///
    /// ```
    /// use ial::prelude::*;
    /// use ial::asm::assemble;
    /// // short intcode program that sets an unset int to the HALT instruction, then executes it
    /// let intcode = assemble("ADD #90, #9, halt\nhalt:").unwrap();
    /// let mut interp = Interpreter::new(intcode);
    /// interp.run_through_inputs(empty()).unwrap();
    /// let expected: &[i64] = &[1101, 90, 9, 4, 99];
    /// assert_eq!(interp.get_range(0..5).unwrap(), expected);
    /// ```
    ///
    /// Works even if the range is split across multiple allocations (see Note below):
    ///
    /// ```
    /// use ial::prelude::*;
    /// use ial::OpCode;
    /// // generate code large enough that it will be split
    /// let code = (0..8192).fold(
    ///     Vec::with_capacity(16384),
    ///     |mut v, i| { v.extend([OpCode::Out as i64 + 100, i]); v }
    /// );
    /// let interp = Interpreter::new(code.clone());
    /// assert_eq!(interp.get_range(0..16384).unwrap(), &code);
    /// ```
    ///
    /// Works if the span is outside the bounds of the actually-stored memory
    /// ```
    /// use ial::prelude::*;
    /// use ial::OpCode;
    /// let interp = Interpreter::new([OpCode::Halt as i64]);
    /// assert_eq!(interp.get_range(100..1000).unwrap(), [0_i64; 900].as_slice());
    /// ```
    ///
    /// # Note
    ///
    /// Given the current strategy for handling high intcode indexes, the range may be split across
    /// multiple heap allocations, so this function currently returns a
    /// [`Cow<'_, [i64]>`][std::borrow::Cow], though this may change in the future.
    ///
    /// # Errors
    ///
    /// If the range starts with a negative index, returns [`NegativeMemAccess`] containing that
    /// index.
    pub fn get_range(
        &self,
        range: Range<i64>,
    ) -> Result<impl AsRef<[i64]> + Debug + PartialEq<&[i64]> + Clone, NegativeMemAccess> {
        if range.start >= 0 {
            Ok(self.code.get_range(range))
        } else {
            Err(NegativeMemAccess(range.start))
        }
    }
    /// Write human-readable diagnostic information about the interpreter's state to `writer`
    ///
    /// Uses [`debug_info.labels`][DebugInfo::labels] to determine points of interest, and to
    /// disassemble the intcode memory.
    ///
    /// # Errors
    ///
    /// If writing to `writer` fails, returns the resulting [`io::Error`].
    ///
    /// If `debug_info` fails to apply to this [`Interpreter`], then it does not return an error,
    /// but it does write the error message instead of writing the dissassembly to the output.
    pub fn write_diagnostic<W: Write>(
        &self,
        debug_info: &DebugInfo,
        writer: &mut W,
    ) -> io::Result<()> {
        use std::collections::BTreeMap;
        let label_map = debug_info
            .labels
            .iter()
            .map(|(s, a)| (a, s.inner.as_ref()))
            .into_group_map();
        let directive_starts = debug_info
            .directives
            .iter()
            .enumerate()
            .filter_map(|(i, dir)| {
                i64::try_from(dir.output_span.start)
                    .ok()
                    .map(|start| (start, i + 1))
            })
            .collect::<BTreeMap<i64, usize>>();

        writeln!(writer, "INTERPRETER STATE")?;
        if let Some(labels) = label_map.get(&self.index) {
            writeln!(
                writer,
                "    instruction pointer: {} ({})",
                self.index,
                labels.join(", ")
            )?;
        } else {
            writeln!(writer, "    instruction pointer: {}", self.index)?;
        }
        if let Some(i) = directive_starts.get(&self.index) {
            writeln!(writer, "        directive #{i}")
        } else {
            writeln!(writer, "        not a directive boundary")
        }?;

        if let Some(labels) = label_map.get(&self.rel_offset) {
            writeln!(
                writer,
                "    relative base: {} ({})",
                self.rel_offset,
                labels.join(", ")
            )?;
        } else {
            writeln!(writer, "    relative base {}", self.rel_offset)?;
        }

        match disassemble_with_debug(self.code.clone(), debug_info) {
            Ok(dis) => writeln!(writer, "\n\nDISASSEMBLY\n{dis}")?,
            Err(e) => writeln!(
                writer,
                "unable to disassemble with provided debug_info: {e}"
            )?,
        }
        Ok(())
    }
}
