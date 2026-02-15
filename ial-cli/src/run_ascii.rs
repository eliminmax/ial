// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Run interactively in Aft Scaffolding Control and Information Interface mode, using stdin and
//! stdout for I/O

use anyhow::Result;
use clap::{ArgAction, Parser, ValueHint};
use ial::asm::{assemble_with_debug, build_ast};
use ial::debug_info::DebugInfo;
use ial::{State, StepOutcome, prelude::*};
use std::error::Error;
use std::fmt::{self, Display};
use std::fs::{OpenOptions, read_to_string};
use std::io::{self, stderr, stdin};
use std::path::PathBuf;

use crate::{checked_ast_fn, checked_assemble, debug_path};

#[derive(Debug, Parser)]
#[allow(
    clippy::struct_excessive_bools,
    clippy::option_option,
    reason = "clap args struct"
)]
pub(crate) struct RunAsciiArgs {
    // File containing the source code to interpret
    #[arg(value_name = "CODE", value_hint = ValueHint::FilePath)]
    code: PathBuf,
    /// Load debug info from file
    ///
    /// If no filename is provided, uses the intcode file name with the extension replaced with
    /// "ialdbg". If the intcode file has no extension, then ".ialdbg" is simply appended to it.
    ///
    /// If no filename or intcode file are provided, uses the name "ialdbg" in the current
    /// directory.
    #[arg(short = 'g', long, value_name = "DEBUG", value_hint = ValueHint::FilePath)]
    debug_info: Option<Option<PathBuf>>,
    /// Error out on invalid ASCII
    #[arg(short, long, action = ArgAction::SetTrue)]
    strict_ascii: bool,
    /// Read CODE as IAL instead of Intcode
    ///
    /// The IAL will be assembled immediately before execution, with debug info generated and
    /// stored in memory.
    ///
    /// Conflicts with --debug-info
    #[arg(short, long, action = ArgAction::SetTrue)]
    #[arg(conflicts_with = "debug-info")]
    assemble_intcode: bool,
    /// Disable buffering of output
    #[arg(short, long, action = ArgAction::SetTrue)]
    unbuffered_output: bool,
    /// Show a trace of the interpreter as it runs
    ///
    /// Requires unbuffered output
    #[arg(short = 't', long, action = ArgAction::SetTrue)]
    #[arg(requires = "unbuffered-output")]
    show_trace: bool,
}

macro_rules! to_ascii_char {
    ($e: expr) => {{
        #[allow(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "in macro to make it explicit"
        )]
        {
            $e as u8 as char
        }
    }};
}

fn get_line(strict: bool) -> Result<impl Iterator<Item = i64>, AsciiError> {
    let mut buf = String::new();
    stdin().read_line(&mut buf).map_err(AsciiError::IoError)?;
    if !strict || buf.is_ascii() {
        Ok(buf.into_bytes().into_iter().map(i64::from))
    } else {
        let bad_char = buf
            .chars()
            .find(|c| !c.is_ascii())
            .expect("non-ASCII char will be in non-ASCII string");
        Err(AsciiError::InvalidAsciiChar(bad_char))
    }
}

fn print_ascii(intcode_output: Vec<i64>, strict: bool) -> Result<(), AsciiError> {
    let mut s = String::with_capacity(intcode_output.len());
    for i in intcode_output {
        if let c @ 0..127 = i {
            s.push(to_ascii_char!(c));
        } else if strict {
            return Err(AsciiError::InvalidAsciiInt(i));
        } else {
            print!("{s}«non-ASCII value {i}»");
            s.clear();
        }
    }
    print!("{s}");
    Ok(())
}

macro_rules! err_with_interp {
    ($e: expr, $i: ident) => {{
        match $e {
            Ok(ok) => ok,
            Err(err) => return Err((err.into(), $i)),
        }
    }};
}

fn interactive_unbufferred(
    mut interp: Interpreter,
    strict: bool,
    trace: bool,
) -> Result<(), (AsciiError, Interpreter)> {
    if trace {
        interp.start_trace();
    }
    err_with_interp!(interp.precompute(), interp);
    if trace && let Some(t) = interp.start_trace().unwrap().0.first() {
        eprintln!("{t:?}");
    }
    let mut inputs = None;
    loop {
        let mut output = Vec::with_capacity(1);
        let step_outcome = if let Some(inputs) = inputs.as_mut() {
            interp.exec_instruction(inputs, &mut output)
        } else {
            interp.exec_instruction(&mut empty(), &mut output)
        };
        match err_with_interp!(step_outcome, interp) {
            StepOutcome::Running => {
                err_with_interp!(print_ascii(output, strict), interp);
                if trace {
                    eprintln!("{:?}", interp.start_trace().unwrap().0[0]);
                }
            }
            StepOutcome::Stopped(State::Awaiting) => {
                inputs = Some(err_with_interp!(get_line(strict), interp));
            }
            StepOutcome::Stopped(State::Halted) => break,
        }
    }
    if trace {
        eprintln!("{:?}", interp.end_trace().unwrap());
    }
    Ok(())
}

fn interactive_run(mut interp: Interpreter, strict: bool) -> Result<(), (AsciiError, Interpreter)> {
    let (output, mut state) = err_with_interp!(interp.run_through_inputs(empty()), interp);
    err_with_interp!(print_ascii(output, strict), interp);
    while state != State::Halted {
        let (output, new_state) = err_with_interp!(
            interp.run_through_inputs(err_with_interp!(get_line(strict), interp)),
            interp
        );
        err_with_interp!(print_ascii(output, strict), interp);
        state = new_state;
    }
    Ok(())
}

impl RunAsciiArgs {
    pub(crate) fn run(&self) -> Result<()> {
        let (prog, debug_info) = if self.assemble_intcode {
            let src = read_to_string(&self.code)?;
            let path = self.code.as_os_str().to_string_lossy();
            let ast = checked_ast_fn(
                build_ast,
                &path,
                &src,
            );
            let (prog, debug_info) = checked_assemble(assemble_with_debug, ast, &path, &src);
            (prog, Some(debug_info))
        } else {
            let prog = read_to_string(&self.code)?
                .trim()
                .split(',')
                .map(str::parse)
                .collect::<Result<Vec<i64>, _>>()?;

            let debug_info = if let Some(path) = &self.debug_info {
                Some(DebugInfo::read(
                    OpenOptions::new()
                        .read(true)
                        .open(debug_path(path.as_ref()))?,
                )?)
            } else {
                None
            };

            (prog, debug_info)
        };

        let interp = Interpreter::new(prog);

        let run_outcome = if self.unbuffered_output || self.show_trace {
            interactive_unbufferred(interp, self.strict_ascii, self.show_trace)
        } else {
            interactive_run(interp, self.strict_ascii)
        };

        if let Err((err, interp)) = run_outcome {
            if let Some(debug_info) = debug_info.as_ref() {
                eprintln!("INTERPRETER ERROR\n\n");
                interp.write_diagnostic(debug_info, &mut stderr())?;
            }
            Err(err.into())
        } else {
            Ok(())
        }
    }
}

#[derive(Debug)]
pub enum AsciiError {
    IoError(io::Error),
    InvalidAsciiChar(char),
    InvalidAsciiInt(i64),
    InterpreterError(ial::InterpreterError),
}

impl Error for AsciiError {}
impl Display for AsciiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AsciiError::IoError(e) => write!(f, "an I/O error occured: {e}"),
            AsciiError::InvalidAsciiInt(n) => write!(f, "{n} is not a valid ASCII character"),
            AsciiError::InvalidAsciiChar(c) => write!(f, "{c:?} is not a valid ASCII character"),
            AsciiError::InterpreterError(e) => Display::fmt(e, f),
        }
    }
}

impl From<ial::InterpreterError> for AsciiError {
    fn from(e: ial::InterpreterError) -> Self {
        Self::InterpreterError(e)
    }
}
