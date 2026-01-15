// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Run interactively in Aft Scaffolding Control and Information Interface mode, using stdin and
//! stdout for I/O

use ial::Interpreter;
use std::env::args_os;
use std::error::Error;
use std::fmt::{self, Display};
use std::fs::read_to_string;

fn get_line() -> Result<impl Iterator<Item = i64>, AsciiError> {
    let mut buf = String::new();
    std::io::stdin()
        .read_line(&mut buf)
        .map_err(AsciiError::IoError)?;
    if buf.is_ascii() {
        Ok(buf.into_bytes().into_iter().map(i64::from))
    } else {
        let bad_char = buf
            .chars()
            .find(|c| !c.is_ascii())
            .expect("non-ASCII char will be in non-ASCII string");
        Err(AsciiError::InvalidAsciiChar(bad_char))
    }
}

fn print_ascii(intcode_output: Vec<i64>) -> Result<(), AsciiError> {
    let mut s = String::with_capacity(intcode_output.len());
    for i in intcode_output {
        match i {
            0..127 => s.push(i as u8 as char),
            _ => return Err(AsciiError::InvalidAsciiInt(i)),
        }
    }
    print!("{s}");
    Ok(())
}

fn interactive_run(mut interp: Interpreter) -> Result<(), AsciiError> {
    let (output, mut state) = interp.run_through_inputs(std::iter::empty())?;
    print_ascii(output)?;
    while state != ial::State::Halted {
        let (output, new_state) = interp.run_through_inputs(get_line()?)?;
        print_ascii(output)?;
        state = new_state;
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = read_to_string(args_os().nth(1).ok_or("no program provided")?)?;
    let prog = Interpreter::new(input.trim().split(',').map(str::parse).map(Result::unwrap));
    interactive_run(prog).map_err(Into::into)
}

#[derive(Debug)]
pub enum AsciiError {
    IoError(std::io::Error),
    InvalidAsciiChar(char),
    InvalidAsciiInt(i64),
    InterpreterError(ial::ErrorState),
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

impl From<ial::ErrorState> for AsciiError {
    fn from(e: ial::ErrorState) -> Self {
        Self::InterpreterError(e)
    }
}
