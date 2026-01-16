// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Run interactively in Aft Scaffolding Control and Information Interface mode, using stdin and
//! stdout for I/O

use ial::asm::DebugInfo;
use ial::prelude::*;
use std::error::Error;
use std::fmt::{self, Display};
use std::fs::{self, OpenOptions, read_to_string};
use std::io::{self, stderr, stdin};
use std::path::{Path, PathBuf};

use clap::{Parser, ValueEnum};

#[derive(PartialEq, Clone, Copy, ValueEnum)]
enum CodeFormat {
    /// comma-separated ASCII-encoded decimal numbers
    #[value(alias("text"))]
    #[value(alias("aoc"))]
    Ascii,
    /// little-endian 64-bit integers
    #[cfg_attr(target_endian = "little", value(alias("binary-native")))]
    #[value(name("binary-little-endian"), alias("binle"))]
    LittleEndian,
    #[cfg_attr(target_endian = "big", value(alias("binary-native")))]
    #[value(name("binary-big-endian"), alias("binbe"))]
    /// big-endian 64-bit integers
    BigEndian,
}

const VERSION: &str = concat!(env!("CARGO_CRATE_NAME"), '-', env!("CARGO_PKG_VERSION"));

#[derive(Parser)]
#[command(version = env!("CARGO_PKG_VERSION"))]
#[command(long_version = VERSION)]
#[command(about = "IAC Assembler", long_about = None)]
struct Args {
    #[arg(help = "The source code to interpret")]
    source: PathBuf,
    #[arg(short = 'g', long = "debug-file")]
    #[arg(help = "File containing debug info")]
    debug_info: Option<PathBuf>,
    #[arg(help = "Input format for the intcode")]
    #[arg(short, long)]
    #[arg(default_value = "ascii")]
    format: CodeFormat,
}

fn get_line() -> Result<impl Iterator<Item = i64>, AsciiError> {
    let mut buf = String::new();
    stdin().read_line(&mut buf).map_err(AsciiError::IoError)?;
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

fn interactive_run(mut interp: Interpreter) -> Result<(), (AsciiError, Interpreter)> {
    macro_rules! err_with_interp {
        ($e: expr) => {{
            match $e {
                Ok(ok) => ok,
                Err(err) => return Err((err.into(), interp)),
            }
        }};
    }
    let (output, mut state) = err_with_interp!(interp.run_through_inputs(empty()));
    err_with_interp!(print_ascii(output));
    while state != ial::State::Halted {
        let (output, new_state) =
            err_with_interp!(interp.run_through_inputs(err_with_interp!(get_line())));
        err_with_interp!(print_ascii(output));
        state = new_state;
    }
    Ok(())
}

fn read_bin_file<F: Fn([u8; 8]) -> i64>(file: &Path, func: F) -> Result<Vec<i64>, Box<dyn Error>> {
    let input = fs::read(file)?;
    let (chunks, remainder) = input.as_chunks::<8>();
    if !remainder.is_empty() {
        return Err(Box::new(IncompleteI64(Box::from(remainder))));
    }
    Ok(chunks.iter().map(|c| func(*c)).collect())
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    let prog = match args.format {
        CodeFormat::Ascii => read_to_string(args.source)?
            .split(',')
            .map(str::trim)
            .map(str::parse)
            .collect::<Result<Vec<i64>, _>>()?,
        CodeFormat::LittleEndian => read_bin_file(&args.source, i64::from_le_bytes)?,
        CodeFormat::BigEndian => read_bin_file(&args.source, i64::from_be_bytes)?,
    };

    let debug_info = if let Some(path) = args.debug_info.as_deref() {
        let f = (OpenOptions::new().read(true).open(path))
            .map_err(|e| format!("failed to read {}: {e}", path.display()))?;
        Some(DebugInfo::read(f)?)
    } else {
        None
    };

    let prog = Interpreter::new(prog);
    if let Err((err, interp)) = interactive_run(prog) {
        if let Some(debug_info) = debug_info.as_ref() {
            interp.diagnose(debug_info, &mut stderr())?;
        }
        Err(err.into())
    } else {
        Ok(())
    }
}

#[derive(Debug)]
struct IncompleteI64(Box<[u8]>);

impl IncompleteI64 {}

impl Display for IncompleteI64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "expected 8 bytes, got {}: {:02x?}", self.0.len(), self.0)
    }
}
impl Error for IncompleteI64 {}

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
