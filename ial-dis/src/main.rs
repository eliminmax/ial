// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use clap::Parser;
use ial_cli_helpers::{BinaryFormat, DisplayedError};
use ial::debug_info::DebugInfo;
use ial::disasm::{disassemble, disassemble_with_debug};
use std::borrow::Cow;
use std::fmt::{self, Debug, Display};
use std::fs::{self, OpenOptions};
use std::io::{self, Read};
use std::path::PathBuf;

const VERSION: &str = concat!(env!("CARGO_CRATE_NAME"), '-', env!("CARGO_PKG_VERSION"));
const INTCODE_HELP: &str =
    "Compiled file containing the intcode\nuses stdin if unset or set to '-'";
const OUTPUT_HELP: &str =
    "Output file for the disassembled IAL\nuses stdout if unset or set to '-'";

#[derive(Parser)]
#[command(version = env!("CARGO_PKG_VERSION"))]
#[command(long_version = VERSION)]
#[command(about = "IAC Assembler", long_about = None)]
struct Args {
    #[arg(help = INTCODE_HELP.split_once("\n").unwrap().0)]
    #[arg(long_help = INTCODE_HELP)]
    input: Option<PathBuf>,
    #[arg(help = OUTPUT_HELP.split_once("\n").unwrap().0)]
    #[arg(long_help = OUTPUT_HELP)]
    output: Option<PathBuf>,
    #[arg(short = 'g', long = "debug-file")]
    #[arg(help = "File containing debug info")]
    debug_info: Option<PathBuf>,
    #[arg(help = "Format for the written intcode")]
    #[arg(short, long)]
    #[arg(default_value = "ascii")]
    format: BinaryFormat,
}

#[derive(Debug)]
struct InputFormatError {
    msg: Cow<'static, str>,
}

impl Display for InputFormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error parsing input: {}", self.msg)
    }
}

impl std::error::Error for InputFormatError {}

fn load_bin<F: Fn([u8; 8]) -> i64>(input: &[u8], func: F) -> Result<Vec<i64>, InputFormatError> {
    let (chunks, remainder) = input.as_chunks::<8>();
    if remainder.is_empty() {
        Ok(chunks.iter().copied().map(func).collect())
    } else {
        Err(InputFormatError {
            msg: Cow::Owned(format!("{} extra bytes", remainder.len())),
        })
    }
}

fn parse_with_format(format: BinaryFormat, input: &[u8]) -> Result<Vec<i64>, InputFormatError> {
    match format {
        BinaryFormat::Ascii => {
            let input = str::from_utf8(input).map_err(|e| e.to_string())?.trim();
            if input.is_empty() {
                return Ok(Vec::new());
            }
            input
                .split(',')
                .map(str::trim)
                .map(str::parse::<i64>)
                .collect::<Result<_, _>>()
                .map_err(|e| e.to_string().into())
        }
        BinaryFormat::LittleEndian => load_bin(input, i64::from_le_bytes),
        BinaryFormat::BigEndian => load_bin(input, i64::from_be_bytes),
    }
}

impl<IntoCow: Into<Cow<'static, str>>> From<IntoCow> for InputFormatError {
    fn from(cow: IntoCow) -> Self {
        Self { msg: cow.into() }
    }
}

fn main() -> Result<(), DisplayedError<'static>> {
    let args = Args::parse();
    let input = if let Some(path) = args.input.as_deref()
        && path != "-"
    {
        fs::read(path)?
    } else {
        let mut v = Vec::new();
        io::stdin().read_to_end(&mut v)?;
        v
    };

    let code = parse_with_format(args.format, &input)?;

    let dissassembly = if let Some(debug_info) = args.debug_info.as_ref() {
        disassemble_with_debug(
            code,
            &DebugInfo::read(OpenOptions::new().read(true).open(debug_info)?)?,
        )?
    } else {
        disassemble(code)
    };

    if let Some(outfile) = args.output.as_deref()
        && outfile != "-"
    {
        fs::write(outfile, dissassembly.as_bytes())?;
    } else {
        print!("{dissassembly}");
    }

    Ok(())
}
