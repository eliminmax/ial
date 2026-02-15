// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use anyhow::Result;
use clap::{Parser, ValueHint};
use std::path::PathBuf;
use ial_debug_info::DebugInfo;
use ial::disasm::{disassemble, disassemble_with_debug};
use std::fs::{self, File};

use crate::debug_path;

#[derive(Debug, Parser)]
pub(crate) struct DisassembleArgs {
    /// File containing Intcode
    ///
    /// Expected format is the same as Advent of Code - a comma-delimited, arbitrary-length list of
    /// decimal integers. A single trailing newling can be present. If it is, it will be ignored.
    ///
    /// If not set, the Intcode will be read from STDIN.
    #[arg(value_name = "FILE", value_hint = ValueHint::FilePath, required = false)]
    intcode: Option<PathBuf>,
    /// Load debug info from file
    ///
    /// If no filename is provided, uses the intcode file name with the extension replaced with
    /// "ialdbg". If the intcode file has no extension, then ".ialdbg" is simply appended to it.
    ///
    /// If no filename or intcode file are provided, uses the name "ialdbg" in the current
    /// directory.
    #[arg(short = 'g', long)]
    #[arg(value_name = "DEBUG")]
    #[arg(value_hint = ValueHint::FilePath)]
    #[allow(clippy::option_option, reason = "used to parse properly")]
    debug_info: Option<Option<PathBuf>>,
    /// Output file for disassembled IAL
    ///
    /// writes to STDOUT if unset
    #[arg(value_name = "OUTPUT")]
    #[arg(value_hint = ValueHint::FilePath)]
    #[arg(short, long)]
    output: Option<PathBuf>,
}

impl DisassembleArgs {
    pub(crate) fn run(&self) -> Result<()> {
        let intcode = crate::read_intcode(self.intcode.as_ref())?;

        let disasm = if let Some(dbg) = self.debug_info.as_ref() {
            let debug_info = DebugInfo::read(File::open(debug_path(dbg.as_ref()))?)?;
            disassemble_with_debug(intcode, &debug_info)?
        } else {
            disassemble(intcode)
        };

        if let Some(path) = self.output.as_deref() {
            fs::write(path, disasm)?;
        } else {
            print!("{disasm}");
        }

        Ok(())
    }
}
