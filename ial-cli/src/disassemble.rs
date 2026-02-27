// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use anyhow::Result;
use clap::{Parser, ValueHint};
use ial::debug_info::DebugInfo;
use ial::disasm::{disassemble, disassemble_with_debug};
use std::fs::{self, File};
use std::path::PathBuf;

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
    /// Load debug info from provided file
    #[arg(short = 'g', long)]
    #[arg(value_name = "DEBUG")]
    #[arg(value_hint = ValueHint::FilePath)]
    debug_info: Option<PathBuf>,
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
            let debug_info = DebugInfo::read(File::open(dbg)?)?;
            disassemble_with_debug(intcode, &debug_info)
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
