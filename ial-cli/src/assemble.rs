// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! implementation of `ial-cli assemble`

use crate::{checked_assemble, checked_ast_fn, debug_path, read_src};
use anyhow::Result;
use clap::{Parser, ValueHint};
use ial::asm::{AstBuildErr, assemble_ast, assemble_with_debug, build_ast};
use itertools::Itertools;
use std::fs::{self, OpenOptions};
use std::path::PathBuf;

#[derive(Debug, Parser)]
pub(crate) struct AssembleArgs {
    /// File containing the IAL assembly
    ///
    /// reads STDIN if unset
    #[arg(value_name = "INPUT", value_hint = ValueHint::FilePath, required = false)]
    input: Option<PathBuf>,
    /// Output file for assembled intcode
    ///
    /// writes to STDOUT if unset
    #[arg(value_name = "OUTPUT")]
    #[arg(value_hint = ValueHint::FilePath)]
    output: Option<PathBuf>,
    /// Output debug info to file
    ///
    /// If no filename is provided, uses the output file name with the extension replaced with
    /// "ialdbg". If the output file has no extension, then ".ialdbg" is simply appended to it.
    ///
    /// If no filename or output file are provided, uses the name "ialdbg" in the current
    /// directory.
    #[arg(short = 'g', long)]
    #[arg(value_name = "DEBUG")]
    #[arg(value_hint = ValueHint::FilePath)]
    #[allow(clippy::option_option, reason = "used to parse properly")]
    debug_info: Option<Option<PathBuf>>,
}

impl AssembleArgs {
    pub(crate) fn run(&self) -> Result<()> {
        let (src_file, input) = read_src(self.input.as_ref())?;
        let ast = checked_ast_fn(
            |s| build_ast(s).map_err(AstBuildErr::into_inner),
            &src_file,
            &input,
        );
        let intcode = match self.debug_info.as_ref() {
            Some(dbg_path) => {
                let (intcode, dbg) = checked_assemble(assemble_with_debug, ast, &src_file, &input);
                dbg.write(
                    OpenOptions::new()
                        .create(true)
                        .write(true)
                        .truncate(true)
                        .open(debug_path(dbg_path.as_ref()))?,
                )?;

                intcode
            }
            None => checked_assemble(assemble_ast, ast, &src_file, &input),
        };

        match self.output.as_deref() {
            Some(path) => fs::write(path, intcode.into_iter().join(","))?,
            None => print!("{}", intcode.into_iter().format(",")),
        }
        Ok(())
    }
}
