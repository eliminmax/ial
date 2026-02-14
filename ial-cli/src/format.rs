// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! implementation of `ial-cli format`

use crate::read_src;
use anyhow::Result;
use clap::{ArgAction, Parser, ValueHint};
use std::fs;
use std::path::PathBuf;

#[derive(Debug, Parser)]
pub(crate) struct FormatArgs {
    /// File containing the IAL assembly (reads stdin if unset)
    #[arg(value_name = "FILE", value_hint = ValueHint::FilePath, required = false)]
    input: Option<PathBuf>,
    /// Output file for formatted IAL
    #[arg(short, long, value_name = "FILE", conflicts_with = "in_place")]
    #[arg(value_hint = ValueHint::FilePath)]
    output: Option<PathBuf>,
    #[arg(short, long, action = ArgAction::SetTrue, requires = "input")]
    /// Overwrite the source file
    in_place: bool,
}

fn checked_format(f: &str, s: &str) -> String {
    crate::checked_ast_fn(ial_ast::format, f, s)
}

impl FormatArgs {
    pub(crate) fn run(&self) -> Result<()> {
        if self.in_place {
            let path = self.input.as_deref().expect("enforced by clap Parser");
            let input = fs::read_to_string(path)?;
            let file = path.as_os_str().to_string_lossy();
            let formatted = checked_format(&file, &input);
            fs::write(path, formatted)?;
        } else {
            let (src_file, input) = read_src(self.input.as_ref())?;
            let formatted = checked_format(&src_file, &input);
            if let Some(out) = self.output.as_deref() {
                fs::write(out, formatted)?;
            } else {
                print!("{formatted}");
            }
        }
        Ok(())
    }
}
