// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! implementation of `ial-cli format`

use crate::print_parse_errors;
use anyhow::Result;
use clap::{ArgAction, Parser, ValueHint};
use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;

#[derive(Debug, Parser)]
pub(crate) struct FormatArgs {
    /// File containing the IAL assembly (reads stdin if unset)
    #[arg(value_name = "FILE", value_hint = ValueHint::FilePath, required = false)]
    pub(crate) input: Option<PathBuf>,
    /// Output file for formatted IAL
    #[arg(short, long, value_name = "FILE", conflicts_with = "in_place")]
    #[arg(value_hint = ValueHint::FilePath)]
    pub(crate) output: Option<PathBuf>,
    #[arg(short, long, action = ArgAction::SetTrue, requires = "input")]
    /// Overwrite the source file
    pub(crate) in_place: bool,
}

impl FormatArgs {
    pub(crate) fn run(&self) -> Result<()> {
        if self.in_place {
            let path = self.input.as_deref().expect("enforced by clap Parser");
            let src = fs::read_to_string(path)?;
            return match ial_ast::format(&src) {
                Ok(formatted) => fs::write(path, formatted).map_err(Into::into),
                Err(errs) => {
                    print_parse_errors(&errs, &path.as_os_str().to_string_lossy(), &src)
                }
            };
        }

        let (src_file, input) = if let Some(path) = self.input.as_deref() {
            (
                path.as_os_str().to_string_lossy(),
                fs::read_to_string(path)?,
            )
        } else {
            let mut s = String::new();
            io::stdin().read_to_string(&mut s)?;
            ("stdin".into(), s)
        };
        match ial_ast::format(&input) {
            Ok(formatted) => {
                if let Some(out) = self.output.as_deref() {
                    fs::write(out, formatted).map_err(Into::into)
                } else {
                    print!("{formatted}");
                    Ok(())
                }
            }
            Err(errs) => print_parse_errors(&errs, &src_file, &input),
        }
    }
}

