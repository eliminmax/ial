// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use anyhow::Result;
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::error::{Rich, RichPattern};
use clap::{ArgAction, Parser, ValueHint};
use itertools::Itertools;
use std::fmt::Write;
use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;

#[derive(Parser, Debug)]
enum Action {
    /// Format the IAL code, attempting to preserve indentation
    #[command(alias = "fmt")]
    Format(FormatArgs),
    Assemble,
    Disassemble,
    RunAscii,
    Debug,
}

impl Action {
    fn run(&self) -> Result<()> {
        match self {
            Action::Format(format_args) => format_args.run(),
            Action::Assemble => todo!(),
            Action::Disassemble => todo!(),
            Action::RunAscii => todo!(),
            Action::Debug => todo!(),
        }
    }
}

fn report_ast_build_err(err: &Rich<'_, char>, file: &str, source: &str) -> Result<()> {
    let mut builder = Report::build(ReportKind::Error, (file, err.span().into_range()))
        .with_message(format!("Failed to parse {}", file.fg(Color::Red)));

    if let Some(found) = err.found() {
        builder = builder.with_label(
            Label::new((file, err.span().into_range()))
                .with_message(format!(
                    "Found token \'{}\'",
                    found.escape_default().fg(Color::Cyan)
                ))
                .with_color(Color::Yellow),
        );
    } else {
        builder = builder.with_label(
            Label::new((file, err.span().into_range()))
                .with_message("Unexpected end of input")
                .with_color(Color::Yellow),
        )
    }

    let mut expected = err
        .expected()
        // no need to explicitly mention whitespace
        .filter(|pat| !matches!(pat, RichPattern::Label(s) if *s == "inline whitespace"))
        // make sure that "something else" is the last listed entry
        .sorted_unstable_by(|&a, &b| {
            use std::cmp::Ordering;
            match (a, b) {
                (RichPattern::SomethingElse, _) => Ordering::Greater,
                (_, RichPattern::SomethingElse) => Ordering::Less,
                (a, b) => a.cmp(b),
            }
        });

    if let Some(expected_0) = expected.next() {
        if let Some(expected_1) = expected.next() {
            let mut note = String::from("Expected one of the following:\n");
            for pat in std::iter::once(expected_0)
                .chain(std::iter::once(expected_1))
                .chain(expected)
            {
                writeln!(&mut note, "- {}", pat.fg(Color::Blue))?;
            }
            builder = builder.with_note(note);
        } else {
            builder = builder.with_note(format!("Expected \"{}\"", expected_0.fg(Color::Blue)));
        }
    }

    builder
        .finish()
        .eprint((file, Source::from(source)))
        .map_err(Into::into)
}

#[derive(Debug, Parser)]
struct FormatArgs {
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

impl FormatArgs {
    fn run(&self) -> Result<()> {
        if self.in_place {
            let path = self.input.as_deref().expect("enforced by clap Parser");
            let src = fs::read_to_string(path)?;
            return match ial_ast::format(&src) {
                Ok(formatted) => fs::write(path, formatted).map_err(Into::into),
                Err(errs) => print_parse_errors(&errs, &path.as_os_str().to_string_lossy(), &src),
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

// NOTE: Should return `Result<!>` once the never type is stabilized, as it calls
// `std::process::exit` once all error messages have been printed successfully
fn print_parse_errors(errs: &[Rich<'_, char>], file: &str, src: &str) -> Result<()> {
    for err in errs {
        eprintln!("report_ast_build_err({err:?}, {file:?}, ...");
        report_ast_build_err(err, file, src)?;
    }
    std::process::exit(1);
}

fn main() -> Result<()> {
    Action::parse().run()
}
