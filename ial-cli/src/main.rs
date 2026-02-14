// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use anyhow::Result;
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::error::{Rich, RichPattern};
use clap::Parser;
use itertools::Itertools;
use std::fmt::Write;

mod format;

#[derive(Parser, Debug)]
enum Action {
    /// Format the IAL code, attempting to preserve indentation
    #[command(alias = "fmt")]
    Format(format::FormatArgs),
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
