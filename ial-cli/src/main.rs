// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use anyhow::Result;
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::error::{Rich, RichPattern};
use clap::Parser;
use ial_ast::{AssemblyError, Line};
use itertools::Itertools;
use std::borrow::Cow;
use std::fs;
use std::io::{self, Read};
use std::path::Path;

mod assemble;
mod format;

#[derive(Parser, Debug)]
enum Action {
    /// Format the IAL code, attempting to preserve indentation
    #[command(alias = "fmt")]
    Format(format::FormatArgs),
    /// Assemble the IAL into Intcode
    #[command(alias = "asm")]
    Assemble(assemble::AssembleArgs),
    Disassemble,
    RunAscii,
    Debug,
}

impl Action {
    fn run(&self) -> Result<()> {
        match self {
            Action::Format(format_args) => format_args.run(),
            Action::Assemble(assemble_args) => assemble_args.run(),
            Action::Disassemble => todo!(),
            Action::RunAscii => todo!(),
            Action::Debug => todo!(),
        }
    }
}

fn debug_path<P: AsRef<Path>>(outfile_path: Option<&P>) -> Cow<'static, Path> {
    match outfile_path {
        Some(path) => Cow::Owned(path.as_ref().with_extension(".ialdbg")),
        None => Cow::Borrowed(Path::new("ialdbg")),
    }
}

fn read_src<P: AsRef<Path>>(input: Option<&P>) -> Result<(Cow<'_, str>, String)> {
    Ok(if let Some(path) = input {
        (
            path.as_ref().as_os_str().to_string_lossy(),
            fs::read_to_string(path)?,
        )
    } else {
        let mut s = String::new();
        io::stdin().read_to_string(&mut s)?;
        ("stdin".into(), s)
    })
}

fn report_ast_build_err(err: &Rich<'_, char>, file: &str, source: &str) {
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
        );
    }

    let mut expected = err
        .expected()
        // no need to explicitly mention whitespace
        .filter(|pat| !matches!(pat, RichPattern::Label(s) if *s == "inline whitespace"))
        .collect_vec();

    // make sure that "something else" is the last listed entry
    expected.sort_unstable_by(|&a, &b| {
        use std::cmp::Ordering;
        match (a, b) {
            (RichPattern::SomethingElse, _) => Ordering::Greater,
            (_, RichPattern::SomethingElse) => Ordering::Less,
            (a, b) => a.cmp(b),
        }
    });

    match expected.as_slice() {
        &[] => (),
        &[pat] => {
            builder = builder.with_note(format!("Expected \"{}\"", pat.fg(Color::Blue)));
        }
        pats => {
            builder = builder.with_note(format!(
                "Expected one of the following:\n{}",
                pats.iter()
                    .format_with("\n", |p, f| f(&format_args!("- {}", p.fg(Color::Blue))))
            ));
        }
    }

    builder
        .finish()
        .eprint((file, Source::from(source)))
        .unwrap_or_else(|e| panic!("failure to write to stderr: {e}"));
}

fn print_parse_errors(errs: &[Rich<'_, char>], file: &str, src: &str) -> ! {
    for err in errs {
        eprintln!("report_ast_build_err({err:?}, {file:?}, ...");
        report_ast_build_err(err, file, src);
    }
    #[allow(clippy::exit, reason = "explicitly documented in print_parse_errors")]
    std::process::exit(1)
}

/// Wrap around `f(src)` passing errors into [`print_parse_errors`] using the provided `file`
///
/// On error, prints the appropriate errors and [exits][std::process::exit].
fn checked_ast_fn<'a, T, F>(f: F, file: &str, src: &'a str) -> T
where
    F: Fn(&'a str) -> Result<T, Vec<Rich<'a, char>>>,
{
    match f(src) {
        Ok(val) => val,
        Err(errs) => print_parse_errors(&errs, file, src),
    }
}

fn report_ast_assembly_err(err: &AssemblyError<'_>, file: &str, source: &str) {
    match err {
        AssemblyError::UnresolvedLabel { label, span } => {
            Report::build(ReportKind::Error, (file, span.into_range()))
                .with_message(format!(
                    "Unable to resolve label \"{}\"",
                    label.fg(Color::Red)
                ))
                .with_label(Label::new((file, span.into_range())).with_color(Color::Yellow))
        }
        AssemblyError::DuplicateLabel { label, spans } => {
            Report::build(ReportKind::Error, (file, spans[1].into_range()))
                .with_message(format!(
                    "Multiple definitions of label \"{}\"",
                    label.fg(Color::Red)
                ))
                .with_label(
                    Label::new((file, spans[0].into_range()))
                        .with_message("previously defined here")
                        .with_color(Color::Yellow),
                )
                .with_label(
                    Label::new((file, spans[1].into_range()))
                        .with_message("redefined here")
                        .with_color(Color::Blue),
                )
        }
        AssemblyError::DirectiveTooLarge { size, span } => {
            Report::build(ReportKind::Error, (file, span.into_range()))
                .with_message("Directive too large")
                .with_label(
                    Label::new((file, span.into_range()))
                        .with_message(format!(
                            "This directive's output size is {}",
                            size.fg(Color::Cyan)
                        ))
                        .with_color(Color::Red),
                )
                .with_note(format!(
                    "The maximum directive size possible is {} ({})",
                    "2^63 - 1".fg(Color::Yellow),
                    i64::MAX.fg(Color::Yellow)
                ))
        }
        AssemblyError::DivisionByZero {
            lhs_span,
            div_index,
            rhs_span,
        } => Report::build(ReportKind::Error, (file, lhs_span.start..rhs_span.end))
            .with_message("Division by zero")
            .with_label(
                Label::new((file, lhs_span.start..*div_index + 1)).with_color(Color::Yellow),
            )
            .with_label(
                Label::new((file, rhs_span.into_range()))
                    .with_message("This expression evaluates to 0")
                    .with_color(Color::Red),
            ),
        err => Report::build(ReportKind::Error, (file, 0..0))
            .with_message(format!("Unknown error occured: {err}")),
    }
    .finish()
    .eprint((file, Source::from(source)))
    .unwrap_or_else(|e| panic!("failure to write to stderr: {e}"));
}

/// Wrap around `f(ast)`, displaying the appropriate error message and exiting on failure
///
/// On error, calls [`report_ast_assembly_err(&err, file, src)`][report_ast_build_err]
/// then [exits][std::process::exit] with exit code 1.
fn checked_assemble<'a, F, T>(f: F, ast: Vec<Line<'a>>, file: &str, src: &'a str) -> T
where
    F: Fn(Vec<Line<'a>>) -> Result<T, AssemblyError<'a>>,
{
    match f(ast) {
        Ok(val) => val,
        Err(ast_err) => {
            report_ast_assembly_err(&ast_err, file, src);
            #[allow(clippy::exit, reason = "explicitly documented in docstring")]
            std::process::exit(1);
        }
    }
}

fn main() -> Result<()> {
    Action::parse().run()
}
