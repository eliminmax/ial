// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use anyhow::{Context, Result};
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::error::{Rich, RichPattern};
use clap::Parser;
use ial::asm::Ast;
use ial_core::AssemblyError;
use itertools::Itertools;
use std::borrow::Cow;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};

mod assemble;
mod disassemble;
mod format;
mod run_ascii;

const LONG_VERSION: &str = const_format::formatcp!(
    "{}\n(built with ial {} and ial-ast {})",
    env!("CARGO_PKG_VERSION"),
    ial::VERSION,
    ial_ast::VERSION
);

#[cfg(feature = "man")]
#[derive(Parser, Debug)]
struct GenerateManpageArgs {
    /// The manpath to write to
    manpath: PathBuf,
}

#[cfg(feature = "completion")]
#[derive(Parser, Debug)]
struct ShellChoice {
    /// The shell to generate completion for
    shell: clap_complete::Shell,
}

#[derive(Parser, Debug)]
#[command(version = env!("CARGO_PKG_VERSION"))]
#[command(long_version = LONG_VERSION)]
enum Action {
    /// Format the IAL code, attempting to preserve indentation
    #[command(visible_alias = "fmt")]
    Format(format::FormatArgs),
    /// Assemble the IAL into Intcode
    #[command(visible_alias = "asm")]
    Assemble(assemble::AssembleArgs),
    /// Disassemble Intcode into IAL
    #[command(visible_alias = "disasm")]
    Disassemble(disassemble::DisassembleArgs),
    /// Run Intcode program
    #[command(visible_alias = "run")]
    RunAscii(run_ascii::RunAsciiArgs),
    /// Print out a man page
    #[cfg(feature = "man")]
    #[command(visible_alias = "man")]
    GenerateManpage(GenerateManpageArgs),
    /// Generate shell completion
    #[cfg(feature = "completion")]
    Complete(ShellChoice),
}

impl Action {
    fn run(self) -> Result<()> {
        match self {
            Action::Format(format_args) => format_args.run(),
            Action::Assemble(assemble_args) => assemble_args.run(),
            Action::Disassemble(disassemble_args) => disassemble_args.run(),
            Action::RunAscii(run_ascii_args) => run_ascii_args.run(),
            #[cfg(feature = "man")]
            Action::GenerateManpage(GenerateManpageArgs { mut manpath }) => {
                use clap::CommandFactory;
                manpath.push("man1");
                clap_mangen::generate_to(Self::command(), manpath)?;
                Ok(())
            }
            #[cfg(feature = "completion")]
            Action::Complete(ShellChoice { shell }) => {
                use clap::CommandFactory;
                clap_complete::aot::generate(
                    shell,
                    &mut Self::command(),
                    "ial-cli",
                    &mut io::stdout(),
                );
                Ok(())
            }
        }
    }
}

fn debug_path<P: AsRef<Path>>(outfile_path: Option<&P>) -> Cow<'static, Path> {
    match outfile_path {
        Some(path) => Cow::Owned(path.as_ref().with_extension(".ialdbg")),
        None => Cow::Borrowed(Path::new("ialdbg")),
    }
}

fn read_intcode<P: AsRef<Path>>(input: Option<&P>) -> Result<Vec<i64>> {
    let text = if let Some(path) = input {
        fs::read_to_string(path)
            .with_context(|| format!("unable to read {}", path.as_ref().display()))?
    } else {
        let mut s = String::new();
        io::stdin()
            .read_to_string(&mut s)
            .context("unable to read input")?;
        s
    };

    let s = text.trim();
    Ok(if s.is_empty() {
        vec![]
    } else {
        s.split(',')
            .map(str::parse)
            .collect::<Result<Vec<i64>, _>>()
            .context("invalid integer in intcode")?
    })
}

fn read_src<P: AsRef<Path>>(input: Option<&P>) -> Result<(Cow<'_, str>, String)> {
    Ok(if let Some(path) = input {
        (
            path.as_ref().as_os_str().to_string_lossy(),
            fs::read_to_string(path)
                .with_context(|| format!("unable to read {}", path.as_ref().display()))?,
        )
    } else {
        let mut s = String::new();
        io::stdin()
            .read_to_string(&mut s)
            .context("unable to read input")?;
        (Cow::Borrowed("stdin"), s)
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
            Report::build(ReportKind::Error, (file, span.clone()))
                .with_message(format!(
                    "Unable to resolve label \"{}\"",
                    label.fg(Color::Red)
                ))
                .with_label(Label::new((file, span.clone())).with_color(Color::Yellow))
        }
        AssemblyError::DuplicateLabel { label, spans } => {
            Report::build(ReportKind::Error, (file, spans[1].clone()))
                .with_message(format!(
                    "Multiple definitions of label \"{}\"",
                    label.fg(Color::Red)
                ))
                .with_label(
                    Label::new((file, spans[0].clone()))
                        .with_message("previously defined here")
                        .with_color(Color::Yellow),
                )
                .with_label(
                    Label::new((file, spans[1].clone()))
                        .with_message("redefined here")
                        .with_color(Color::Blue),
                )
        }
        AssemblyError::DirectiveTooLarge { size, span } => {
            Report::build(ReportKind::Error, (file, span.clone()))
                .with_message("Directive too large")
                .with_label(
                    Label::new((file, span.clone()))
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
                Label::new((file, rhs_span.clone()))
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
fn checked_assemble<'a, F, T>(f: F, ast: Ast<'a>, file: &str, src: &'a str) -> T
where
    F: Fn(Ast<'a>) -> Result<T, AssemblyError<'a>>,
{
    match f(ast) {
        Ok(val) => val,
        Err(ast_err) => {
            report_ast_assembly_err(&ast_err, file, src);
            std::process::exit(1);
        }
    }
}

fn main() -> Result<()> {
    Action::parse().run()
}
