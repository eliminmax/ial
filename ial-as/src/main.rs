// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::error::{Rich, RichPattern};
use clap::Parser;
use ial::asm::{assemble_ast, assemble_with_debug, build_ast};
use ial_ast::AssemblyError;
use ial_cli_helpers::{BinaryFormat, DisplayedError, EmptyError, ErrorMessage};
use std::fs::{self, OpenOptions, read_to_string};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

fn output_with_format<W: Write>(
    format: BinaryFormat,
    intcode: Vec<i64>,
    mut writer: W,
) -> io::Result<()> {
    match format {
        BinaryFormat::Ascii => {
            use itertools::Itertools;
            writeln!(&mut writer, "{}", intcode.into_iter().format(","))
        }
        BinaryFormat::LittleEndian => {
            for i in intcode {
                writer.write_all(&i.to_le_bytes())?;
            }
            Ok(())
        }
        BinaryFormat::BigEndian => {
            for i in intcode {
                writer.write_all(&i.to_be_bytes())?;
            }
            Ok(())
        }
    }
}

const VERSION: &str = concat!(env!("CARGO_CRATE_NAME"), '-', env!("CARGO_PKG_VERSION"));

const INPUT_HELP: &str = "Input file containing the assembly\nuses stdin if unset or set to '-'";
const OUTPUT_HELP: &str =
    "Output file for the assembled intcode\nuses stdout if unset or set to '-'";

#[derive(Parser)]
#[command(version = env!("CARGO_PKG_VERSION"))]
#[command(long_version = VERSION)]
#[command(about = "IAC Assembler", long_about = None)]
struct Args {
    #[arg(help = INPUT_HELP.split_at(34).0)]
    #[arg(long_help = INPUT_HELP)]
    input: Option<PathBuf>,
    #[arg(help = OUTPUT_HELP.split_at(37).0)]
    #[arg(long_help = OUTPUT_HELP)]
    output: Option<PathBuf>,
    #[arg(help = "output debug info")]
    #[arg(short = 'g', long = "debug-file")]
    debug: Option<PathBuf>,
    #[arg(help = "format source code instead of assembling")]
    #[arg(short, long, action)]
    format: bool,
    #[arg(help = "Output format for the assembled intcode")]
    #[arg(short, long)]
    #[arg(default_value = "ascii")]
    output_format: BinaryFormat,
}

fn report_ast_build_err(err: &Rich<'_, char>, file: &str, source: &str) -> EmptyError {
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
    }

    let mut expected: Vec<_> = err.expected().collect();
    // no need to explicitly mention whitespace
    expected.retain(|pat| !matches!(pat, RichPattern::Label(s) if *s == "inline whitespace"));

    // make sure that "something else" is the last listed entry
    expected.sort_unstable_by(|&a, &b| {
        use std::cmp::Ordering;
        match (a, b) {
            (RichPattern::SomethingElse, _) => Ordering::Greater,
            (_, RichPattern::SomethingElse) => Ordering::Less,
            (a, b) => a.cmp(b),
        }
    });

    match &expected[..] {
        &[] => (),
        &[pat] => {
            builder = builder.with_note(format!("Expected \"{}\"", pat.fg(Color::Blue)));
        }
        pats => {
            let mut note = String::from("Expected one of the following:\n");
            for pat in pats {
                use std::fmt::Write;
                writeln!(&mut note, "- {}", pat.fg(Color::Blue)).expect("can write to &mut String");
            }
            builder = builder.with_note(note);
        }
    }

    builder
        .finish()
        .eprint((file, Source::from(source)))
        .unwrap();
    EmptyError
}

fn report_ast_assembly_err(err: &AssemblyError<'_>, file: &str, source: &str) -> EmptyError {
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
    .unwrap();
    EmptyError
}

fn open_writable(outfile: &Path) -> io::Result<impl Write> {
    OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(outfile)
}

fn main() -> Result<(), DisplayedError<'static>> {
    let args = Args::parse();
    let (file, input) = {
        use std::borrow::Cow;
        if let Some(path) = args.input.as_deref()
            && path != "-"
        {
            (path.to_string_lossy(), read_to_string(path))
        } else {
            (Cow::Borrowed("stdin"), io::read_to_string(io::stdin()))
        }
    };

    let input = input.map_err(|e| ErrorMessage(format!("Error reading input: {e}")))?;

    if args.format {
        let formatted = ial_ast::format(&input).map_err(|errs| {
            for err in errs {
                report_ast_build_err(&err, &file, &input);
            }
            EmptyError
        })?;

        if let Some(outfile) = args.output.as_deref()
            && outfile != "-"
        {
            fs::write(outfile, formatted)?;
        } else {
            print!("{formatted}");
        }
        return Ok(());
    }

    let ast = build_ast(&input).map_err(|errs| {
        for err in errs {
            report_ast_build_err(&err, &file, &input);
        }
        EmptyError
    })?;

    let intcode = if let Some(debug_path) = args.debug.as_deref() {
        let (code, debug) =
            assemble_with_debug(ast).map_err(|e| report_ast_assembly_err(&e, &file, &input))?;
        let w = open_writable(debug_path)?;
        debug.write(w).map_err(|e| {
            ErrorMessage(format!(
                "Failed to write debug info to {}: {e}",
                debug_path.display()
            ))
        })?;
        code
    } else {
        assemble_ast(ast).map_err(|e| report_ast_assembly_err(&e, &file, &input))?
    };

    if let Some(outfile) = args.output.as_deref()
        && outfile != "-"
    {
        output_with_format(args.output_format, intcode, open_writable(outfile)?)
    } else {
        output_with_format(args.output_format, intcode, io::stdout())
    }
    .map_err(Into::into)
}
