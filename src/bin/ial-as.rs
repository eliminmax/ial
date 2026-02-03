// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::error::{Rich, RichPattern};
use clap::Parser;
use ial::asm::{AssemblyError, assemble_ast, assemble_with_debug, build_ast};
use ial::bin_helpers::BinaryFormat;
use std::fs::{OpenOptions, read_to_string};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

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
    #[arg(help = "Output format for the assembled intcode")]
    #[arg(short, long)]
    #[arg(default_value = "ascii")]
    format: BinaryFormat,
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
                        .with_message(format!(
                            "The maximum size possible is {}",
                            i64::MAX.fg(Color::Yellow)
                        ))
                        .with_color(Color::Red),
                )
        }
    }
    .finish()
    .eprint((file, Source::from(source)))
    .unwrap();
}

fn open_writable(outfile: &Path) -> io::Result<impl Write> {
    OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(outfile)
}

fn main() -> ExitCode {
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

    let input = match input {
        Ok(i) => i,
        Err(e) => {
            eprintln!("Error reading input: {e}");
            return ExitCode::FAILURE;
        }
    };

    let ast = match build_ast(&input) {
        Ok(ast) => ast,
        Err(errs) => {
            for err in errs {
                report_ast_build_err(&err, &file, &input);
            }

            return ExitCode::FAILURE;
        }
    };

    let intcode = if let Some(debug_path) = args.debug.as_deref() {
        match assemble_with_debug(ast) {
            Ok((code, debug)) => {
                match open_writable(debug_path) {
                    Ok(w) => {
                        if let Err(e) = debug.write(w) {
                            eprintln!(
                                "Failed to write debug info to {}: {e}",
                                debug_path.display()
                            );
                            return ExitCode::FAILURE;
                        }
                    }
                    Err(e) => {
                        eprintln!("Failed to open {} for writing: {e}", debug_path.display());
                        return ExitCode::FAILURE;
                    }
                }
                code
            }
            Err(e) => {
                report_ast_assembly_err(&e, &file, &input);
                return ExitCode::FAILURE;
            }
        }
    } else {
        match assemble_ast(ast) {
            Ok(code) => code,
            Err(e) => {
                report_ast_assembly_err(&e, &file, &input);
                return ExitCode::FAILURE;
            }
        }
    };

    if let Some(outfile) = args.output.as_deref()
        && outfile != "-"
    {
        let writer = match open_writable(outfile) {
            Ok(w) => w,
            Err(e) => {
                eprintln!("Failed to open {} for writing: {e}.", outfile.display());
                return ExitCode::FAILURE;
            }
        };
        match output_with_format(args.format, intcode, writer) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("Failed to write to {}: {e}.", outfile.display());
                ExitCode::FAILURE
            }
        }
    } else {
        match output_with_format(args.format, intcode, io::stdout()) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("Failed to write to stdout: {e}.");
                ExitCode::FAILURE
            }
        }
    }
}
