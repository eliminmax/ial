// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use chumsky::error::{Rich, RichPattern};
use intcode::asm::{AssemblyError, assemble_ast, build_ast};

use std::process::ExitCode;

#[cfg(feature = "ariadne")]
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};

#[cfg(not(feature = "ariadne"))]
fn report_ast_build_err(err: Rich<'_, char>, file: &str, _: &str) {
    eprintln!("error parsing {file}:");
    if let Some(found) = err.found() {
        eprintln!("Found token \'{}\'", found.escape_default())
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
        &[pat] => eprintln!("Expected \"{}\"", pat),
        pats => {
            eprintln!("Expected one of the following:");
            for pat in pats {
                eprintln!("- {pat}");
            }
        }
    }
}

#[cfg(feature = "ariadne")]
fn report_ast_build_err(err: Rich<'_, char>, file: &str, source: &str) {
    use std::fmt::Write;

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
                writeln!(&mut note, "- {}", pat.fg(Color::Blue)).expect("can write to &mut String");
            }
            builder = builder.with_note(note);
        }
    }

    builder
        .finish()
        .eprint((file, Source::from(source)))
        .expect("failed to print to stderr");
}

#[cfg(not(feature = "ariadne"))]
fn report_ast_assembly_err(err: AssemblyError<'_>, file: &str, _: &str) {
    eprintln!("error assembling {file}:\t{err}");
}

#[cfg(feature = "ariadne")]
fn report_ast_assembly_err(err: AssemblyError<'_>, file: &str, source: &str) {
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

fn main() -> ExitCode {
    use std::env::args_os;
    use std::fs::read_to_string;
    let input_file = args_os().nth(1).expect("must provide filename");
    let input = read_to_string(&input_file).expect("must be able to read");

    let ast = match build_ast(&input) {
        Ok(ast) => ast,
        Err(errs) => {
            let escaped_filename = input_file.to_string_lossy();
            for err in errs {
                report_ast_build_err(err, &escaped_filename, &input);
            }
            return ExitCode::FAILURE;
        }
    };

    let intcode = match assemble_ast(ast) {
        Ok(code) => code,
        Err(e) => {
            report_ast_assembly_err(e, &input_file.to_string_lossy(), &input);
            return ExitCode::FAILURE;
        }
    };
    let intcode: Vec<String> = intcode.into_iter().map(|i| i.to_string()).collect();
    println!("{}", intcode.join(","));
    ExitCode::SUCCESS
}
