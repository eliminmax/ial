// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! [`chumsky`]-powered parsers for AST nodes
use super::SingleByteSpan;

use super::prelude::*;
pub use chumsky::Parser;
use chumsky::prelude::*;

type RichErr<'a> = chumsky::extra::Err<Rich<'a, char>>;

/// Extension trait for [clonable][Clone] [parsers][Parser]s, used to simplify return types
///
/// A type which implements `ClonableParser<'a, T>` must also implement both `Clone` and
/// `chumsky::Parser<'a, &'a str, T, chumsky::extra::Err<Rich<'a, char>>>`, and a blanket `impl`
/// exists for all types that meet that requirement.
pub trait ClonableParser<'a, T>: Clone + Parser<'a, &'a str, T, RichErr<'a>> {}

impl<'a, T, P: Clone + Parser<'a, &'a str, T, RichErr<'a>>> ClonableParser<'a, T> for P {}

fn padded<'a, T, P: ClonableParser<'a, T>>(parser: P) -> impl ClonableParser<'a, T> {
    parser.padded_by(text::inline_whitespace())
}

fn with_sep<'a, T, P: ClonableParser<'a, T>>(parser: P) -> impl ClonableParser<'a, T> {
    parser.then_ignore(text::inline_whitespace().at_least(1))
}

fn comma_delimiter<'a>() -> impl ClonableParser<'a, ()> {
    padded(just(',')).ignored().labelled("comma delimiter")
}

/// Generate a [parser][Parser] for a [Parameter]
#[must_use]
pub fn parameter<'a>() -> impl ClonableParser<'a, Parameter<'a>> {
    padded(
        choice((
            just('#')
                .to(ParamMode::Immediate)
                .labelled("immediate mode prefix ('#')"),
            just('@')
                .to(ParamMode::Relative)
                .labelled("relative mode prefix ('@')"),
            empty().to(ParamMode::Positional),
        ))
        .then(outer_expr()),
    )
    .map(|(mode, expr)| Parameter(mode, Box::new(expr)))
    .labelled("parameter")
    .as_context()
}

fn outer_expr<'a>() -> impl ClonableParser<'a, OuterExpr<'a>> {
    labels()
        .then(expr())
        .map(|(labels, expr)| OuterExpr { labels, expr })
}

/// Generate a [parser][Parser] for a (possibly empty) sequence of [`Label`]s
#[must_use]
pub fn labels<'a>() -> impl ClonableParser<'a, Vec<Label<'a>>> {
    text::ident()
        .spanned()
        .then_ignore(just(':'))
        .map(Label)
        .labelled("label")
        .as_context()
        .then_ignore(text::inline_whitespace())
        .repeated()
        .collect()
}

/// Generate a [parser][Parser] for a case-insensitive keyword or mnemonic from `kw`
///
/// On a successful match, returns the [span][SimpleSpan] of the matched keyword in the source.
#[must_use]
pub fn mnemonic<'a>(kw: &'static str) -> impl ClonableParser<'a, SimpleSpan> {
    text::ascii::ident().try_map(move |s: &'a str, span| {
        if s.eq_ignore_ascii_case(kw) {
            Ok(span)
        } else {
            Err(Rich::custom(span, format!("failed to match keyword {kw}")))
        }
    })
}

fn params<'a, const N: usize>() -> impl ClonableParser<'a, [Parameter<'a>; N]> {
    parameter()
        .separated_by(comma_delimiter())
        .exactly(N)
        .allow_trailing()
        .collect_exactly()
}

fn op3<'a>(
    mnemonic_parser: impl ClonableParser<'a, SimpleSpan>,
    f: impl Fn(Parameter<'a>, Parameter<'a>, Parameter<'a>) -> Instr<'a> + Copy,
) -> impl ClonableParser<'a, Instr<'a>> {
    mnemonic_parser.ignore_then(params().map(move |[a, b, c]| f(a, b, c)))
}

fn op2<'a>(
    mnemonic_parser: impl ClonableParser<'a, SimpleSpan>,
    f: impl Fn(Parameter<'a>, Parameter<'a>) -> Instr<'a> + Copy,
) -> impl ClonableParser<'a, Instr<'a>> {
    mnemonic_parser.ignore_then(params().map(move |[a, b]| f(a, b)))
}

fn op1<'a>(
    mnemonic_parser: impl ClonableParser<'a, SimpleSpan>,
    f: impl Fn(Parameter<'a>) -> Instr<'a> + Copy,
) -> impl ClonableParser<'a, Instr<'a>> {
    mnemonic_parser.ignore_then(params().map(move |[a]| f(a)))
}

/// Return a [parser][Parser] for an [`Instr`]
#[must_use]
pub fn instr<'a>() -> impl ClonableParser<'a, Instr<'a>> {
    padded(choice((
        op3(mnemonic("ADD"), Instr::Add),
        op3(mnemonic("MUL"), Instr::Mul),
        op1(mnemonic("IN"), Instr::In),
        op1(mnemonic("OUT"), Instr::Out),
        op2(mnemonic("JNZ"), Instr::Jnz),
        op2(mnemonic("JZ"), Instr::Jz),
        op3(mnemonic("LT").or(mnemonic("SLT")), Instr::Lt),
        op3(mnemonic("EQ").or(mnemonic("SEQ")), Instr::Eq),
        op1(mnemonic("RBO"), Instr::Rbo),
        op1(mnemonic("INCB"), Instr::Rbo),
        mnemonic("HALT").to(Instr::Halt),
    )))
    .labelled("instruction")
    .as_context()
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum UnaryOp {
    Add,
    Negate,
}

fn folder<'a>(
    lhs: Spanned<Expr<'a>>,
    (op, rhs): (Spanned<BinOperator>, Spanned<Expr<'a>>),
) -> Spanned<Expr<'a>> {
    let span = SimpleSpan::from(lhs.span.start..rhs.span.end);
    let inner = Expr::BinOp {
        lhs: Box::new(lhs),
        op: Spanned {
            inner: op.inner,
            span: SingleByteSpan(op.span.start),
        },
        rhs: Box::new(rhs),
    };
    Spanned { span, inner }
}

/// Generate a [parser][Parser] for a ([spanned][Spanned]) [`Expr`]
#[must_use]
pub fn expr<'a>() -> impl ClonableParser<'a, Spanned<Expr<'a>>> {
    recursive(|expr| {
        let int = text::int(10)
            .try_map(|s: &str, span| {
                s.parse::<i64>()
                    .map(Expr::Number)
                    .map_err(|e| Rich::custom(span, format!("error parsing {s} as i64: {e}")))
            })
            .labelled("integer literal");
        let ident = text::ident()
            .map(|s: &str| Expr::Ident(s))
            .labelled("label");
        let bracketed = expr
            .delimited_by(just('('), just(')'))
            .map(|e| Expr::Parenthesized(Box::new(e)))
            .labelled("bracketed expression");
        let atom = int.or(ident).or(ascii_char()).or(bracketed).spanned();
        let unary =
            padded(choice((just('-').to(UnaryOp::Negate), just('+').to(UnaryOp::Add))).spanned())
                .repeated()
                .foldr(
                    atom,
                    |Spanned { inner, mut span }: Spanned<_>, rhs: Spanned<Expr<'a>>| {
                        span.end = rhs.span.end;
                        Spanned {
                            inner: match inner {
                                UnaryOp::Add => Expr::UnaryAdd(Box::new(rhs)),
                                UnaryOp::Negate => Expr::Negate(Box::new(rhs)),
                            },
                            span,
                        }
                    },
                )
                .labelled("unary expression");

        let prod = unary
            .clone()
            .foldl(
                padded(
                    choice((
                        just('*').to(BinOperator::Mul),
                        just('/').to(BinOperator::Div),
                    ))
                    .labelled("binary operator (* or /)")
                    .spanned(),
                )
                .then(unary)
                .repeated(),
                folder,
            )
            .labelled("multiplication or division expression");

        prod.clone().foldl(
            padded(
                choice((
                    just('+').to(BinOperator::Add),
                    just('-').to(BinOperator::Sub),
                ))
                .labelled("binary operator (+ or -)")
                .spanned(),
            )
            .then(prod)
            .repeated(),
            folder,
        )
    })
    .labelled("expression")
    .as_context()
}

fn hex_byte<'a>() -> impl ClonableParser<'a, u8> {
    let hex_digit = || {
        choice((
            one_of("0123456789").map(|c| c as u8 - b'0'),
            one_of("ABCDEF").map(|c| c as u8 - b'A' + 10),
            one_of("abcdef").map(|c| c as u8 - b'a' + 10),
        ))
    };
    hex_digit().then(hex_digit()).map(|(a, b)| (a << 4) | b)
}

fn oct_byte<'a>() -> impl ClonableParser<'a, u8> {
    (one_of("0123")
        .then(one_of("01234567").repeated().at_most(2))
        .to_slice())
    .or(one_of("01234567")
        .repeated()
        .at_least(1)
        .at_most(2)
        .to_slice())
    .map(|s| u8::from_str_radix(s, 8).unwrap())
}

fn ascii_escape<'a>() -> impl ClonableParser<'a, u8> {
    just('\\').ignore_then(
        choice((
            just('\\').to(b'\\'),
            just('\'').to(b'\''),
            just('\"').to(b'\"'),
            just('n').to(b'\n'),
            just('t').to(b'\t'),
            just('r').to(b'\r'),
            just('e').to(b'\x1b'),
            oct_byte(),
            just('x').ignore_then(hex_byte()),
        ))
        .map_err(|e| {
            Rich::custom(
                SimpleSpan {
                    start: e.span().start - 1,
                    ..*e.span()
                },
                match e.found() {
                    Some(t) => format!("invalid escape sequence: \\{t}"),
                    None => String::from("unexpected EOF"),
                },
            )
        }),
    )
}

fn ascii_char<'a>() -> impl ClonableParser<'a, Expr<'a>> {
    just('\'')
        .ignore_then(choice((
            none_of("'\\")
                .filter(|c: &char| c.is_ascii())
                .map(|c| c as u8),
            ascii_escape(),
        )))
        .then_ignore(just('\''))
        .map(Expr::AsciiChar)
        .labelled("character literal")
}

/// Generate a [parser][Parser] for a ([spanned][Spanned]) ASCII string as a [`Vec<u8>`]
#[must_use]
pub fn ascii_string<'a>() -> impl ClonableParser<'a, Spanned<Vec<u8>>> {
    padded(
        just('"')
            .ignore_then(
                choice((
                    none_of("\"\\")
                        .filter(|c: &char| c.is_ascii())
                        .map(|c| c as u8),
                    ascii_escape(),
                ))
                .repeated()
                .collect(),
            )
            .then_ignore(just('"'))
            .spanned(),
    )
    .labelled("ascii string")
    .as_context()
}

/// Generate a [parser][Parser] for an ([optional][Option], [spanned][Spanned]) [`Directive`]
#[must_use]
pub fn directive<'a>() -> impl ClonableParser<'a, Option<Spanned<Directive<'a>>>> {
    padded(
        choice((
            with_sep(mnemonic("DATA"))
                .ignore_then(expr().separated_by(comma_delimiter()).collect())
                .map(Directive::Data)
                .labelled("data directive")
                .as_context(),
            with_sep(mnemonic("ASCII"))
                .ignore_then(ascii_string())
                .map(Directive::Ascii)
                .labelled("ASCII directive")
                .as_context(),
            instr().map(Box::new).map(Directive::Instruction),
        ))
        .spanned(),
    )
    .or_not()
    .labelled("directive")
    .as_context()
}

fn comment<'a>() -> impl ClonableParser<'a, Option<Spanned<&'a str>>> {
    text::inline_whitespace()
        .ignore_then(
            just(';')
                .then(any().and_is(just('\n').not()).repeated())
                .to_slice()
                .spanned()
                .labelled("comment")
                .as_context(),
        )
        .or_not()
}

/// Generate a [parser][Parser] for a [`Line`]
#[must_use]
pub fn line<'a>() -> impl ClonableParser<'a, Line<'a>> {
    padded(group((labels(), directive(), comment())))
        .map(|(labels, directive, comment)| Line {
            labels,
            directive,
            comment,
        })
        .labelled("line")
}

/// Generate a [parser][Parser] for a full IAL program
#[must_use]
pub fn ial<'a>() -> impl ClonableParser<'a, Vec<Line<'a>>> {
    line()
        .separated_by(just('\n').labelled("newline"))
        .collect()
}

#[cfg(test)]
mod ast_tests {

    use super::*;
    use crate::util::*;

    #[test]
    fn parse_blank_line() {
        assert_eq!(
            line().parse("").unwrap(),
            Line {
                labels: vec![],
                directive: None,
                comment: None,
            }
        );
    }

    #[test]
    fn parse_whitespace_only_line() {
        assert_eq!(
            line().parse("\t  \t  \t  \t  \t").unwrap(),
            Line {
                labels: vec![],
                directive: None,
                comment: None,
            }
        );
    }

    #[test]
    fn unbalanced_parens() {
        assert!(expr().parse("(").has_errors());
        assert!(expr().parse(")").has_errors());
        assert!(expr().parse(")(").has_errors());
    }

    #[test]
    fn indendet_comment() {
        assert_eq!(
            line().parse("    ; comment").unwrap(),
            Line {
                labels: vec![],
                directive: None,
                comment: Some(span("; comment", 4..13)),
            }
        );
    }

    #[test]
    fn parse_char_literal() {
        assert_eq!(expr().parse("'0'").unwrap(), span(expr!(:b'0'), 0..3));
    }

    #[test]
    fn parse_data() {
        assert_eq!(
            directive().parse("DATA 1, 1, 1").unwrap(),
            Some(span(
                Directive::Data(vec![
                    span(expr!(1), 5..6),
                    span(expr!(1), 8..9),
                    span(expr!(1), 11..12),
                ]),
                0..12
            ))
        );
    }

    #[test]
    fn multiple_labels() {
        macro_rules! l {
            ($text: expr, $span: expr) => {{ Label(span($text, $span)) }};
        }
        assert_eq!(
            line().parse("foo:bar: baz:DATA 0").unwrap(),
            Line {
                labels: vec![l!("foo", 0..3), l!("bar", 4..7), l!("baz", 9..12)],
                directive: Some(span(Directive::Data(vec![span(expr!(0), 18..19)]), 13..19)),
                comment: None,
            }
        );
    }

    #[test]
    fn parse_instrs() {
        let parser = instr();
        macro_rules! p {
            ($t: tt $e: tt, $start: expr, $end: expr) => {
                param!($t <expr!($e);>[$start..$end])
            };
            ($e: tt, $start: expr, $end: expr) => {
                param!(<expr!($e);>[$start..$end])
            };
        }
        macro_rules! i {
            [$i: ident] => { Instr::$i };
            [$i: ident ($($params: expr),+)] => { Instr::$i ($($params),+ ) };
        }
        macro_rules! parse {
            ($text: literal) => {
                parser.parse($text).unwrap()
            };
        }
        assert_eq!(
            parse!("ADD #1, @1, 1"),
            i![Add(p!(#1, 4, 6), p!(@1, 8, 10), p!(1, 12, 13))]
        );
        assert_eq!(
            parse!("MUL 3, @20, e"),
            i![Mul(p!(3, 4, 5), p!(@20, 7, 10), p!(e, 12, 13))]
        );
        assert_eq!(parse!("IN #e"), i![In(p!(#e, 3, 5))]);
        assert_eq!(parse!("OUT #5"), i![Out(p!(#5, 4, 6))]);
        assert_eq!(parse!("JNZ @a, #b"), i![Jnz(p!(@a, 4, 6), p!(#b, 8, 10))]);
        assert_eq!(parse!("JZ @a, #b"), i![Jz(p!(@a, 3, 5), p!(#b, 7, 9))]);
        assert_eq!(
            parse!("SLT 1,@1, #5"),
            i![Lt(p!(1, 4, 5), p!(@1, 6, 8), p!(#5, 10, 12))]
        );
        assert_eq!(
            parse!("LT 1,@1, #5"),
            i![Lt(p!(1, 3, 4), p!(@1, 5, 7), p!(#5, 9, 11))]
        );
        assert_eq!(
            parse!("SEQ @3, 32, 1"),
            i![Eq(p!(@3, 4, 6), p!(32, 8, 10), p!(1, 12, 13))]
        );
        assert_eq!(
            parse!("EQ @3, 32, 1"),
            i![Eq(p!(@3, 3, 5), p!(32, 7, 9), p!(1, 11, 12))]
        );
        assert_eq!(parse!("INCB #hello"), i![Rbo(p!(#hello, 5, 11))]);
        assert_eq!(parse!("HALT"), i![Halt]);
    }

    #[test]
    fn parse_param_labels() {
        let parser = instr();
        let expected_param = Parameter(
            ParamMode::Immediate,
            boxed(OuterExpr {
                labels: vec![Label(span("out_val", 5..12))],
                expr: span(expr!(0), 14..15),
            }),
        );
        let expected = Instr::Out(expected_param);
        assert_eq!(parser.parse("OUT #out_val: 0").unwrap(), expected);
    }

    #[test]
    fn parse_exprs() {
        let expr_parse = expr();

        macro_rules! expr_test {
            ($expr: literal, $expected: expr) => {
                let parsed = expr_parse.parse($expr).unwrap().inner;
                assert_eq!(parsed, $expected, "{{ {} }} != {{ {parsed} }}", $expr);
            };
        }

        expr_test!("1", expr!(1));

        expr_test!(
            "1 + 1",
            expr!(
                expr!(1);[0..1] +[2] expr!(1);[4..5]
            )
        );

        expr_test!(
            "1 * 1 + 1",
            expr!(
                expr!(
                    expr!(1);[0..1] *[2] expr!(1);[4..5]
                );[0..5]
                +[6]
                expr!(1);[8..9]
            )
        );

        let expected = expr!( (expr!(+expr!(e);[2..3]);[1..3]) );
        expr_test!("(+e)", expected);

        let expected = expr!(
            expr!((
                expr!(
                    expr!(1);[1..2]
                    +[3]
                    expr!(
                        +expr!(
                            - expr!(e);[7..8]
                        );[6..8]
                    );[5..8]
                );[1..8]
            ));[0..9]
            -[10]
            expr!(1);[12..13]
        );
        expr_test!("(1 + +-e) - 1", expected);
    }

    #[test]
    fn ascii_escapes() {
        macro_rules! char_test {
            ($text: expr, $val: expr) => {{
                assert_eq!(ascii_char().parse($text).unwrap(), Expr::AsciiChar($val));
            }};
        }
        char_test!(r"'\\'", b'\\');
        char_test!(r"'\''", b'\'');
        char_test!(r"'\n'", b'\n');
        char_test!(r"'\t'", b'\t');
        char_test!(r"'\r'", b'\r');
        char_test!(r"'\e'", b'\x1b');

        for n in 0..0x80 {
            let literal_char = format!("'{}'", n as char);
            if matches!(n, b'\\' | b'\'') {
                assert!(
                    ascii_char().parse(&literal_char).has_errors(),
                    "{literal_char:?}"
                );
            } else {
                char_test!(&literal_char, n);
            }
        }
        for n in 0..=u8::MAX {
            let hex = format!("'\\x{n:02x}'");
            char_test!(&hex, n);
            let oct_nopad = format!("'\\{n:o}'");
            char_test!(&oct_nopad, n);
            let oct_pad2 = format!("'\\{n:02o}'");
            char_test!(&oct_pad2, n);
            let oct_pad3 = format!("'\\{n:03o}'");
            char_test!(&oct_pad3, n);
        }
    }
}
