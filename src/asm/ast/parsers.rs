// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use super::SingleByteSpan;

use super::prelude::*;
use chumsky::prelude::*;

macro_rules! padded {
    ($inner: expr) => {{ $inner.padded_by(text::inline_whitespace()) }};
}

macro_rules! with_sep {
    ($inner: expr) => {{ $inner.then_ignore(text::inline_whitespace().at_least(1)) }};
}

type RichErr<'a> = chumsky::extra::Err<Rich<'a, char>>;

fn comma_delimiter<'a>() -> impl Parser<'a, &'a str, (), RichErr<'a>> {
    padded!(just(',')).ignored().labelled("comma delimiter")
}

fn param<'a>() -> impl Parser<'a, &'a str, Parameter<'a>, RichErr<'a>> {
    padded!(
        choice((
            just('#')
                .to(ParamMode::Immediate)
                .labelled("immediate mode prefix ('#')"),
            just('@')
                .to(ParamMode::Relative)
                .labelled("relative mode prefix ('@')"),
            empty().to(ParamMode::Positional),
        ))
        .then(outer_expr())
    )
    .map(|(mode, expr)| Parameter(mode, Box::new(expr)))
    .labelled("parameter")
    .as_context()
}

fn outer_expr<'a>() -> impl Parser<'a, &'a str, OuterExpr<'a>, RichErr<'a>> {
    labels()
        .then(expr())
        .map(|(labels, expr)| OuterExpr { labels, expr })
}

fn labels<'a>() -> impl Parser<'a, &'a str, Vec<Label<'a>>, RichErr<'a>> {
    text::ident()
        .spanned()
        .then_ignore(just(":"))
        .map(Label)
        .labelled("label")
        .as_context()
        .then_ignore(text::inline_whitespace())
        .repeated()
        .collect()
}

fn mnemonic<'a>(kw: &'static str) -> impl Parser<'a, &'a str, (), RichErr<'a>> {
    text::ascii::ident().try_map(move |s: &'a str, span| {
        if s.eq_ignore_ascii_case(kw) {
            Ok(())
        } else {
            Err(Rich::custom(span, format!("failed to match keyword {kw}")))
        }
    })
}

fn instr<'a>() -> impl Parser<'a, &'a str, Instr<'a>, RichErr<'a>> {
    macro_rules! params {
        ($n: literal) => {{
            param()
                .separated_by(comma_delimiter())
                .exactly($n)
                .allow_trailing()
                .collect::<Vec<_>>()
                .map(|v| <[Parameter; $n]>::try_from(v).expect("sized"))
        }};
    }
    macro_rules! op {
        ($name: literal, $variant: ident::<1>) => {
            padded!(mnemonic($name).labelled($name))
                .ignore_then(param().map(Instr::$variant))
                .labelled(concat!($name, " instruction parameter"))
        };
        ($name: literal, $variant: ident::<2>) => {
            padded!(mnemonic($name).labelled($name))
                .ignore_then((params!(2)).map(|[a, b]| Instr::$variant(a, b)))
                .labelled(concat!("2 ", $name, " instruction parameters"))
        };
        ($name: literal, $variant: ident::<3>) => {
            padded!(mnemonic($name).labelled($name))
                .ignore_then((params!(3)).map(|[a, b, c]| Instr::$variant(a, b, c)))
                .labelled(concat!("3 ", $name, " instruction parameters"))
        };
    }

    padded!(choice((
        op!("ADD", Add::<3>),
        op!("MUL", Mul::<3>),
        op!("IN", In::<1>),
        op!("OUT", Out::<1>),
        op!("JNZ", Jnz::<2>),
        op!("JZ", Jz::<2>),
        op!("LT", Lt::<3>),
        op!("SLT", Lt::<3>),
        op!("EQ", Eq::<3>),
        op!("SEQ", Eq::<3>),
        op!("RBO", Rbo::<1>),
        op!("INCB", Rbo::<1>),
        just("HALT").to(Instr::Halt).labelled("HALT"),
    )))
    .labelled("instruction")
    .as_context()
}

fn expr<'a>() -> impl Parser<'a, &'a str, Spanned<Expr<'a>>, RichErr<'a>> + Clone {
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
        let unary = padded!(one_of("-+").spanned())
            .repeated()
            .foldr(
                atom,
                |Spanned { inner, mut span }: Spanned<char>, rhs: Spanned<Expr<'a>>| {
                    span.end = rhs.span.end;
                    Spanned {
                        inner: match inner {
                            '+' => Expr::UnaryAdd(Box::new(rhs)),
                            '-' => Expr::Negate(Box::new(rhs)),
                            _ => unreachable!(),
                        },
                        span,
                    }
                },
            )
            .labelled("unary expression");

        let folder = |lhs: Spanned<Expr<'a>>,
                      (op, rhs): (Spanned<BinOperator>, Spanned<Expr<'a>>)| {
            let span = SimpleSpan {
                start: lhs.span.start,
                end: rhs.span.end,
                context: (),
            };
            let op = Spanned {
                inner: op.inner,
                span: SingleByteSpan(op.span.start),
            };
            let inner = Expr::BinOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            };
            Spanned { span, inner }
        };

        let prod = unary
            .clone()
            .foldl(
                padded!(
                    choice((
                        just('*').to(BinOperator::Mul),
                        just('/').to(BinOperator::Div),
                    ))
                    .labelled("binary operator (* or /)")
                    .spanned()
                )
                .then(unary)
                .repeated(),
                folder,
            )
            .labelled("multiplication or division expression");

        prod.clone().foldl(
            padded!(
                choice((
                    just('+').to(BinOperator::Add),
                    just('-').to(BinOperator::Sub),
                ))
                .labelled("binary operator (+ or -)")
                .spanned()
            )
            .then(prod)
            .repeated(),
            folder,
        )
    })
    .labelled("expression")
    .as_context()
}

fn ascii_escape<'a>() -> impl Parser<'a, &'a str, u8, RichErr<'a>> + Clone {
    const HEX_DIGITS: &str = "0123456789ABCDEFabcdef";
    const OCT_DIGITS: &str = "01234567";

    fn strict_hex_val(c: char) -> u8 {
        assert!(
            c.is_ascii(),
            "non ascii should've been caught before calling strict_hex_val"
        );
        #[expect(
            non_contiguous_range_endpoints,
            reason = "mask leaves 1 byte value before b'a' possible"
        )]
        match c as u8 | 0x20 {
            d @ b'0'..=b'9' => d - b'0',
            l @ b'a'..=b'f' => l - b'a' + 10,
            ..32 | 64..96 => unreachable!("masked out"),
            128 => unreachable!("known to be ascii"),
            c => panic!("invalid hex digit: {}", c.escape_ascii()),
        }
    }

    just('\\').ignore_then(choice((
        just('\\').to(b'\\'),
        just('\'').to(b'\''),
        just('\"').to(b'\"'),
        just('n').to(b'\n'),
        just('t').to(b'\t'),
        just('r').to(b'\r'),
        just('e').to(b'\x1b'),
        just('3')
            .ignore_then(one_of(OCT_DIGITS).then(one_of(OCT_DIGITS)))
            .map(|(a, b)| 0o300 + ((a as u8 - b'0') * 8) + (b as u8 - b'0')),
        (one_of(OCT_DIGITS).repeated().at_least(1).at_most(2))
            .fold(0, |acc, x| acc * 8 + (x as u8 - b'0')),
        just('x')
            .ignore_then(one_of(HEX_DIGITS).then(one_of(HEX_DIGITS)))
            .map(|(a, b)| (strict_hex_val(a) << 4) | strict_hex_val(b)),
    )))
}

fn ascii_char<'a>() -> impl Parser<'a, &'a str, Expr<'a>, RichErr<'a>> + Clone {
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

fn ascii_string<'a>() -> impl Parser<'a, &'a str, Spanned<Vec<u8>>, RichErr<'a>> {
    padded!(
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
            .spanned()
    )
    .labelled("ascii string")
    .as_context()
}

fn directive<'a>() -> impl Parser<'a, &'a str, Option<Spanned<Directive<'a>>>, RichErr<'a>> {
    padded!(
        choice((
            with_sep!(just("DATA"))
                .ignore_then(expr().separated_by(comma_delimiter()).collect())
                .map(Directive::Data)
                .labelled("data directive")
                .as_context(),
            with_sep!(just("ASCII"))
                .ignore_then(ascii_string())
                .map(Directive::Ascii)
                .labelled("ASCII directive")
                .as_context(),
            instr().map(Box::new).map(Directive::Instruction),
        ))
        .spanned()
    )
    .or_not()
    .labelled("directive")
    .as_context()
}

fn comment<'a>() -> impl Parser<'a, &'a str, Option<Spanned<&'a str>>, RichErr<'a>> {
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

fn line<'a>() -> impl Parser<'a, &'a str, Line<'a>, RichErr<'a>> {
    padded!(group((labels(), directive(), comment())))
        .map(|(labels, directive, comment)| Line {
            labels,
            directive,
            comment,
        })
        .labelled("line")
}

pub(in crate::asm) fn grammar<'a>() -> impl Parser<'a, &'a str, Vec<Line<'a>>, RichErr<'a>> {
    line()
        .separated_by(just("\n").labelled("newline"))
        .collect()
}

#[cfg(test)]
mod ast_tests {
    // SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
    //
    // SPDX-License-Identifier: 0BSD

    use super::*;
    use crate::asm::ast::util::*;

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
    fn parse_char_literal() {
        assert_eq!(expr().parse("'0'").unwrap(), span(expr!(:b'0'), 0..3),);
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
}
