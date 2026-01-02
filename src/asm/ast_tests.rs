// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use super::*;

macro_rules! span {
    ($start: expr, $end: expr) => {
        SimpleSpan {
            start: $start,
            end: $end,
            context: (),
        }
    };
}

macro_rules! spanned {
    ($inner: expr, $start: expr, $end: expr) => {
        Spanned {
            inner: $inner,
            span: span!($start, $end),
        }
    };
}

#[test]
fn parse_blank_line() {
    assert_eq!(
        parse_line().parse("").unwrap(),
        Line {
            label: None,
            inner: None
        }
    )
}

#[test]
fn parse_data() {
    assert_eq!(
        line_inner().parse("DATA 1, 1, 1").unwrap(),
        Some(spanned!(
            Directive::DataDirective(vec![
                Spanned {
                    inner: Expr::Number(1),
                    span: span!(5, 6)
                },
                Spanned {
                    inner: Expr::Number(1),
                    span: span!(8, 9)
                },
                Spanned {
                    inner: Expr::Number(1),
                    span: span!(11, 12)
                },
            ]),
            0,
            12
        ))
    );
}

#[test]
fn parse_instrs() {
    let parser = instr();
    macro_rules! p {
        (#$e: literal, $start: expr, $end: expr) => {
            Parameter(
                spanned!(ParamMode::Immediate, $start, $start + 1),
                Arc::new(spanned!(Expr::Number($e), $start + 1, $end)),
            )
        };
        (@$e: literal, $start: expr, $end: expr) => {
            Parameter(
                spanned!(ParamMode::Relative, $start, $start + 1),
                Arc::new(spanned!(Expr::Number($e), $start + 1, $end)),
            )
        };
        ($e: literal, $start: expr, $end: expr) => {
            Parameter(
                spanned!(ParamMode::Positional, $start, $start),
                Arc::new(spanned!(Expr::Number($e), $start, $end)),
            )
        };
        (#$e: ident, $start: expr, $end: expr) => {
            Parameter(
                spanned!(ParamMode::Immediate, $start, $start + 1),
                Arc::new(spanned!(Expr::Ident(stringify!($e)), $start + 1, $end)),
            )
        };
        (@$e: ident, $start: expr, $end: expr) => {
            Parameter(
                spanned!(ParamMode::Relative, $start, $start + 1),
                Arc::new(spanned!(Expr::Ident(stringify!($e)), $start + 1, $end)),
            )
        };
        ($e: ident, $start: expr, $end: expr) => {
            Parameter(
                spanned!(ParamMode::Positional, $start, $start),
                Arc::new(spanned!(Expr::Ident(stringify!($e)), $start, $end)),
            )
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
        i![Slt(p!(1, 4, 5), p!(@1, 6, 8), p!(#5, 10, 12))]
    );
    assert_eq!(
        parse!("LT 1,@1, #5"),
        i![Slt(p!(1, 3, 4), p!(@1, 5, 7), p!(#5, 9, 11))]
    );
    assert_eq!(
        parse!("SEQ @3, 32, 1"),
        i![Seq(p!(@3, 4, 6), p!(32, 8, 10), p!(1, 12, 13))]
    );
    assert_eq!(
        parse!("EQ @3, 32, 1"),
        i![Seq(p!(@3, 3, 5), p!(32, 7, 9), p!(1, 11, 12))]
    );
    assert_eq!(parse!("INCB #hello"), i![Incb(p!(#hello, 5, 11))]);
    assert_eq!(parse!("HALT"), i![Halt]);
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

    expr_test!("1", Expr::Number(1));

    let n0 = Arc::new(spanned!(Expr::Number(1), 0, 1));
    let n1 = Arc::new(spanned!(Expr::Number(1), 4, 5));
    let n2 = Arc::new(spanned!(Expr::Number(1), 8, 9));
    let expected = Expr::BinOp {
        lhs: Arc::clone(&n0),
        op: spanned!(BinOperator::Add, 2, 3),
        rhs: Arc::clone(&n1),
    };
    expr_test!("1 + 1", expected);

    let expected = Expr::BinOp {
        lhs: Arc::new(spanned!(
            Expr::BinOp {
                lhs: Arc::clone(&n0),
                op: spanned!(BinOperator::Mul, 2, 3),
                rhs: Arc::clone(&n1),
            },
            0,
            5
        )),
        op: spanned!(BinOperator::Add, 6, 7),
        rhs: Arc::clone(&n2),
    };
    expr_test!("1 * 1 + 1", expected);

    let mut expected = Expr::Ident("e");
    expected = Expr::UnaryAdd(Arc::new(spanned!(expected, 2, 3)));
    expected = Expr::Inner(Arc::new(spanned!(expected, 1, 3)));
    expr_test!("(+e)", expected);

    let lhs = Arc::new(spanned!(
        Expr::Inner({
            let lhs = Arc::new(spanned!(Expr::Number(1), 1, 2));
            let op = spanned!(BinOperator::Add, 3, 4);
            let mut rhs = Arc::new(spanned!(Expr::Ident("e"), 7, 8));
            rhs = Arc::new(spanned!(Expr::Negate(rhs), 6, 8));
            rhs = Arc::new(spanned!(Expr::UnaryAdd(rhs), 5, 8));
            Arc::new(spanned!(Expr::BinOp { lhs, op, rhs }, 1, 8))
        }),
        0,
        9
    ));
    let rhs = Arc::new(spanned!(Expr::Number(1), 12, 13));

    let expected = Expr::BinOp {
        lhs,
        op: spanned!(BinOperator::Sub, 10, 11),
        rhs,
    };
    expr_test!("(1 + +-e) - 1", expected);
}
