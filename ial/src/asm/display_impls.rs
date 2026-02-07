// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use chumsky::span::Spanned;

use super::AssemblyError;
use super::ast::{BinOperator, Directive, Expr, Instr, Label, Line, OuterExpr, Parameter};

use std::fmt::{self, Display};

impl Display for BinOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOperator::Add => write!(f, "+"),
            BinOperator::Sub => write!(f, "-"),
            BinOperator::Mul => write!(f, "*"),
            BinOperator::Div => write!(f, "/"),
        }
    }
}

impl Display for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Number(n) => write!(f, "{n}"),
            Expr::AsciiChar(c) => write!(f, "'{}'", c.escape_ascii()),
            Expr::Ident(id) => write!(f, "{id}"),
            Expr::BinOp { lhs, op, rhs } => {
                write!(f, "{} {} {}", lhs.inner, op.inner, rhs.inner)
            }
            Expr::Negate(e) => write!(f, "-{}", e.inner),
            Expr::UnaryAdd(e) => write!(f, "+{}", e.inner),
            Expr::Parenthesized(e) => write!(f, "({})", e.inner),
        }
    }
}

impl Display for Label<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:", self.0.inner)
    }
}

impl Display for OuterExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for label in &self.labels {
            write!(f, "{label}\t")?;
        }
        write!(f, "{}", self.expr.inner)
    }
}

impl Display for Parameter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.0, self.1)
    }
}

impl Display for Instr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instr::Add(a, b, c) => write!(f, "ADD {a}, {b}, {c}"),
            Instr::Mul(a, b, c) => write!(f, "MUL {a}, {b}, {c}"),
            Instr::In(a) => write!(f, "IN {a}"),
            Instr::Out(a) => write!(f, "OUT {a}"),
            Instr::Jnz(a, b) => write!(f, "JNZ {a}, {b}"),
            Instr::Jz(a, b) => write!(f, "JZ {a}, {b}"),
            Instr::Lt(a, b, c) => write!(f, "LT {a}, {b}, {c}"),
            Instr::Eq(a, b, c) => write!(f, "EQ {a}, {b}, {c}"),
            Instr::Rbo(a) => write!(f, "RBO {a}"),
            Instr::Halt => write!(f, "HALT"),
        }
    }
}

impl Display for Directive<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Directive::Data(exprs) => {
                write!(f, "DATA ")?;
                if let Some(expr) = exprs.first() {
                    write!(f, "{}", expr.inner)?;
                }
                for expr in &exprs[1..] {
                    write!(f, ", {}", expr.inner)?;
                }
                Ok(())
            }
            Directive::Ascii(spanned) => {
                write!(f, "ASCII {}", spanned.inner.escape_ascii())
            }
            Directive::Instruction(instr) => write!(f, "{instr}"),
        }
    }
}

impl Display for Line<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for Label(Spanned { inner, .. }) in &self.labels {
            write!(f, "{inner}:\t")?;
        }
        if let Some(Spanned { inner, .. }) = &self.directive {
            write!(f, "{inner}")?;
        }
        Ok(())
    }
}

impl Display for AssemblyError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AssemblyError::UnresolvedLabel { label, .. } => {
                write!(f, "unresolved label: {label:?}")
            }
            AssemblyError::DuplicateLabel { label, .. } => write!(f, "duplicate label: {label:?}"),
            AssemblyError::DirectiveTooLarge { size, .. } => {
                write!(
                    f,
                    "directive too large: size {size} is more than maximum {}",
                    i64::MAX
                )
            }
            AssemblyError::DivisionByZero { .. } => write!(f, "division by zero"),
        }
    }
}
