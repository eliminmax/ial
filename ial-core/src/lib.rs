// SPDX-FileCopyrightText: 2024 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Core types used throughout the IAL workspace
#![warn(missing_docs)]

use std::error::Error;
use std::fmt::{self, Debug, Display};

/// Parameter mode for Intcode instruction
///
/// Intcode instruction parameters each have a mode:  [positional], [immediate], or [relative].
///
/// When executing an intcode instruction, the instruction's parameters are interpreted in
/// accordance with their associated modes.
///
/// [positional]: ParamMode::Positional
/// [immediate]: ParamMode::Immediate
/// [relative]: ParamMode::Relative
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum ParamMode {
    /// Positional Mode
    ///
    /// A parameter in positional mode evaluates to the value at the address specified by the
    /// parameter.
    Positional = 0,
    /// Immediate Mode
    ///
    /// A parameter in immediate mode evaluates directly to the value specified. Instructions which
    /// write to memory may not use immediate mode for their destinations.
    #[doc(alias = "#")]
    Immediate = 1,
    /// Relative Mode
    ///
    /// A parameter in positional mode evaluates to the value at the address specified by the
    /// parameter, added to the [Relative Base], which starts out as `0` but can be modified
    /// throughout the program's execution.
    ///
    /// [Relative Base]: https://adventofcode.com/2019/day/9
    #[doc(alias = "@")]
    Relative = 2,
}

impl ParamMode {
    /// Extract the parameter modes from the provided opcode [i64]
    ///
    /// Digits are read from the absolute value of `op_int`.
    ///
    /// # Examples
    ///
    /// ```
    ///# use ial_core::{ParamMode, UnknownMode};
    /// assert_eq!(
    ///     ParamMode::extract(21001).unwrap(),
    ///     [
    ///         ParamMode::Positional,
    ///         ParamMode::Immediate,
    ///         ParamMode::Relative,
    ///     ],
    /// );
    /// assert_eq!(
    ///     ParamMode::extract(-21001).unwrap(),
    ///     [
    ///         ParamMode::Positional,
    ///         ParamMode::Immediate,
    ///         ParamMode::Relative,
    ///     ],
    /// );
    /// assert!(ParamMode::extract(31001).is_err());
    /// ```
    /// # Errors
    ///
    /// If any of the hundred's, thousand's, or ten thousand's digits are not a valid mode defined
    /// in ether Advent Of Code day [5] or [9], returns an [`UnknownMode`] containing the mode
    /// digit.
    ///
    /// [5]: https://adventofcode.com/2019/day/5
    /// [9]: https://adventofcode.com/2019/day/9
    pub fn extract(op_int: i64) -> Result<[Self; 3], UnknownMode> {
        let op_int = op_int.abs();
        Ok([
            ((op_int / 100) % 10).try_into()?,
            ((op_int / 1000) % 10).try_into()?,
            ((op_int / 10000) % 10).try_into()?,
        ])
    }
}

impl Display for ParamMode {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamMode::Positional => Ok(()),
            ParamMode::Immediate => write!(fmt, "#"),
            ParamMode::Relative => write!(fmt, "@"),
        }
    }
}

impl TryFrom<i64> for ParamMode {
    type Error = UnknownMode;
    fn try_from(i: i64) -> Result<Self, Self::Error> {
        match i {
            0 => Ok(ParamMode::Positional),
            1 => Ok(ParamMode::Immediate),
            2 => Ok(ParamMode::Relative),
            _ => Err(Self::Error {
                mode_digit: (i % 10) as i8,
            }),
        }
    }
}


#[derive(Debug)]
/// An unknown mode was specified in an instruction
pub struct UnknownMode {
    mode_digit: i8,
}

impl Display for UnknownMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "encountered unknown parameter mode {}", self.digit())
    }
}

impl UnknownMode {
    /// Get the digit of the mode as an [`i8`]
    pub fn digit(&self) -> i8 {
        self.mode_digit
    }
}

impl Error for UnknownMode {}
