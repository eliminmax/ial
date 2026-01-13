// SPDX-FileCopyrightText: 2024 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use super::*;

impl Interpreter {
    // Given a 5 digit number, digits ABCDE are used as follows:
    // DE is the two-digit opcode
    // C is the 1st parameter's mode
    // B is the 2nd parameter's mode
    // A is the 3rd parameter's mode
    //
    // So *0*1202 would be parsed as follows:
    //
    // Opcode 02 is multiply
    // C=2: 1st parameter is in relative mode
    // B=1: 2nd parameter is in immediate mode
    // A=0: 3rd parameter is in positional mode
    pub(crate) fn parse_op(op: i64) -> Result<(OpCode, [ParamMode; 3]), ErrorState> {
        let modes: [ParamMode; 3] = [
            ((op / 100) % 10).try_into()?,   // C (hundreds place)
            ((op / 1000) % 10).try_into()?,  // B (thousands place)
            ((op / 10000) % 10).try_into()?, // A (ten thousands place)
        ];
        match op % 100 {
            ..-99 | 100.. => unreachable!("modulo makes this impossible"),
            -99..=0 | 10..99 => Err(ErrorState::UnrecognizedOpcode(op)),
            1 => Ok(OpCode::Add),
            2 => Ok(OpCode::Mul),
            3 => Ok(OpCode::In),
            4 => Ok(OpCode::Out),
            5 => Ok(OpCode::Jnz),
            6 => Ok(OpCode::Jz),
            7 => Ok(OpCode::Lt),
            8 => Ok(OpCode::Eq),
            9 => Ok(OpCode::Rbo),
            99 => Ok(OpCode::Halt),
        }
        .map(|op| (op, modes))
    }

    /// Wraps [Interpreter::mem_get], marking the interpreter as poisoned on error
    pub(crate) fn checked_access(&mut self, address: i64) -> Result<i64, NegativeMemAccess> {
        let result = self.mem_get(address);
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    /// Processes the int in memory at `address` into a concrete value using the method appropriate
    /// for `mode`.
    /// If that would involve accessing memory at a negative index, instead marks `self` as
    /// poisoned and returns the error
    pub(crate) fn resolve_param(
        &mut self,
        mode: ParamMode,
        offset: i64,
    ) -> Result<i64, NegativeMemAccess> {
        match mode {
            ParamMode::Positional => self
                .checked_access(self.index + offset)
                .map(|i| self.code[i]),
            ParamMode::Immediate => Ok(self.code[self.index + offset]),
            ParamMode::Relative => self
                .checked_access(self.index + offset)
                .map(|i| self.code[i + self.rel_offset]),
        }
    }

    /// Processes turns `address` into a concrete index according to `mode`.
    /// If that would involve accessing memory at a negative index, or if `mode` is
    /// [ParamMode::Immediate], it instead marks `self` as poisoned and returns the error
    pub(crate) fn resolve_dest(&mut self, mode: ParamMode, offset: i64) -> Result<i64, ErrorState> {
        match (mode, self.code[self.index + offset]) {
            (ParamMode::Positional, n @ ..=-1) => {
                self.poisoned = true;
                Err(ErrorState::NegativeMemAccess(n))
            }
            (ParamMode::Relative, n) if n + self.rel_offset < 0 => {
                self.poisoned = true;
                Err(ErrorState::NegativeMemAccess(n))
            }
            (ParamMode::Immediate, n) => {
                self.poisoned = true;
                Err(ErrorState::WriteToImmediate(n))
            }
            (ParamMode::Positional, n) => Ok(n),
            (ParamMode::Relative, n) => Ok(n + self.rel_offset),
        }
    }

    /// common logic of all 4 instructions that take 3 parameters
    pub(crate) fn op3(
        &mut self,
        modes: [ParamMode; 3],
        operation: impl Fn(i64, i64) -> i64,
    ) -> Result<StepOutcome, ErrorState> {
        let a = self.resolve_param(modes[0], 1)?;
        let b = self.resolve_param(modes[1], 2)?;
        let dest = self.resolve_dest(modes[2], 3)?;
        let val = operation(a, b);
        self.trace([
            (self.code[self.index + 1], a),
            (self.code[self.index + 2], b),
            (self.code[self.index + 3], val),
        ]);
        self.code[dest] = val;
        self.index += 4;
        Ok(StepOutcome::Running)
    }

    pub(crate) fn jump(
        &mut self,
        modes: [ParamMode; 3],
        func: impl Fn(i64) -> bool,
    ) -> Result<StepOutcome, ErrorState> {
        let expr = self.resolve_param(modes[0], 1)?;
        let dest = self.resolve_param(modes[1], 2)?;
        self.trace([
            (self.code[self.index + 1], expr),
            (self.code[self.index + 2], dest),
        ]);
        if func(expr) {
            self.index = dest;
            if dest < 0 {
                self.poisoned = true;
                return Err(ErrorState::JumpToNegative(dest));
            }
        } else {
            self.index += 3;
        }
        Ok(StepOutcome::Running)
    }
}
