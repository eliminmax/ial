// SPDX-FileCopyrightText: 2024 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use crate::State;

use super::{
    IntcodeMem, Interpreter, InterpreterError, NegativeMemAccess, OpCode, ParamMode, StepOutcome,
};

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
pub(crate) fn parse_op(op: i64) -> Result<(OpCode, [ParamMode; 3]), InterpreterError> {
    Ok((
        OpCode::try_from(op % 100).map_err(|_| InterpreterError::UnrecognizedOpcode(op))?,
        ParamMode::extract(op)?,
    ))
}

type OperationResult = Result<StepOutcome, InterpreterError>;
impl<Mem: IntcodeMem> Interpreter<Mem> {
    /// Wraps [`Interpreter::mem_get`], marking the interpreter as poisoned on error
    fn resolve(&mut self, address: i64) -> Result<i64, NegativeMemAccess> {
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
            ParamMode::Positional => self.resolve(self.code[self.index + offset]),
            ParamMode::Immediate => Ok(self.code[self.index + offset]),
            ParamMode::Relative => self.resolve(self.rel_offset + self.code[self.index + offset]),
        }
    }

    /// Processes turns `address` into a concrete index according to `mode`.
    /// If that would involve accessing memory at a negative index, or if `mode` is
    /// [`ParamMode::Immediate`], it instead marks `self` as poisoned and returns the error
    pub(crate) fn resolve_dest(
        &mut self,
        mode: ParamMode,
        offset: i64,
    ) -> Result<i64, InterpreterError> {
        match (mode, self.code[self.index + offset]) {
            (ParamMode::Positional, n @ ..=-1) => {
                self.poisoned = true;
                Err(InterpreterError::NegativeMemAccess(NegativeMemAccess(n)))
            }
            (ParamMode::Relative, n) if n + self.rel_offset < 0 => {
                self.poisoned = true;
                Err(InterpreterError::NegativeMemAccess(NegativeMemAccess(
                    n + self.rel_offset,
                )))
            }
            (ParamMode::Immediate, n) => {
                self.poisoned = true;
                Err(InterpreterError::WriteToImmediate(n))
            }
            (ParamMode::Positional, n) => Ok(n),
            (ParamMode::Relative, n) => Ok(n + self.rel_offset),
        }
    }

    pub(crate) fn input(
        &mut self,
        mode: ParamMode,
        input: &mut impl Iterator<Item = i64>,
    ) -> OperationResult {
        let Some(input) = input.next() else {
            return Ok(StepOutcome::Stopped(super::State::Awaiting));
        };
        let dest = self.resolve_dest(mode, 1)?;
        self.trace([(self.code[self.index + 1], input)]);
        self.code[dest] = input;
        self.index += 2;
        Ok(StepOutcome::Running)
    }

    pub(crate) fn output(&mut self, mode: ParamMode, output: &mut Vec<i64>) -> OperationResult {
        let out_val = self.resolve_param(mode, 1)?;
        self.trace([(self.code[self.index + 1], out_val)]);
        output.push(out_val);
        self.index += 2;
        Ok(StepOutcome::Running)
    }

    pub(crate) fn rbo(&mut self, mode: ParamMode) -> OperationResult {
        let offset = self.resolve_param(mode, 1)?;
        self.trace([(self.code[self.index + 1], offset)]);
        self.rel_offset += offset;
        self.index += 2;
        Ok(StepOutcome::Running)
    }

    pub(crate) fn halt(&mut self) -> StepOutcome {
        self.trace([]);
        self.halted = true;
        StepOutcome::Stopped(State::Halted)
    }

    /// common logic of all 4 instructions that take 3 parameters
    pub(crate) fn op3(
        &mut self,
        modes: [ParamMode; 3],
        operation: impl Fn(i64, i64) -> i64,
    ) -> OperationResult {
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

    /// common logic of both jump instructions
    pub(crate) fn jump(
        &mut self,
        modes: [ParamMode; 3],
        jump_if: impl Fn(i64) -> bool,
    ) -> OperationResult {
        let expr = self.resolve_param(modes[0], 1)?;
        let dest = self.resolve_param(modes[1], 2)?;
        self.trace([
            (self.code[self.index + 1], expr),
            (self.code[self.index + 2], dest),
        ]);
        if jump_if(expr) {
            self.index = dest;
            if dest < 0 {
                self.poisoned = true;
                return Err(InterpreterError::JumpToNegative(dest));
            }
        } else {
            self.index += 3;
        }
        Ok(StepOutcome::Running)
    }
}

#[cfg(test)]
mod fallback_tests {
    //! Some tests that hit parts of the internals that aren't hit by integration tests or other
    //! modules' unit tests

    use super::*;
    use std::iter::empty;
    type InterpreterV = crate::Interpreter<crate::VecMem>;
    type InterpreterP = crate::Interpreter<crate::PagedMem>;

    fn assemble(s: &'static str) -> Vec<i64> {
        crate::asm::assemble(s).unwrap()
    }

    macro_rules! assert_poisoned {
        ($interp: ident) => {{
            assert!($interp.poisoned);
            let poisoned_err = $interp.exec_instruction(&mut empty(), &mut vec![]);
            assert_eq!(poisoned_err, Err(InterpreterError::Poisoned));
        }};
    }

    #[test]
    fn relative_dest() {
        let mut interp = InterpreterV::new(assemble("RBO #h\nMUL #11, #9, @0\nh:DATA 0"));
        interp.start_trace();
        let (output, state) = interp.run_through_inputs([]).unwrap();
        assert!(output.is_empty());
        assert_eq!(state, crate::State::Halted);
        let trace = interp.end_trace().unwrap();
        let traced_instrs = trace.as_slice();
        assert_eq!(traced_instrs.len(), 3);
        assert_eq!(traced_instrs[1].op_code(), crate::OpCode::Mul);
        assert_eq!(traced_instrs[1].stored_val(), Some(99));
        assert!(matches!(
            traced_instrs[1].param_modes(),
            [_, _, ParamMode::Relative]
        ));
    }

    #[test]
    fn jump_to_negative() {
        let mut interp = InterpreterV::new([1105, 1, -1]); // JNZ #1, #-1
        let jump_err = interp
            .exec_instruction(&mut empty(), &mut vec![])
            .unwrap_err();
        assert_eq!(jump_err, InterpreterError::JumpToNegative(-1));
        assert_poisoned!(interp);
    }

    #[test]
    fn bad_indices() {
        let neg_mem = InterpreterError::NegativeMemAccess(NegativeMemAccess(-1));
        // read from negative positional
        let mut interp = InterpreterP::new(assemble("ADD -1, #0, 4"));
        let pos_read_err = interp.precompute().unwrap_err();
        assert_eq!(pos_read_err, neg_mem);
        assert_poisoned!(interp);

        // read from negative relative
        let mut interp = InterpreterV::new(assemble("RBO -1\nADD @0, #0, 50"));
        let rel_read_err = interp.precompute().unwrap_err();
        assert_eq!(rel_read_err, neg_mem);
        assert_poisoned!(interp);

        // write to negative positional
        let mut interp = InterpreterV::new(assemble("ADD #0, #1, -1"));
        let pos_write_err = interp.precompute().unwrap_err();
        assert_eq!(pos_write_err, neg_mem);
        assert_poisoned!(interp);

        // write to negative relative
        let mut interp = InterpreterV::new(assemble("RBO #-2\nADD #0, #0, @1"));
        let rel_write_err = interp.precompute().unwrap_err();
        assert_eq!(rel_write_err, neg_mem);
        assert_poisoned!(interp);

        // write to immediate
        let mut interp = InterpreterP::new(assemble("add #1, #1, #0"));
        let imm_write_err = interp.precompute().unwrap_err();
        assert_eq!(imm_write_err, InterpreterError::WriteToImmediate(0));
        assert_poisoned!(interp);
    }
}
