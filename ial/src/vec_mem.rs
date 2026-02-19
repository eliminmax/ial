// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use crate::{IntcodeMem, IntcodeMemIndex, NegativeMemAccess};
use std::ops::{Index, IndexMut};

#[derive(Debug, PartialEq, Clone)]
/// A simple type implementing [`IntcodeMem`], using a [`Vec<i64>`] to store the memory.
///
/// Unlike [`PagedMem`][crate::PagedMem], memory is stored inline, which is a good thing if a fixed
/// amount of memory is used, but can be a bad thing:
///
/// # Examples
///
/// ## *When not to use*
///
/// The following example, when run, uses around 16 GiB of heap memory, given the large address
/// accessed, but using [`PagedMem`][crate::PagedMem] would only use around 60 KiB.
///
/// ```no_run
/// use ial::{Interpreter, VecMem};
///
/// let mut vec_mem: Interpreter<VecMem> =
///     Interpreter::new([
///         // sets address 1000000000 to HALT
///         1101, 0, 99, 1000000000,
///         // copy HALT instruction from 1000000000 back to the next instruction index
///         101, 0, 1000000000, 8
/// ]);
/// ```
pub struct VecMem(Vec<i64>);

impl Index<i64> for VecMem {
    type Output = i64;

    fn index(&self, index: i64) -> &Self::Output {
        self.0
            .get(usize::try_from(index).expect("index in range 0..=usize::MAX"))
            .unwrap_or(&0)
    }
}
impl IndexMut<i64> for VecMem {
    fn index_mut(&mut self, index: i64) -> &mut Self::Output {
        let index = usize::try_from(index).expect("index in range 0..=usize::MAX");
        if self.0.len() <= index {
            self.0.extend(vec![0; 1 + index - self.0.len()]);
        }
        self.0.index_mut(index)
    }
}
impl IntcodeMemIndex for VecMem {}

impl IntoIterator for VecMem {
    type Item = i64;

    type IntoIter = <Vec<i64> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<i64> for VecMem {
    fn from_iter<T: IntoIterator<Item = i64>>(iter: T) -> Self {
        Self(Vec::from_iter(iter))
    }
}

impl IntcodeMem for VecMem {
    type MemSlice<'a> = &'a [i64];

    fn get_range(
        &self,
        range: std::ops::Range<i64>,
    ) -> Result<Self::MemSlice<'_>, NegativeMemAccess> {
        if range.start < 0 {
            Err(NegativeMemAccess(range.start))
        } else {
            let start = usize::try_from(range.start).expect("range starts past usize::MAX");
            let end = usize::try_from(range.end).expect("range ends past usize::MAX");
            Ok(&self.0[start..end])
        }
    }
}
