// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use itertools::Itertools;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::ops::Range;

use crate::{IntcodeMem, IntcodeMemIndex, NegativeMemAccess};

macro_rules! page_index {
    ($i: expr) => {{
        #[allow(clippy::cast_sign_loss, reason = "masked down anyway")]
        {
            ($i & 0x1ff) as usize
        }
    }};
}

/// A type that implements [`IntcodeMem`] by splitting the memory into 4096-byte heap-allocated
/// segments (each of which fits 512 [`i64`]s).
///
/// Uses more indirection[^1] than [`VecMem`][crate::VecMem`], but if a high address is used, it
/// won't need to zero-fill the entirety of the address space and store it in actual RAM, and it
/// can support addresses above [`usize::MAX`] on 32-bit platforms.
///
/// When [cloning][Clone], fully-zeroed segments are omitted, and [`PagedMem::prune`] can be called
/// manually to remove them and shrink the allocation.
///
/// [^1]: Specifically, it uses a [`HashMap<i64, Box<[i64; 512]>>`][HashMap] mapping segment starts
/// to the segment contents. The segments are [`Box<[i64; 512]>`][Box]ed so that they don't need to
/// be moved when reallocating the [`HashMap`], at the expense of extra indirection and heap
/// fragmentation.
//
/// # Examples
///
/// In following example, if `vec_mem` were to execute even a single instruction, it would use
/// around 16 GiB of heap memory, given the large address accessed, but `page_mem` would only use
/// around 60 KiB.
///
/// ```no_run
/// use ial::{Interpreter, PagedMem, VecMem};
/// const CODE: [i64; 8] = [
///         // sets address 1000000000 to HALT
///         1101, 0, 99, 1000000000,
///         // copy HALT instruction from 1000000000 back to the next instruction index
///         101, 0, 1000000000, 8
/// ];
///
/// let vec_mem: Interpreter<VecMem> = Interpreter::new(CODE);
///
/// let page_mem: Interpreter<PagedMem> = Interpreter::new(CODE);
/// ```
pub struct PagedMem {
    segments: HashMap<i64, Box<[i64; 512]>>,
}

static EMPTY: [i64; 512] = [0; 512];

impl PagedMem {
    fn active_segments(&self) -> BTreeSet<i64> {
        self.segments
            .iter()
            .filter_map(|(&k, v)| (v.as_ref() == &EMPTY).then_some(k))
            .collect()
    }

    fn get_segment(&self, segment_num: i64) -> &[i64; 512] {
        self.segments
            .get(&segment_num)
            .map_or(&EMPTY, |s| s.as_ref())
    }
}

impl PartialEq for PagedMem {
    fn eq(&self, other: &Self) -> bool {
        let active_segments = self.active_segments();
        other.active_segments() == active_segments
            && active_segments
                .into_iter()
                .all(|seg| self.segments[&seg] == other.segments[&seg])
    }
}

impl FromIterator<i64> for PagedMem {
    fn from_iter<I: IntoIterator<Item = i64>>(iter: I) -> Self {
        let iter = iter.into_iter();

        let mut segments = HashMap::with_capacity(iter.size_hint().0.div_ceil(512));

        let mut current_segment = 0;

        for chunk in &iter.chunks(512) {
            segments.insert(
                current_segment,
                Box::new(
                    chunk
                        .chain([0].into_iter().cycle())
                        .take(512)
                        .collect_array::<512>()
                        .expect("always 512 long"),
                ),
            );
            current_segment += 512;
        }

        Self { segments }
    }
}

impl std::ops::Index<i64> for PagedMem {
    type Output = i64;
    fn index(&self, i: i64) -> &i64 {
        self.segments
            .get(&(i & !0x1ff))
            .map_or(&0, |s| s.index(page_index!(i)))
    }
}

impl IntcodeMemIndex for PagedMem {}

impl IntcodeMem for PagedMem {
    fn get_range(&self, range: Range<i64>) -> Result<Cow<'_, [i64]>, NegativeMemAccess> {
        let first = range.start;
        if first < 0 {
            return Err(NegativeMemAccess(first));
        }
        let last = range.end - 1;
        let first_segment = first & !0x1ff;
        let last_segment = last & !0x1ff;
        if first & !0x1ff == last & !0x1ff {
            Ok(Cow::Borrowed(
                &self.get_segment(first_segment)[page_index!(first)..=page_index!(last)],
            ))
        } else {
            let mut v = Vec::with_capacity(range.clone().count());
            v.extend_from_slice(&self.get_segment(first_segment)[page_index!(first)..]);
            for segment in ((first_segment + 512)..last_segment).step_by(512) {
                v.extend_from_slice(self.get_segment(segment));
            }
            v.extend_from_slice(&self.get_segment(last_segment)[..=page_index!(last)]);

            Ok(Cow::Owned(v))
        }
    }

    fn prune(&mut self) {
        self.segments.retain(|_, s| s[..] != EMPTY);
        self.segments.shrink_to_fit();
    }
}

impl std::ops::IndexMut<i64> for PagedMem {
    fn index_mut(&mut self, i: i64) -> &mut i64 {
        self.segments
            .entry(i & !0x1ff)
            .or_insert(Box::new([0; 512]))
            .index_mut(page_index!(i))
    }
}

impl Clone for PagedMem {
    fn clone(&self) -> Self {
        // don't copy blank pages
        let segments = self
            .segments
            .iter()
            .filter(|&(&_index, mem)| mem.as_ref() != &EMPTY)
            .map(|(&index, mem)| (index, mem.clone()))
            .collect();
        Self { segments }
    }
}

pub struct Iter {
    segments: BTreeMap<i64, [i64; 512]>,
    current_segment: i64,
    segment_index: usize,
}

impl Iterator for Iter {
    type Item = i64;
    fn next(&mut self) -> Option<i64> {
        if self.current_segment > self.segments.keys().max().copied().unwrap_or_default() {
            return None;
        }
        let ret: i64;
        if let Some(segment) = self.segments.get(&self.current_segment) {
            ret = segment[self.segment_index];
        } else {
            ret = 0;
        }

        self.segment_index += 1;
        if self.segment_index == 512 {
            self.segment_index = 0;
            self.segments.remove(&self.current_segment);
            self.current_segment += 512;
        }

        Some(ret)
    }
}

impl IntoIterator for PagedMem {
    type Item = i64;
    type IntoIter = Iter;
    fn into_iter(mut self) -> Iter {
        self.prune();
        Iter {
            segments: self.segments.into_iter().map(|(k, v)| (k, *v)).collect(),
            current_segment: 0,
            segment_index: 0,
        }
    }
}

#[cfg(not(tarpaulin_include))]
impl fmt::Debug for PagedMem {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut fmtstruct = fmt.debug_map();
        for sn in self.segments.keys().sorted_unstable() {
            if self.segments[sn].as_ref() != &EMPTY {
                fmtstruct.entry(
                    &format_args!("{{ segment 0x{sn:04x} }}"),
                    &format_args!("{:?}", self.segments[sn]),
                );
            }
        }
        fmtstruct.finish()
    }
}
