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

/// a virtual memory management unit
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

    /// remove all segments that are filled with zeroes, and shrink `self.segments`'s allocation
    pub(super) fn prune(&mut self) {
        self.segments.retain(|_, s| s[..] != EMPTY);
        self.segments.shrink_to_fit();
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
    type MemSlice<'a> = Cow<'a, [i64]>;

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

/// An [`Iterator`] created with [`IntcodeMem::into_iter`]
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
