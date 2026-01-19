// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

/// a virtual memory management unit
pub(super) struct IntcodeMem {
    segments: HashMap<i64, Box<[i64; 512]>>,
}

impl IntcodeMem {
    fn active_segments(&self) -> BTreeSet<i64> {
        self.segments
            .iter()
            .filter_map(|(&k, v)| (v.as_ref() == &[0; 512]).then_some(k))
            .collect()
    }

    /// remove all segments that are filled with zeroes, and
    pub(super) fn prune(&mut self) {
        self.segments.retain(|_, s| s[..] != [0; 512]);
        self.segments.shrink_to_fit();
    }
}

impl PartialEq for IntcodeMem {
    fn eq(&self, other: &Self) -> bool {
        let active_segments = self.active_segments();
        other.active_segments() == active_segments
            && active_segments
                .into_iter()
                .all(|seg| self.segments[&seg] == other.segments[&seg])
    }
}

impl std::iter::FromIterator<i64> for IntcodeMem {
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

macro_rules! page_index {
    ($i: expr) => {
        #[allow(clippy::cast_sign_loss, reason = "masked down anyway")]
        {
            ($i & 0x1ff) as usize
        }
    };
}

impl std::ops::Index<i64> for IntcodeMem {
    type Output = i64;
    fn index(&self, i: i64) -> &i64 {
        self.segments
            .get(&(i & !0x1ff))
            .map_or(&0, |s| s.index(page_index!(i)))
    }
}

impl std::ops::IndexMut<i64> for IntcodeMem {
    fn index_mut(&mut self, i: i64) -> &mut i64 {
        self.segments
            .entry(i & !0x1ff)
            .or_insert(Box::new([0; 512]))
            .index_mut(page_index!(i))
    }
}

impl Clone for IntcodeMem {
    fn clone(&self) -> Self {
        // don't copy blank pages
        let segments = self
            .segments
            .iter()
            .filter(|&(&_index, mem)| mem.as_ref() != &[0_i64; 512])
            .map(|(&index, mem)| (index, mem.clone()))
            .collect();
        Self { segments }
    }
}

pub(super) struct IntcodeMemIter {
    segments: BTreeMap<i64, [i64; 512]>,
    current_segment: i64,
    segment_index: usize,
}

impl Iterator for IntcodeMemIter {
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

impl IntoIterator for IntcodeMem {
    type Item = i64;
    type IntoIter = IntcodeMemIter;
    fn into_iter(mut self) -> IntcodeMemIter {
        self.prune();
        IntcodeMemIter {
            segments: self.segments.into_iter().map(|(k, v)| (k, *v)).collect(),
            current_segment: 0,
            segment_index: 0,
        }
    }
}

impl fmt::Debug for IntcodeMem {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut fmtstruct = fmt.debug_map();
        for sn in self.segments.keys().sorted_unstable() {
            if self.segments[sn].as_ref() != &[0; 512] {
                fmtstruct.entry(
                    &format_args!("{{ segment 0x{sn:04x} }}"),
                    &format_args!("{:?}", self.segments[sn]),
                );
            }
        }
        fmtstruct.finish()
    }
}
