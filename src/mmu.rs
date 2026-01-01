// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

/// a virtual memory management unit
pub(super) struct IntcodeMem {
    segments: HashMap<u64, Box<[i64; 512]>>,
}

impl IntcodeMem {
    fn active_segments(&self) -> BTreeSet<u64> {
        self.segments
            .iter()
            .filter_map(|(&k, v)| if v.as_ref() == &[0; 512] { Some(k) } else { None })
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

        let mut chunk = [0; 512];
        let mut i = 0;
        let mut current_segment = 0;
        let mut segments = HashMap::with_capacity(iter.size_hint().0.div_ceil(512));

        for n in iter {
            chunk[i] = n;
            i += 1;
            if i == chunk.len() {
                i = 0;
                segments.insert(current_segment, Box::new(chunk));
                chunk = [0; 512];
                current_segment += 512;
            }
        }
        segments.insert(current_segment, Box::new(chunk));

        Self { segments }
    }
}

impl std::ops::Index<u64> for IntcodeMem {
    type Output = i64;
    fn index(&self, i: u64) -> &i64 {
        self.segments
            .get(&(i & !0x1ff))
            .map(|s| s.index((i & 0x1ff) as usize))
            .unwrap_or(&0)
    }
}

impl std::ops::IndexMut<u64> for IntcodeMem {
    fn index_mut(&mut self, i: u64) -> &mut i64 {
        let segment_index = i as usize & 0x1ff;
        &mut self.segments.entry(i & !0x1ff).or_insert(Box::new([0; 512]))[segment_index]
    }
}

impl Clone for IntcodeMem {
    fn clone(&self) -> Self {
        // don't copy blank pages
        let segments = self
            .segments
            .iter()
            .filter_map(|(&index, mem)| {
                if mem.as_ref() != &[0_i64; 512] {
                    Some((index, mem.clone()))
                } else {
                    None
                }
            })
            .collect();
        Self { segments }
    }
}

pub(super) struct IntcodeMemIter {
    segments: BTreeMap<u64, [i64; 512]>,
    current_segment: u64,
    segment_index: usize,
}

impl Iterator for IntcodeMemIter {
    type Item = i64;
    fn next(&mut self) -> Option<i64> {
        if self.current_segment > self.segments.keys().max().cloned().unwrap_or_default() {
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
        // collect into an ordered set
        for sn in self.segments.keys().collect::<BTreeSet<_>>() {
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
