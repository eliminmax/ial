// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

#![allow(
    unused_must_use,
    reason = "testing validation function called in constructor"
)]

use super::{BitCounter, EncodedSize, NeededBits};

#[test]
fn encoded_size_test() {
    let encoded_0xff = EncodedSize::from_slice(&[0b1111_1111, 0b0000_0001]);
    assert_eq!(Box::<EncodedSize>::from(0xff_usize).as_ref(), encoded_0xff);
    assert_eq!(
        usize::try_from(encoded_0xff).unwrap(),
        0xff,
        "{encoded_0xff:?}"
    );
    let encoded_usize_max = Box::<EncodedSize>::from(usize::MAX);
    assert_eq!(usize::try_from(&*encoded_usize_max), Ok(usize::MAX));
    let mut v = encoded_usize_max.to_vec();
    if let Some(l) = v.last_mut()
        && *l != 0xff
    {
        let mut shift = 0;
        while *l & (1 << shift) != 0 {
            shift += 1;
        }
        assert!(shift < 7);
        *l |= 1 << shift;
    } else {
        v.push(0b1000_0001);
    }

    let encoded_usize_overflow = EncodedSize::from_boxed_slice(v.into_boxed_slice());
    assert_eq!(
        usize::try_from(encoded_usize_overflow.as_ref()),
        Err(NeededBits(usize::BITS as BitCounter + 1)),
        "{encoded_usize_overflow:?}"
    );

    for power in 1..=4 {
        for base in [2, 7] {
            let base_val = usize::pow(base, power);
            for i in [base_val - 1, base_val, base_val + 1] {
                let expected_bit_width = (usize::BITS - i.leading_zeros()) as BitCounter;
                let expected_byte_width = expected_bit_width.div_ceil(7);
                let encoded = Box::<EncodedSize>::from(i);
                assert_eq!(usize::try_from(&*encoded), Ok(i), "{i}, {encoded:?}");
                assert_eq!(encoded.len() as BitCounter, expected_byte_width);
            }
        }
    }
}

#[test]
#[should_panic = "EncodedSize must not be empty"]
fn empty_encoded_size() {
    EncodedSize::from_slice(&[]);
}

#[test]
#[cfg_attr(
    debug_assertions,
    should_panic = "Invalid final byte for EncodedSize: 0x80 (most significant bit is 1)"
)]
fn invalid_encoded_size_final_byte() {
    EncodedSize::from_slice(&[0x80, 0x80]);
}

#[test]
#[cfg_attr(
    debug_assertions,
    should_panic = "Invalid non-final byte for EncodedSize: 0x7f (most significant bit is 0)"
)]
fn invalid_encoded_size_non_final_byte() {
    EncodedSize::from_slice(&[0x7f, 0x7f]);
}

#[test]
fn encode_into_vec() {
    let mut buf = Vec::new();
    let es = EncodedSize::encode_into_vec(&mut buf, 0xcafe);
    assert_eq!(usize::try_from(es).unwrap(), 0xcafe);
    assert_eq!(&es[..], &[0xfe, 0x95, 0x03]);
}
