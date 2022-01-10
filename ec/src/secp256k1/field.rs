/**
 * Copyright (c) 2013 Pieter Wuille
 * Copyleft (c) 2022 nanorust developers
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
**/

use crate::{endian::Endian, error::Error, util::{cmp, reverse32}};
use super::consts::FIELD_MOD_INFO;
use super::modinv::{ModInfo, Signed30};

pub fn verify_bits<
    T: Default + From<u8> + PartialEq + core::fmt::Debug + core::ops::Shr<Output = T>,
>(
    x: T,
    n: T,
) {
    assert_eq!(x >> n, 0u8.into());
}

const fn const_mask(d: [u32; 8]) -> [u32; 10] {
    let [d0, d1, d2, d3, d4, d5, d6, d7] = d;
    [
        d0 & 0x3FFFFFF,
        (d0 >> 26) | ((d1 & 0xfffff) << 6),
        (d1 >> 20) | ((d2 & 0x3fff) << 12),
        (d2 >> 14) | ((d3 & 0xff) << 18),
        (d3 >> 8) | ((d4 & 0x3) << 24),
        (d4 >> 2) & 0x3ffffff,
        (d4 >> 28) | ((d5 & 0x3fffff) << 4),
        (d5 >> 22) | ((d6 & 0xffff) << 10),
        (d6 >> 16) | ((d7 & 0x3ff) << 16),
        d7 >> 10,
    ]
}

// Convert constant array to a FieldElement
pub(crate) const fn const_to_field(d: [u32; 8]) -> FieldElement {
    let (normalized, magnitude) = if cfg!(feature = "verify") {
        (true, 1)
    } else {
        (false, 0)
    };
    let n = const_mask(reverse32(&d));
    FieldElement {
        normalized,
        magnitude,
        n,
    }
}

#[derive(Clone, Copy)]
pub struct FieldElement {
    pub(crate) normalized: bool,
    pub(crate) magnitude: i32,
    pub(crate) n: [u32; 10],
}

impl Default for FieldElement {
    fn default() -> Self {
        Self::new()
    }
}

impl From<[u32; 8]> for FieldElement {
    fn from(d: [u32; 8]) -> Self {
        const_to_field(d)
    }
}

impl FieldElement {
    pub const M: u32 = 0x3ffffff;
    pub const R0: u32 = 0x3d10;
    pub const R1: u32 = 0x400;

    pub fn new() -> Self {
        Self {
            magnitude: 0,
            normalized: true,
            n: [0; 10],
        }
    }

    pub fn normalized(&self) -> bool {
        self.normalized
    }

    pub fn magnitude(&self) -> i32 {
        self.magnitude
    }

    pub fn set_magnitude(&mut self, magnitude: i32) -> Result<(), Error> {
        if magnitude < 0 || magnitude > 32 {
            Err(Error::InvalidMagnitude)
        } else {
            self.magnitude = magnitude;
            Ok(())
        }
    }

    pub fn verify(&self) {
        let m = if self.normalized {
            1
        } else {
            2u64 * self.magnitude as u64
        };
        let mut r = 1;
        r &= (self.n[0] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[1] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[2] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[3] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[4] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[5] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[6] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[7] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[8] <= (0x3ffffffu64 * m) as u32) as u8;
        r &= (self.n[9] <= (0x03fffffu64 * m) as u32) as u8;
        r &= (self.magnitude >= 0) as u8; // useless since not using i32 for magnitude
        r &= (self.magnitude <= 32) as u8;
        if self.normalized {
            r &= (self.magnitude <= 1) as u8;
            if r != 0 && self.n[9] == 0x03fffff {
                let mid = self.n[8]
                    & self.n[7]
                    & self.n[6]
                    & self.n[5]
                    & self.n[4]
                    & self.n[3]
                    & self.n[2];
                if mid == 0x3ffffff {
                    r &= ((self.n[1] + 0x40 + ((self.n[0] + 0x3d1) >> 26)) <= 0x3ffffff) as u8;
                }
            }
        }
        assert_eq!(r, 1);
    }

    pub fn normalize(&mut self) {
        let (mut t0, mut t1, mut t2, mut t3, mut t4, mut t5, mut t6, mut t7, mut t8, mut t9) = (
            self.n[0], self.n[1], self.n[2], self.n[3], self.n[4], self.n[5], self.n[6], self.n[7],
            self.n[8], self.n[9],
        );

        /* Reduce t9 at the start so there will be at most a single carry from the first pass */
        let (mut m, mut x) = (t2, t9 >> 22);
        t9 &= 0x03fffff;

        /* The first pass ensures the magnitude is 1, ... */
        t0 += x * 0x3d1;
        t1 += x << 6;
        t1 += t0 >> 26;
        t0 &= 0x3ffffff;
        t2 += t1 >> 26;
        t1 &= 0x3ffffff;
        t3 += t2 >> 26;
        t2 &= 0x3ffffff;
        t4 += t3 >> 26;
        t3 &= 0x3ffffff;
        m &= t3;
        t5 += t4 >> 26;
        t4 &= 0x3ffffff;
        m &= t4;
        t6 += t5 >> 26;
        t5 &= 0x3ffffff;
        m &= t5;
        t7 += t6 >> 26;
        t6 &= 0x3ffffff;
        m &= t6;
        t8 += t7 >> 26;
        t7 &= 0x3ffffff;
        m &= t7;
        t9 += t8 >> 26;
        t8 &= 0x3ffffff;
        m &= t8;

        /* ... except for a possible carry at bit 22 of t9 (i.e. bit 256 of the field element) */
        assert_eq!(t9 >> 23, 0);

        /* At most a single final reduction is needed; check if the value is >= the field characteristic */
        x = (t9 >> 22)
            | ((t9 == 0x03fffff) as u32
                & (m == 0x3ffffff) as u32
                & ((t1 + 0x40 + ((t0 + 0x3d1) >> 26)) > 0x3ffffff) as u32);

        /* Apply the final reduction (for constant-time behaviour, we do it always) */
        t0 += x * 0x3d1;
        t1 += x << 6;
        t1 += t0 >> 26;
        t0 &= 0x3ffffff;
        t2 += t1 >> 26;
        t1 &= 0x3ffffff;
        t3 += t2 >> 26;
        t2 &= 0x3ffffff;
        t4 += t3 >> 26;
        t3 &= 0x3ffffff;
        t5 += t4 >> 26;
        t4 &= 0x3ffffff;
        t6 += t5 >> 26;
        t5 &= 0x3ffffff;
        t7 += t6 >> 26;
        t6 &= 0x3ffffff;
        t8 += t7 >> 26;
        t7 &= 0x3ffffff;
        t9 += t8 >> 26;
        t8 &= 0x3ffffff;

        /* If t9 didn't carry to bit 22 already, then it should have after any final reduction */
        assert_eq!(t9 >> 22, x);

        /* Mask off the possible multiple of 2^256 from the final reduction */
        t9 &= 0x03fffff;

        self.n[0] = t0;
        self.n[1] = t1;
        self.n[2] = t2;
        self.n[3] = t3;
        self.n[4] = t4;
        self.n[5] = t5;
        self.n[6] = t6;
        self.n[7] = t7;
        self.n[8] = t8;
        self.n[9] = t9;

        if cfg!(feature = "verify") {
            self.magnitude = 1;
            self.normalized = true;
            self.verify();
        }
    }

    pub fn normalize_weak(&mut self) {
        let (mut t0, mut t1, mut t2, mut t3, mut t4, mut t5, mut t6, mut t7, mut t8, mut t9) = (
            self.n[0], self.n[1], self.n[2], self.n[3], self.n[4], self.n[5], self.n[6], self.n[7],
            self.n[8], self.n[9],
        );

        /* Reduce t9 at the start so there will be at most a single carry from the first pass */
        let x = t9 >> 22;
        t9 &= 0x03fffff;

        /* The first pass ensures the magnitude is 1, ... */
        t0 += x * 0x3d1;
        t1 += x << 6;
        t1 += t0 >> 26;
        t0 &= 0x3ffffff;
        t2 += t1 >> 26;
        t1 &= 0x3ffffff;
        t3 += t2 >> 26;
        t2 &= 0x3ffffff;
        t4 += t3 >> 26;
        t3 &= 0x3ffffff;
        t5 += t4 >> 26;
        t4 &= 0x3ffffff;
        t6 += t5 >> 26;
        t5 &= 0x3ffffff;
        t7 += t6 >> 26;
        t6 &= 0x3ffffff;
        t8 += t7 >> 26;
        t7 &= 0x3ffffff;
        t9 += t8 >> 26;
        t8 &= 0x3ffffff;

        /* ... except for a possible carry at bit 22 of t9 (i.e. bit 256 of the field element) */
        assert_eq!(t9 >> 23, 0);

        self.n[0] = t0;
        self.n[1] = t1;
        self.n[2] = t2;
        self.n[3] = t3;
        self.n[4] = t4;
        self.n[5] = t5;
        self.n[6] = t6;
        self.n[7] = t7;
        self.n[8] = t8;
        self.n[9] = t9;

        if cfg!(feature = "verify") {
            self.magnitude = 1;
            self.verify();
        }
    }

    pub fn normalizes_to_zero(&self) -> bool {
        let n = &self.n;
        let (mut t0, mut t1, mut t2, mut t3, mut t4, mut t5, mut t6, mut t7, mut t8, mut t9) =
            (n[0], n[1], n[2], n[3], n[4], n[5], n[6], n[7], n[8], n[9]);

        /* z0 tracks a possible raw value of 0, z1 tracks a possible raw value of P */
        let (mut z0, mut z1, x) = (t0, t0 ^ 0x3d0, t9 >> 22);

        /* Reduce t9 at the start so there will be at most a single carry from the first pass */
        t9 = t9 & 0x3fffff;

        /* The first pass ensures the magnitude is 1, ... */
        t0 += x * 0x3d1;
        t1 += x << 6;
        t1 += t0 >> 26; /*t0 &= 0x3ffffff;*/
        t2 += t1 >> 26;
        t1 &= 0x3ffffff;
        z0 |= t1;
        z1 &= t1 ^ 0x40;
        t3 += t2 >> 26;
        t2 &= 0x3ffffff;
        z0 |= t2;
        z1 &= t2;
        t4 += t3 >> 26;
        t3 &= 0x3ffffff;
        z0 |= t3;
        z1 &= t3;
        t5 += t4 >> 26;
        t4 &= 0x3ffffff;
        z0 |= t4;
        z1 &= t4;
        t6 += t5 >> 26;
        t5 &= 0x3ffffff;
        z0 |= t5;
        z1 &= t5;
        t7 += t6 >> 26;
        t6 &= 0x3ffffff;
        z0 |= t6;
        z1 &= t6;
        t8 += t7 >> 26;
        t7 &= 0x3ffffff;
        z0 |= t7;
        z1 &= t7;
        t9 += t8 >> 26;
        t8 &= 0x3ffffff;
        z0 |= t8;
        z1 &= t8;
        z0 = z0 | t9;
        z1 = z1 & (t9 ^ 0x3c00000);

        /* ... except for a possible carry at bit 22 of t9 (i.e. bit 256 of the field element) */
        assert_eq!(t9 >> 23, 0);

        return (z0 == 0) || (z1 == 0x3ffffff);
    }

    #[inline(always)]
    pub fn set_int(&mut self, a: u32) {
        self.n[0] = a;
        self.n[1..].swap_with_slice(&mut [0u32; 9]);
        self.magnitude = 1;
        self.normalized = true;
        self.verify();
    }

    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        if cfg!(feature = "verify") {
            assert!(self.normalized);
            self.verify();
        }
        let t = &self.n;
        (t[0] | t[1] | t[2] | t[3] | t[4] | t[5] | t[6] | t[7] | t[8] | t[9]) == 0
    }

    #[inline(always)]
    pub fn is_odd(&self) -> bool {
        if cfg!(feature = "verify") {
            assert!(self.normalized);
            self.verify();
        }
        self.n[0] & 1 != 0
    }

    #[inline(always)]
    pub fn clear(&mut self) {
        if cfg!(feature = "verify") {
            self.magnitude = 0;
            self.normalized = true;
        }
        self.n.swap_with_slice(&mut [0u32; 10]);
    }

    #[inline(always)]
    pub fn cmp(&self, oth: &Self) -> i8 {
        if cfg!(feature = "verify") {
            assert!(self.normalized);
            assert!(oth.normalized);
            self.verify();
            oth.verify();
        }
        cmp(&self.n, &oth.n, Endian::Little)
    }

    pub fn equal(&self, oth: &Self) -> bool {
        self.cmp(oth) == 0
    }

    #[inline(always)]
    pub fn set_b32(&mut self, a: &[u8; 32]) -> u32 {
        self.n[0] = a[31] as u32
            | ((a[30] as u32) << 8)
            | ((a[29] as u32) << 16)
            | (((a[28] & 0x3) as u32) << 24);
        self.n[1] = ((a[28] >> 2) & 0x3f) as u32
            | ((a[27] as u32) << 6)
            | ((a[26] as u32) << 14)
            | (((a[25] & 0xf) as u32) << 22);
        self.n[2] = ((a[25] >> 4) as u32 & 0xf)
            | ((a[24] as u32) << 4)
            | ((a[23] as u32) << 12)
            | (((a[22] & 0x3f) as u32) << 20);
        self.n[3] = ((a[22] >> 6) as u32 & 0x3)
            | ((a[21] as u32) << 2)
            | ((a[20] as u32) << 10)
            | ((a[19] as u32) << 18);
        self.n[4] = a[18] as u32
            | ((a[17] as u32) << 8)
            | ((a[16] as u32) << 16)
            | (((a[15] & 0x3) as u32) << 24);
        self.n[5] = ((a[15] >> 2) & 0x3f) as u32
            | ((a[14] as u32) << 6)
            | ((a[13] as u32) << 14)
            | (((a[12] & 0xf) as u32) << 22);
        self.n[6] = ((a[12] >> 4) & 0xf) as u32
            | ((a[11] as u32) << 4)
            | ((a[10] as u32) << 12)
            | (((a[9] & 0x3f) as u32) << 20);
        self.n[7] = ((a[9] >> 6) & 0x3) as u32
            | ((a[8] as u32) << 2)
            | ((a[7] as u32) << 10)
            | ((a[6] as u32) << 18);
        self.n[8] = a[5] as u32
            | ((a[4] as u32) << 8)
            | ((a[3] as u32) << 16)
            | (((a[2] & 0x3) as u32) << 24);
        self.n[9] = ((a[2] >> 2) & 0x3f) as u32 | ((a[1] as u32) << 6) | ((a[0] as u32) << 14);

        let ret = !((self.n[9] == 0x3fffff) as u32
            & ((self.n[8] & self.n[7] & self.n[6] & self.n[5] & self.n[4] & self.n[3] & self.n[2])
                == 0x3ffffff) as u32
            & ((self.n[1] + 0x40 + ((self.n[0] + 0x3d1) >> 26)) > 0x3ffffff) as u32);
        if cfg!(feature = "verify") {
            self.magnitude = 1;
            if ret != 0 {
                self.normalized = true;
                self.verify();
            } else {
                self.normalized = false;
            }
        }
        ret
    }

    /** Convert a field element to a 32-byte big endian value. Requires the input to be normalized */
    #[inline(always)]
    pub fn get_b32(&self) -> [u8; 32] {
        if cfg!(feature = "verify") {
            assert!(self.normalized);
            self.verify();
        }
        [
            ((self.n[9] >> 14) & 0xff) as u8,
            ((self.n[9] >> 6) & 0xff) as u8,
            (((self.n[9] & 0x3F) << 2) | ((self.n[8] >> 24) & 0x3)) as u8,
            ((self.n[8] >> 16) & 0xff) as u8,
            ((self.n[8] >> 8) & 0xff) as u8,
            (self.n[8] & 0xff) as u8,
            ((self.n[7] >> 18) & 0xff) as u8,
            ((self.n[7] >> 10) & 0xff) as u8,
            ((self.n[7] >> 2) & 0xff) as u8,
            (((self.n[7] & 0x3) << 6) | ((self.n[6] >> 20) & 0x3f)) as u8,
            ((self.n[6] >> 12) & 0xff) as u8,
            ((self.n[6] >> 4) & 0xff) as u8,
            (((self.n[6] & 0xf) << 4) | ((self.n[5] >> 22) & 0xf)) as u8,
            ((self.n[5] >> 14) & 0xff) as u8,
            ((self.n[5] >> 6) & 0xff) as u8,
            (((self.n[5] & 0x3f) << 2) | ((self.n[4] >> 24) & 0x3)) as u8,
            ((self.n[4] >> 16) & 0xff) as u8,
            ((self.n[4] >> 8) & 0xff) as u8,
            (self.n[4] & 0xff) as u8,
            ((self.n[3] >> 18) & 0xff) as u8,
            ((self.n[3] >> 10) & 0xff) as u8,
            ((self.n[3] >> 2) & 0xff) as u8,
            (((self.n[3] & 0x3) << 6) | ((self.n[2] >> 20) & 0x3f)) as u8,
            ((self.n[2] >> 12) & 0xff) as u8,
            ((self.n[2] >> 4) & 0xff) as u8,
            (((self.n[2] & 0xf) << 4) | ((self.n[1] >> 22) & 0xf)) as u8,
            ((self.n[1] >> 14) & 0xff) as u8,
            ((self.n[1] >> 6) & 0xff) as u8,
            (((self.n[1] & 0x3f) << 2) | ((self.n[0] >> 24) & 0x3)) as u8,
            ((self.n[0] >> 16) & 0xff) as u8,
            ((self.n[0] >> 8) & 0xff) as u8,
            (self.n[0] & 0xff) as u8,
        ]
    }

    #[inline(always)]
    pub fn negate(&self) -> Self {
        let mut r = self.clone();
        r.negate_assign();
        r
    }

    #[inline(always)]
    pub fn negate_assign(&mut self) {
        if cfg!(feature = "verify") {
            self.verify();
        }
        let m = self.magnitude as u32 + 1;
        let mask0 = (0x3fffc2fu32 * 2).saturating_mul(m);
        let mask1 = (0x3ffffbfu32 * 2).saturating_mul(m);
        let mask2 = (0x3ffffffu32 * 2).saturating_mul(m);
        let mask3 = (0x03fffffu32 * 2).saturating_mul(m);
        let mut r = Self {
            normalized: true,
            magnitude: 0,
            n: [
                mask0 - self.n[0],
                mask1 - self.n[1],
                mask2 - self.n[2],
                mask2 - self.n[3],
                mask2 - self.n[4],
                mask2 - self.n[5],
                mask2 - self.n[6],
                mask2 - self.n[7],
                mask2 - self.n[8],
                mask3 - self.n[9],
            ],
        };
        if cfg!(feature = "verify") {
            r.magnitude = m as i32;
            r.normalized = false;
            r.verify();
        }
        *self = r;
    }

    #[inline(always)]
    pub fn mul_int(&self, a: u32) -> Self {
        let mut r = self.clone();
        r.mul_int_assign(a);
        r
    }

    #[inline(always)]
    pub fn mul_int_assign(&mut self, a: u32) {
        let mut r = self.clone();
        r.n[0] = ((r.n[0] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[1] = ((r.n[1] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[2] = ((r.n[2] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[3] = ((r.n[3] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[4] = ((r.n[4] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[5] = ((r.n[5] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[6] = ((r.n[6] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[7] = ((r.n[7] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[8] = ((r.n[8] as u64 * a as u64) & 0xffff_ffff) as u32;
        r.n[9] = ((r.n[9] as u64 * a as u64) & 0xffff_ffff) as u32;
        if cfg!(feature = "verify") {
            r.magnitude *= a as i32;
            r.normalized = false;
            r.verify();
        }
        *self = r;
    }

    #[inline(always)]
    pub fn add_assign(&mut self, oth: &Self) {
        if cfg!(feature = "verify") {
            oth.verify();
        }
        self.n[0] += oth.n[0];
        self.n[1] += oth.n[1];
        self.n[2] += oth.n[2];
        self.n[3] += oth.n[3];
        self.n[4] += oth.n[4];
        self.n[5] += oth.n[5];
        self.n[6] += oth.n[6];
        self.n[7] += oth.n[7];
        self.n[8] += oth.n[8];
        self.n[9] += oth.n[9];
        if cfg!(feature = "verify") {
            self.magnitude += oth.magnitude;
            self.normalized = false;
            self.verify();
        }
    }

    #[inline(always)]
    pub fn add(&self, oth: &Self) -> Self {
        let mut ret = self.clone();
        ret.add_assign(oth);
        ret
    }

    #[inline(always)]
    fn mul_inner(r: &mut [u32], a: &[u32], b: &[u32]) {
        verify_bits(a[0], 30);
        verify_bits(a[1], 30);
        verify_bits(a[2], 30);
        verify_bits(a[3], 30);
        verify_bits(a[4], 30);
        verify_bits(a[5], 30);
        verify_bits(a[6], 30);
        verify_bits(a[7], 30);
        verify_bits(a[8], 30);
        verify_bits(a[9], 26);
        verify_bits(b[0], 30);
        verify_bits(b[1], 30);
        verify_bits(b[2], 30);
        verify_bits(b[3], 30);
        verify_bits(b[4], 30);
        verify_bits(b[5], 30);
        verify_bits(b[6], 30);
        verify_bits(b[7], 30);
        verify_bits(b[8], 30);
        verify_bits(b[9], 26);

        // /** [... a b c] is a shorthand for ... + a<<52 + b<<26 + c<<0 mod n.
        //  *  for 0 <= x <= 9, px is a shorthand for sum(a[i]*b[x-i], i=0..x).
        //  *  for 9 <= x <= 18, px is a shorthand for sum(a[i]*b[x-i], i=(x-9)..9)
        //  *  Note that [x 0 0 0 0 0 0 0 0 0 0] = [x*R1 x*R0].
        //  */
        let mut d = a[0] as u64 * b[9] as u64
            + a[1] as u64 * b[8] as u64
            + a[2] as u64 * b[7] as u64
            + a[3] as u64 * b[6] as u64
            + a[4] as u64 * b[5] as u64
            + a[5] as u64 * b[4] as u64
            + a[6] as u64 * b[3] as u64
            + a[7] as u64 * b[2] as u64
            + a[8] as u64 * b[1] as u64
            + a[9] as u64 * b[0] as u64;
        /* verify_bits(d, 64); */
        /* [d 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */
        let t9 = d as u32 & Self::M;
        d >>= 26;
        verify_bits(t9, 26);
        verify_bits(d, 38);
        /* [d t9 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */

        let mut c = a[0] as u64 * b[0] as u64;
        verify_bits(c, 60);
        /* [d t9 0 0 0 0 0 0 0 0 c] = [p9 0 0 0 0 0 0 0 0 p0] */
        d += a[1] as u64 * b[9] as u64
            + a[2] as u64 * b[8] as u64
            + a[3] as u64 * b[7] as u64
            + a[4] as u64 * b[6] as u64
            + a[5] as u64 * b[5] as u64
            + a[6] as u64 * b[4] as u64
            + a[7] as u64 * b[3] as u64
            + a[8] as u64 * b[2] as u64
            + a[9] as u64 * b[1] as u64;
        verify_bits(d, 63);
        /* [d t9 0 0 0 0 0 0 0 0 c] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
        let u0 = d & Self::M as u64;
        d >>= 26;
        c += u0 * Self::R0 as u64;
        verify_bits(u0, 26);
        verify_bits(d, 37);
        verify_bits(c, 61);
        /* [d u0 t9 0 0 0 0 0 0 0 0 c-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
        let t0 = c as u32 & Self::M;
        c >>= 26;
        c += u0 * Self::R1 as u64;
        verify_bits(t0, 26);
        verify_bits(c, 37);
        /* [d u0 t9 0 0 0 0 0 0 0 c-u0*R1 t0-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
        /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */

        c += a[0] as u64 * b[1] as u64 + a[1] as u64 * b[0] as u64;
        verify_bits(c, 62);
        /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 p1 p0] */
        d += a[2] as u64 * b[9] as u64
            + a[3] as u64 * b[8] as u64
            + a[4] as u64 * b[7] as u64
            + a[5] as u64 * b[6] as u64
            + a[6] as u64 * b[5] as u64
            + a[7] as u64 * b[4] as u64
            + a[8] as u64 * b[3] as u64
            + a[9] as u64 * b[2] as u64;
        verify_bits(d, 63);
        /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
        let u1 = d & Self::M as u64;
        d >>= 26;
        c += u1 * Self::R0 as u64;
        verify_bits(u1, 26);
        verify_bits(d, 37);
        verify_bits(c, 63);
        /* [d u1 0 t9 0 0 0 0 0 0 0 c-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
        let t1 = c as u32 & Self::M;
        c >>= 26;
        c += u1 * Self::R1 as u64;
        verify_bits(t1, 26);
        verify_bits(c, 38);
        /* [d u1 0 t9 0 0 0 0 0 0 c-u1*R1 t1-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
        /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */

        c += a[0] as u64 * b[2] as u64 + a[1] as u64 * b[1] as u64 + a[2] as u64 * b[0] as u64;
        verify_bits(c, 62);
        /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
        d += a[3] as u64 * b[9] as u64
            + a[4] as u64 * b[8] as u64
            + a[5] as u64 * b[7] as u64
            + a[6] as u64 * b[6] as u64
            + a[7] as u64 * b[5] as u64
            + a[8] as u64 * b[4] as u64
            + a[9] as u64 * b[3] as u64;
        verify_bits(d, 63);
        /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
        let u2 = d & Self::M as u64;
        d >>= 26;
        c += u2 * Self::R0 as u64;
        verify_bits(u2, 26);
        verify_bits(d, 37);
        verify_bits(c, 63);
        /* [d u2 0 0 t9 0 0 0 0 0 0 c-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
        let t2 = c as u32 & Self::M;
        c >>= 26;
        c += u2 * Self::R1 as u64;
        verify_bits(t2, 26);
        verify_bits(c, 38);
        /* [d u2 0 0 t9 0 0 0 0 0 c-u2*R1 t2-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
        /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */

        c += a[0] as u64 * b[3] as u64
            + a[1] as u64 * b[2] as u64
            + a[2] as u64 * b[1] as u64
            + a[3] as u64 * b[0] as u64;
        verify_bits(c, 63);
        /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
        d += a[4] as u64 * b[9] as u64
            + a[5] as u64 * b[8] as u64
            + a[6] as u64 * b[7] as u64
            + a[7] as u64 * b[6] as u64
            + a[8] as u64 * b[5] as u64
            + a[9] as u64 * b[4] as u64;
        verify_bits(d, 63);
        /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
        let u3 = d & Self::M as u64;
        d >>= 26;
        c += u3 * Self::R0 as u64;
        verify_bits(u3, 26);
        verify_bits(d, 37);
        /* verify_bits(c, 64); */
        /* [d u3 0 0 0 t9 0 0 0 0 0 c-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
        let t3 = c as u32 & Self::M;
        c >>= 26;
        c += u3 * Self::R1 as u64;
        verify_bits(t3, 26);
        verify_bits(c, 39);
        /* [d u3 0 0 0 t9 0 0 0 0 c-u3*R1 t3-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
        /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */

        c += a[0] as u64 * b[4] as u64
            + a[1] as u64 * b[3] as u64
            + a[2] as u64 * b[2] as u64
            + a[3] as u64 * b[1] as u64
            + a[4] as u64 * b[0] as u64;
        verify_bits(c, 63);
        /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
        d += a[5] as u64 * b[9] as u64
            + a[6] as u64 * b[8] as u64
            + a[7] as u64 * b[7] as u64
            + a[8] as u64 * b[6] as u64
            + a[9] as u64 * b[5] as u64;
        verify_bits(d, 62);
        /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
        let u4 = d & Self::M as u64;
        d >>= 26;
        c += u4 * Self::R0 as u64;
        verify_bits(u4, 26);
        verify_bits(d, 36);
        /* verify_bits(c, 64); */
        /* [d u4 0 0 0 0 t9 0 0 0 0 c-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
        let t4 = c as u32 & Self::M;
        c >>= 26;
        c += u4 * Self::R1 as u64;
        verify_bits(t4, 26);
        verify_bits(c, 39);
        /* [d u4 0 0 0 0 t9 0 0 0 c-u4*R1 t4-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */

        c += a[0] as u64 * b[5] as u64
            + a[1] as u64 * b[4] as u64
            + a[2] as u64 * b[3] as u64
            + a[3] as u64 * b[2] as u64
            + a[4] as u64 * b[1] as u64
            + a[5] as u64 * b[0] as u64;
        verify_bits(c, 63);
        /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
        d += a[6] as u64 * b[9] as u64
            + a[7] as u64 * b[8] as u64
            + a[8] as u64 * b[7] as u64
            + a[9] as u64 * b[6] as u64;
        verify_bits(d, 62);
        /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
        let u5 = d & Self::M as u64;
        d >>= 26;
        c += u5 * Self::R0 as u64;
        verify_bits(u5, 26);
        verify_bits(d, 36);
        /* verify_bits(c, 64); */
        /* [d u5 0 0 0 0 0 t9 0 0 0 c-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
        let t5 = c as u32 & Self::M;
        c >>= 26;
        c += u5 * Self::R1 as u64;
        verify_bits(t5, 26);
        verify_bits(c, 39);
        /* [d u5 0 0 0 0 0 t9 0 0 c-u5*R1 t5-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */

        c += a[0] as u64 * b[6] as u64
            + a[1] as u64 * b[5] as u64
            + a[2] as u64 * b[4] as u64
            + a[3] as u64 * b[3] as u64
            + a[4] as u64 * b[2] as u64
            + a[5] as u64 * b[1] as u64
            + a[6] as u64 * b[0] as u64;
        verify_bits(c, 63);
        /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
        d += a[7] as u64 * b[9] as u64 + a[8] as u64 * b[8] as u64 + a[9] as u64 * b[7] as u64;
        verify_bits(d, 61);
        /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
        let u6 = d & Self::M as u64;
        d >>= 26;
        c += u6 * Self::R0 as u64;
        verify_bits(u6, 26);
        verify_bits(d, 35);
        /* verify_bits(c, 64); */
        /* [d u6 0 0 0 0 0 0 t9 0 0 c-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
        let t6 = c as u32 & Self::M;
        c >>= 26;
        c += u6 * Self::R1 as u64;
        verify_bits(t6, 26);
        verify_bits(c, 39);
        /* [d u6 0 0 0 0 0 0 t9 0 c-u6*R1 t6-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */

        c += a[0] as u64 * b[7] as u64
            + a[1] as u64 * b[6] as u64
            + a[2] as u64 * b[5] as u64
            + a[3] as u64 * b[4] as u64
            + a[4] as u64 * b[3] as u64
            + a[5] as u64 * b[2] as u64
            + a[6] as u64 * b[1] as u64
            + a[7] as u64 * b[0] as u64;
        /* verify_bits(c, 64); */
        assert!(c <= 0x8000007C00000007);
        /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
        d += a[8] as u64 * b[9] as u64 + a[9] as u64 * b[8] as u64;
        verify_bits(d, 58);
        /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
        let u7 = d & Self::M as u64;
        d >>= 26;
        c += u7 * Self::R0 as u64;
        verify_bits(u7, 26);
        verify_bits(d, 32);
        /* verify_bits(c, 64); */
        assert!(c <= 0x800001703FFFC2F7);
        /* [d u7 0 0 0 0 0 0 0 t9 0 c-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
        let t7 = c as u32 & Self::M;
        c >>= 26;
        c += u7 * Self::R1 as u64;
        verify_bits(t7, 26);
        verify_bits(c, 38);
        /* [d u7 0 0 0 0 0 0 0 t9 c-u7*R1 t7-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */

        c += a[0] as u64 * b[8] as u64
            + a[1] as u64 * b[7] as u64
            + a[2] as u64 * b[6] as u64
            + a[3] as u64 * b[5] as u64
            + a[4] as u64 * b[4] as u64
            + a[5] as u64 * b[3] as u64
            + a[6] as u64 * b[2] as u64
            + a[7] as u64 * b[1] as u64
            + a[8] as u64 * b[0] as u64;
        /* verify_bits(c, 64); */
        assert!(c <= 0x9000007B80000008);
        /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        d += a[9] as u64 * b[9] as u64;
        verify_bits(d, 57);
        /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        let _u8 = d & Self::M as u64;
        d >>= 26;
        c += _u8 * Self::R0 as u64;
        verify_bits(_u8, 26);
        verify_bits(d, 31);
        /* verify_bits(c, 64); */
        assert!(c <= 0x9000016FBFFFC2F8);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

        r[3] = t3;
        verify_bits(r[3], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        r[4] = t4;
        verify_bits(r[4], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        r[5] = t5;
        verify_bits(r[5], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        r[6] = t6;
        verify_bits(r[6], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        r[7] = t7;
        verify_bits(r[7], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

        r[8] = c as u32 & Self::M;
        c >>= 26;
        c += _u8 * Self::R1 as u64;
        verify_bits(r[8], 26);
        verify_bits(c, 39);
        /* [d u8 0 0 0 0 0 0 0 0 t9+c-u8*R1 r8-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 0 0 0 t9+c r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        c += d * Self::R0 as u64 + t9 as u64;
        verify_bits(c, 45);
        /* [d 0 0 0 0 0 0 0 0 0 c-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        r[9] = c as u32 & (Self::M >> 4);
        c >>= 22;
        c += d * (Self::R1 << 4) as u64;
        verify_bits(r[9], 22);
        verify_bits(c, 46);
        /* [d 0 0 0 0 0 0 0 0 r9+((c-d*R1<<4)<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 0 -d*R1 r9+(c<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

        d = c * (Self::R0 >> 4) as u64 + t0 as u64;
        verify_bits(d, 56);
        /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 d-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        r[0] = d as u32 & Self::M;
        d >>= 26;
        verify_bits(r[0], 26);
        verify_bits(d, 30);
        /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1+d r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        d += c * (Self::R1 >> 4) as u64 + t1 as u64;
        verify_bits(d, 53);
        assert!(d <= 0x10000003FFFFBF);
        /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 d-c*R1>>4 r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [r9 r8 r7 r6 r5 r4 r3 t2 d r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        r[1] = d as u32 & Self::M;
        d >>= 26;
        verify_bits(r[1], 26);
        verify_bits(d, 27);
        assert!(d <= 0x4000000);
        /* [r9 r8 r7 r6 r5 r4 r3 t2+d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        d += t2 as u64;
        verify_bits(d, 27);
        /* [r9 r8 r7 r6 r5 r4 r3 d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        r[2] = d as u32;
        verify_bits(r[2], 27);
        /* [r9 r8 r7 r6 r5 r4 r3 r2 r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    }

    #[inline(always)]
    fn sqr_inner(&mut self) {
        let a = &self.n;

        verify_bits(a[0], 30);
        verify_bits(a[1], 30);
        verify_bits(a[2], 30);
        verify_bits(a[3], 30);
        verify_bits(a[4], 30);
        verify_bits(a[5], 30);
        verify_bits(a[6], 30);
        verify_bits(a[7], 30);
        verify_bits(a[8], 30);
        verify_bits(a[9], 26);

        // /** [... a b c] is a shorthand for ... + a<<52 + b<<26 + c<<0 mod n.
        //  *  px is a shorthand for sum(a[i]*a[x-i], i=0..x).
        //  *  Note that [x 0 0 0 0 0 0 0 0 0 0] = [x*R1 x*R0].
        //  */
        let mut d = (a[0] as u64 * 2) * a[9] as u64
            + (a[1] as u64 * 2) * a[8] as u64
            + (a[2] as u64 * 2) * a[7] as u64
            + (a[3] as u64 * 2) * a[6] as u64
            + (a[4] as u64 * 2) * a[5] as u64;
        /* verify_bits(d, 64); */
        /* [d 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */
        let t9 = d as u32 & Self::M;
        d >>= 26;
        verify_bits(t9, 26);
        verify_bits(d, 38);
        /* [d t9 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */

        let mut c = a[0] as u64 * a[0] as u64;
        verify_bits(c, 60);
        /* [d t9 0 0 0 0 0 0 0 0 c] = [p9 0 0 0 0 0 0 0 0 p0] */
        d += (a[1] as u64 * 2) * a[9] as u64
            + (a[2] as u64 * 2) * a[8] as u64
            + (a[3] as u64 * 2) * a[7] as u64
            + (a[4] as u64 * 2) * a[6] as u64
            + a[5] as u64 * a[5] as u64;
        verify_bits(d, 63);
        /* [d t9 0 0 0 0 0 0 0 0 c] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
        let u0 = d & Self::M as u64;
        d >>= 26;
        c += u0 * Self::R0 as u64;
        verify_bits(u0, 26);
        verify_bits(d, 37);
        verify_bits(c, 61);
        /* [d u0 t9 0 0 0 0 0 0 0 0 c-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
        let t0 = c as u32 & Self::M;
        c >>= 26;
        c += u0 * Self::R1 as u64;
        verify_bits(t0, 26);
        verify_bits(c, 37);
        /* [d u0 t9 0 0 0 0 0 0 0 c-u0*R1 t0-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
        /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */

        c += (a[0] as u64 * 2) * a[1] as u64;
        verify_bits(c, 62);
        /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 p1 p0] */
        d += (a[2] as u64 * 2) * a[9] as u64
            + (a[3] as u64 * 2) * a[8] as u64
            + (a[4] as u64 * 2) * a[7] as u64
            + (a[5] as u64 * 2) * a[6] as u64;
        verify_bits(d, 63);
        /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
        let u1 = d & Self::M as u64;
        d >>= 26;
        c += u1 * Self::R0 as u64;
        verify_bits(u1, 26);
        verify_bits(d, 37);
        verify_bits(c, 63);
        /* [d u1 0 t9 0 0 0 0 0 0 0 c-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
        let t1 = c as u32 & Self::M;
        c >>= 26;
        c += u1 * Self::R1 as u64;
        verify_bits(t1, 26);
        verify_bits(c, 38);
        /* [d u1 0 t9 0 0 0 0 0 0 c-u1*R1 t1-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
        /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */

        c += (a[0] as u64 * 2) * a[2] as u64 + a[1] as u64 * a[1] as u64;
        verify_bits(c, 62);
        /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
        d += (a[3] as u64 * 2) * a[9] as u64
            + (a[4] as u64 * 2) * a[8] as u64
            + (a[5] as u64 * 2) * a[7] as u64
            + a[6] as u64 * a[6] as u64;
        verify_bits(d, 63);
        /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
        let u2 = d & Self::M as u64;
        d >>= 26;
        c += u2 * Self::R0 as u64;
        verify_bits(u2, 26);
        verify_bits(d, 37);
        verify_bits(c, 63);
        /* [d u2 0 0 t9 0 0 0 0 0 0 c-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
        let t2 = c as u32 & Self::M;
        c >>= 26;
        c += u2 * Self::R1 as u64;
        verify_bits(t2, 26);
        verify_bits(c, 38);
        /* [d u2 0 0 t9 0 0 0 0 0 c-u2*R1 t2-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
        /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */

        c += (a[0] as u64 * 2) * a[3] as u64 + (a[1] as u64 * 2) * a[2] as u64;
        verify_bits(c, 63);
        /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
        d += (a[4] as u64 * 2) * a[9] as u64
            + (a[5] as u64 * 2) * a[8] as u64
            + (a[6] as u64 * 2) * a[7] as u64;
        verify_bits(d, 63);
        /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
        let u3 = d & Self::M as u64;
        d >>= 26;
        c += u3 * Self::R0 as u64;
        verify_bits(u3, 26);
        verify_bits(d, 37);
        /* verify_bits(c, 64); */
        /* [d u3 0 0 0 t9 0 0 0 0 0 c-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
        let t3 = c as u32 & Self::M;
        c >>= 26;
        c += u3 * Self::R1 as u64;
        verify_bits(t3, 26);
        verify_bits(c, 39);
        /* [d u3 0 0 0 t9 0 0 0 0 c-u3*R1 t3-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
        /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */

        c += (a[0] as u64 * 2) * a[4] as u64
            + (a[1] as u64 * 2) * a[3] as u64
            + a[2] as u64 * a[2] as u64;
        verify_bits(c, 63);
        /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
        d += (a[5] as u64 * 2) * a[9] as u64
            + (a[6] as u64 * 2) * a[8] as u64
            + a[7] as u64 * a[7] as u64;
        verify_bits(d, 62);
        /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
        let u4 = d & Self::M as u64;
        d >>= 26;
        c += u4 * Self::R0 as u64;
        verify_bits(u4, 26);
        verify_bits(d, 36);
        /* verify_bits(c, 64); */
        /* [d u4 0 0 0 0 t9 0 0 0 0 c-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
        let t4 = c as u32 & Self::M;
        c >>= 26;
        c += u4 * Self::R1 as u64;
        verify_bits(t4, 26);
        verify_bits(c, 39);
        /* [d u4 0 0 0 0 t9 0 0 0 c-u4*R1 t4-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */

        c += (a[0] as u64 * 2) * a[5] as u64
            + (a[1] as u64 * 2) * a[4] as u64
            + (a[2] as u64 * 2) * a[3] as u64;
        verify_bits(c, 63);
        /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
        d += (a[6] as u64 * 2) * a[9] as u64 + (a[7] as u64 * 2) * a[8] as u64;
        verify_bits(d, 62);
        /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
        let u5 = d & Self::M as u64;
        d >>= 26;
        c += u5 * Self::R0 as u64;
        verify_bits(u5, 26);
        verify_bits(d, 36);
        /* verify_bits(c, 64); */
        /* [d u5 0 0 0 0 0 t9 0 0 0 c-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
        let t5 = c as u32 & Self::M;
        c >>= 26;
        c += u5 * Self::R1 as u64;
        verify_bits(t5, 26);
        verify_bits(c, 39);
        /* [d u5 0 0 0 0 0 t9 0 0 c-u5*R1 t5-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */

        c += (a[0] as u64 * 2) * a[6] as u64
            + (a[1] as u64 * 2) * a[5] as u64
            + (a[2] as u64 * 2) * a[4] as u64
            + a[3] as u64 * a[3] as u64;
        verify_bits(c, 63);
        /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
        d += (a[7] as u64 * 2) * a[9] as u64 + a[8] as u64 * a[8] as u64;
        verify_bits(d, 61);
        /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
        let u6 = d & Self::M as u64;
        d >>= 26;
        c += u6 * Self::R0 as u64;
        verify_bits(u6, 26);
        verify_bits(d, 35);
        /* verify_bits(c, 64); */
        /* [d u6 0 0 0 0 0 0 t9 0 0 c-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
        let t6 = c as u32 & Self::M;
        c >>= 26;
        c += u6 * Self::R1 as u64;
        verify_bits(t6, 26);
        verify_bits(c, 39);
        /* [d u6 0 0 0 0 0 0 t9 0 c-u6*R1 t6-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */

        c += (a[0] as u64 * 2) * a[7] as u64
            + (a[1] as u64 * 2) * a[6] as u64
            + (a[2] as u64 * 2) * a[5] as u64
            + (a[3] as u64 * 2) * a[4] as u64;
        /* verify_bits(c, 64); */
        assert!(c <= 0x8000007C00000007);
        /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
        d += (a[8] as u64 * 2) * a[9] as u64;
        verify_bits(d, 58);
        /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
        let u7 = d & Self::M as u64;
        d >>= 26;
        c += u7 * Self::R0 as u64;
        verify_bits(u7, 26);
        verify_bits(d, 32);
        /* verify_bits(c, 64); */
        assert!(c <= 0x800001703FFFC2F7);
        /* [d u7 0 0 0 0 0 0 0 t9 0 c-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
        let t7 = c as u32 & Self::M;
        c >>= 26;
        c += u7 * Self::R1 as u64;
        verify_bits(t7, 26);
        verify_bits(c, 38);
        /* [d u7 0 0 0 0 0 0 0 t9 c-u7*R1 t7-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */

        c += (a[0] as u64 * 2) * a[8] as u64
            + (a[1] as u64 * 2) * a[7] as u64
            + (a[2] as u64 * 2) * a[6] as u64
            + (a[3] as u64 * 2) * a[5] as u64
            + a[4] as u64 * a[4] as u64;
        /* verify_bits(c, 64); */
        assert!(c <= 0x9000007B80000008);
        /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        d += a[9] as u64 * a[9] as u64;
        verify_bits(d, 57);
        /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        let _u8 = d & Self::M as u64;
        d >>= 26;
        c += _u8 * Self::R0 as u64;
        verify_bits(_u8, 26);
        verify_bits(d, 31);
        /* verify_bits(c, 64); */
        assert!(c <= 0x9000016FBFFFC2F8);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

        self.n[3] = t3;
        verify_bits(self.n[3], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        self.n[4] = t4;
        verify_bits(self.n[4], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        self.n[5] = t5;
        verify_bits(self.n[5], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        self.n[6] = t6;
        verify_bits(self.n[6], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        self.n[7] = t7;
        verify_bits(self.n[7], 26);
        /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

        self.n[8] = c as u32 & Self::M;
        c >>= 26;
        c += _u8 * Self::R1 as u64;
        verify_bits(self.n[8], 26);
        verify_bits(c, 39);
        /* [d u8 0 0 0 0 0 0 0 0 t9+c-u8*R1 r8-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 0 0 0 t9+c r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        c += d * Self::R0 as u64 + t9 as u64;
        verify_bits(c, 45);
        /* [d 0 0 0 0 0 0 0 0 0 c-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        self.n[9] = c as u32 & (Self::M >> 4);
        c >>= 22;
        c += d * (Self::R1 << 4) as u64;
        verify_bits(self.n[9], 22);
        verify_bits(c, 46);
        /* [d 0 0 0 0 0 0 0 0 r9+((c-d*R1<<4)<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [d 0 0 0 0 0 0 0 -d*R1 r9+(c<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

        d = c * (Self::R0 >> 4) as u64 + t0 as u64;
        verify_bits(d, 56);
        /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 d-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        self.n[0] = d as u32 & Self::M;
        d >>= 26;
        verify_bits(self.n[0], 26);
        verify_bits(d, 30);
        /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1+d r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        d += c * (Self::R1 >> 4) as u64 + t1 as u64;
        verify_bits(d, 53);
        assert!(d <= 0x10000003FFFFBF);
        /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 d-c*R1>>4 r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        /* [r9 r8 r7 r6 r5 r4 r3 t2 d r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        self.n[1] = d as u32 & Self::M;
        d >>= 26;
        verify_bits(self.n[1], 26);
        verify_bits(d, 27);
        assert!(d <= 0x4000000);
        /* [r9 r8 r7 r6 r5 r4 r3 t2+d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        d += t2 as u64;
        verify_bits(d, 27);
        /* [r9 r8 r7 r6 r5 r4 r3 d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
        self.n[2] = d as u32;
        verify_bits(self.n[2], 27);
        /* [r9 r8 r7 r6 r5 r4 r3 r2 r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    }

    pub fn mul(&self, oth: &Self) -> Self {
        let mut r = self.clone();
        r.mul_assign(oth);
        r
    }

    pub fn mul_assign(&mut self, oth: &Self) {
        *self = self.mul(oth);
        if cfg!(feature = "verify") {
            assert!(self.magnitude <= 8);
            assert!(oth.magnitude <= 8);
            self.verify();
            oth.verify();
        }
        let mut r = Self::default();
        Self::mul_inner(&mut r.n, &self.n, &oth.n);
        if cfg!(feature = "verify") {
            r.magnitude = 1;
            r.normalized = false;
            r.verify();
        }
        *self = r;
    }

    pub fn sqr(&self) -> Self {
        let mut ret = self.clone();
        ret.sqr_assign();
        ret
    }

    pub fn sqr_assign(&mut self) {
        if cfg!(feature = "verify") {
            assert!(self.magnitude <= 8);
            self.verify();
        }
        self.sqr_inner();
        if cfg!(feature = "verify") {
            self.magnitude = 1;
            self.normalized = false;
            self.verify();
        }
    }

    /// Given that p is congruent to 3 mod 4, we can compute the square root of
    /// a mod p as the (p+1)/4'th power of a.
    ///
    /// As (p+1)/4 is an even number, it will have the same result for a and for
    /// (-a). Only one of these two numbers actually has a square root however,
    /// so we test at the end by squaring and comparing to the input.
    /// Also because (p+1)/4 is an even number, the computed square root is
    /// itself always a square (a ** ((p+1)/4) is the square of a ** ((p+1)/8)).
    ///
    /// The binary representation of (p + 1)/4 has 3 blocks of 1s, with lengths in
    /// { 2, 22, 223 }. Use an addition chain to calculate 2^n - 1 for each block:
    /// 1, [2], 3, 6, 9, 11, [22], 44, 88, 176, 220, [223]
    pub fn sqrt(&self) -> Result<Self, Error> {
        let mut r = self.clone();
        r.sqrt_assign()?;
        Ok(r)
    }

    pub fn sqrt_assign(&mut self) -> Result<(), Error> {
        let mut x2 = self.sqr();
        x2.mul_assign(&self);

        let mut x3 = x2.sqr();
        x3.mul_assign(&self);

        let mut x6 = x3.clone();
        for _j in 0..3 {
            x6.sqr_assign();
        }
        x6.mul_assign(&x3);

        let mut x9 = x6.clone();
        for _j in 0..3 {
            x9.sqr_assign();
        }
        x9.mul_assign(&x3);

        let mut x11 = x9.clone();
        for _j in 0..2 {
            x11.sqr_assign();
        }
        x11.mul_assign(&x2);

        let mut x22 = x11.clone();
        for _j in 0..11 {
            x22.sqr_assign();
        }
        x22.mul_assign(&x11);

        let mut x44 = x22.clone();
        for _j in 0..22 {
            x44.sqr_assign();
        }
        x44.mul_assign(&x22);

        let mut x88 = x44.clone();
        for _j in 0..44 {
            x88.sqr_assign();
        }
        x88.mul_assign(&x44);

        let mut x176 = x88.clone();
        for _j in 0..88 {
            x176.sqr_assign();
        }
        x176.mul_assign(&x88);

        let mut x220 = x176.clone();
        for _j in 0..44 {
            x220.sqr_assign();
        }
        x220.mul_assign(&x44);

        let mut x223 = x220.clone();
        for _j in 0..3 {
            x223.sqr_assign();
        }
        x223.mul_assign(&x3);

        /* The final result is then assembled using a sliding window over the blocks. */
        let mut t1 = x223.clone();
        for _j in 0..23 {
            t1.sqr_assign();
        }
        t1.mul_assign(&x22);
        for _j in 0..6 {
            t1.sqr_assign();
        }
        t1.mul_assign(&x2);
        t1.sqr_assign();
        t1.sqr_assign();

        /* Check that a square root was actually calculated */
        if t1.sqr().equal(&self) {
            *self = t1;
            Ok(())
        } else {
            Err(Error::InvalidSquareRoot)
        }
    }

    #[inline(always)]
    pub fn cmov(&mut self, oth: &Self, flag: bool) {
        /*VG_CHECK_VERIFY(self.n, sizeof(r->n));*/
        let mask0 = flag as u32 + !0;
        let mask1 = !mask0;
        self.n[0] = (self.n[0] & mask0) | (oth.n[0] & mask1);
        self.n[1] = (self.n[1] & mask0) | (oth.n[1] & mask1);
        self.n[2] = (self.n[2] & mask0) | (oth.n[2] & mask1);
        self.n[3] = (self.n[3] & mask0) | (oth.n[3] & mask1);
        self.n[4] = (self.n[4] & mask0) | (oth.n[4] & mask1);
        self.n[5] = (self.n[5] & mask0) | (oth.n[5] & mask1);
        self.n[6] = (self.n[6] & mask0) | (oth.n[6] & mask1);
        self.n[7] = (self.n[7] & mask0) | (oth.n[7] & mask1);
        self.n[8] = (self.n[8] & mask0) | (oth.n[8] & mask1);
        self.n[9] = (self.n[9] & mask0) | (oth.n[9] & mask1);
        if cfg!(feature = "verify") {
            if flag {
                self.magnitude = oth.magnitude;
                self.normalized = oth.normalized;
            }
        }
    }

    #[inline(always)]
    pub fn to_storage(&self) -> FieldElementStorage {
        if cfg!(feature = "verify") {
            assert!(self.normalized);
        }

        FieldElementStorage {
            n: [
                self.n[0] | self.n[1] << 26,
                self.n[1] >> 6 | self.n[2] << 20,
                self.n[2] >> 12 | self.n[3] << 14,
                self.n[3] >> 18 | self.n[4] << 8,
                self.n[4] >> 24 | self.n[5] << 2 | self.n[6] << 28,
                self.n[6] >> 4 | self.n[7] << 22,
                self.n[7] >> 10 | self.n[8] << 16,
                self.n[8] >> 16 | self.n[9] << 10,
            ],
        }
    }

    #[inline(always)]
    pub fn from_storage(a: &FieldElementStorage) -> Self {
        let (magnitude, normalized) = if cfg!(feature = "verify") {
            (1, true)
        } else {
            (0, false)
        };
        Self {
            magnitude,
            normalized,
            n: [
                a.n[0] & 0x3ffffff,
                a.n[0] >> 26 | ((a.n[1] << 6) & 0x3ffffff),
                a.n[1] >> 20 | ((a.n[2] << 12) & 0x3ffffff),
                a.n[2] >> 14 | ((a.n[3] << 18) & 0x3ffffff),
                a.n[3] >> 8 | ((a.n[4] << 24) & 0x3ffffff),
                (a.n[4] >> 2) & 0x3ffffff,
                a.n[4] >> 28 | ((a.n[5] << 4) & 0x3ffffff),
                a.n[5] >> 22 | ((a.n[6] << 10) & 0x3ffffff),
                a.n[6] >> 16 | ((a.n[7] << 16) & 0x3ffffff),
                a.n[7] >> 10,
            ],
        }
    }

    #[inline(always)]
    pub fn from_signed30(a: &Signed30) -> Self {
        const M26: u32 = core::u32::MAX >> 6;
        let (a0, a1, a2, a3, a4, a5, a6, a7, a8) = (
            a.v[0], a.v[1], a.v[2], a.v[3], a.v[4], a.v[5], a.v[6], a.v[7], a.v[8],
        );

        /* The output from rustsecp256k1_v0_4_1_modinv32{_var} should be normalized to range [0,modulus), and
         * have limbs in [0,2^30). The modulus is < 2^256, so the top limb must be below 2^(256-30*8).
         */
        verify_bits(a0, 30);
        verify_bits(a1, 30);
        verify_bits(a2, 30);
        verify_bits(a3, 30);
        verify_bits(a4, 30);
        verify_bits(a5, 30);
        verify_bits(a6, 30);
        verify_bits(a7, 30);
        verify_bits(a8, 16);

        let (magnitude, normalized) = if cfg!(feature = "verify") {
            (1, true)
        } else {
            (0, false)
        };
        let r = Self {
            magnitude,
            normalized,
            n: [
                a0 as u32 & M26,
                (a0 >> 26 | a1 << 4) as u32 & M26,
                (a1 >> 22 | a2 << 8) as u32 & M26,
                (a2 >> 18 | a3 << 12) as u32 & M26,
                (a3 >> 14 | a4 << 16) as u32 & M26,
                (a4 >> 10 | a5 << 20) as u32 & M26,
                (a5 >> 6 | a6 << 24) as u32 & M26,
                (a6 >> 2) as u32 & M26,
                (a6 >> 28 | a7 << 2) as u32 & M26,
                (a7 >> 24 | a8 << 6) as u32,
            ],
        };
        if cfg!(feature = "verify") {
            r.verify();
        }
        r
    }

    #[inline(always)]
    pub fn to_signed30(&self) -> Signed30 {
        const M30: u32 = core::u32::MAX >> 2;
        let (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) = (
            self.n[0], self.n[1], self.n[2], self.n[3], self.n[4], self.n[5], self.n[6], self.n[7],
            self.n[8], self.n[9],
        );

        if cfg!(feature = "verify") {
            assert!(self.normalized);
        }

        Signed30 {
            v: [
                ((a0 | a1 << 26) & M30) as i32,
                ((a1 >> 4 | a2 << 22) & M30) as i32,
                ((a2 >> 8 | a3 << 18) & M30) as i32,
                ((a3 >> 12 | a4 << 14) & M30) as i32,
                ((a4 >> 16 | a5 << 10) & M30) as i32,
                ((a5 >> 20 | a6 << 6) & M30) as i32,
                ((a6 >> 24 | a7 << 2 | a8 << 28) & M30) as i32,
                ((a8 >> 2 | a9 << 24) & M30) as i32,
                (a9 >> 6) as i32,
            ],
        }
    }

    pub fn inv(&self) -> Self {
        self.inv_with_info(&FIELD_MOD_INFO)
    }

    pub fn inv_with_info(&self, mod_info: &ModInfo) -> Self {
        let mut tmp = self.clone();
        tmp.normalize();
        let mut s = tmp.to_signed30();
        s.modinv_with_info(mod_info);
        Self::from_signed30(&s)
    }
}

pub struct FieldElementStorage {
    n: [u32; 8],
}

impl FieldElementStorage {
    #[inline(always)]
    pub fn cmov(&mut self, oth: &Self, flag: bool) {
        /*VG_CHECK_VERIFY(r->n, sizeof(r->n));*/
        let mask0 = flag as u32 + !0u32;
        let mask1 = !mask0;
        self.n[0] = (self.n[0] & mask0) | (oth.n[0] & mask1);
        self.n[1] = (self.n[1] & mask0) | (oth.n[1] & mask1);
        self.n[2] = (self.n[2] & mask0) | (oth.n[2] & mask1);
        self.n[3] = (self.n[3] & mask0) | (oth.n[3] & mask1);
        self.n[4] = (self.n[4] & mask0) | (oth.n[4] & mask1);
        self.n[5] = (self.n[5] & mask0) | (oth.n[5] & mask1);
        self.n[6] = (self.n[6] & mask0) | (oth.n[6] & mask1);
        self.n[7] = (self.n[7] & mask0) | (oth.n[7] & mask1);
    }

    pub fn get(&self) -> [u32; 8] {
        [
            self.n[7], self.n[6], self.n[5], self.n[4], self.n[3], self.n[2], self.n[1], self.n[0],
        ]
    }
}

impl From<[u32; 8]> for FieldElementStorage {
    fn from(n: [u32; 8]) -> Self {
        Self {
            n: [n[7], n[6], n[5], n[4], n[3], n[2], n[1], n[0]],
        }
    }
}

impl From<&FieldElementStorage> for [u32; 8] {
    fn from(f: &FieldElementStorage) -> [u32; 8] {
        f.get()
    }
}
