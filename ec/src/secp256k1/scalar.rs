#![allow(unused)]

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

use super::consts::*;
use super::modinv::Signed30;
use crate::{error::Error, util};

/* Limbs of the secp256k1 order. */
const N_0: u32 = 0xd0364141;
const N_1: u32 = 0xbfd25e8c;
const N_2: u32 = 0xaf48a03b;
const N_3: u32 = 0xbaaedce6;
const N_4: u32 = 0xfffffffe;
const N_5: u32 = 0xffffffff;
const N_6: u32 = 0xffffffff;
const N_7: u32 = 0xffffffff;

/* Limbs of 2^256 minus the secp256k1 order. */
const N_C_0: u32 = !N_0 + 1;
const N_C_1: u32 = !N_1;
const N_C_2: u32 = !N_2;
const N_C_3: u32 = !N_3;
const N_C_4: u32 = 1;

/* Limbs of half the secp256k1 order. */
const N_H_0: u32 = 0x681b20a0;
const N_H_1: u32 = 0xdfe92f46;
const N_H_2: u32 = 0x57a4501d;
const N_H_3: u32 = 0x5d576e73;
const N_H_4: u32 = 0xffffffff;
const N_H_5: u32 = 0xffffffff;
const N_H_6: u32 = 0xffffffff;
const N_H_7: u32 = 0x7fffffff;

pub struct Accumulator(pub(crate) (u32, u32, u32));

impl Accumulator {
    pub fn new() -> Self {
        Self((0, 0, 0))
    }

    pub fn c0(&self) -> u32 {
        self.0 .0
    }

    pub fn c1(&self) -> u32 {
        self.0 .1
    }

    pub fn c2(&self) -> u32 {
        self.0 .2
    }

    /// Add a*b to the number defined by (c0,c1,c2). c2 must never overflow.
    pub fn muladd(&mut self, a: u32, b: u32) {
        let t = a as u64 * b as u64;
        let mut th = (t >> 32) as u32; /* at most 0xFFFFFFFE */
        self.0 .0 += t as u32; /* overflow is handled on the next line */
        th += (self.0 .0 < t as u32) as u32; /* at most 0xFFFFFFFF */
        self.0 .1 += th; /* overflow is handled on the next line */
        self.0 .2 += (self.0 .1 < th) as u32; /* never overflows by contract (verified in the next line) */
        assert!((self.0 .1 >= th) || (self.0 .2 != 0));
    }

    /// Add a*b to the number defined by (c0,c1). c1 must never overflow.
    pub fn muladd_fast(&mut self, a: u32, b: u32) {
        let t = a as u64 * b as u64;
        let mut th = (t >> 32) as u32; /* at most 0xFFFFFFFE */
        self.0 .0 += t as u32; /* overflow is handled on the next line */
        th += (self.0 .0 < t as u32) as u32; /* at most 0xFFFFFFFF */
        self.0 .1 += th; /* never overflows by contract (verified in the next line) */
        assert!(self.0 .1 >= th);
    }

    /// Add a to the number defined by (c0,c1,c2). c2 must never overflow.
    pub fn sumadd(&mut self, a: u32) {
        self.0 .0 += a; /* overflow is handled on the next line */
        let over = (self.0 .0 < a) as u32;
        self.0 .1 += over; /* overflow is handled on the next line */
        self.0 .2 += (self.0 .1 < over) as u32; /* never overflows by contract */
    }

    /// Add a to the number defined by (c0,c1). c1 must never overflow, c2 must be zero.
    pub fn sumadd_fast(&mut self, a: u32) {
        self.0 .0 += a; /* overflow is handled on the next line */
        self.0 .1 += (self.0 .0 < a) as u32; /* never overflows by contract (verified the next line) */
        assert!(self.0 .1 != 0 || self.0 .0 >= a);
        assert_eq!(self.0 .2, 0);
    }

    /// Extract the lowest 32 bits of (c0,c1,c2) into n, and left shift the number 32 bits.
    pub fn extract(&mut self) -> u32 {
        let n = self.0 .0;
        self.0 .0 = self.0 .1;
        self.0 .1 = self.0 .2;
        self.0 .2 = 0;
        n
    }

    /// Extract the lowest 32 bits of (c0,c1,c2) into n, and left shift the number 32 bits. c2 is required to be zero.
    pub fn extract_fast(&mut self) -> u32 {
        let n = self.0 .0;
        self.0 .0 = self.0 .1;
        self.0 .1 = 0;
        assert_eq!(self.0 .2, 0);
        n
    }
}

#[derive(Clone)]
pub struct Scalar {
    d: [u32; 8],
}

impl From<[u32; 8]> for Scalar {
    fn from(d: [u32; 8]) -> Self {
        Self::from_const(d)
    }
}

impl Scalar {
    pub fn new() -> Self {
        Self { d: [0; 8] }
    }

    pub fn from_const(d: [u32; 8]) -> Self {
        Self {
            d: util::reverse32(&d),
        }
    }

    pub fn clear(&mut self) {
        self.d.swap_with_slice(&mut [0, 0, 0, 0, 0, 0, 0, 0]);
    }

    pub fn set_int(&mut self, v: u32) {
        self.d.swap_with_slice(&mut [v, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[inline(always)]
    fn get_bits(&self, offset: u32, count: u32) -> u32 {
        assert_eq!((offset + count - 1) >> 5, offset >> 5);
        (self.d[offset as usize >> 5] >> (offset & 0x1f)) & ((1 << count) - 1)
    }

    #[inline(always)]
    pub fn check_overflow(&self) -> bool {
        let mut yes = 0;
        let mut no = 0;

        no |= (self.d[7] < N_7) as u8; /* No need for a > check. */
        no |= (self.d[6] < N_6) as u8; /* No need for a > check. */
        no |= (self.d[5] < N_5) as u8; /* No need for a > check. */
        no |= (self.d[4] < N_4) as u8;
        yes |= (self.d[4] > N_4) as u8 & !no;
        no |= (self.d[3] < N_3) as u8 & !yes;
        yes |= (self.d[3] > N_3) as u8 & !no;
        no |= (self.d[2] < N_2) as u8 & !yes;
        yes |= (self.d[2] > N_2) as u8 & !no;
        no |= (self.d[1] < N_1) as u8 & !yes;
        yes |= (self.d[1] > N_1) as u8 & !no;
        yes |= (self.d[0] >= N_0) as u8 & !no;

        yes != 0
    }

    #[inline(always)]
    pub fn reduce_assign(&mut self) {
        let mut t = self.d[0] as u64 + N_C_0 as u64;
        self.d[0] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += self.d[1] as u64 + N_C_1 as u64;
        self.d[1] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += self.d[2] as u64 + N_C_2 as u64;
        self.d[2] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += self.d[3] as u64 + N_C_3 as u64;
        self.d[3] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += self.d[4] as u64 + N_C_4 as u64;
        self.d[4] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += self.d[5] as u64;
        self.d[5] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += self.d[6] as u64;
        self.d[6] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += self.d[7] as u64;
        self.d[7] = (t & 0xffffffff) as u32;
    }

    pub fn reduce(&self) -> Self {
        let mut r = self.clone();
        r.reduce_assign();
        r
    }

    #[inline(always)]
    pub fn add_assign(&mut self, oth: &Self) -> Result<(), Error> {
        let mut t: u64 = self.d[0] as u64 + oth.d[0] as u64;
        let mut r = self.clone();
        r.d[0] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[1] as u64 + oth.d[1] as u64;
        r.d[1] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[2] as u64 + oth.d[2] as u64;
        r.d[2] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[3] as u64 + oth.d[3] as u64;
        r.d[3] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[4] as u64 + oth.d[4] as u64;
        r.d[4] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[5] as u64 + oth.d[5] as u64;
        r.d[5] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[6] as u64 + oth.d[6] as u64;
        r.d[6] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[7] as u64 + oth.d[7] as u64;
        r.d[7] = (t & 0xffffffff) as u32;
        t >>= 32;
        let overflow = t + r.check_overflow() as u64;
        r.reduce_assign();
        if overflow != 0 {
            Err(Error::ScalarAdditionOverflow)
        } else {
            *self = r;
            Ok(())
        }
    }

    pub fn add(&self, oth: &Self) -> Result<Self, Error> {
        let mut r = self.clone();
        r.add_assign(oth)?;
        Ok(r)
    }

    #[inline(always)]
    pub fn cadd_bit_assign(&mut self, mut bit: u32, flag: bool) -> Result<(), Error> {
        let ret = if bit < 256 {
            Ok(())
        } else {
            bit = 0;
            Err(Error::InvalidBitIndex)
        };
        bit += (flag as u32 - 1) & 0x100; /* forcing (bit >> 5) > 7 makes this a noop */
        let mut r = self.clone();
        let mut t = r.d[0] as u64 + ((((bit >> 5) == 0) as u32) << (bit & 0x1f)) as u64;
        r.d[0] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[1] as u64 + ((((bit >> 5) == 1) as u32) << (bit & 0x1f)) as u64;
        r.d[1] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[2] as u64 + ((((bit >> 5) == 2) as u32) << (bit & 0x1f)) as u64;
        r.d[2] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[3] as u64 + ((((bit >> 5) == 3) as u32) << (bit & 0x1f)) as u64;
        r.d[3] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[4] as u64 + ((((bit >> 5) == 4) as u32) << (bit & 0x1f)) as u64;
        r.d[4] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[5] as u64 + ((((bit >> 5) == 5) as u32) << (bit & 0x1f)) as u64;
        r.d[5] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[6] as u64 + ((((bit >> 5) == 6) as u32) << (bit & 0x1f)) as u64;
        r.d[6] = (t & 0xffffffff) as u32;
        t >>= 32;
        t += r.d[7] as u64 + ((((bit >> 5) == 7) as u32) << (bit & 0x1f)) as u64;
        r.d[7] = (t & 0xffffffff) as u32;
        if cfg!(feature = "verify") {
            assert_eq!(t >> 32, 0);
            assert_eq!(r.check_overflow(), false);
        }
        if ret.is_ok() {
            *self = r;
        }
        ret
    }

    pub fn cadd_bit(&self, bit: u32, flag: bool) -> Result<Self, Error> {
        let mut r = self.clone();
        r.cadd_bit_assign(bit, flag)?;
        Ok(r)
    }

    pub fn set_b32(&mut self, b32: &[u8; 32]) -> Result<(), Error> {
        let mut r = Self {
            d: [
                u32::from_le_bytes([b32[28], b32[29], b32[30], b32[31]]),
                u32::from_le_bytes([b32[24], b32[25], b32[26], b32[27]]),
                u32::from_le_bytes([b32[20], b32[21], b32[22], b32[23]]),
                u32::from_le_bytes([b32[16], b32[17], b32[18], b32[19]]),
                u32::from_le_bytes([b32[12], b32[13], b32[14], b32[15]]),
                u32::from_le_bytes([b32[8], b32[9], b32[10], b32[11]]),
                u32::from_le_bytes([b32[4], b32[5], b32[6], b32[7]]),
                u32::from_le_bytes([b32[0], b32[1], b32[2], b32[3]]),
            ],
        };
        let overflow = r.check_overflow();
        r.reduce_assign();
        if overflow {
            Err(Error::ScalarOverflow)
        } else {
            *self = r;
            Ok(())
        }
    }

    pub fn get_b32(&self) -> [u8; 32] {
        let mut r = [0u8; 32];
        r[0..4].swap_with_slice(&mut self.d[7].to_le_bytes());
        r[4..8].swap_with_slice(&mut self.d[6].to_le_bytes());
        r[8..12].swap_with_slice(&mut self.d[5].to_le_bytes());
        r[12..16].swap_with_slice(&mut self.d[4].to_le_bytes());
        r[16..20].swap_with_slice(&mut self.d[3].to_le_bytes());
        r[20..24].swap_with_slice(&mut self.d[2].to_le_bytes());
        r[24..28].swap_with_slice(&mut self.d[1].to_le_bytes());
        r[28..].swap_with_slice(&mut self.d[0].to_le_bytes());
        r
    }

    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.d[0]
            | self.d[1]
            | self.d[2]
            | self.d[3]
            | self.d[4]
            | self.d[5]
            | self.d[6]
            | self.d[7]
            == 0
    }

    #[inline(always)]
    pub fn is_one(&self) -> bool {
        (self.d[0] ^ 1)
            | self.d[1]
            | self.d[2]
            | self.d[3]
            | self.d[4]
            | self.d[5]
            | self.d[6]
            | self.d[7]
            == 0
    }

    #[inline(always)]
    pub fn negate_assign(&mut self) {
        let nonzero = 0xFFFFFFFF * (!self.is_zero()) as u64;
        let mut t = (!self.d[0]) as u64 + N_0 as u64 + 1;
        self.d[0] = (t & nonzero) as u32;
        t >>= 32;
        t += (!self.d[1]) as u64 + N_1 as u64;
        self.d[1] = (t & nonzero) as u32;
        t >>= 32;
        t += (!self.d[2]) as u64 + N_2 as u64;
        self.d[2] = (t & nonzero) as u32;
        t >>= 32;
        t += (!self.d[3]) as u64 + N_3 as u64;
        self.d[3] = (t & nonzero) as u32;
        t >>= 32;
        t += (!self.d[4]) as u64 + N_4 as u64;
        self.d[4] = (t & nonzero) as u32;
        t >>= 32;
        t += (!self.d[5]) as u64 + N_5 as u64;
        self.d[5] = (t & nonzero) as u32;
        t >>= 32;
        t += (!self.d[6]) as u64 + N_6 as u64;
        self.d[6] = (t & nonzero) as u32;
        t >>= 32;
        t += (!self.d[7]) as u64 + N_7 as u64;
        self.d[7] = (t & nonzero) as u32;
    }

    pub fn negate(&self) -> Self {
        let mut r = self.clone();
        r.negate_assign();
        r
    }

    #[inline(always)]
    pub fn is_high(&self) -> bool {
        let (mut yes, mut no) = (0, 0);
        no |= (self.d[7] < N_H_7) as u8;
        yes |= (self.d[7] > N_H_7) as u8 & !no;
        no |= (self.d[6] < N_H_6) as u8 & !yes; /* No need for a > check. */
        no |= (self.d[5] < N_H_5) as u8 & !yes; /* No need for a > check. */
        no |= (self.d[4] < N_H_4) as u8 & !yes; /* No need for a > check. */
        no |= (self.d[3] < N_H_3) as u8 & !yes;
        yes |= (self.d[3] > N_H_3) as u8 & !no;
        no |= (self.d[2] < N_H_2) as u8 & !yes;
        yes |= (self.d[2] > N_H_2) as u8 & !no;
        no |= (self.d[1] < N_H_1) as u8 & !yes;
        yes |= (self.d[1] > N_H_1) as u8 & !no;
        yes |= (self.d[0] > N_H_0) as u8 & !no;
        yes != 0
    }

    #[inline(always)]
    pub fn cond_negate_assign(&mut self, flag: bool) {
        /* If we are flag = 0, mask = 00...00 and this is a no-op;
         * if we are flag = 1, mask = 11...11 and this is identical to rustsecp256k1_v0_4_1_scalar_negate */
        let mask = (!flag) as u32 - 1;
        let nonzero = 0xffff_ffff_ffff_ffffu64 * self.is_zero() as u64;
        let mut t = (self.d[0] ^ mask) as u64 + ((N_0 + 1) & mask) as u64;

        self.d[0] = (t & nonzero) as u32;
        t >>= 32;
        t += (self.d[1] ^ mask) as u64 + (N_1 & mask) as u64;
        self.d[1] = (t & nonzero) as u32;
        t >>= 32;
        t += (self.d[2] ^ mask) as u64 + (N_2 & mask) as u64;
        self.d[2] = (t & nonzero) as u32;
        t >>= 32;
        t += (self.d[3] ^ mask) as u64 + (N_3 & mask) as u64;
        self.d[3] = (t & nonzero) as u32;
        t >>= 32;
        t += (self.d[4] ^ mask) as u64 + (N_4 & mask) as u64;
        self.d[4] = (t & nonzero) as u32;
        t >>= 32;
        t += (self.d[5] ^ mask) as u64 + (N_5 & mask) as u64;
        self.d[5] = (t & nonzero) as u32;
        t >>= 32;
        t += (self.d[6] ^ mask) as u64 + (N_6 & mask) as u64;
        self.d[6] = (t & nonzero) as u32;
        t >>= 32;
        t += (self.d[7] ^ mask) as u64 as u64 + (N_7 & mask) as u64;
        self.d[7] = (t & nonzero) as u32;
    }

    pub fn cond_negate(&self, flag: bool) -> Self {
        let mut r = self.clone();
        r.cond_negate_assign(flag);
        r
    }

    #[inline(always)]
    fn reduce_512_assign(&mut self, l: &[u32]) -> Result<(), Error> {
        let (n0, n1, n2, n3, n4, n5, n6, n7) =
            (l[8], l[9], l[10], l[11], l[12], l[13], l[14], l[15]);
        let mut acc = Accumulator::new();

        acc.muladd_fast(n0, N_C_0);
        let m0 = acc.extract_fast();

        acc.sumadd_fast(l[1]);
        acc.muladd(n1, N_C_0);
        acc.muladd(n0, N_C_1);
        let m1 = acc.extract();

        acc.sumadd(l[2]);
        acc.muladd(n2, N_C_0);
        acc.muladd(n1, N_C_1);
        acc.muladd(n0, N_C_2);
        let m2 = acc.extract();

        acc.sumadd(l[3]);
        acc.muladd(n3, N_C_0);
        acc.muladd(n2, N_C_1);
        acc.muladd(n1, N_C_2);
        acc.muladd(n0, N_C_3);
        let m3 = acc.extract();

        acc.sumadd(l[4]);
        acc.muladd(n4, N_C_0);
        acc.muladd(n3, N_C_1);
        acc.muladd(n2, N_C_2);
        acc.muladd(n1, N_C_3);
        acc.sumadd(n0);
        let m4 = acc.extract();

        acc.sumadd(l[5]);
        acc.muladd(n5, N_C_0);
        acc.muladd(n4, N_C_1);
        acc.muladd(n3, N_C_2);
        acc.muladd(n2, N_C_3);
        acc.sumadd(n1);
        let m5 = acc.extract();

        acc.sumadd(l[6]);
        acc.muladd(n6, N_C_0);
        acc.muladd(n5, N_C_1);
        acc.muladd(n4, N_C_2);
        acc.muladd(n3, N_C_3);
        acc.sumadd(n2);
        let m6 = acc.extract();

        acc.sumadd(l[7]);
        acc.muladd(n7, N_C_0);
        acc.muladd(n6, N_C_1);
        acc.muladd(n5, N_C_2);
        acc.muladd(n4, N_C_3);
        acc.sumadd(n3);
        let m7 = acc.extract();

        acc.muladd(n7, N_C_1);
        acc.muladd(n6, N_C_2);
        acc.muladd(n5, N_C_3);
        acc.sumadd(n4);
        let m8 = acc.extract();

        acc.muladd(n7, N_C_2);
        acc.muladd(n6, N_C_3);
        acc.sumadd(n5);
        let m9 = acc.extract();

        acc.muladd(n7, N_C_3);
        acc.sumadd(n6);
        let m10 = acc.extract();

        acc.sumadd_fast(n7);
        let m11 = acc.extract_fast();
        assert!(acc.c0() <= 1);
        let m12 = acc.c0();

        /* Reduce 385 bits into 258. */
        /* p[0..8] = m[0..7] + m[8..12] * SECP256K1_N_C. */
        acc.0 .0 = m0;
        acc.0 .1 = 0;
        acc.0 .2 = 0;

        acc.muladd_fast(m8, N_C_0);
        let p0 = acc.extract_fast();

        acc.sumadd_fast(m1);
        acc.muladd(m9, N_C_0);
        acc.muladd(m8, N_C_1);
        let p1 = acc.extract();

        acc.sumadd(m2);
        acc.muladd(m10, N_C_0);
        acc.muladd(m9, N_C_1);
        acc.muladd(m8, N_C_2);
        let p2 = acc.extract();

        acc.sumadd(m3);
        acc.muladd(m11, N_C_0);
        acc.muladd(m10, N_C_1);
        acc.muladd(m9, N_C_2);
        acc.muladd(m8, N_C_3);
        let p3 = acc.extract();

        acc.sumadd(m4);
        acc.muladd(m12, N_C_0);
        acc.muladd(m11, N_C_1);
        acc.muladd(m10, N_C_2);
        acc.muladd(m9, N_C_3);
        acc.sumadd(m8);
        let p4 = acc.extract();

        acc.sumadd(m5);
        acc.muladd(m12, N_C_1);
        acc.muladd(m11, N_C_2);
        acc.muladd(m10, N_C_3);
        acc.sumadd(m9);
        let p5 = acc.extract();

        acc.sumadd(m6);
        acc.muladd(m12, N_C_2);
        acc.muladd(m11, N_C_3);
        acc.sumadd(m10);
        let p6 = acc.extract();

        acc.sumadd_fast(m7);
        acc.muladd_fast(m12, N_C_3);
        acc.sumadd_fast(m11);
        let p7 = acc.extract_fast();

        let p8 = acc.c0() + m12;
        assert!(p8 <= 2);

        /* Reduce 258 bits into 256. */
        /* r[0..7] = p[0..7] + p[8] * SECP256K1_N_C. */
        let mut c = p0 as u64 + N_C_0 as u64 * p8 as u64;
        let mut r = Self::new();
        r.d[0] = (c & 0xffffffff) as u32;
        c >>= 32;
        c += p1 as u64 + N_C_1 as u64 * p8 as u64;
        r.d[1] = (c & 0xffffffff) as u32;
        c >>= 32;
        c += p2 as u64 + N_C_2 as u64 * p8 as u64;
        r.d[2] = (c & 0xffffffff) as u32;
        c >>= 32;
        c += p3 as u64 + N_C_3 as u64 * p8 as u64;
        r.d[3] = (c & 0xffffffff) as u32;
        c >>= 32;
        c += p4 as u64 + p8 as u64;
        r.d[4] = (c & 0xffffffff) as u32;
        c >>= 32;
        c += p5 as u64;
        r.d[5] = (c & 0xffffffff) as u32;
        c >>= 32;
        c += p6 as u64;
        r.d[6] = (c & 0xffffffff) as u32;
        c >>= 32;
        c += p7 as u64;
        r.d[7] = (c & 0xffffffff) as u32;
        c >>= 32;
        let over = (c | r.check_overflow() as u64) != 0;
        /* Final reduction of r. */
        r.reduce();

        if over {
            Err(Error::ScalarAdditionOverflow)
        } else {
            *self = r;
            Ok(())
        }
    }

    fn reduce_512(&self, l: &[u32]) -> Result<Self, Error> {
        let mut r = self.clone();
        r.reduce_512_assign(l)?;
        Ok(r)
    }

    #[inline(always)]
    fn mul_512(&self, oth: &Self) -> [u32; 16] {
        /* l[0..15] = a[0..7] * b[0..7]. */
        let mut l = [0u32; 16];
        let mut acc = Accumulator::new();

        acc.muladd_fast(self.d[0], oth.d[0]);
        l[0] = acc.extract_fast();

        acc.muladd(self.d[0], oth.d[1]);
        acc.muladd(self.d[1], oth.d[0]);
        l[1] = acc.extract();

        acc.muladd(self.d[0], oth.d[2]);
        acc.muladd(self.d[1], oth.d[1]);
        acc.muladd(self.d[2], oth.d[0]);
        l[2] = acc.extract();

        acc.muladd(self.d[0], oth.d[3]);
        acc.muladd(self.d[1], oth.d[2]);
        acc.muladd(self.d[2], oth.d[1]);
        acc.muladd(self.d[3], oth.d[0]);
        l[3] = acc.extract();

        acc.muladd(self.d[0], oth.d[4]);
        acc.muladd(self.d[1], oth.d[3]);
        acc.muladd(self.d[2], oth.d[2]);
        acc.muladd(self.d[3], oth.d[1]);
        acc.muladd(self.d[4], oth.d[0]);
        l[4] = acc.extract();

        acc.muladd(self.d[0], oth.d[5]);
        acc.muladd(self.d[1], oth.d[4]);
        acc.muladd(self.d[2], oth.d[3]);
        acc.muladd(self.d[3], oth.d[2]);
        acc.muladd(self.d[4], oth.d[1]);
        acc.muladd(self.d[5], oth.d[0]);
        l[5] = acc.extract();

        acc.muladd(self.d[0], oth.d[6]);
        acc.muladd(self.d[1], oth.d[5]);
        acc.muladd(self.d[2], oth.d[4]);
        acc.muladd(self.d[3], oth.d[3]);
        acc.muladd(self.d[4], oth.d[2]);
        acc.muladd(self.d[5], oth.d[1]);
        acc.muladd(self.d[6], oth.d[0]);
        l[6] = acc.extract();

        acc.muladd(self.d[0], oth.d[7]);
        acc.muladd(self.d[1], oth.d[6]);
        acc.muladd(self.d[2], oth.d[5]);
        acc.muladd(self.d[3], oth.d[4]);
        acc.muladd(self.d[4], oth.d[3]);
        acc.muladd(self.d[5], oth.d[2]);
        acc.muladd(self.d[6], oth.d[1]);
        acc.muladd(self.d[7], oth.d[0]);
        l[7] = acc.extract();

        acc.muladd(self.d[1], oth.d[7]);
        acc.muladd(self.d[2], oth.d[6]);
        acc.muladd(self.d[3], oth.d[5]);
        acc.muladd(self.d[4], oth.d[4]);
        acc.muladd(self.d[5], oth.d[3]);
        acc.muladd(self.d[6], oth.d[2]);
        acc.muladd(self.d[7], oth.d[1]);
        l[8] = acc.extract();

        acc.muladd(self.d[2], oth.d[7]);
        acc.muladd(self.d[3], oth.d[6]);
        acc.muladd(self.d[4], oth.d[5]);
        acc.muladd(self.d[5], oth.d[4]);
        acc.muladd(self.d[6], oth.d[3]);
        acc.muladd(self.d[7], oth.d[2]);
        l[9] = acc.extract();

        acc.muladd(self.d[3], oth.d[7]);
        acc.muladd(self.d[4], oth.d[6]);
        acc.muladd(self.d[5], oth.d[5]);
        acc.muladd(self.d[6], oth.d[4]);
        acc.muladd(self.d[7], oth.d[3]);
        l[10] = acc.extract();

        acc.muladd(self.d[4], oth.d[7]);
        acc.muladd(self.d[5], oth.d[6]);
        acc.muladd(self.d[6], oth.d[5]);
        acc.muladd(self.d[7], oth.d[4]);
        l[11] = acc.extract();

        acc.muladd(self.d[5], oth.d[7]);
        acc.muladd(self.d[6], oth.d[6]);
        acc.muladd(self.d[7], oth.d[5]);
        l[12] = acc.extract();

        acc.muladd(self.d[6], oth.d[7]);
        acc.muladd(self.d[7], oth.d[6]);
        l[13] = acc.extract();

        acc.muladd_fast(self.d[7], oth.d[7]);
        l[14] = acc.extract_fast();

        assert_eq!(acc.c1(), 0);
        l[15] = acc.c0();
        l
    }

    pub fn mul(&self, oth: &Self) -> Result<Self, Error> {
        self.reduce_512(&self.mul_512(oth))
    }

    #[inline(always)]
    pub fn shr_int_assign(&mut self, n: u32) -> u32 {
        assert!(n > 0);
        assert!(n < 16);
        let ret = self.d[0] & ((1 << n) - 1);
        self.d[0] = (self.d[0] >> n) + (self.d[1] << (32 - n));
        self.d[1] = (self.d[1] >> n) + (self.d[2] << (32 - n));
        self.d[2] = (self.d[2] >> n) + (self.d[3] << (32 - n));
        self.d[3] = (self.d[3] >> n) + (self.d[4] << (32 - n));
        self.d[4] = (self.d[4] >> n) + (self.d[5] << (32 - n));
        self.d[5] = (self.d[5] >> n) + (self.d[6] << (32 - n));
        self.d[6] = (self.d[6] >> n) + (self.d[7] << (32 - n));
        self.d[7] = self.d[7] >> n;
        ret
    }

    #[inline(always)]
    pub fn split_128(&self) -> (Scalar, Scalar) {
        (
            Scalar {
                d: [self.d[0], self.d[1], self.d[2], self.d[3], 0, 0, 0, 0],
            },
            Scalar {
                d: [self.d[4], self.d[5], self.d[6], self.d[7], 0, 0, 0, 0],
            },
        )
    }

    #[inline(always)]
    pub fn equal(&self, oth: &Self) -> bool {
        (self.d[0] ^ oth.d[0])
            | (self.d[1] ^ oth.d[1])
            | (self.d[2] ^ oth.d[2])
            | (self.d[3] ^ oth.d[3])
            | (self.d[4] ^ oth.d[4])
            | (self.d[5] ^ oth.d[5])
            | (self.d[6] ^ oth.d[6])
            | (self.d[7] ^ oth.d[7])
            == 0
    }

    #[inline(always)]
    pub fn cmov(&mut self, oth: &Self, flag: bool) {
        let mask0 = flag as u32 + !0;
        let mask1 = !mask0;
        self.d[0] = (self.d[0] & mask0) | (oth.d[0] & mask1);
        self.d[1] = (self.d[1] & mask0) | (oth.d[1] & mask1);
        self.d[2] = (self.d[2] & mask0) | (oth.d[2] & mask1);
        self.d[3] = (self.d[3] & mask0) | (oth.d[3] & mask1);
        self.d[4] = (self.d[4] & mask0) | (oth.d[4] & mask1);
        self.d[5] = (self.d[5] & mask0) | (oth.d[5] & mask1);
        self.d[6] = (self.d[6] & mask0) | (oth.d[6] & mask1);
        self.d[7] = (self.d[7] & mask0) | (oth.d[7] & mask1);
    }

    pub fn is_even(&self) -> bool {
        self.d[0] & 1 == 0
    }

    #[inline(always)]
    pub fn from_signed30(s: Signed30) -> Self {
        let (a0, a1, a2, a3, a4, a5, a6, a7, a8) = (
            s.v[0], s.v[1], s.v[2], s.v[3], s.v[4], s.v[5], s.v[6], s.v[7], s.v[8],
        );
        /* The output from rustsecp256k1_v0_4_1_modinv32{_var} should be normalized to range [0,modulus), and
         * have limbs in [0,2^30). The modulus is < 2^256, so the top limb must be below 2^(256-30*8).
         */
        assert_eq!(a0 >> 30, 0);
        assert_eq!(a1 >> 30, 0);
        assert_eq!(a2 >> 30, 0);
        assert_eq!(a3 >> 30, 0);
        assert_eq!(a4 >> 30, 0);
        assert_eq!(a5 >> 30, 0);
        assert_eq!(a6 >> 30, 0);
        assert_eq!(a7 >> 30, 0);
        assert_eq!(a8 >> 16, 0);
        let r = Self {
            d: [
                (a0 | a1 << 30) as u32,
                (a1 >> 2 | a2 << 28) as u32,
                (a2 >> 4 | a3 << 26) as u32,
                (a3 >> 6 | a4 << 24) as u32,
                (a4 >> 8 | a5 << 22) as u32,
                (a5 >> 10 | a6 << 20) as u32,
                (a6 >> 12 | a7 << 18) as u32,
                (a7 >> 14 | a8 << 16) as u32,
            ],
        };
        if cfg!(feature = "verify") {
            assert!(!r.check_overflow());
        }
        r
    }

    #[inline(always)]
    pub fn to_signed30(&self) -> Signed30 {
        if cfg!(feature = "verify") {
            assert!(!self.check_overflow());
        }
        const M30: u32 = core::u32::MAX >> 2;
        let (a0, a1, a2, a3, a4, a5, a6, a7) = (
            self.d[0], self.d[1], self.d[2], self.d[3], self.d[4], self.d[5], self.d[6], self.d[7],
        );
        Signed30 {
            v: [
                (a0 & M30) as i32,
                ((a0 >> 30 | a1 << 2) & M30) as i32,
                ((a1 >> 28 | a2 << 4) & M30) as i32,
                ((a2 >> 26 | a3 << 6) & M30) as i32,
                ((a3 >> 24 | a4 << 8) & M30) as i32,
                ((a4 >> 22 | a5 << 10) & M30) as i32,
                ((a5 >> 20 | a6 << 12) & M30) as i32,
                ((a6 >> 18 | a7 << 14) & M30) as i32,
                (a7 >> 16) as i32,
            ],
        }
    }

    pub fn inverse_assign(&mut self) {
        let mut s = self.to_signed30();
        s.modinv_scalar();
        let r = Self::from_signed30(s);
        if cfg!(feature = "verify") {
            assert_eq!(r.is_zero(), self.is_zero());
        }
        *self = r;
    }

    pub fn inverse(&self) -> Self {
        let mut r = self.clone();
        r.inverse_assign();
        r
    }
}
