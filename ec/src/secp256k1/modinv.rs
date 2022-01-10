/***********************************************************************
 * Copyright (c) 2020 Peter Dettman                                    *
 * Copyleft (c) 2022 nanorust developers                               *
 * Distributed under the MIT software license, see the accompanying    *
 * file COPYING or https://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

/* This file implements modular inversion based on the paper "Fast constant-time gcd computation and
 * modular inversion" by Daniel J. Bernstein and Bo-Yin Yang.
 *
 * For an explanation of the algorithm, see doc/safegcd_implementation.md. This file contains an
 * implementation for N=30, using 30-bit signed limbs represented as int32_t.
 */

use crate::{endian::Endian, util::cmp};
use super::consts::*;

#[derive(Clone, Debug)]
pub struct Signed30 {
    pub(crate) v: [i32; 9],
}

impl PartialEq for Signed30 {
    fn eq(&self, o: &Self) -> bool {
        self.cmp(o) == 0
    }
}

impl From<[i32; 9]> for Signed30 {
    fn from(v: [i32; 9]) -> Self {
        Self::from_i32(v)
    }
}

#[derive(Clone)]
pub struct ModInfo {
    pub(crate) modulus: Signed30,
    pub(crate) modulus_inv30: u32,
}

impl From<Signed30> for ModInfo {
    fn from(modulus: Signed30) -> Self {
        Self {
            modulus,
            modulus_inv30: 0,
        }
    }
}

impl ModInfo {
    pub fn modulus(&self) -> &Signed30 {
        &self.modulus
    }

    pub fn modulus_mut(&mut self) -> &mut Signed30 {
        &mut self.modulus
    }

    pub fn modulus_inv30(&self) -> u32 {
        self.modulus_inv30
    }

    pub fn set_modulus_inv30(&mut self, mi30: u32) {
        self.modulus_inv30 = mi30;
    }
}

impl Signed30 {
    pub fn new() -> Self {
        Self { v: [0; 9] }
    }

    pub fn from_i32(v: [i32; 9]) -> Self {
        Self { v: [v[8], v[7], v[6], v[5], v[4], v[3], v[2], v[1], v[0]] }
    }

    pub fn is_zero(&self) -> bool {
        self.v[0]
            | self.v[1]
            | self.v[2]
            | self.v[3]
            | self.v[4]
            | self.v[5]
            | self.v[6]
            | self.v[7]
            | self.v[8]
            == 0
    }

    pub fn v(&self) -> &[i32; 9] {
        &self.v
    }

    /// Compute a*factor and put it in r. All but the top limb in r will be in range [0,2^30).
    pub fn mul(&self, len: usize, factor: i32) -> Self {
        let mut c = 0i64;
        let mut r = Self::new();
        for i in 0..8 {
            c = c
                .overflowing_add((i < len) as i64 * self.v[i] as i64 * factor as i64)
                .0;
            r.v[i] = c as i32 & M30;
            c >>= 30;
        }

        let (c, overflow) = c.overflowing_add((8 < len) as i64 * self.v[8] as i64 * factor as i64);
        assert!(!overflow);
        r.v[8] = c as i32;
        r
    }

    /// Return -1 for a<b*factor, 0 for a==b*factor, 1 for a>b*factor. A consists of alen limbs; b has 9.
    pub fn mul_cmp(&self, len: usize, oth: &Self, factor: i32) -> i8 {
        let am = self.mul(len, 1); /* Normalize all but the top limb of a. */
        let bm = oth.mul(9, factor);
        for (av, bv) in am.v[..8].iter().zip(bm.v[..8].iter()) {
            /* Verify that all but the top limb of a and b are normalized. */
            assert_eq!(av >> 30, 0);
            assert_eq!(bv >> 30, 0);
        }
        for (av, bv) in am.v.iter().zip(bm.v.iter()).rev() {
            if av < bv {
                return -1;
            }
            if av > bv {
                return 1;
            }
        }
        0
    }

    pub fn cmp(&self, oth: &Self) -> i8 {
        cmp(&self.v, &oth.v, Endian::Little)
    }

    /// Take as input a signed30 number in range (-2*modulus,modulus), and add a multiple of the modulus
    /// to it to bring it to range [0,modulus). If sign < 0, the input will also be negated in the
    /// process. The input must have limbs in range (-2^30,2^30). The output will have limbs in range
    /// [0,2^30).
    pub fn normalize_field(&mut self, sign: i32) {
        self.normalize_with_info(sign, &FIELD_MOD_INFO);
    }

    pub fn normalize_scalar(&mut self, sign: i32) {
        self.normalize_with_info(sign, &SCALAR_MOD_INFO);
    }

    pub fn normalize_with_info(&mut self, sign: i32, mod_info: &ModInfo) {
        let (mut r0, mut r1, mut r2, mut r3, mut r4, mut r5, mut r6, mut r7, mut r8) = (
            self.v[0], self.v[1], self.v[2], self.v[3], self.v[4], self.v[5], self.v[6], self.v[7],
            self.v[8],
        );

        if cfg!(feature = "verify") {
            /* Verify that all limbs are in range (-2^30,2^30). */
            for &v in self.v.iter() {
                assert!(v >= -M30);
                assert!(v <= M30);
            }
            assert!(self.mul_cmp(9, &mod_info.modulus, -2) > 0); /* r > -2*modulus */
            assert!(self.mul_cmp(9, &mod_info.modulus, 1) < 0); /* r < modulus */
        }

        /* In a first step, add the modulus if the input is negative, and then negate if requested.
         * This brings r from range (-2*modulus,modulus) to range (-modulus,modulus). As all input
         * limbs are in range (-2^30,2^30), this cannot overflow an int32_t. Note that the right
         * shifts below are signed sign-extending shifts (see assumptions.h for tests that that is
         * indeed the behavior of the right shift operator). */
        let mut cond_add = r8 >> 31;
        r0 += mod_info.modulus.v[0] & cond_add;
        r1 += mod_info.modulus.v[1] & cond_add;
        r2 += mod_info.modulus.v[2] & cond_add;
        r3 += mod_info.modulus.v[3] & cond_add;
        r4 += mod_info.modulus.v[4] & cond_add;
        r5 += mod_info.modulus.v[5] & cond_add;
        r6 += mod_info.modulus.v[6] & cond_add;
        r7 += mod_info.modulus.v[7] & cond_add;
        r8 += mod_info.modulus.v[8] & cond_add;
        let cond_negate = sign >> 31;
        r0 = (r0 ^ cond_negate) - cond_negate;
        r1 = (r1 ^ cond_negate) - cond_negate;
        r2 = (r2 ^ cond_negate) - cond_negate;
        r3 = (r3 ^ cond_negate) - cond_negate;
        r4 = (r4 ^ cond_negate) - cond_negate;
        r5 = (r5 ^ cond_negate) - cond_negate;
        r6 = (r6 ^ cond_negate) - cond_negate;
        r7 = (r7 ^ cond_negate) - cond_negate;
        r8 = (r8 ^ cond_negate) - cond_negate;
        /* Propagate the top bits, to bring limbs back to range (-2^30,2^30). */
        r1 += r0 >> 30;
        r0 &= M30;
        r2 += r1 >> 30;
        r1 &= M30;
        r3 += r2 >> 30;
        r2 &= M30;
        r4 += r3 >> 30;
        r3 &= M30;
        r5 += r4 >> 30;
        r4 &= M30;
        r6 += r5 >> 30;
        r5 &= M30;
        r7 += r6 >> 30;
        r6 &= M30;
        r8 += r7 >> 30;
        r7 &= M30;

        /* In a second step add the modulus again if the result is still negative, bringing r to range
         * [0,modulus). */
        cond_add = r8 >> 31;
        r0 += mod_info.modulus.v[0] & cond_add;
        r1 += mod_info.modulus.v[1] & cond_add;
        r2 += mod_info.modulus.v[2] & cond_add;
        r3 += mod_info.modulus.v[3] & cond_add;
        r4 += mod_info.modulus.v[4] & cond_add;
        r5 += mod_info.modulus.v[5] & cond_add;
        r6 += mod_info.modulus.v[6] & cond_add;
        r7 += mod_info.modulus.v[7] & cond_add;
        r8 += mod_info.modulus.v[8] & cond_add;
        /* And propagate again. */
        r1 += r0 >> 30;
        r0 &= M30;
        r2 += r1 >> 30;
        r1 &= M30;
        r3 += r2 >> 30;
        r2 &= M30;
        r4 += r3 >> 30;
        r3 &= M30;
        r5 += r4 >> 30;
        r4 &= M30;
        r6 += r5 >> 30;
        r5 &= M30;
        r7 += r6 >> 30;
        r6 &= M30;
        r8 += r7 >> 30;
        r7 &= M30;

        if cfg!(feature = "verify") {
            assert_eq!(r0 >> 30, 0);
            assert_eq!(r1 >> 30, 0);
            assert_eq!(r2 >> 30, 0);
            assert_eq!(r3 >> 30, 0);
            assert_eq!(r4 >> 30, 0);
            assert_eq!(r5 >> 30, 0);
            assert_eq!(r6 >> 30, 0);
            assert_eq!(r7 >> 30, 0);
            assert_eq!(r8 >> 30, 0);
            assert!(self.mul_cmp(9, &mod_info.modulus, 0) >= 0); /* r >= 0 */
            assert!(self.mul_cmp(9, &mod_info.modulus, 1) < 0); /* r < modulus */
        }

        self.v[0] = r0;
        self.v[1] = r1;
        self.v[2] = r2;
        self.v[3] = r3;
        self.v[4] = r4;
        self.v[5] = r5;
        self.v[6] = r6;
        self.v[7] = r7;
        self.v[8] = r8;
    }

    /// Compute the inverse of x modulo MOD_INFO->modulus, and replace x with it (constant time in x).
    pub fn modinv_field(&mut self) {
        self.modinv_with_info(&FIELD_MOD_INFO);
    }

    pub fn modinv_scalar(&mut self) {
        self.modinv_with_info(&SCALAR_MOD_INFO);
    }

    pub fn modinv_with_info(&mut self, mod_info: &ModInfo) {
        /* Start with d=0, e=1, f=modulus, g=x, zeta=-1. */
        let mut d = Signed30 { v: [0; 9] };
        let mut e = Signed30 { v: [1, 0, 0, 0, 0, 0, 0, 0, 0] };
        let mut f = mod_info.modulus.clone();
        let mut g = self.clone();
        let mut zeta = -1i32; /* zeta = -(delta+1/2); delta is initially 1/2. */

        /* Do 20 iterations of 30 divsteps each = 600 divsteps. 590 suffices for 256-bit inputs. */
        for _i in 0..20 {
            /* Compute transition matrix and new zeta after 30 divsteps. */
            let t = Trans2x2::divsteps(&mut zeta, f.v[0] as u32, g.v[0] as u32);
            /* Update d,e using that transition matrix. */
            t.update_de(&mut d, &mut e, &mod_info);
            /* Update f,g using that transition matrix. */
            if cfg!(feature = "verify") {
                assert!(f.mul_cmp(9, &mod_info.modulus, -1) > 0); /* f > -modulus */
                assert!(f.mul_cmp(9, &mod_info.modulus, 1) <= 0); /* f <= modulus */
                assert!(g.mul_cmp(9, &mod_info.modulus, -1) > 0); /* g > -modulus */
                assert!(g.mul_cmp(9, &mod_info.modulus, 1) < 0); /* g <  modulus */
            }
            t.update_fg(&mut f, &mut g);
            if cfg!(feature = "verify") {
                assert!(f.mul_cmp(9, &mod_info.modulus, -1) > 0); /* f > -modulus */
                assert!(f.mul_cmp(9, &mod_info.modulus, 1) <= 0); /* f <= modulus */
                assert!(g.mul_cmp(9, &mod_info.modulus, -1) > 0); /* g > -modulus */
                assert!(g.mul_cmp(9, &mod_info.modulus, 1) < 0); /* g <  modulus */
            }
        }

        /* At this point sufficient iterations have been performed that g must have reached 0
         * and (if g was not originally 0) f must now equal +/- GCD of the initial f, g
         * values i.e. +/- 1, and d now contains +/- the modular inverse. */
        if cfg!(feature = "verify") {
            let one = Signed30 { v: [1, 0, 0, 0, 0, 0, 0, 0, 0] };
            /* g == 0 */
            assert_eq!(g.mul_cmp(9, &one, 0), 0);
            /* |f| == 1, or (x == 0 and d == 0 and |f|=modulus) */
            assert!(
                f.mul_cmp(9, &one, -1) == 0
                    || f.mul_cmp(9, &one, 1) == 0
                    || (self.mul_cmp(9, &one, 0) == 0
                        && d.mul_cmp(9, &one, 0) == 0
                        && (f.mul_cmp(9, &mod_info.modulus, 1) == 0
                            || f.mul_cmp(9, &mod_info.modulus, -1) == 0))
            );
        }

        /* Optionally negate d, normalize to [0,modulus), and return it. */
        d.normalize_with_info(f.v[8], &mod_info);
        *self = d;
    }

    /* Test functions */
    pub fn from_u16(d: [u16; 16]) -> Self {
        let mut r = Self::new();
        for i in 0..256 {
            r.v[i / 30] |= (((d[i >> 4] >> (i & 15)) & 1) as i32) << (i % 30) as i32;
        }
        r
    }

    pub fn to_u16(&self) -> [u16; 16] {
        let mut out = [0; 16];

        for i in 0..256 {
            out[i >> 4] |= (((self.v[i / 30] >> (i as i32 % 30)) & 1) << (i & 15)) as u16;
        }

        out
    }

    pub fn mutate(&mut self, positions: &[usize; 16]) {
        for &pos in positions {
            if self.v[pos] > 0 && self.v[pos + 1] <= 0x3fffffff {
                self.v[pos] -= 0x40000000;
                self.v[pos + 1] += 1;
            } else if self.v[pos] < 0 && self.v[pos + 1] >= 0x3fffffff {
                self.v[pos] += 0x40000000;
                self.v[pos + 1] -= 1;
            }
        }
    }
    /* End test functions */
}

/// Data type for transition matrices (see section 3 of explanation).
///
/// t = [ u  v ]
///     [ q  r ]
pub struct Trans2x2 {
    u: i32,
    v: i32,
    q: i32,
    r: i32,
}

impl Trans2x2 {
    pub fn new() -> Self {
        Self {
            u: 0,
            v: 0,
            q: 0,
            r: 0,
        }
    }

    /// Compute the transition matrix and zeta for 30 divsteps.
    ///
    /// Input:  zeta: initial zeta
    ///         f0:   bottom limb of initial f
    ///         g0:   bottom limb of initial g
    /// Output: t: transition matrix
    /// Return: final zeta
    ///
    /// Implements the divsteps_n_matrix function from the explanation.
    pub fn divsteps(zeta: &mut i32, f0: u32, g0: u32) -> Self {
        /* u,v,q,r are the elements of the transformation matrix being built up,
         * starting with the identity matrix. Semantically they are signed integers
         * in range [-2^30,2^30], but here represented as unsigned mod 2^32. This
         * permits left shifting (which is UB for negative numbers). The range
         * being inside [-2^31,2^31) means that casting to signed works correctly.
         */
        let (mut u, mut v, mut q, mut r) = (1u32, 0u32, 0u32, 1u32);
        let (mut f, mut g) = (f0, g0);

        for i in 0..30 {
            assert_eq!(f & 1, 1); /* f must always be odd */
            assert_eq!(
                u.overflowing_mul(f0)
                    .0
                    .overflowing_add(v.overflowing_mul(g0).0)
                    .0,
                f << i
            );
            assert_eq!(
                q.overflowing_mul(f0)
                    .0
                    .overflowing_add(r.overflowing_mul(g0).0)
                    .0,
                g << i
            );
            /* Compute conditional masks for (zeta < 0) and for (g & 1). */
            let mut c1 = (*zeta >> 31) as u32;
            let c2 = -((g & 1) as i32) as u32;
            /* Compute x,y,z, conditionally negated versions of f,u,v. */
            let x = (f ^ c1).overflowing_sub(c1).0;
            let y = (u ^ c1).overflowing_sub(c1).0;
            let z = (v ^ c1).overflowing_sub(c1).0;
            /* Conditionally add x,y,z to g,q,r. */
            g = g.overflowing_add(x & c2).0;
            q = q.overflowing_add(y & c2).0;
            r = r.overflowing_add(z & c2).0;
            /* In what follows, c1 is a condition mask for (zeta < 0) and (g & 1). */
            c1 &= c2;
            /* Conditionally change zeta into -zeta-2 or zeta-1. */
            *zeta = (*zeta ^ c1 as i32) - 1;
            /* Conditionally add g,q,r to f,u,v. */
            f = f.overflowing_add(g & c1).0;
            u = u.overflowing_add(q & c1).0;
            v = v.overflowing_add(r & c1).0;
            /* Shifts */
            g >>= 1;
            u <<= 1;
            v <<= 1;
            /* Bounds on zeta that follow from the bounds on iteration count (max 20*30 divsteps). */
            assert!(*zeta >= -601 && *zeta <= 601);
        }

        /* The determinant of t must be a power of two. This guarantees that multiplication with t
         * does not change the gcd of f and g, apart from adding a power-of-2 factor to it (which
         * will be divided out again). As each divstep's individual matrix has determinant 2, the
         * aggregate of 30 of them will have determinant 2^30. */
        let det = u.overflowing_mul(r).0.overflowing_sub(v.overflowing_mul(q).0).0 as i32;
        let exp_det = 1 << 30;
        assert_eq!(det, exp_det, "determinant: {:16x}, expected: {:16x}", det, exp_det);

        Self { u: u as i32, v: v as i32, q: q as i32, r: r as i32 }
    }

    /// Compute (t/2^30) * [d, e] mod modulus, where t is a transition matrix for 30 divsteps.
    ///
    /// On input and output, d and e are in range (-2*modulus,modulus). All output limbs will be in range
    /// (-2^30,2^30).
    ///
    /// This implements the update_de function from the explanation.
    pub fn update_de(&self, d: &mut Signed30, e: &mut Signed30, mod_info: &ModInfo) {
        let (u, v, q, r) = (self.u, self.v, self.q, self.r);

        if cfg!(feature = "verify") {
            assert!(d.mul_cmp(9, &mod_info.modulus, -2) > 0); /* d > -2*modulus */
            assert!(d.mul_cmp(9, &mod_info.modulus, 1) < 0); /* d <    modulus */
            assert!(e.mul_cmp(9, &mod_info.modulus, -2) > 0); /* e > -2*modulus */
            assert!(e.mul_cmp(9, &mod_info.modulus, 1) < 0); /* e <    modulus */
            assert!(u.abs() + v.abs() >= 0); /* |u|+|v| doesn't overflow */
            assert!(q.abs() + r.abs() >= 0); /* |q|+|r| doesn't overflow */
            assert!(u.abs() + v.abs() <= M30 + 1); /* |u|+|v| <= 2^30 */
            assert!(q.abs() + r.abs() <= M30 + 1); /* |q|+|r| <= 2^30 */
        }
        /* [md,me] start as zero; plus [u,q] if d is negative; plus [v,r] if e is negative. */
        let sd = d.v[8] >> 31;
        let se = e.v[8] >> 31;
        let mut md = ((u & sd) + (v & se)) as i32;
        let mut me = ((q & sd) + (r & se)) as i32;
        /* Begin computing t*[d,e]. */
        let mut di = d.v[0] as i32;
        let mut ei = e.v[0] as i32;
        let mut cd = u.overflowing_mul(di).0.overflowing_add(v.overflowing_mul(ei).0).0 as i64;
        let mut ce = q.overflowing_mul(di).0.overflowing_add(r.overflowing_mul(ei).0).0 as i64;
        /* Correct md,me so that t*[d,e]+modulus*[md,me] has 30 zero bottom bits. */
        md -= ((mod_info.modulus_inv30)
               .overflowing_mul(cd as u32)
               .0
               .overflowing_add(md as u32)
               .0) as i32
               & M30 as i32;
        me -= ((mod_info.modulus_inv30)
               .overflowing_mul(ce as u32)
               .0
               .overflowing_add(me as u32)
               .0) as i32
               & M30 as i32;
        /* Update the beginning of computation for t*[d,e]+modulus*[md,me] now md,me are known. */
        cd += (mod_info.modulus.v[0] as i64) * md as i64;
        ce += (mod_info.modulus.v[0] as i64) * me as i64;
        /* Verify that the low 30 bits of the computation are indeed zero, and then throw them away. */
        assert_eq!((cd as i32 & M30), 0);
        cd >>= 30;
        assert_eq!(ce as i32 & M30, 0);
        ce >>= 30;
        /* Now iteratively compute limb i=1..8 of t*[d,e]+modulus*[md,me], and store them in output
         * limb i-1 (shifting down by 30 bits). */
        for i in 1..9 {
            di = d.v[i];
            ei = e.v[i];
            cd += u as i64 * di as i64 + v as i64 * ei as i64;
            ce += q as i64 * di as i64 + r as i64 * ei as i64;
            cd += mod_info.modulus.v[i] as i64 * md as i64;
            ce += mod_info.modulus.v[i] as i64 * me as i64;
            d.v[i - 1] = cd as i32 & M30;
            cd >>= 30;
            e.v[i - 1] = ce as i32 & M30;
            ce >>= 30;
        }
        if cfg!(feature = "verify") {
            assert!(d.mul_cmp(9, &mod_info.modulus, -2) > 0); /* d > -2*modulus */
            assert!(d.mul_cmp(9, &mod_info.modulus, 1) < 0); /* d <    modulus */
            assert!(e.mul_cmp(9, &mod_info.modulus, -2) > 0); /* e > -2*modulus */
            assert!(e.mul_cmp(9, &mod_info.modulus, 1) < 0); /* e <    modulus */
        }
        /* What remains is limb 9 of t*[d,e]+modulus*[md,me]; store it as output limb 8. */
        d.v[8] = cd as i32;
        e.v[8] = ce as i32;
    }

    /// Compute (t/2^30) * [f, g], where t is a transition matrix for 30 divsteps.
    ///
    /// This implements the update_fg function from the explanation.
    pub fn update_fg(&self, f: &mut Signed30, g: &mut Signed30) {
        let (u, v, q, r) = (self.u, self.v, self.q, self.r);
        /* Start computing t*[f,g]. */
        let (mut fi, mut gi) = (f.v[0], g.v[0]);
        let mut cf = u as i64 * fi as i64 + v as i64 * gi as i64;
        let mut cg = q as i64 * fi as i64 + r as i64 * gi as i64;
        /* Verify that the bottom 30 bits of the result are zero, and then throw them away. */
        assert_eq!(cf as i32 & M30, 0);
        cf >>= 30;
        assert_eq!(cg as i32 & M30, 0);
        cg >>= 30;
        /* Now iteratively compute limb i=1..8 of t*[f,g], and store them in output limb i-1 (shifting
         * down by 30 bits). */
        for i in 1..9 {
            fi = f.v[i];
            gi = g.v[i];
            cf += u as i64 * fi as i64 + v as i64 * gi as i64;
            cg += q as i64 * fi as i64 + r as i64 * gi as i64;
            f.v[i - 1] = cf as i32 & M30;
            cf >>= 30;
            g.v[i - 1] = cg as i32 & M30;
            cg >>= 30;
        }
        /* What remains is limb 9 of t*[f,g]; store it as output limb 8. */
        f.v[8] = cf as i32;
        g.v[8] = cg as i32;
    }
}
