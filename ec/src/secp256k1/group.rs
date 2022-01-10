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

use crate::error::Error;
use super::field::{const_to_field, FieldElement, FieldElementStorage};

/// Generator for secp256k1, value 'g' defined in
/// "Standards for Efficient Cryptography" (SEC2) 2.7.1.
pub const G: GroupElement = GroupElement {
    x: const_to_field([
        0x79be667e, 0xf9dcbbac, 0x55a06295, 0xce870b07, 0x029bfcdb, 0x2dce28d9, 0x59f2815b,
        0x16f81798,
    ]),
    y: const_to_field([
        0x483ada77, 0x26a3c465, 0x5da4fbfc, 0x0e1108a8, 0xfd17b448, 0xa6855419, 0x9c47d08f,
        0xfb10d4b8,
    ]),
    infinity: false,
};

/// Constant value 'b' for the equation y^2 = x^3 + b
pub const B: FieldElement = const_to_field([0, 0, 0, 0, 0, 0, 0, 7]);
pub const LAMBDA: FieldElement = const_to_field([
    0x7ae96a2b, 0x657c0710, 0x6e64479e, 0xac3434e9, 0x9cf04975, 0x12f58995, 0xc1396c28, 0x719501ee,
]);

/// A group element of the secp256k1 curve, in affine coordinates.
#[derive(Clone, Copy)]
pub struct GroupElement {
    x: FieldElement,
    y: FieldElement,
    infinity: bool, // /* whether this represents the point at infinity */
}

impl From<([u32; 8], [u32; 8])> for GroupElement {
    fn from(x_y: ([u32; 8], [u32; 8])) -> Self {
        Self {
            x: FieldElement::from(x_y.0),
            y: FieldElement::from(x_y.1),
            infinity: false,
        }
    }
}

impl GroupElement {
    pub fn new() -> Self {
        Self {
            x: FieldElement::new(),
            y: FieldElement::new(),
            infinity: false,
        }
    }

    pub fn infinity() -> Self {
        Self {
            x: FieldElement::from([0, 0, 0, 0, 0, 0, 0, 0]),
            y: FieldElement::from([0, 0, 0, 0, 0, 0, 0, 0]),
            infinity: true,
        }
    }

    pub fn x(&self) -> &FieldElement {
        &self.x
    }

    pub fn y(&self) -> &FieldElement {
        &self.y
    }

    pub fn is_infinity(&self) -> bool {
        self.infinity
    }

    pub fn set_gej_zinv(&mut self, a: &GroupElementJacobian, zi: &FieldElement) {
        let zi2 = zi.sqr();
        let zi3 = zi2.mul(zi);
        self.x = a.x.mul(&zi2);
        self.y = a.y.mul(&zi3);
        self.infinity = a.infinity;
    }

    pub fn set_gej(&mut self, a: &mut GroupElementJacobian) {
        a.z = a.z.inv();
        let z2 = a.z.sqr();
        let z3 = a.z.mul(&z2);
        a.z.set_int(1);
        self.x = a.x.mul(&z2);
        self.y = a.y.mul(&z3);
        self.infinity = a.infinity;
    }

    pub fn set_xy(&mut self, x: FieldElement, y: FieldElement) {
        self.infinity = false;
        self.x = x;
        self.y = y;
    }

    pub fn negate_assign(&mut self) {
        self.y.normalize_weak();
        self.y.negate_assign();
    }

    pub fn negate(&self) -> Self {
        let mut r = self.clone();
        r.negate_assign();
        r
    }

    pub fn is_valid(&self) -> bool {
        // /* y^2 = x^3 + 7 */
        let y2 = self.y.sqr();
        let mut x3 = self
            .x
            .sqr() // x^2
            .mul(&self.x) // x^3
            .add(&B); // x^3 + B
        x3.normalize_weak();
        // y^2 = x^3 + B and !INFINITY
        (y2.equal(&x3) as u8 * !self.infinity as u8) != 0
    }

    pub fn set_infinity(&mut self) {
        self.infinity = true;
        self.x.clear();
        self.y.clear();
    }

    pub fn clear(&mut self) {
        self.infinity = false;
        self.x.clear();
        self.y.clear();
    }

    pub fn set_xo(&mut self, x: &FieldElement, odd: bool) -> Result<(), Error> {
        self.x = x.clone();
        let x2 = x.sqr();
        let mut x3 = x.mul(&x2);
        self.infinity = false;
        x3.add_assign(&B);

        let mut ret = Ok(());
        match x3.sqrt() {
            Ok(y) => self.y = y.clone(),
            Err(e) => ret = Err(e),
        }
        self.y.normalize();
        let odd_match = self.y.is_odd() == odd;
        self.y = self
            .y
            .negate()
            .mul_int((!odd_match) as u32) // add negation if oddity does not match, else add zero
            .add(&self.y.mul_int(odd_match as u32)); // add Y to re-assign original if oddity match, else add zero
        ret
    }

    pub fn to_storage(&self) -> GroupElementStorage {
        assert!(!self.infinity);

        let mut x = self.x.clone();
        let mut y = self.y.clone();
        x.normalize();
        y.normalize();

        GroupElementStorage {
            x: x.to_storage(),
            y: y.to_storage(),
        }
    }

    pub fn from_storage(a: GroupElementStorage) -> Self {
        Self {
            infinity: false,
            x: FieldElement::from_storage(&a.x),
            y: FieldElement::from_storage(&a.y),
        }
    }

    pub fn mul_lambda(&self) -> Self {
        let mut r = self.clone();
        r.mul_lambda_assign();
        r
    }

    pub fn mul_lambda_assign(&mut self) {
        self.x.mul_assign(&LAMBDA);
    }
}

/// A group element of the secp256k1 curve, in jacobian coordinates.
#[derive(Clone)]
pub struct GroupElementJacobian {
    x: FieldElement, // /* actual X: x/z^2 */
    y: FieldElement, // /* actual Y: y/z^3 */
    z: FieldElement,
    infinity: bool, // /* whether this represents the point at infinity */
}

impl GroupElementJacobian {
    pub fn new() -> Self {
        Self {
            x: FieldElement::new(),
            y: FieldElement::new(),
            z: FieldElement::new(),
            infinity: false,
        }
    }

    pub fn x(&self) -> &FieldElement {
        &self.x
    }

    pub fn y(&self) -> &FieldElement {
        &self.y
    }

    pub fn z(&self) -> &FieldElement {
        &self.z
    }

    pub fn is_infinity(&self) -> bool {
        self.infinity
    }

    pub fn set_infinity(&mut self) {
        self.infinity = true;
        self.x.clear();
        self.y.clear();
        self.z.clear();
    }

    pub fn clear(&mut self) {
        self.infinity = false;
        self.x.clear();
        self.y.clear();
        self.z.clear();
    }

    /// In:
    ///    Eric Brier and Marc Joye, Weierstrass Elliptic Curves and Side-Channel Attacks.
    ///    In D. Naccache and P. Paillier, Eds., Public Key Cryptography, vol. 2274 of Lecture Notes in Computer Science, pages 335-345. Springer-Verlag, 2002.
    ///  we find as solution for a unified addition/doubling formula:
    ///    lambda = ((x1 + x2)^2 - x1 * x2 + a) / (y1 + y2), with a = 0 for secp256k1's curve equation.
    ///    x3 = lambda^2 - (x1 + x2)
    ///    2*y3 = lambda * (x1 + x2 - 2 * x3) - (y1 + y2).
    ///
    ///  Substituting x_i = Xi / Zi^2 and yi = Yi / Zi^3, for i=1,2,3, gives:
    ///    U1 = X1*Z2^2, U2 = X2*Z1^2
    ///    S1 = Y1*Z2^3, S2 = Y2*Z1^3
    ///    Z = Z1*Z2
    ///    T = U1+U2
    ///    M = S1+S2
    ///    Q = T*M^2
    ///    R = T^2-U1*U2
    ///    X3 = 4*(R^2-Q)
    ///    Y3 = 4*(R*(3*Q-2*R^2)-M^4)
    ///    Z3 = 2*M*Z
    ///  (Note that the paper uses xi = Xi / Zi and yi = Yi / Zi instead.)
    ///
    ///  This formula has the benefit of being the same for both addition
    ///  of distinct points and doubling. However, it breaks down in the
    ///  case that either point is infinity, or that y1 = -y2. We handle
    ///  these cases in the following ways:
    ///
    ///    - If b is infinity we simply bail by means of a VERIFY_CHECK.
    ///
    ///    - If a is infinity, we detect this, and at the end of the
    ///      computation replace the result (which will be meaningless,
    ///      but we compute to be constant-time) with b.x : b.y : 1.
    ///
    ///    - If a = -b, we have y1 = -y2, which is a degenerate case.
    ///      But here the answer is infinity, so we simply set the
    ///      infinity flag of the result, overriding the computed values
    ///      without even needing to cmov.
    ///
    ///    - If y1 = -y2 but x1 != x2, which does occur thanks to certain
    ///      properties of our curve (specifically, 1 has nontrivial cube
    ///      roots in our field, and the curve equation has no x coefficient)
    ///      then the answer is not infinity but also not given by the above
    ///      equation. In this case, we cmov in place an alternate expression
    ///      for lambda. Specifically (y1 - y2)/(x1 - x2). Where both these
    ///      expressions for lambda are defined, they are equal, and can be
    ///      obtained from each other by multiplication by (y1 + y2)/(y1 + y2)
    ///      then substitution of x^3 + 7 for y^2 (using the curve equation).
    ///      For all pairs of nonzero points (a, b) at least one is defined,
    ///      so this covers everything.
    pub fn add_ge(&self, b: &GroupElement) -> Self {
        // /* Operations: 7 mul, 5 sqr, 4 normalize, 21 mul_int/add/negate/cmov */
        const FE_1: FieldElement = const_to_field([0, 0, 0, 0, 0, 0, 0, 1]);
        assert!(!b.infinity);

        let zz = self.z.sqr(); // /* z = Z1^2 */
        let mut u1 = self.x.clone();
        u1.normalize_weak(); // /* u1 = U1 = X1*Z2^2 (1) */
        let u2 = b.x.mul(&zz); // /* u2 = U2 = X2*Z1^2 (1) */
        let mut s1 = self.y.clone();
        s1.normalize_weak(); // /* s1 = S1 = Y1*Z2^3 (1) */
        let s2 = b.y.mul(&zz).mul(&self.z); // /* s2 = Y2*Z1^2 (1) */
                                            // /* s2 = S2 = Y2*Z1^3 (1) */
        let mut t = u1.add(&u2); // /* t = T = U1+U2 (2) */
        let m = s1.add(&s2); // /* m = M = S1+S2 (2) */
        let mut rr = t.sqr(); // /* rr = T^2 (1) */
        let mut m_alt = u2.negate(); // /* Malt = -X2*Z1^2 */
        let tt = u1.mul(&m_alt); // /* tt = -U1*U2 (2) */
        rr.add_assign(&tt); // /* rr = R = T^2-U1*U2 (3) */
                            /* If lambda = R/M = 0/0 we have a problem (except in the "trivial"
                             *  case that Z = z1z2 = 0, and this is special-cased later on). */
        let degenerate = m.normalizes_to_zero() && rr.normalizes_to_zero();

        /* This only occurs when y1 == -y2 and x1^3 == x2^3, but x1 != x2.
         * This means either x1 == beta*x2 or beta*x1 == x2, where beta is
         * a nontrivial cube root of one. In either case, an alternate
         * non-indeterminate expression for lambda is (y1 - y2)/(x1 - x2),
         * so we set R/M equal to this. */
        let mut rr_alt = s1.clone();
        rr_alt.mul_int_assign(2); // /* rr = Y1*Z2^3 - Y2*Z1^3 (2) */
        m_alt.add_assign(&u1); // /* Malt = X1*Z2^2 - X2*Z1^2 */
        rr_alt.cmov(&rr, !degenerate);
        m_alt.cmov(&m, !degenerate);
        /* Now Ralt / Malt = lambda and is guaranteed not to be 0/0.
         * From here on out Ralt and Malt represent the numerator
         * and denominator of lambda; R and M represent the explicit
         * expressions x1^2 + x2^2 + x1x2 and y1 + y2. */
        let mut n = m_alt.sqr(); // /* n = Malt^2 (1) */
        let mut q = n.mul(&t); // /* q = Q = T*Malt^2 (1) */
                               /* These two lines use the observation that either M == Malt or M == 0,
                                * so M^3 * Malt is either Malt^4 (which is computed by squaring), or
                                * zero (which is "computed" by cmov). So the cost is one squaring
                                * versus two multiplications. */
        n.sqr_assign();
        n.cmov(&m, degenerate); // /* n = M^3 * Malt (2) */
        t = rr_alt.sqr(); // /* t = Ralt^2 (1) */
        let mut r = Self::new();
        r.z = self.z.mul(&m_alt); // /* r->z = Malt*Z (1) */
        let infinity = r.z.normalizes_to_zero() & !self.infinity;
        r.z.mul_int_assign(2); // /* r->z = Z3 = 2*Malt*Z (2) */
        q.negate_assign(); // /* q = -Q (2) */
        t.add_assign(&q); // /* t = Ralt^2-Q (3) */
        t.normalize_weak();
        r.x = t.clone(); // /* r->x = Ralt^2-Q (1) */
        t.mul_int_assign(2); // /* t = 2*x3 (2) */
        t.add_assign(&q); // /* t = 2*x3 - Q: (4) */
        t.mul_assign(&rr_alt); // /* t = Ralt*(2*x3 - Q) (1) */
        t.add_assign(&n); // /* t = Ralt*(2*x3 - Q) + M^3*Malt (3) */
        t.magnitude = 3;
        r.y = t.negate(); // /* r->y = Ralt*(Q - 2x3) - M^3*Malt (4) */
        r.y.normalize_weak();
        r.x.mul_int_assign(4); // /* r->x = X3 = 4*(Ralt^2-Q) */
        r.y.mul_int_assign(4); // /* r->y = Y3 = 4*Ralt*(Q - 2x3) - 4*M^3*Malt (4) */
                               // /** In case a->infinity == 1, replace r with (b->x, b->y, 1). */
        r.x.cmov(&b.x, self.infinity);
        r.y.cmov(&b.y, self.infinity);
        r.z.cmov(&FE_1, self.infinity);
        r.infinity = infinity;
        r
    }

    pub fn set_ge(&mut self, a: &GroupElement) {
        self.infinity = a.infinity;
        self.x = a.x.clone();
        self.y = a.y.clone();
        self.z.set_int(1);
    }

    pub fn equal_x(&self, x: &FieldElement) -> bool {
        assert!(!self.infinity);
        let mut r = self.z.sqr();
        r.mul_assign(x);
        let mut r2 = self.x.clone();
        r2.normalize_weak();
        r.equal(&r2)
    }

    pub fn negate(&self) -> Self {
        let mut r = self.clone();
        r.y.normalize_weak();
        r.y.negate_assign();
        r
    }

    pub fn negate_assign(&mut self) {
        *self = self.negate();
    }

    /// Operations: 3 mul, 4 sqr, 0 normalize, 12 mul_int/add/negate.
    ///
    /// Note that there is an implementation described at
    ///     https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
    /// which trades a multiply for a square, but in practice this is actually slower,
    /// mainly because it requires more normalizations.
    #[inline(always)]
    pub fn double(&self) -> Self {
        let mut r = self.clone();
        r.double_assign();
        r
    }

    pub fn double_assign(&mut self) {
        let (x, y) = (self.x.clone(), self.y.clone());

        self.z.mul_assign(&y);
        self.z.mul_int_assign(2); // /* Z' = 2*Y*Z (2) */
        let mut t1 = x.sqr();
        t1.mul_int_assign(3); // /* T1 = 3*X^2 (3) */
        let mut t2 = t1.sqr(); // /* T2 = 9*X^4 (1) */
        let mut t3 = y.sqr();
        t3.mul_int_assign(2); // /* T3 = 2*Y^2 (2) */
        let mut t4 = t3.sqr();
        t4.mul_int_assign(2); // /* T4 = 8*Y^4 (2) */
        t3.mul_assign(&x); // /* T3 = 2*X*Y^2 (1) */
        self.x = t3.clone();
        self.x.mul_int_assign(4); // /* X' = 8*X*Y^2 (4) */
        self.x.magnitude = 4;
        self.x.negate_assign(); // /* X' = -8*X*Y^2 (5) */
        self.x.add_assign(&t2); // /* X' = 9*X^4 - 8*X*Y^2 (6) */
        t2.magnitude = 1;
        t2.negate_assign(); // /* T2 = -9*X^4 (2) */
        t3.mul_int_assign(6); // /* T3 = 12*X*Y^2 (6) */
        t3.add_assign(&t2); // /* T3 = 12*X*Y^2 - 9*X^4 (8) */
        self.y = t2.mul(&t3); // /* Y' = 36*X^3*Y^2 - 27*X^6 (1) */
        t4.magnitude = 2;
        t2 = t4.negate(); // /* T2 = -8*Y^4 (3) */
        self.y.add_assign(&t2); // /* Y' = 36*X^3*Y^2 - 27*X^6 - 8*Y^4 (4) */
    }

    /// Operations: 4 mul, 1 sqr
    pub fn rescale(&self, s: &FieldElement) -> Self {
        let mut r = self.clone();
        r.rescale_assign(s);
        r
    }

    pub fn rescale_assign(&mut self, s: &FieldElement) {
        assert!(!s.is_zero());
        let zz = s.sqr();
        self.x.mul_assign(&zz); // /* r->x *= s^2 */
        self.y.mul_assign(&zz);
        self.y.mul_assign(s); // /* r->y *= s^3 */
        self.z.mul_assign(s); // /* r->z *= s   */
    }
}

pub struct GroupElementStorage {
    x: FieldElementStorage,
    y: FieldElementStorage,
}

impl GroupElementStorage {
    pub fn x(&self) -> &FieldElementStorage {
        &self.x
    }

    pub fn y(&self) -> &FieldElementStorage {
        &self.y
    }

    #[inline(always)]
    pub fn cmov(&mut self, oth: &Self, flag: bool) {
        self.x.cmov(oth.x(), flag);
        self.y.cmov(oth.y(), flag);
    }
}

pub fn globalz_set_table_gej<const N: usize>(
    a: &[GroupElementJacobian; N],
    zr: &[FieldElement; N],
) -> ([GroupElement; N], FieldElement) {
    assert!(N > 0);
    let len = N;
    let mut r = [GroupElement::new(); N];
    // /* The z of the final point gives us the "global Z" for the table. */
    r[len - 1].x = a[len - 1].x.clone();
    r[len - 1].y = a[len - 1].y.clone();
    // /* Ensure all y values are in weak normal form for fast negation of points */
    r[len - 1].y.normalize_weak();
    r[len - 1].infinity = false;
    let globalz = a[len - 1].z.clone();
    let mut zs = zr[len - 1].clone();

    // /* Work our way backwards, using the z-ratios to scale the x/y values. */
    for (i, r) in r.iter_mut().rev().enumerate() {
        if i != len - 1 {
            zs.mul_assign(&zr[i]);
        } else {
            // /* Spin for constant-time */
            let _ = zs.mul(&zr[i]);
        }
        r.set_gej_zinv(&a[i], &zs);
    }

    (r, globalz)
}
