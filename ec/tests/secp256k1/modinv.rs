use super::consts::{CASES, RANDOM_CASE_LEN};
use ec::secp256k1::modinv::{ModInfo, Signed30};

use rand::{thread_rng, Rng, rngs::ThreadRng};

fn modinv2p64(x: u64) -> u64 {
    /* If w = 1/x mod 2^(2^L), then w*(2 - w*x) = 1/x mod 2^(2^(L+1)). See
     * Hacker's Delight second edition, Henry S. Warren, Jr., pages 245-247 for
     * why. Start with L=0, for which it is true for every odd x that
     * 1/x=1 mod 2. Iterating 6 times gives us 1/x mod 2^64. */
    let mut w = 1u64;
    assert!(x & 1 != 0);
    for _ in 0..6 {
        w = w.overflowing_mul(2u64.overflowing_sub(w.overflowing_mul(x).0).0).0;
    }
    w
}

/* compute out = (a*b) mod m; if b=NULL, treat b=1.
 *
 * Out is a 512-bit number (represented as 32 uint16_t's in LE order). The other
 * arguments are 256-bit numbers (represented as 16 uint16_t's in LE order). */
fn mulmod256(a: &[u16; 16], b: Option<&[u16; 16]>, m: &[u16; 16]) -> [u16; 32] {
    let mut c = 0u64;
    let (mut m_bitlen, mut mul_bitlen) = (0i32, 0i32);
    let mut mul = [0u16; 32];

    if let Some(b) = b {
        /* Compute the product of a and b, and put it in mul. */
        for i in 0..32 {
            let r = if i < 16 { 0 } else { i - 15 };
            let s = core::cmp::min(i + 1, 16);
            for j in r..s {
                c += a[j] as u64 * b[i - j] as u64;
            }
            mul[i] = (c & 0xffff) as u16;
            c >>= 16;
        }
        debug_assert_eq!(c, 0);

        /* compute the highest set bit in mul */
        for i in (0..512).rev() {
            if (mul[i >> 4] >> (i & 15)) & 1 != 0 {
                mul_bitlen = i as i32;
                break;
            }
        }
    } else {
        /* if b==NULL, set mul=a. */
        mul[..16].copy_from_slice(a);
        /* compute the highest set bit in mul */
        for i in (0..256).rev() {
            if (mul[i >> 4] >> (i & 15)) & 1 != 0 {
                mul_bitlen = i as i32;
                break;
            }
        }
    }

    /* Compute the highest set bit in m. */
    for i in (0..256).rev() {
        if (m[i >> 4] >> (i & 15)) & 1 != 0 {
            m_bitlen = i as i32;
            break;
        }
    }

    /* Try do mul -= m<<i, for i going down to 0, whenever the result is not negative */
    let mut i = mul_bitlen - m_bitlen;
    while i >= 0 {
        /* Compute mul2 = mul - m<<i. */
        let mut mul2 = [0u16; 32];
        let mut cs = 0i64; /* accumulator */
        for j in 0..32usize {
            /* j loops over the output limbs in mul2. */
            /* Compute sub: the 16 bits in m that will be subtracted from mul2[j]. */
            let mut sub = 0u16;
            for p in 0..16 {
                /* p loops over the bit positions in mul2[j]. */
                let bitpos = j as i32 * 16i32 - i as i32 + p as i32; /* bitpos is the correspond bit position in m. */
                if bitpos >= 0 && bitpos < 256 {
                    let bitpos = bitpos as usize;
                    sub |= (((m[bitpos >> 4] >> (bitpos & 15) as u16) & 1) as u16) << (p as u16);
                }
            }
            /* Add mul[j]-sub to accumulator, and shift bottom 16 bits out to mul2[j]. */
            cs += mul[j] as i64;
            cs -= sub as i64;
            mul2[j] = (cs & 0xffff) as u16;
            cs >>= 16;
        }
        /* If remainder of subtraction is 0, set mul = mul2. */
        if cs == 0 {
            mul = mul2;
        }
        i -= 1;
    }
    /* Sanity check: test that all limbs higher than m's highest are zero */
    for i in ((m_bitlen >> 4) + 1) as usize..32 {
        assert_eq!(mul[i], 0);
    }
    mul
}

fn coprime(a: &[u16; 16], b: &[u16; 16]) -> bool {
    let (mut x, mut y) = (a.clone(), b.clone());
    loop {
        let mut iszero = true;
        for xi in x {
            if xi != 0 {
                iszero = false;
                break;
            }
        }
        if iszero { break };
        let mut t = mulmod256(&y, None, &x);
        y.swap_with_slice(&mut x);
        x.swap_with_slice(&mut t[..16]);
    }

    !(y[0] != 1 || &y[1..] != &[0; 15][..])
}

fn test_sixteen_bit_limbs(rng: &mut ThreadRng, in16: &[u16; 16], mod16: &[u16; 16]) -> [u16; 16] {
    let mut x = Signed30::from_u16(in16.clone());
    let nonzero = !x.is_zero();
    let mut m = ModInfo::from(Signed30::from_u16(mod16.clone()));

    let mut pos_a = [0usize; 16];
    for pos in pos_a.iter_mut() {
        *pos = rng.gen_range(0..8);
    }
    m.modulus_mut().mutate(&pos_a);

    /* compute 1/modulus mod 2^30 */
    m.set_modulus_inv30((modinv2p64(m.modulus().v()[0] as u64) & 0x3fffffff) as u32);
    assert_eq!(
        ((m.modulus_inv30() as i64 * m.modulus().v()[0] as i64) & 0x3fffffff) as i32,
        1
    );

    /* compute inverse */
    x.modinv_with_info(&m);

    /* produce output */
    let out = x.to_u16();

    /* check if the inverse times the input is 1 (mod m), unless x is 0. */
    let tmp = mulmod256(&out, Some(in16), mod16);
    assert_eq!(tmp[0], nonzero as u16);
    assert_eq!(&tmp[1..], &[0u16; 31][..]);

    /* invert again */
    x.modinv_with_info(&m);

    /* check if the result is equal to the input */
    assert_eq!(&x.to_u16(), in16);

    out
}

fn test_random_input_and_modulus(rng: &mut ThreadRng) -> usize {
    let mut passed = 0;
    let mut ok = false;
    for i in 0..RANDOM_CASE_LEN {
        let [mut xd, mut md, zero] = [[0u16; 16]; 3];
        while !(ok && coprime(&xd, &md)) {
            rng.fill(&mut xd);
            rng.fill(&mut md);
            md[0] |= 1;
            ok = md[0] != 1;
            for &m in md[1..].iter() {
                ok |= m != 0;
            }
            let mut tmp = mulmod256(&xd, None, &md);
            xd.swap_with_slice(&mut tmp[..16]);
        }
        let _ = test_sixteen_bit_limbs(rng, &xd, &md);
        if i < 50 {
            let _ = test_sixteen_bit_limbs(rng, &zero, &md);
        }
        passed += 1;
    }
    passed
}

#[test]
fn run_libsecp256k1_cases() {
    let mut passed = 0;
    let cases = CASES;

    let mut rng = thread_rng();

    for case in cases.iter() {
        let tmp = mulmod256(&case[0], Some(&case[2]), &case[1]);
        assert_eq!(tmp[0], 1);
        assert_eq!(&tmp[1..], &[0; 31][..]);
        if test_sixteen_bit_limbs(&mut rng, &case[0], &case[1]) == case[2] {
            passed += 1;
        }
    }

    passed += test_random_input_and_modulus(&mut rng);
    let total = cases.len() + RANDOM_CASE_LEN;
    let failed = total - passed;

    assert_eq!(passed, total, "Passed: {}, Failed: {}, Total: {}", passed, failed, total);
}

#[test]
fn cmp() {
    let a = Signed30::from([0, 0, 0, 0, 0, 0, 0, 0, 1]);
    let b = Signed30::from([0, 0, 0, 0, 0, 0, 0, 1, 1]);
    let c = Signed30::from([0, 0, 0, 0, 0, 0, 1, 0, 0]);

    assert_eq!(a.cmp(&a), 0);
    assert_eq!(a.cmp(&b), -1);
    assert_eq!(a.cmp(&c), -1);
    assert_eq!(c.cmp(&a), 1);
    assert_eq!(c.cmp(&b), 1);
}
