use crate::endian::Endian;

#[inline(always)]
pub const fn reverse32(d: &[u32; 8]) -> [u32; 8] {
    [d[7], d[6], d[5], d[4], d[3], d[2], d[1], d[0]]
}

#[inline(always)]
pub fn cmp<T: PartialOrd, const N: usize>(a: &[T; N], b: &[T; N], endian: Endian) -> i8 {
    let mut ret = 0;
    let mut inner_loop = |av, bv| {
        let r = ((av < bv) as i8 * -1) + ((av > bv) as i8 * 1);
        ret += (r != 0) as i8 * (ret == 0) as i8 * r;
    };
    match endian {
        Endian::Little => {
            for (av, bv) in a.iter().zip(b.iter()).rev() {
                inner_loop(av, bv);
            }
        },
        Endian::Big => {
            for (av, bv) in a.iter().zip(b.iter()) {
                inner_loop(av, bv);
            }
        },
    };
    ret
}
