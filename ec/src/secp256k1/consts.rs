use super::modinv::{ModInfo, Signed30};

pub const M30: i32 = (core::u32::MAX >> 2) as i32;

pub const FIELD_MOD_INFO: ModInfo = ModInfo {
    modulus: Signed30 {
        v: [-0x3d1, -4, 0, 0, 0, 0, 0, 0, 65536],
    },
    modulus_inv30: 0x2ddacacf,
};

pub const SCALAR_MOD_INFO: ModInfo = ModInfo {
    modulus: Signed30 {
        v: [
            0x10364141, 0x3f497a33, 0x348a03bb, 0x2bb739ab, -0x146, 0, 0, 0, 65536,
        ],
    },
    modulus_inv30: 0x2a774ec1,
};
