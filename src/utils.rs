use core::fmt::{self, Write};
use heapless::String;

pub fn to_hex(b: &[u8]) -> Result<String<64>, fmt::Error> {
    let mut h: String<64> = String::new();
    for _b in &b[..32] {
        write!(h, "{:02x}", _b)?;
    }
    Ok(h)
}

