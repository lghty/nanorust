use longan_nano::hal::{adc::Adc, pac::ADC0};
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

/// Sample ambient temperature readings from the ADC peripheral
///
/// Use the sampled readings to seed a ChaCha20 CSPRNG
///
/// ***WARNING***: vulnerable to physical attacks against the ADC peripheral
///
/// For sensitive cryptographic applications use another source of entropy,
/// like boards with Zkr instructions from the RISC-V Cryptography extension: https://github.com/riscv/riscv-crypto
///
/// The Longan Nano doesn't support Zkr instructions, so this is a temporary best-effort to at
/// least sample *some* physical entropy.
pub fn adc_rng(adc0: &mut Adc<ADC0>) -> ChaCha20Rng {
    let mut seed = [0u8; 32];
    for germ in seed.chunks_exact_mut(4) {
        germ.swap_with_slice(&mut adc0.read_temp().to_le_bytes());
    }
    ChaCha20Rng::from_seed(seed)
}
