#![no_std]
#![no_main]

use panic_halt as _;

use longan_nano::hal::{adc::Adc, delay::McycleDelay, pac, prelude::*};
use longan_nano::{lcd, lcd_pins};
use rand_chacha::rand_core::RngCore;
use riscv_rt::entry;

mod led;
mod rand;
mod text;
mod utils;

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();

    // Configure clocks
    let mut rcu = dp
        .RCU
        .configure()
        .ext_hf_clock(8.mhz())
        .sysclk(108.mhz())
        .freeze();
    let mut afio = dp.AFIO.constrain(&mut rcu);

    // Split GPIO pins to drive LCD screen and LED lights
    let gpioa = dp.GPIOA.split(&mut rcu);
    let gpiob = dp.GPIOB.split(&mut rcu);

    // Configure the LCD
    let lcd_pins = lcd_pins!(gpioa, gpiob);
    let mut lcd = lcd::configure(dp.SPI0, lcd_pins, &mut afio, &mut rcu);

    // Get random bytes seeded from ADC ambient temperature readings
    // Uses the seed as input to a ChaCha20 CSPRNG
    let mut adc0 = Adc::adc0(dp.ADC0, &mut rcu);
    let mut rng = rand::adc_rng(&mut adc0);
    let mut rand128 = [0u8; 16];

    let mut delay = McycleDelay::new(&rcu.clocks);

    loop {
        for chunk in rand128.chunks_exact_mut(8) {
            chunk.swap_with_slice(&mut rng.next_u64().to_le_bytes());
        }

        // Hash random bytes
        let mut hasher = hashes::Sha256::new();
        hasher.update(&rand128);
        let hash = hasher.finalize();

        // Draw text to the LCD
        text::hash_text(&mut lcd, hash.as_ref());
        delay.delay_ms(1729);
    }
}
