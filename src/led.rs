use longan_nano::hal::{delay::McycleDelay, prelude::*};
use longan_nano::led::{Led, BLUE, GREEN, RED};

/// Loop through led lights
#[allow(unused)]
pub fn led_loop(mut red: RED, mut green: GREEN, mut blue: BLUE, mut delay: McycleDelay) -> ! {
    let leds: [&mut dyn Led; 3] = [&mut red, &mut green, &mut blue];
    let led_delay: u16 = 750;

    let mut i = 0;
    loop {
        let i1 = (i + 1) % leds.len();
        let i2 = (i + 2) % leds.len();
        leds[i].on();
        delay.delay_ms(led_delay);
        leds[i1].on();
        delay.delay_ms(led_delay);
        leds[i].off();
        leds[i2].on();
        delay.delay_ms(led_delay);
        leds[i1].off();
        delay.delay_ms(led_delay);
        leds[i].on();
        delay.delay_ms(led_delay);
        leds[i2].off();
        leds[i].off();

        i = i2;
    }
}
