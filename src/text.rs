use embedded_graphics::mono_font::{ascii::FONT_6X13_BOLD, MonoTextStyleBuilder};
use embedded_graphics::pixelcolor::Rgb565;
use embedded_graphics::prelude::*;
use embedded_graphics::primitives::{PrimitiveStyle, Rectangle};
use embedded_graphics::text::Text;

use heapless::String;

use crate::utils::to_hex;
use longan_nano::lcd::Lcd;

pub fn hash_text(lcd: &mut Lcd, hash: &[u8]) {
    let (width, height) = (lcd.size().width as i32, lcd.size().height as i32);

    let hash_hex = to_hex(hash).unwrap();
    let text0 = "hash";
    let text1 = hex_split::<26>(&hash_hex[..24], 3);
    let text2 = hex_split::<26>(&hash_hex[24..48], 3);
    let text3 = hex_split::<17>(&hash_hex[48..], 2);

    let orange = Rgb565::new(255, 153, 0);

    // Clear screen
    Rectangle::new(Point::new(0, 0), Size::new(width as u32, height as u32))
        .into_styled(PrimitiveStyle::with_fill(Rgb565::BLACK))
        .draw(lcd)
        .unwrap();

    let style = MonoTextStyleBuilder::new()
        .font(&FONT_6X13_BOLD)
        .text_color(orange)
        .background_color(Rgb565::BLACK)
        .build();

    Text::new(
        &text0,
        Point::new((width - (text0.len() * 6) as i32) / 2, 10),
        style,
    )
    .draw(lcd)
    .unwrap();

    let style = MonoTextStyleBuilder::new()
        .font(&FONT_6X13_BOLD)
        .text_color(Rgb565::WHITE)
        .background_color(Rgb565::BLACK)
        .build();

    Text::new(
        &text1,
        Point::new((width - (text1.len() * 6) as i32) / 2, 45),
        style,
    )
    .draw(lcd)
    .unwrap();

    let style = MonoTextStyleBuilder::new()
        .font(&FONT_6X13_BOLD)
        .text_color(orange)
        .background_color(Rgb565::BLACK)
        .build();

    Text::new(
        &text2,
        Point::new((width - (text2.len() * 6) as i32) / 2, 60),
        style,
    )
    .draw(lcd)
    .unwrap();

    let style = MonoTextStyleBuilder::new()
        .font(&FONT_6X13_BOLD)
        .text_color(Rgb565::WHITE)
        .background_color(Rgb565::BLACK)
        .build();

    Text::new(
        &text3,
        Point::new((width - (text3.len() * 6) as i32) / 2, 75),
        style,
    )
    .draw(lcd)
    .unwrap();
}

fn hex_split<const N: usize>(hex_str: &str, groups: u8) -> String<N> {
    let mut s: String<N> = String::new();
    let hex = hex_str.as_bytes();
    match groups {
        2 => {
            for &b in &hex[..8] {
                s.push(b as char).unwrap();
            }
            s.push(' ').unwrap();
            for &b in &hex[8..] {
                s.push(b as char).unwrap();
            }
            s
        }
        3 => {
            for &b in &hex[..8] {
                s.push(b as char).unwrap();
            }
            s.push(' ').unwrap();
            for &b in &hex[8..16] {
                s.push(b as char).unwrap();
            }
            s.push(' ').unwrap();
            for &b in &hex[16..] {
                s.push(b as char).unwrap();
            }
            s
        }
        _ => unreachable!("bad hex groups"),
    }
}
