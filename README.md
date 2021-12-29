# Rust Firmware Experiments for the Sipeed Longan Nano

Some code to test out ideas and projects using embedded Rust on the [Longan Nano](https://longan.sipeed.com)

## Setup

- [stm32flash](https://sourceforge.net/projects/stm32flash/)
- [riscv32-elf-objcopy](https://github.com/riscv-mcu/riscv-binutils-gdb)
- [longan-nano](https://longan.sipeed.com)
- [Rust 1.51+](https://rustup.rs)

## Building

Install (or update) the `riscv32imac-unknown-none-elf` target:

```
rustup target add riscv32imac-unknown-none-elf
```

Then run the release build for the project:

```
$ cargo build --release
```

which produces the firmware binary (cross-compiled to `riscv32imac-unknown-none-elf` target).

Next, to create the raw firmware binary using objcopy from riscv32 binutils:

```
$ riscv32-elf-objcopy -O binary target/riscv32imac-unknown-elf/release/<project-name> firmware.bin
```

where `<project-name>` is replaced with the name of the crate.

## Flashing over other protocols

- dfu-util: https://github.com/riscv-rust/longan-nano#using-dfu-util-for-flashing
- openocd: https://github.com/riscv-rust/longan-nano#using-openocd-for-flashing-and-debugging
- rv-link: https://github.com/riscv-rust/longan-nano#using-rv-link-for-flashing-and-debugging
- serial: https://github.com/riscv-rust/longan-nano#using-serial-for-flashing

## Troubleshooting

If there is an error when flashing the Longan Nano, check if the device is in DFU-mode, and that `/dev/ttyUSB0` is writeable by the current user (or run `stm32flash` as root).

To enter DFU-mode:

- press and hold the `BOOT0` button
- press and release the `RESET` button
- release the `BOOT0` button

or

- press and hold the `BOOT0` button while device is off
- power on the device
- release the `BOOT0` button

Then, retry flashing the device.
