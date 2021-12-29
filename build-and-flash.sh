#!/usr/bin/env bash

cargo build --release
riscv-nuclei-elf-objcopy -O binary target/riscv32imac-unknown-none-elf/release/nanorust firmware.bin
stm32flash -g 0x08000000 -b 115200 -w firmware.bin /dev/ttyUSB0
