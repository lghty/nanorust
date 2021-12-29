#![no_std]

/**
 * Copyright (c) 2006-2009 Graydon Hoare
 * Copyright (c) 2009-2013 Mozilla Foundation
 * Copyright (c) 2016 Artyom Pavlov
 * Copyleft (c) 2021 nanorust developers
 *
 * Permission is hereby granted, free of charge, to any
 * person obtaining a copy of this software and associated
 * documentation files (the "Software"), to deal in the
 * Software without restriction, including without
 * limitation the rights to use, copy, modify, merge,
 * publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software
 * is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice
 * shall be included in all copies or substantial portions
 * of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
 * ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
 * TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
 * PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
 * SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
 * IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

mod consts;
mod inner;

use consts::*;
use inner::compress256;

/// Based on the sha2 SHA-256 implementation
///
/// Removes traits to improve performance (no dynamic dispatch).
pub struct Sha256 {
    state: [u32; STATE_LEN],
    block: [u8; 64],
    block_pos: u64,
    digest_len: u64,
}

impl Sha256 {
    #[inline]
    pub fn new() -> Self {
        Self {
            state: STATE,
            block: [0u8; COMP_BLOCK_LEN],
            block_pos: 0,
            digest_len: 0,
        }
    }

    #[inline]
    pub fn update(&mut self, data: &[u8]) {
        let data_len = data.len();
        let mut rem = COMP_BLOCK_LEN - self.block_pos as usize;
        let mut data_rem = data_len;
        let mut data_pos = 0;

        while data_rem >= rem {
            let block_pos = self.block_pos as usize;

            let block_end = block_pos + rem;
            let data_end = data_pos + rem;
            self.block[block_pos..block_end].copy_from_slice(&data[data_pos..data_end]);

            self.digest_len = self.digest_len + rem as u64;
            self.block_pos = 0;

            data_pos = data_end;
            data_rem = data_rem - rem;

            compress256(&mut self.state, &self.block);

            rem = COMP_BLOCK_LEN;
        }

        if data_rem > 0 {
            let block_pos = self.block_pos as usize;
            let fill_pos = block_pos + data_rem;
            self.block[block_pos..fill_pos].copy_from_slice(&data[data_pos..data_pos+data_rem]);
            self.block_pos = self.block_pos + data_rem as u64;
            self.digest_len = self.digest_len + data_rem as u64;

            if self.block_pos == 64 {
                compress256(&mut self.state, &self.block);
                self.block_pos = 0;
            }
        }
    }

    #[inline]
    pub fn finalize(mut self) -> [u8; 32] {
        let bit_len = 8 * self.digest_len;
        self.digest_pad(&bit_len.to_be_bytes());

        let mut out = [0u8; 32];
        for (chunk, v) in out.chunks_exact_mut(4).zip(self.state.iter()) {
            chunk.copy_from_slice(&v.to_be_bytes());
        }

        out
    }

    #[inline(always)]
    fn digest_pad(&mut self, suffix: &[u8]) {
        let pos = self.block_pos as usize;
        self.block[pos] = 0x80;
        for b in &mut self.block[pos + 1..] {
            *b = 0;
        }

        let n = COMP_BLOCK_LEN - suffix.len();
        if COMP_BLOCK_LEN - pos - 1 < suffix.len() {
            compress256(&mut self.state, &self.block);
            let mut block = [0u8; COMP_BLOCK_LEN];
            block[n..].copy_from_slice(suffix);
            compress256(&mut self.state, &block);
        } else {
            self.block[n..].copy_from_slice(suffix);
            compress256(&mut self.state, &self.block);
        }
        self.block_pos = 0;
    }
}
