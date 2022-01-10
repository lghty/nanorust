#[derive(Debug)]
pub enum Error {
    InvalidBitIndex,
    InvalidMagnitude,
    InvalidSquareRoot,
    ScalarAdditionOverflow,
    ScalarOverflow,
}
