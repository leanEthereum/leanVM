//! A run's output: the public half of its statement.

use std::fmt::{self, Display, Formatter};

/// The four words a run outputs: the registers `a0..a3` when it calls exit.
///
/// With the program, it is the whole statement a proof is checked against.
///
/// A Rust guest's output is the digest of the values it commits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Output([u64; 4]);

impl Output {
    /// The output of these four words, `a0` first.
    #[must_use]
    pub const fn new(words: [u64; 4]) -> Self {
        Self(words)
    }

    /// The output's four words, `a0` first.
    #[must_use]
    pub const fn words(&self) -> &[u64; 4] {
        &self.0
    }
}

impl From<[u64; 4]> for Output {
    fn from(words: [u64; 4]) -> Self {
        Self(words)
    }
}

impl From<Output> for [u64; 4] {
    fn from(output: Output) -> Self {
        output.0
    }
}

impl PartialEq<[u64; 4]> for Output {
    fn eq(&self, words: &[u64; 4]) -> bool {
        self.0 == *words
    }
}

impl Display for Output {
    /// The four words in hexadecimal, `a0` first.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Each word is zero-padded to its 16 hex digits, so the columns line up across outputs.
        let [a0, a1, a2, a3] = self.0;
        write!(f, "{a0:016x} {a1:016x} {a2:016x} {a3:016x}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_displays_each_register_in_order_and_zero_padded() {
        // Fixture state: small, mid-sized, all-ones and zero words, in register order.
        //
        //     a0 = 1,  a1 = 0xab,  a2 = 2^64 - 1,  a3 = 0
        let output = Output::new([1, 0xab, u64::MAX, 0]);

        // Every word is 16 hex digits wide, whatever its size.
        assert_eq!(
            output.to_string(),
            "0000000000000001 00000000000000ab ffffffffffffffff 0000000000000000"
        );
    }
}
