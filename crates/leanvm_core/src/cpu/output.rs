//! A run's output: the public half of its statement.
//!
//! A run that verifies proofs in the guest assumes them: its output then also commits to those assumptions.

use primitives::hash::{Hasher, digest_words};
use std::fmt::{self, Display, Formatter};

/// The four words a run outputs: the registers `a0..a3` when it calls exit.
///
/// With the program, it is the whole statement a proof is checked against.
///
/// A Rust guest's output is the digest of the values it commits, or, if it assumed proofs, that digest and its
/// assumptions hashed together ([`Output::assuming`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Output([u64; 4]);

/// A proof a run assumes: a run of the program of this digest exits with this output.
///
/// A guest records one with `leanvm_guest::verify_proof`, which proves nothing by itself: its run's proof holds only
/// once a proof of each assumption is given, which an aggregation tree that resolves them checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Assumption {
    /// The assumed program's digest, as four little-endian words.
    program: [u64; 4],
    /// The output its run exits with.
    output: Output,
}

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

    /// The output of a run that commits values of digest `self` and assumes these proofs, in order.
    ///
    /// It is `self` when the run assumes none, and otherwise the BLAKE2s-256 personalized by `assuming` of each
    /// assumption's program digest and output words, then of `self`'s words: so the output binds every assumption,
    /// their order and their number, and is never the digest of committed values alone.
    #[must_use]
    pub fn assuming(self, assumptions: &[Assumption]) -> Self {
        if assumptions.is_empty() {
            return self;
        }
        let mut h = Hasher::personal(&Assumption::PERSONALIZATION);
        let words = (assumptions.iter())
            .flat_map(|a| a.program.into_iter().chain(a.output.0))
            .chain(self.0);
        for word in words {
            h.update(&word.to_le_bytes());
        }
        Self(digest_words(&h.finalize()))
    }
}

impl Assumption {
    /// The personalization of the hash that folds assumptions into an output.
    pub(crate) const PERSONALIZATION: [u8; 8] = *b"assuming";

    /// The assumption that a run of the program of this digest, as four little-endian words, exits with `output`.
    #[must_use]
    pub const fn new(program: [u64; 4], output: Output) -> Self {
        Self { program, output }
    }

    /// The assumed program's digest, as four little-endian words.
    #[must_use]
    pub const fn program(&self) -> &[u64; 4] {
        &self.program
    }

    /// The output the assumed run exits with.
    #[must_use]
    pub const fn output(&self) -> Output {
        self.output
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
