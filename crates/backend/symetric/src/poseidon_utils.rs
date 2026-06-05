use std::sync::OnceLock;

use field::PrimeCharacteristicRing;
use koala_bear::{KoalaBear, Poseidon1KoalaBear16, default_koalabear_poseidon1_16, symmetric::Permutation};

use crate::{CAPACITY, Compression, DIGEST_ELEMS, RATE, WIDTH};

pub type Poseidon16 = Poseidon1KoalaBear16;

static POSEIDON_16_INSTANCE: OnceLock<Poseidon16> = OnceLock::new();
static POSEIDON_16_OF_ZERO: OnceLock<[KoalaBear; 8]> = OnceLock::new();

#[inline(always)]
pub fn get_poseidon16() -> &'static Poseidon16 {
    POSEIDON_16_INSTANCE.get_or_init(default_koalabear_poseidon1_16)
}

#[inline(always)]
pub fn get_poseidon_16_of_zero() -> &'static [KoalaBear; 8] {
    POSEIDON_16_OF_ZERO.get_or_init(|| poseidon16_compress([KoalaBear::default(); 16]))
}

#[inline(always)]
pub fn poseidon16_compress(input: [KoalaBear; 16]) -> [KoalaBear; 8] {
    get_poseidon16().compress(input)[0..8].try_into().unwrap()
}

#[inline(always)]
pub fn poseidon16_permute(input: [KoalaBear; 16]) -> [KoalaBear; 16] {
    get_poseidon16().permute(input)
}

pub fn poseidon16_compress_pair(left: &[KoalaBear; 8], right: &[KoalaBear; 8]) -> [KoalaBear; 8] {
    let mut input = [KoalaBear::default(); 16];
    input[..8].copy_from_slice(left);
    input[8..].copy_from_slice(right);
    poseidon16_compress(input)
}

// Overwrite-sponge
pub fn poseidon_hash_slice(data: &[KoalaBear]) -> [KoalaBear; DIGEST_ELEMS] {
    assert!(!data.is_empty());
    assert!(data.len().is_multiple_of(RATE));
    let mut state = [KoalaBear::default(); WIDTH];
    state[0] = KoalaBear::from_usize(data.len());
    for chunk in data.chunks(RATE) {
        state[CAPACITY..].copy_from_slice(chunk);
        state = poseidon16_permute(state);
    }
    state[CAPACITY..].try_into().unwrap()
}
