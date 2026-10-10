pub fn roundtrip_word(word: u64) -> u64 {
    u64::from_le_bytes(word.to_le_bytes())
}
