const LABEL: &[u8] = b"abc";

pub fn copy_label(seed: u8) -> [u8; 3] {
    let mut bytes = [seed; 3];
    bytes[..LABEL.len()].copy_from_slice(LABEL);
    bytes
}

pub fn repeat_seed(seed: u8) -> [u8; 3] {
    [seed; 3]
}
