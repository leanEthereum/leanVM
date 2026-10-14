#![allow(dead_code)]

#[inline(never)]
fn initialize(hashes: &mut [std::mem::MaybeUninit<[u8; 32]>]) {
    for (i, hash) in hashes.iter_mut().enumerate() {
        hash.write([i as u8; 32]);
    }
}

pub fn initialized_hashes(n: usize) -> Vec<[u8; 32]> {
    let mut hashes = Box::new_uninit_slice(n);
    initialize(&mut hashes);
    // SAFETY: every element has just been initialized.
    unsafe { hashes.assume_init() }.into_vec()
}
