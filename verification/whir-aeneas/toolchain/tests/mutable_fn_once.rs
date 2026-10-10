pub fn apply<F: FnOnce(&mut u32) -> u32>(state: &mut u32, callback: F) -> u32 {
    callback(state)
}

pub fn increment(state: &mut u32) -> u32 {
    apply(state, |value| {
        *value += 1;
        *value
    })
}
