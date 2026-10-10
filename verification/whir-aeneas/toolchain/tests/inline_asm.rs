pub fn add_word(word: &mut u32, value: u32) {
    unsafe {
        core::arch::asm!(
            "add dword ptr [{pointer}], {value:e}",
            pointer = in(reg) word as *mut u32,
            value = in(reg) value,
            options(nostack)
        );
    }
}
