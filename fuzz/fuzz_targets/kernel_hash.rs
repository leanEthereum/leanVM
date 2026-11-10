#![no_main]
libfuzzer_sys::fuzz_target!(|data: &[u8]| fuzz::libfuzzer_case("kernel-hash", data));
