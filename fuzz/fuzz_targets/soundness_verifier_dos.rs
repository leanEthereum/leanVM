#![no_main]
libfuzzer_sys::fuzz_target!(|data: &[u8]| fuzz::libfuzzer_case("soundness-verifier-dos", data));
