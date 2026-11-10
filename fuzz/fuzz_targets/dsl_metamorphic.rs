#![no_main]
libfuzzer_sys::fuzz_target!(|data: &[u8]| fuzz::libfuzzer_case("dsl-metamorphic", data));
