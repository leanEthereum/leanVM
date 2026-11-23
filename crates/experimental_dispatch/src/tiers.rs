// Written by ../../experimental_tiers/generate.sh.
tiers! {
    #[cfg(all(feature = "cpu_tiers", target_arch = "x86_64", not(all(target_feature = "avx2", target_feature = "bmi1", target_feature = "bmi2", target_feature = "fma", target_feature = "lzcnt", target_feature = "movbe", target_feature = "f16c", target_feature = "popcnt", target_feature = "pclmulqdq", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512cd", target_feature = "avx512dq", target_feature = "avx512vl", target_feature = "vpclmulqdq", target_feature = "gfni", target_feature = "avx512vbmi"))))]
    x86v4gfni => std::arch::is_x86_feature_detected!("avx2") && std::arch::is_x86_feature_detected!("bmi1") && std::arch::is_x86_feature_detected!("bmi2") && std::arch::is_x86_feature_detected!("fma") && std::arch::is_x86_feature_detected!("lzcnt") && std::arch::is_x86_feature_detected!("movbe") && std::arch::is_x86_feature_detected!("f16c") && std::arch::is_x86_feature_detected!("popcnt") && std::arch::is_x86_feature_detected!("pclmulqdq") && std::arch::is_x86_feature_detected!("avx512f") && std::arch::is_x86_feature_detected!("avx512bw") && std::arch::is_x86_feature_detected!("avx512cd") && std::arch::is_x86_feature_detected!("avx512dq") && std::arch::is_x86_feature_detected!("avx512vl") && std::arch::is_x86_feature_detected!("vpclmulqdq") && std::arch::is_x86_feature_detected!("gfni") && std::arch::is_x86_feature_detected!("avx512vbmi"), ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq", "avx512f", "avx512bw", "avx512cd", "avx512dq", "avx512vl", "vpclmulqdq", "gfni", "avx512vbmi"],
    #[cfg(all(feature = "cpu_tiers", target_arch = "x86_64", not(all(target_feature = "avx2", target_feature = "bmi1", target_feature = "bmi2", target_feature = "fma", target_feature = "lzcnt", target_feature = "movbe", target_feature = "f16c", target_feature = "popcnt", target_feature = "pclmulqdq", target_feature = "vpclmulqdq", target_feature = "gfni"))))]
    x86v3gfni => std::arch::is_x86_feature_detected!("avx2") && std::arch::is_x86_feature_detected!("bmi1") && std::arch::is_x86_feature_detected!("bmi2") && std::arch::is_x86_feature_detected!("fma") && std::arch::is_x86_feature_detected!("lzcnt") && std::arch::is_x86_feature_detected!("movbe") && std::arch::is_x86_feature_detected!("f16c") && std::arch::is_x86_feature_detected!("popcnt") && std::arch::is_x86_feature_detected!("pclmulqdq") && std::arch::is_x86_feature_detected!("vpclmulqdq") && std::arch::is_x86_feature_detected!("gfni"), ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq", "vpclmulqdq", "gfni"],
    #[cfg(all(feature = "cpu_tiers", target_arch = "x86_64", not(all(target_feature = "avx2", target_feature = "bmi1", target_feature = "bmi2", target_feature = "fma", target_feature = "lzcnt", target_feature = "movbe", target_feature = "f16c", target_feature = "popcnt", target_feature = "pclmulqdq", target_feature = "vpclmulqdq"))))]
    x86v3clmul => std::arch::is_x86_feature_detected!("avx2") && std::arch::is_x86_feature_detected!("bmi1") && std::arch::is_x86_feature_detected!("bmi2") && std::arch::is_x86_feature_detected!("fma") && std::arch::is_x86_feature_detected!("lzcnt") && std::arch::is_x86_feature_detected!("movbe") && std::arch::is_x86_feature_detected!("f16c") && std::arch::is_x86_feature_detected!("popcnt") && std::arch::is_x86_feature_detected!("pclmulqdq") && std::arch::is_x86_feature_detected!("vpclmulqdq"), ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq", "vpclmulqdq"],
    #[cfg(all(feature = "cpu_tiers", target_arch = "x86_64", not(all(target_feature = "avx2", target_feature = "bmi1", target_feature = "bmi2", target_feature = "fma", target_feature = "lzcnt", target_feature = "movbe", target_feature = "f16c", target_feature = "popcnt", target_feature = "pclmulqdq", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512cd", target_feature = "avx512dq", target_feature = "avx512vl"))))]
    x86v4 => std::arch::is_x86_feature_detected!("avx2") && std::arch::is_x86_feature_detected!("bmi1") && std::arch::is_x86_feature_detected!("bmi2") && std::arch::is_x86_feature_detected!("fma") && std::arch::is_x86_feature_detected!("lzcnt") && std::arch::is_x86_feature_detected!("movbe") && std::arch::is_x86_feature_detected!("f16c") && std::arch::is_x86_feature_detected!("popcnt") && std::arch::is_x86_feature_detected!("pclmulqdq") && std::arch::is_x86_feature_detected!("avx512f") && std::arch::is_x86_feature_detected!("avx512bw") && std::arch::is_x86_feature_detected!("avx512cd") && std::arch::is_x86_feature_detected!("avx512dq") && std::arch::is_x86_feature_detected!("avx512vl"), ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq", "avx512f", "avx512bw", "avx512cd", "avx512dq", "avx512vl"],
    #[cfg(all(feature = "cpu_tiers", target_arch = "aarch64", not(all(target_feature = "aes", target_feature = "sha3"))))]
    armsha3 => std::arch::is_aarch64_feature_detected!("aes") && std::arch::is_aarch64_feature_detected!("sha3"), ["aes", "sha3"],
    #[cfg(all(feature = "cpu_tiers", target_arch = "aarch64", not(all(target_feature = "aes"))))]
    armaes => std::arch::is_aarch64_feature_detected!("aes"), ["aes"],
}

#[cfg(target_arch = "x86_64")]
fn selected() -> Vec<(&'static str, bool, bool)> {
    vec![
        ("avx2", std::arch::is_x86_feature_detected!("avx2"), cfg!(target_feature = "avx2")),
        ("pclmulqdq", std::arch::is_x86_feature_detected!("pclmulqdq"), cfg!(target_feature = "pclmulqdq")),
        ("bmi2", std::arch::is_x86_feature_detected!("bmi2"), cfg!(target_feature = "bmi2")),
        ("vpclmulqdq", std::arch::is_x86_feature_detected!("vpclmulqdq"), cfg!(target_feature = "vpclmulqdq")),
        ("gfni", std::arch::is_x86_feature_detected!("gfni"), cfg!(target_feature = "gfni")),
        ("avx512f", std::arch::is_x86_feature_detected!("avx512f"), cfg!(target_feature = "avx512f")),
        ("avx512bw", std::arch::is_x86_feature_detected!("avx512bw"), cfg!(target_feature = "avx512bw")),
        ("avx512vbmi", std::arch::is_x86_feature_detected!("avx512vbmi"), cfg!(target_feature = "avx512vbmi")),
    ]
}

#[cfg(target_arch = "aarch64")]
fn selected() -> Vec<(&'static str, bool, bool)> {
    vec![
        ("aes", std::arch::is_aarch64_feature_detected!("aes"), cfg!(target_feature = "aes")),
        ("sha3", std::arch::is_aarch64_feature_detected!("sha3"), cfg!(target_feature = "sha3")),
    ]
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
fn selected() -> Vec<(&'static str, bool, bool)> {
    Vec::new()
}
