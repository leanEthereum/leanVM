// Assumes build host == run host, for simplicity (to be changed in the future)

fn main() {
    let cores = std::thread::available_parallelism().unwrap().get();
    let l1_cache_size = match detect_l1_cache_size() {
        Some(size) => size,
        None => {
            eprintln!("Warning: failed to detect L1 cache size, defaulting to 32 KB");
            32 * 1024
        }
    };
    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let path = std::path::Path::new(&out_dir).join("info.rs");
    std::fs::write(
        &path,
        format!(
            "pub const NUM_THREADS: usize = {cores};\n\
             pub const L1_CACHE_SIZE: usize = {l1_cache_size};\n"
        ),
    )
    .unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}

#[cfg(target_os = "linux")]
fn detect_l1_cache_size() -> Option<usize> {
    // /sys reports e.g. "32K\n", "48K\n", "1M\n".
    let s = std::fs::read_to_string("/sys/devices/system/cpu/cpu0/cache/index0/size").ok()?;
    let s = s.trim();
    let last = s.chars().last()?;
    match last {
        'K' | 'k' => s[..s.len() - 1].parse::<usize>().ok().map(|n| n * 1024),
        'M' | 'm' => s[..s.len() - 1].parse::<usize>().ok().map(|n| n * 1024 * 1024),
        c if c.is_ascii_digit() => s.parse().ok(),
        _ => None,
    }
}

#[cfg(target_os = "macos")]
fn detect_l1_cache_size() -> Option<usize> {
    // `hw.l1dcachesize` returns the E-core value on Apple Silicon; prefer the P-core size.
    let read_sysctl = |key: &str| -> Option<usize> {
        let out = std::process::Command::new("sysctl").args(["-n", key]).output().ok()?;
        std::str::from_utf8(&out.stdout).ok()?.trim().parse().ok()
    };
    read_sysctl("hw.perflevel0.l1dcachesize").or_else(|| read_sysctl("hw.l1dcachesize"))
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn detect_l1_cache_size() -> Option<usize> {
    None
}
