//! Build script that verifies, assembles, and localizes the proved leanSPHINCS assembly on Linux.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    println!("cargo:rustc-check-cfg=cfg(proved_sphincs_asm)");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=CLANG");
    println!("cargo:rerun-if-env-changed=LLVM_OBJCOPY");
    println!("cargo:rerun-if-env-changed=LLVM_AR");

    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();

    if target_os != "linux" {
        return;
    }

    let (asm_rel, clang_target) = match target_arch.as_str() {
        "x86_64" => ("asm/signatures-x86_64.s", "x86_64-unknown-linux-musl"),
        "aarch64" => ("asm/signatures-aarch64.s", "aarch64-unknown-linux-musl"),
        _ => return,
    };

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let rustc_dir = manifest_dir.join("../../formal/native/rustc");
    let sha_path = rustc_dir.join("SHA256SUMS");
    let asm_path = rustc_dir.join(asm_rel);

    println!("cargo:rerun-if-changed={}", sha_path.display());
    println!("cargo:rerun-if-changed={}", asm_path.display());

    verify_sha256(&sha_path, asm_rel, &asm_path);

    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));
    let obj_path = out_dir.join("proved_sphincs_asm.o");
    let archive_path = out_dir.join("libproved_sphincs.a");

    let clang = env::var("CLANG").unwrap_or_else(|_| "clang".to_owned());
    let llvm_objcopy = find_llvm_tool("LLVM_OBJCOPY", "llvm-objcopy");
    let llvm_ar = find_llvm_tool_or("LLVM_AR", "llvm-ar", "ar");

    let mut clang_cmd = Command::new(&clang);
    clang_cmd.arg(format!("--target={clang_target}"));
    if target_arch == "x86_64" {
        // Emit non-relaxable R_X86_64_GOTPCREL so linkers (lld, ld.bfd, cgo, zig) never rewrite
        // proved GOT loads/calls into `lea` or `addr32 call`.
        clang_cmd.arg("-Wa,-mrelax-relocations=no");
    }
    run(
        clang_cmd.arg("-c").arg(&asm_path).arg("-o").arg(&obj_path),
        "assemble proved leanSPHINCS assembly",
    );

    run(
        Command::new(&llvm_objcopy)
            .arg("--keep-global-symbol=sphincs_verify")
            .arg("--set-symbol-visibility=sphincs_verify=hidden")
            .arg(&obj_path),
        "localize non-entry symbols in proved_sphincs_asm.o",
    );

    let _ = fs::remove_file(&archive_path);
    run(
        Command::new(&llvm_ar)
            .arg("rcs")
            .arg(&archive_path)
            .arg(&obj_path),
        "archive libproved_sphincs.a",
    );

    println!("cargo:rustc-cfg=proved_sphincs_asm");
    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=proved_sphincs");
}

fn run(cmd: &mut Command, what: &str) {
    let status = cmd
        .status()
        .unwrap_or_else(|err| panic!("failed to {what} ({cmd:?}): {err}"));
    assert!(status.success(), "failed to {what} ({cmd:?}): {status}");
}

fn find_llvm_tool(env_name: &str, tool: &str) -> String {
    if let Ok(path) = env::var(env_name) {
        if !path.is_empty() {
            return path;
        }
    }
    if let Some(path) = rustc_llvm_bin(tool) {
        return path.to_string_lossy().into_owned();
    }
    tool.to_owned()
}

fn find_llvm_tool_or(env_name: &str, tool: &str, fallback: &str) -> String {
    if let Ok(path) = env::var(env_name) {
        if !path.is_empty() {
            return path;
        }
    }
    if let Some(path) = rustc_llvm_bin(tool) {
        return path.to_string_lossy().into_owned();
    }
    if Command::new(tool).arg("--version").output().is_ok() {
        tool.to_owned()
    } else {
        fallback.to_owned()
    }
}

fn rustc_llvm_bin(tool: &str) -> Option<PathBuf> {
    let rustc = env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let sysroot_out = Command::new(&rustc)
        .args(["--print", "sysroot"])
        .output()
        .ok()?;
    if !sysroot_out.status.success() {
        return None;
    }
    let sysroot = String::from_utf8(sysroot_out.stdout)
        .ok()?
        .trim()
        .to_owned();
    let vv_out = Command::new(&rustc).arg("-vV").output().ok()?;
    if !vv_out.status.success() {
        return None;
    }
    let vv = String::from_utf8(vv_out.stdout).ok()?;
    let host = vv
        .lines()
        .find_map(|line| line.strip_prefix("host: "))?
        .trim();
    let candidate = PathBuf::from(sysroot)
        .join("lib/rustlib")
        .join(host)
        .join("bin")
        .join(tool);
    candidate.is_file().then_some(candidate)
}

fn verify_sha256(sha_path: &Path, asm_rel: &str, asm_path: &Path) {
    assert_eq!(
        sha256_hex(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        "internal SHA-256 self-test failed"
    );

    let sums = fs::read_to_string(sha_path)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", sha_path.display()));
    let expected = sums
        .lines()
        .find_map(|line| {
            let mut parts = line.split_whitespace();
            let digest = parts.next()?;
            let file = parts.next()?;
            (file == asm_rel).then_some(digest)
        })
        .unwrap_or_else(|| panic!("{asm_rel} missing from {}", sha_path.display()));

    let asm_bytes = fs::read(asm_path)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", asm_path.display()));
    let actual = sha256_hex(&asm_bytes);
    assert_eq!(
        actual,
        expected,
        "SHA-256 mismatch for {}: expected {expected}, got {actual}",
        asm_path.display()
    );
}

#[allow(clippy::many_single_char_names, clippy::too_many_lines)]
fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a_2f98,
        0x7137_4491,
        0xb5c0_fbcf,
        0xe9b5_dba5,
        0x3956_c25b,
        0x59f1_11f1,
        0x923f_82a4,
        0xab1c_5ed5,
        0xd807_aa98,
        0x1283_5b01,
        0x2431_85be,
        0x550c_7dc3,
        0x72be_5d74,
        0x80de_b1fe,
        0x9bdc_06a7,
        0xc19b_f174,
        0xe49b_69c1,
        0xefbe_4786,
        0x0fc1_9dc6,
        0x240c_a1cc,
        0x2de9_2c6f,
        0x4a74_84aa,
        0x5cb0_a9dc,
        0x76f9_88da,
        0x983e_5152,
        0xa831_c66d,
        0xb003_27c8,
        0xbf59_7fc7,
        0xc6e0_0bf3,
        0xd5a7_9147,
        0x06ca_6351,
        0x1429_2967,
        0x27b7_0a85,
        0x2e1b_2138,
        0x4d2c_6dfc,
        0x5338_0d13,
        0x650a_7354,
        0x766a_0abb,
        0x81c2_c92e,
        0x9272_2c85,
        0xa2bf_e8a1,
        0xa81a_664b,
        0xc24b_8b70,
        0xc76c_51a3,
        0xd192_e819,
        0xd699_0624,
        0xf40e_3585,
        0x106a_a070,
        0x19a4_c116,
        0x1e37_6c08,
        0x2748_774c,
        0x34b0_bcb5,
        0x391c_0cb3,
        0x4ed8_aa4a,
        0x5b9c_ca4f,
        0x682e_6ff3,
        0x748f_82ee,
        0x78a5_636f,
        0x84c8_7814,
        0x8cc7_0208,
        0x90be_fffa,
        0xa450_6ceb,
        0xbef9_a3f7,
        0xc671_78f2,
    ];

    let mut state: [u32; 8] = [
        0x6a09_e667,
        0xbb67_ae85,
        0x3c6e_f372,
        0xa54f_f53a,
        0x510e_527f,
        0x9b05_688c,
        0x1f83_d9ab,
        0x5be0_cd19,
    ];

    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity((data.len() + 9 + 63) & !63);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for block in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, chunk) in block.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        for (s, delta) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *s = s.wrapping_add(delta);
        }
    }

    let mut out = String::with_capacity(64);
    for word in state {
        use std::fmt::Write;
        let _ = write!(&mut out, "{word:08x}");
    }
    out
}
