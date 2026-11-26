use std::ffi::OsStr;
use std::process::{Command, Output};

fn fibonacci(value: &OsStr, before: &[&str], after: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_leanvm-bench"))
        .env("LEANVM_NUM_THREADS", value)
        .args(["--prover", "stable", "--cooldown", "0"])
        .args(before)
        .args(["fibonacci", "--n", "1000"])
        .args(after)
        .output()
        .expect("run leanvm-bench")
}

fn assert_rejected(value: &OsStr) {
    let output = fibonacci(value, &[], &[]);
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr).starts_with("error: LEANVM_NUM_THREADS must be a nonnegative integer"),
        "{output:?}"
    );
}

fn assert_proved(output: Output) {
    assert!(output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("verifying"),
        "{output:?}"
    );
}

#[test]
fn plain_two_is_valid_and_whitespace_padded_two_is_rejected() {
    assert_proved(fibonacci(OsStr::new("2"), &[], &[]));
    let padded = OsStr::new(" 2 ");
    assert_rejected(padded);
    assert_proved(fibonacci(padded, &["--threads", "1"], &[]));
    assert_proved(fibonacci(padded, &[], &["--threads", "1"]));
}

#[cfg(unix)]
#[test]
fn invalid_utf8_is_rejected_unless_threads_is_explicit() {
    use std::os::unix::ffi::OsStrExt;

    let invalid_utf8 = OsStr::from_bytes(b"\xff");
    assert_rejected(invalid_utf8);
    assert_proved(fibonacci(invalid_utf8, &[], &["--threads", "1"]));
}
