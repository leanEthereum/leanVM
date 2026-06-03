use std::process::Command;

use backend::PrimeCharacteristicRing;
use lean_compiler::{ProgramSource, try_compile_and_run};
use lean_vm::{DIGEST_LEN, F};

const CHILD_TEST: &str = "child_calls_try_compile_and_run";
const CHILD_ENV: &str = "LEAN_COMPILER_TRY_COMPILE_AND_RUN_CHILD";

#[test]
fn try_compile_and_run_does_not_print_summary() {
    // Re-exec this test binary so stdout capture stays process-local and does not
    // depend on global test harness state. `--exact` avoids recursively running
    // this parent test in the child process.
    let output = Command::new(std::env::current_exe().unwrap())
        .arg("--exact")
        .arg(CHILD_TEST)
        .arg("--nocapture")
        .env(CHILD_ENV, "1")
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "child test failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("STATS"),
        "try_compile_and_run unexpectedly printed the execution summary:\n{stdout}"
    );
}

#[test]
fn child_calls_try_compile_and_run() {
    // This test only does real work in the child process spawned above.
    if std::env::var_os(CHILD_ENV).is_none() {
        return;
    }

    let summary = try_compile_and_run(
        &ProgramSource::Raw("def main():\n    return\n".to_string()),
        &[F::ZERO; DIGEST_LEN],
        false,
    )
    .unwrap();

    assert!(summary.contains("STATS"));
}
