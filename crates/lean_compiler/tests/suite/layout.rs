use lean_compiler::{compile, heap_bufs_after_calls, parse};
use primitives::field::{F64, F128};

/// A `HeapBuf` allocated after a call is reserved before the callee's frame, right after the
/// caller's own (`formal/lean_vm/LeanVM/Guest/Memory/Alloc.lean`).
#[test]
fn heap_buf_after_a_call_precedes_the_callee_frame() {
    let source = r#"
def square(x):
    return x * x

def main():
    public = 1
    y = square(public[1])
    buf = HeapBuf(2)
    buf[1] = y
    assert buf[1] == public[GEN]
    return
"#;
    let program = compile(&parse(source).unwrap());
    let x = F128::from(F64(3));
    let execution = program.execute([x, x * x]).unwrap();
    let main_frame: usize = (program.advice_text().lines())
        .find_map(|l| l.strip_prefix("main_frame ")?.parse().ok())
        .unwrap();
    assert_eq!(execution.mem.word(main_frame), x * x);
}

/// A `HeapBuf` sized by a call's result stays after it, and is reported.
#[test]
fn heap_buf_sized_by_a_call_is_reported() {
    let source = r#"
def square(x):
    return x * x

def main():
    n = square(GEN)
    buf = HeapBuf(n)
    buf[1] = 1
    return
"#;
    assert_eq!(heap_bufs_after_calls(&parse(source).unwrap()), ["main"]);
}
