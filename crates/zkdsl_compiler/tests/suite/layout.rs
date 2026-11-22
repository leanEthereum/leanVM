use crate::common::compile;
use lean_vm_core::cpu::execute;
use primitives::field::{F64, F128};
use zkdsl_compiler::parse;

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
    let execution = execute(&program, &[], [x, x * x]).unwrap();
    let main_frame: usize = (program.export_hints(&[]).lines())
        .find_map(|l| l.strip_prefix("main_frame ")?.parse().ok())
        .unwrap();
    assert_eq!(execution.mem.word(main_frame), x * x);
}

/// A `HeapBuf` the compiler cannot reserve before its function's first call, sized after it, by a cell a `DEREF`
/// only linked before it, or in a branch, is a compile error naming it.
#[test]
fn heap_buf_not_sized_before_the_first_call_fails() {
    for source in [
        "def square(x):\n    return x * x\n\ndef main():\n    n = square(GEN)\n    late = HeapBuf(n)\n    late[1] = 1\n    return\n",
        "def setbuf(b):\n    b[1] = GEN * GEN\n    return\n\ndef main():\n    buf = HeapBuf(2)\n    n = buf[1]\n    setbuf(buf)\n    late = HeapBuf(n)\n    late[1] = 1\n    return\n",
        "def square(x):\n    return x * x\n\ndef main():\n    public = 1\n    n = public[1]\n    if n != 1:\n        late = HeapBuf(square(n))\n        late[1] = 1\n    return\n",
    ] {
        let ast = parse(source).unwrap();
        let error = std::panic::catch_unwind(|| zkdsl_compiler::compile(&ast)).unwrap_err();
        let error = error.downcast_ref::<String>().unwrap();
        assert!(error.contains("`late`") && error.contains("computed before"), "{error}");
    }
}
