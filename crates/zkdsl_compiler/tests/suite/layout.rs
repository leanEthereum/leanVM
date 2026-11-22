use crate::common::compile;
use isa::RHint;
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
    assert_eq!(execution.mem.word(program.main_frame as usize), x * x);
}

/// Where a `HeapBuf` stays, or moves to, when its function's first call is in a branch: one no run allocates
/// after a call stays (before the call in its arm, in the other arm), and one after a chain of `match`es whose
/// arms hold the first call moves before the chain. A size an arm of every branch writes, or a hint, is known
/// there.
#[test]
fn heap_buf_around_a_call_in_a_branch() {
    let head = "def sq(x):\n    return x * x\n\n@inline\ndef arm(v, k: Const, c: Const):\n    y = v * GEN ** k\n    if const(c == 1):\n        y = sq(v)\n    return y\n\n";
    let main = "def main():\n    public = 1\n    f(public[1], public[GEN])\n    return\n";
    for body in [
        "def f(a, s):\n    if a == 1:\n        buf = HeapBuf(2)\n        buf[1] = a\n        b = sq(a)\n    return\n",
        "def f(a, s):\n    if a == 1:\n        b = sq(a)\n    else:\n        buf = HeapBuf(2)\n        buf[1] = a\n    return\n",
        "def f(a, s):\n    t = StackBuf(1)\n    t[0] = s\n    for i in unroll(0, 2):\n        r = match(log(t[0]), range(0, 2), lambda j: arm(a, j, i))\n    buf = HeapBuf(2)\n    buf[1] = r\n    return\n",
        "def f(a, s):\n    n = match(log(s), range(0, 2), lambda j: arm(GEN, j + 1, 0))\n    b = sq(a)\n    buf = HeapBuf(n)\n    buf[1] = b\n    return\n",
        "def f(a, s):\n    d = StackBuf(1)\n    hint_decompose_digits_exponent(d, GEN ** 2, 2, 1, 2, 0)\n    b = sq(a)\n    buf = HeapBuf(d[0])\n    buf[1] = b\n    return\n",
    ] {
        let program = compile(&parse(&format!("{head}{body}\n{main}")).unwrap());
        for (a, s) in [(1, 1), (3, 2)] {
            execute(&program, &[], [F128::from(F64(a)), F128::from(F64(s))]).unwrap();
        }
    }
}

/// The reservations of `f`, in code order, keep the order of the proof's memory model: its `HeapBuf`s as its body
/// allocates them, then its callee's frame, whether the call is at depth 0 or in a branch.
#[test]
fn heap_bufs_keep_their_order_before_the_callee_frame() {
    let head = "def sq(x):\n    return x * x\n\n";
    let main = "def main():\n    public = 1\n    f(public[1])\n    return\n";
    for body in [
        "def f(a):\n    x = HeapBuf(11)\n    x[1] = a\n    b = sq(a)\n    y = HeapBuf(13)\n    y[1] = b\n    return\n",
        "def f(a):\n    x = HeapBuf(11)\n    x[1] = a\n    if a == 1:\n        b = sq(a)\n    y = HeapBuf(13)\n    y[1] = a\n    return\n",
    ] {
        let program = compile(&parse(&format!("{head}{body}\n{main}")).unwrap());
        let &(_, entry, len) = program.fn_ranges.iter().find(|(name, ..)| name == "f").unwrap();
        let sizes: Vec<u32> = (entry..entry + len)
            .flat_map(|pc| program.hints.get(&pc).into_iter().flatten())
            .filter_map(|h| match *h {
                RHint::Alloc { size, .. } => Some(size),
                _ => None,
            })
            .collect();
        assert!(
            matches!(sizes[..], [11, 13, frame] if frame != 11 && frame != 13),
            "{sizes:?} in\n{body}"
        );
        for a in [1, 3] {
            execute(&program, &[], [F128::from(F64(a)), F128::ONE]).unwrap();
        }
    }
}

/// A `HeapBuf` that would move ahead of one some run allocates before it, in the branch holding the first call, in
/// another arm of it, or between it and a later call, is a compile error naming both.
#[test]
fn heap_buf_passing_one_that_stays_fails() {
    let head = "def sq(x):\n    return x * x\n\n";
    let main = "def main():\n    public = 1\n    f(public[1])\n    return\n";
    let late = "    late = HeapBuf(2)\n    late[1] = a\n    return\n";
    for body in [
        "def f(a):\n    if a == 1:\n        early = HeapBuf(2)\n        early[1] = a\n        b = sq(a)\n",
        "def f(a):\n    if a == 1:\n        b = sq(a)\n    else:\n        early = HeapBuf(2)\n        early[1] = a\n",
        "def f(a):\n    if a == 1:\n        b = sq(a)\n        return\n    early = HeapBuf(2)\n    early[1] = a\n    c = sq(a)\n",
    ] {
        let ast = parse(&format!("{head}{body}{late}\n{main}")).unwrap();
        let error = std::panic::catch_unwind(|| zkdsl_compiler::compile(&ast)).unwrap_err();
        let error = error.downcast_ref::<String>().unwrap();
        assert!(
            error.contains("`late`") && error.contains("ahead of `HeapBuf` `early`"),
            "{error}"
        );
    }
}

/// A `HeapBuf` the compiler cannot reserve before its function's first call, sized after it, by a cell a `DEREF`
/// only linked before it, or in a branch some run reaches after a call, is a compile error naming it.
#[test]
fn heap_buf_not_sized_before_the_first_call_fails() {
    for source in [
        "def square(x):\n    return x * x\n\ndef main():\n    n = square(GEN)\n    late = HeapBuf(n)\n    late[1] = 1\n    return\n",
        "def setbuf(b):\n    b[1] = GEN * GEN\n    return\n\ndef main():\n    buf = HeapBuf(2)\n    n = buf[1]\n    setbuf(buf)\n    late = HeapBuf(n)\n    late[1] = 1\n    return\n",
        "def square(x):\n    return x * x\n\ndef main():\n    public = 1\n    n = public[1]\n    if n != 1:\n        late = HeapBuf(square(n))\n        late[1] = 1\n    return\n",
        "def square(x):\n    return x * x\n\ndef main():\n    public = 1\n    n = public[1]\n    if n != 1:\n        m = square(n)\n    if n != 3:\n        late = HeapBuf(2)\n        late[1] = 1\n    return\n",
    ] {
        let ast = parse(source).unwrap();
        let error = std::panic::catch_unwind(|| zkdsl_compiler::compile(&ast)).unwrap_err();
        let error = error.downcast_ref::<String>().unwrap();
        assert!(error.contains("`late`") && error.contains("computed before"), "{error}");
    }
}
