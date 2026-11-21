use crate::common::compile;
use lean_vm_core::cpu::execute;
use primitives::field::{F64, F128};
use zkdsl_compiler::{HEAP_SIZE_STREAM, advised_heap_bufs, check_heap_advice, parse};

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

/// A `HeapBuf` sized by a call's result is reserved before the callee's frame from advice, and
/// reported.
#[test]
fn heap_buf_sized_by_a_call_is_advice() {
    let source = r#"
def square(x):
    return x * x

def main():
    n = square(GEN)
    buf = HeapBuf(n)
    buf[1] = 1
    return
"#;
    let ast = parse(source).unwrap();
    assert_eq!(advised_heap_bufs(&ast), [("main".to_string(), vec![7])]);
    let program = compile(&ast);
    let witness = [(HEAP_SIZE_STREAM.to_string(), vec![vec![F128::from(F64::G.pow(2))]])];
    let execution = execute(&program, &witness, [F128::ZERO; 2]).unwrap();
    let main_frame: usize = (program.export_hints(&[]).lines())
        .find_map(|l| l.strip_prefix("main_frame ")?.parse().ok())
        .unwrap();
    assert_eq!(execution.mem.word(main_frame), F128::ONE);
}

/// A `HeapBuf` in a branch is reserved before the statement from advice: `[g^size]` where the branch
/// runs, `[]` where it does not, leaving its pointer cell unwritten.
#[test]
fn heap_buf_in_a_branch_not_taken_is_left_unreserved() {
    let source = r#"
def square(x):
    return x * x

def main():
    public = 1
    n = public[1]
    if n != 1:
        buf = HeapBuf(square(n))
        buf[1] = 1
    return
"#;
    let program = compile(&parse(source).unwrap());
    let advice = program.export_hints(&[]);
    let ptr: usize = (advice.split(" av ").nth(1))
        .and_then(|rest| rest.split(' ').next()?.parse().ok())
        .expect("one advised HeapBuf");
    let run = |n: F128, entry: Vec<F128>| {
        let witness = [(HEAP_SIZE_STREAM.to_string(), vec![entry])];
        execute(&program, &witness, [n, F128::ZERO]).unwrap().mem.word(ptr)
    };
    assert_eq!(run(F128::ONE, vec![]), F128::ZERO);
    let g = F128::from(F64::G);
    assert_ne!(run(g, vec![F128::from(F64::G.pow(2))]), F128::ZERO);
}

/// A `HeapBuf` sized by a cell a `DEREF` only linked before the first call, the callee writing it,
/// is reserved from advice: the link leaves the size unwritten where the reservation moves to.
#[test]
fn heap_buf_sized_by_a_linked_cell_is_advice() {
    let source = r#"
def setbuf(b):
    b[1] = GEN * GEN * GEN
    return

def main():
    buf = HeapBuf(2)
    n = buf[1]
    setbuf(buf)
    c = HeapBuf(n)
    c[1] = 1
    return
"#;
    let ast = parse(source).unwrap();
    assert_eq!(advised_heap_bufs(&ast), [("main".to_string(), vec![10])]);
    let program = compile(&ast);
    let witness = [(HEAP_SIZE_STREAM.to_string(), vec![vec![F128::from(F64::G.pow(3))]])];
    execute(&program, &witness, [F128::ZERO; 2]).unwrap();
}

/// A `HeapBuf` reserved from advice fails the run where it is allocated unless the advice reserved
/// it at the size the program computes.
#[test]
fn heap_buf_advice_of_another_size_fails() {
    let source = r#"
def square(x):
    return x * x

def main():
    public = 1
    n = public[1]
    if n != 1:
        buf = HeapBuf(square(n))
        buf[1] = 1
    return
"#;
    let program = compile(&parse(source).unwrap());
    let run = |entry: Vec<F128>| {
        let witness = [(HEAP_SIZE_STREAM.to_string(), vec![entry])];
        execute(&program, &witness, [F128::from(F64::G), F128::ZERO]).map(|_| ())
    };
    let size = |k| vec![F128::from(F64::G.pow(k))];
    run(size(2)).unwrap();
    for entry in [vec![], size(1), size(3)] {
        let error = run(entry).unwrap_err().to_string();
        assert!(error.contains("advice") || error.contains("advised size"), "{error}");
        assert!(error.contains("main (line"), "{error}");
    }
}

/// The compiler marks a `HeapBuf`'s hint late only where its function reserves it from advice
/// before: in a branch, past a `return`, sized after a call, and in every program of
/// `tests/programs/`.
#[test]
fn every_late_heap_buf_has_advice() {
    let sources = [
        r#"
def f(x):
    return x * x

def g(n):
    y = f(n)
    if y == 1:
        return 0
    b = HeapBuf(2)
    b[GEN] = y
    c = HeapBuf(y)
    c[1] = y
    return b[GEN]

def main():
    public = 1
    n = public[1]
    if n != 1:
        buf = HeapBuf(f(n))
        buf[1] = g(n)
    return
"#,
        r#"
def f(x):
    return x * x

def main():
    public = 1
    n = public[1]
    s = f(n)
    d = HeapBuf(s)
    d[1] = s
    return
"#,
    ];
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let files = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| std::fs::read_to_string(e.unwrap().path()).unwrap());
    let mut advised = 0;
    for src in sources.into_iter().map(String::from).chain(files) {
        let ast = parse(&src).unwrap();
        check_heap_advice(&zkdsl_compiler::compile(&ast)).unwrap();
        advised += advised_heap_bufs(&ast).iter().map(|(_, l)| l.len()).sum::<usize>();
    }
    assert!(advised >= 4, "the sources reserve from advice");
}
