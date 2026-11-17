use crate::common::compile;
use lean_vm_core::cpu::execute;
use primitives::field::{F64, F128};
use zkdsl_compiler::{HEAP_SIZE_STREAM, heap_size_advice, parse};

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
    let main_frame: usize = (program.advice_text(&[]).lines())
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
    assert_eq!(heap_size_advice(&ast), ["main"]);
    let program = compile(&ast);
    let witness = [(HEAP_SIZE_STREAM.to_string(), vec![vec![F128::from(F64::G.pow(2))]])];
    let execution = execute(&program, &witness, [F128::ZERO; 2]).unwrap();
    let main_frame: usize = (program.advice_text(&[]).lines())
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
    let advice = program.advice_text(&[]);
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
