//! The next Fibonacci number from two proven ones. The advice holds the Fibonacci program's digest (four words), then
//! `n`, `F(n)` and `F(n + 1)`.
//!
//! The guest assumes the program's runs on `n` and `n + 1`, then commits the program's digest, `n + 2` and
//! `F(n + 2)`.
#![no_std]
#![no_main]

use leanvm_guest::{commit, read, verify_proof};

#[unsafe(no_mangle)]
extern "C" fn main() {
    let program = read::<[u64; 4]>();
    let [n, f0, f1] = *read::<[u64; 3]>();
    let next = defer::next(n, f0, f1);
    verify_proof(program, &defer::fibonacci_output(n, f0));
    verify_proof(program, &defer::fibonacci_output(n + 1, f1));
    commit(program);
    commit(&next);
}
