//! What the crates both provers share (`rec_aggregation`, `lean_da`, `leanvm`) need of a prover. Each prover tree
//! implements [`Prover`] once, beside its `cpu::prove`.

use crate::CompiledProgram;
use verifier::E;

/// A prover of ISA programs, and the thread pool and field kernels it brings for the work around a proof.
pub trait Prover: 'static {
    /// A program assembled for this prover, with the witness streams it runs on.
    type Program: Clone + Send + Sync + 'static;

    /// Start the prover's thread pool. Call it before anything below; a second call does nothing.
    fn init();

    /// `program` as this prover runs it. Costly (it hashes the bytecode into the Fiat-Shamir IV): assemble once.
    fn assemble(program: CompiledProgram) -> Self::Program;

    /// Supply the entries of the witness stream `name`, one per `hint_witness` call, in the order they are popped.
    fn set_witness(program: &mut Self::Program, name: &str, entries: Vec<Vec<E>>);

    /// Prove an execution of `program` on `public_input` at the code rate `2^-log_inv_rate`, or say why there is none.
    fn prove(
        program: &Self::Program,
        public_input: [E; 2],
        log_inv_rate: usize,
    ) -> Result<(verifier::Proof, Stats), String>;

    /// `f(i)` for every `i < n`, on the thread pool. `f` must not dispatch to the pool itself.
    fn map_collect<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T>;

    // The field kernels: the deferred claims' batching (`rec_aggregation`) runs on the first three, LeanDA's
    // encoding on the last.

    /// `a * b`, faster than the verifier's portable product.
    fn mul(a: E, b: E) -> E;

    /// `Σ_r weights[r] · rows[r]`, over the `weights.len()` rows of `K` words that `rows` holds end to end.
    fn combine_rows(rows: &[u64], weights: &[E]) -> Vec<E>;

    /// Each row's dot product with `weights`, over the rows of `weights.len()` `K` words that `rows` holds end to end.
    fn dot_rows(rows: &[u64], weights: &[E]) -> Vec<E>;

    /// Each row of `2^log_k` symbols encoded at rate one half, systematically: each limb of a symbol is the evaluation,
    /// on the standard additive domain of `2^(log_k + 1)` points, of the novel-basis polynomial of degree below `2^log_k`
    /// that the row's limbs interpolate on its first half.
    fn encode_rows(symbols: &[u128], log_k: usize) -> Vec<u128>;
}

/// Run statistics returned with a proof.
#[derive(Clone, Debug, Default)]
pub struct Stats {
    /// Executed instructions.
    pub cycles: usize,
    /// Rows per table the program executed, in the order of [`Self::TABLES`].
    pub rows: [usize; 6],
    /// Committed words: the columns' lengths, before the stack's pad to a power of two.
    pub committed: usize,
    /// Data memory is `2^log_mem` cells.
    pub log_mem: usize,
    /// Cells actually touched, before the pad to `2^log_mem`.
    pub mem_used: usize,
    /// Bytecode instructions, before the pad to a power of two.
    pub bytecode: usize,
}

impl Stats {
    /// Table names in `rows` order.
    pub const TABLES: [&'static str; 6] = ["XOR", "MUL", "SET", "DEREF", "JUMP", "KECCAK"];
}
