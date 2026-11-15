//! Compiling the guest to a fixed point on its own size, and what every prover and verifier derives from it once.

use super::cells::hash_to_scalars;
use super::placeholders::placeholder_map;
use isa::{CompiledProgram, Op, Prover};
use std::any::{Any, TypeId};
use std::sync::{Mutex, OnceLock};
use verifier::E;
use zkdsl_compiler::{compile, parse_with_replacements};

/// The aggregation guest's zkDSL source.
pub(crate) const GUEST_SOURCE: &str =
    include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../guests/lean_ethereum.py"));

/// The compiled aggregation guest.
pub struct Guest {
    program: CompiledProgram,
}

impl Guest {
    /// The bytecode, a power of two long.
    pub fn prog(&self) -> &[Op] {
        &self.program.prog
    }

    /// Function pc-ranges `(name, entry, len)`.
    pub fn fn_ranges(&self) -> &[(String, u32, u32)] {
        &self.program.fn_ranges
    }

    /// Instructions before the pad to a power of two.
    pub fn code_len(&self) -> usize {
        self.fn_ranges().iter().map(|&(_, _, len)| len as usize).sum()
    }
}

/// Build the guest, its tables and `P`'s assembly of it. All are cached, so this only moves the cost out of the first
/// prove or verify.
pub fn warm_up<P: Prover>() {
    assembled::<P>();
    stacked_bytecode();
    scalar_bytecode();
}

/// The stacked bytecode multilinear of a program, as the prover lays it out: what a transcript's IV hashes and the
/// deferred claims are about.
pub fn bytecode_table(prog: &[Op]) -> Vec<u64> {
    leanvm_core::cpu::layout::bytecode_table(prog)
        .iter()
        .map(|word| word.0)
        .collect()
}

/// The aggregation bytecode, compiled to a fixed point on its own size.
///
/// The recursion placeholders are a function of the inner bytecode's log size,
/// and here the inner bytecode is this one, so the size has to agree with
/// itself. Its *digest* needs no such loop: it rides the statement rather than
/// the code. The guess converges in one or two rounds because the map's only
/// size-dependent part is a handful of unrolled sumcheck rounds.
pub fn unified_guest() -> &'static Guest {
    static GUEST: OnceLock<Guest> = OnceLock::new();
    GUEST.get_or_init(|| {
        // A guess at the guest's own size: right, it compiles once; wrong, one more round.
        let mut guess = 19;
        for _ in 0..8 {
            let guest = compile_guest(guess);
            let actual = guest.prog().len().trailing_zeros() as usize;
            if actual == guess {
                return guest;
            }
            guess = actual;
        }
        panic!("the aggregation bytecode's self-referential compile did not converge");
    })
}

/// The guest as prover `P` runs it, assembled once per prover.
pub(crate) fn assembled<P: Prover>() -> &'static P::Program {
    // A generic function's statics are shared by all its instantiations, so the cache is keyed by the prover's type.
    static ASSEMBLED: Mutex<Vec<(TypeId, &'static (dyn Any + Send + Sync))>> = Mutex::new(Vec::new());
    let mut cache = ASSEMBLED.lock().unwrap();
    let program = match cache.iter().find(|(id, _)| *id == TypeId::of::<P>()) {
        Some(&(_, program)) => program,
        None => {
            let program: &'static P::Program = Box::leak(Box::new(P::assemble(unified_guest().program.clone())));
            cache.push((TypeId::of::<P>(), program));
            program
        }
    };
    program.downcast_ref().expect("cached under its prover's type")
}

/// The stacked bytecode polynomial of the aggregation guest: the one fixed table every node's bytecode claims are
/// about.
pub(crate) fn stacked_bytecode() -> &'static [u64] {
    static TABLE: OnceLock<Vec<u64>> = OnceLock::new();
    TABLE.get_or_init(|| bytecode_table(unified_guest().prog()))
}

/// [`stacked_bytecode`] as the `verifier` crate takes it, hashed once: what [`AggregateProof::verify`](super::AggregateProof::verify) checks proofs against, and [`aggregate`](super::aggregate) reads its children with.
pub(crate) fn scalar_bytecode() -> &'static verifier::Bytecode {
    static BYTECODE: OnceLock<verifier::Bytecode> = OnceLock::new();
    BYTECODE.get_or_init(|| verifier::Bytecode::new(stacked_bytecode()))
}

/// The guest's Fiat-Shamir IV as the two words a statement carries it in.
pub(crate) fn fs_seed() -> [E; 2] {
    hash_to_scalars(&scalar_bytecode().fiat_shamir_iv())
}

pub(super) fn compile_guest(kbc: usize) -> Guest {
    let replacements = placeholder_map(kbc);
    // `DBG_PLACEHOLDERS=path`: dump the baked guest constants, to read alongside
    // a `DBG_PROF_DUMP` profile (the guest's shape is entirely in these).
    if let Ok(path) = std::env::var("DBG_PLACEHOLDERS") {
        let dump: String = replacements.iter().map(|(k, v)| format!("{k} = {v}\n")).collect();
        std::fs::write(&path, dump).expect("write DBG_PLACEHOLDERS");
    }
    let guest = Guest {
        program: compile(
            &parse_with_replacements(GUEST_SOURCE, &replacements).expect("the repository aggregation guest must parse"),
        ),
    };
    // `DBG_DISASM=path`: dump the guest's disassembly, to read alongside a
    // `DBG_PROF_DUMP` per-pc profile. Function boundaries lead the dump, so the
    // pc a failed guest check reports can be resolved to a source function
    // without re-deriving the layout by hand.
    if let Ok(path) = std::env::var("DBG_DISASM") {
        let mut ranges: Vec<_> = guest.fn_ranges().iter().collect();
        ranges.sort_by_key(|(_, entry, _)| *entry);
        let mut dump = String::new();
        for (name, entry, len) in ranges {
            dump += &format!("# fn {entry:>7}..{:<7} {name}\n", entry + len);
        }
        dump += &zkdsl_compiler::disassemble(guest.prog());
        std::fs::write(&path, dump).expect("write DBG_DISASM");
    }
    guest
}
