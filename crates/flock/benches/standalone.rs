//! Standalone Flock: a batch of BLAKE2s compressions proven by three sumchecks, its two evaluation claims
//! opened apart (`flock::standalone`).
//!
//! ```text
//! BENCH_REPEAT=3 FLOCK_N_LOG=18 cargo bench -p flock --bench standalone
//! ```
//!
//! `FLOCK_MATRIX=0` leaves the matrices uncommitted and their claim unopened: the table is `2^29` words.
//! `BENCH_TRACING=1` prints the final pass's span tree.

use std::time::Instant;

use bench::{Plan, Timing, env_usize};
use fiat_shamir::transcript::{Proof, ProverState, Receiver, Transmitter, VerifierState};
use flock::hash::{
    Compression, K_LOG, USEFUL_BITS, WalkLincheckCircuit, Z_CONST_POS, generate_witness_with_ab_packed_and_lincheck,
    min_n_blocks_log, pinned_compression, stacked_matrices,
};
use flock::standalone::{self, Witness, opening};
use primitives::{field::F64, pretty_integer, test_rng::Rng};

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

const STAGES: [&str; 5] = [
    "witness-gen",
    "commit witness",
    "sumchecks",
    "open witness",
    "open matrices",
];

fn opening_bytes(proof: &Proof) -> usize {
    let merkle = |m: &fiat_shamir::merkle::PrunedMerklePaths| {
        32 * m.sibling_hashes.len() + m.leaf_data.iter().map(|row| 8 * row.len()).sum::<usize>()
    };
    24 * proof.stream.len() + proof.merkle.iter().map(merkle).sum::<usize>()
}

fn main() {
    bench::init_tracing_from_env();
    let n = 1usize << env_usize("FLOCK_N_LOG", 13);
    let n_log = min_n_blocks_log(n);
    let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let blocks: Vec<Compression> = (0..n)
        .map(|_| pinned_compression(std::array::from_fn(|_| rng.next_u32())))
        .collect();

    // The matrices are the circuit: committed once, the root is part of the statement.
    let t = Instant::now();
    let matrices = (env_usize("FLOCK_MATRIX", 1) == 1).then(|| {
        let table = stacked_matrices();
        let (root, data) = opening::commit(&table);
        (table, root, data)
    });
    let setup_s = t.elapsed().as_secs_f64();
    let mut label = b"standalone-flock".to_vec();
    label.extend_from_slice(&matrices.as_ref().map_or([0; 32], |m| m.1));
    label.push(n_log as u8);

    let prove_pass = || {
        let _span = tracing::info_span!("Standalone prove", n_log).entered();
        let mut secs = [0.0; STAGES.len()];
        let mut stage = 0;
        let mut timed = |secs: &mut [f64; STAGES.len()], t: Instant| {
            secs[stage] = t.elapsed().as_secs_f64();
            stage += 1;
        };

        let t = Instant::now();
        let (z, a, b, z_lincheck) = generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
        // SAFETY: `F64` is `repr(transparent)` over `u64`.
        let packed: &[F64] = unsafe { std::slice::from_raw_parts(z.as_ptr().cast(), z.len()) };
        timed(&mut secs, t);

        let t = Instant::now();
        let (root, data) = opening::commit(packed);
        timed(&mut secs, t);

        let t = Instant::now();
        let mut ps = ProverState::from_label(&label);
        ps.add_root(&root);
        let witness = Witness {
            z: &z,
            a: &a,
            b: &b,
            z_lincheck: &z_lincheck,
        };
        let claims = standalone::prove(&WalkLincheckCircuit, USEFUL_BITS, n_log, witness, &mut ps);
        let proof = ps.into_proof();
        timed(&mut secs, t);
        drop((a, b, z_lincheck));

        let t = Instant::now();
        let witness_opening = opening::open(packed, &root, &data, &claims.witness);
        timed(&mut secs, t);

        let t = Instant::now();
        let matrix_opening = matrices
            .as_ref()
            .map(|(table, root, data)| opening::open(table, root, data, &claims.matrix));
        timed(&mut secs, t);
        ((proof, witness_opening, matrix_opening), secs)
    };

    let plan = Plan::from_env();
    let mut stages: [Timing; STAGES.len()] = std::array::from_fn(|_| Timing::default());
    let ((proof, witness_opening, matrix_opening), _) = plan.warm_then_measure(|final_pass| {
        let _quiet = (!final_pass).then(bench::suppress_tracing);
        let (out, secs) = prove_pass();
        for (timing, s) in stages.iter_mut().zip(secs) {
            timing.push(s);
        }
        out
    });

    // The verifier: the sumchecks down to two claims, then each claim's opening on its own.
    let (claims, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|_| {
        let mut vs = VerifierState::from_label(&label, &proof);
        let root = vs.next_root().expect("witness root");
        let claims = standalone::verify(K_LOG, Z_CONST_POS, n_log, &mut vs).expect("the sumchecks verify");
        vs.finish().expect("proof fully consumed");
        (root, claims)
    });
    let (root, claims) = claims;
    let (_, openings_time) = Plan::new(plan.repeat, 0).measure_quiet(|_| {
        assert!(opening::verify(&root, &claims.witness, &witness_opening));
        if let (Some((_, root, _)), Some(opening)) = (&matrices, &matrix_opening) {
            assert!(opening::verify(root, &claims.matrix, opening));
        }
    });

    println!(
        "\nStandalone Flock, {} BLAKE2s compressions (2^{} constraints)",
        pretty_integer(n),
        K_LOG + n_log
    );
    println!("  setup, matrices committed once    : {:>8.1} ms", setup_s * 1e3);
    for (name, timing) in STAGES.iter().zip(&stages) {
        // The warmup pass pushed a sample too.
        let mut kept = Timing::default();
        timing.samples()[1..].iter().for_each(|&s| kept.push(s));
        println!("  {name:<34}: {:>8.1} ms{}", kept.mean() * 1e3, kept.spread());
    }
    println!(
        "  verify sumchecks                  : {:>8.3} ms",
        verify_time.mean() * 1e3
    );
    println!(
        "  verify openings                   : {:>8.3} ms",
        openings_time.mean() * 1e3
    );
    // The witness root rides the proof as two scalars; everything after it is sumcheck messages.
    println!(
        "  proof                             : {} scalars + root = {} bytes",
        proof.stream.len() - 2,
        24 * (proof.stream.len() - 2) + 32
    );
    println!(
        "  witness opening                   : {:.1} KiB",
        opening_bytes(&witness_opening) as f64 / 1024.0
    );
    if let Some(opening) = &matrix_opening {
        println!(
            "  matrices opening                  : {:.1} KiB",
            opening_bytes(opening) as f64 / 1024.0
        );
    }
    println!(
        "  peak memory                       : {:.1} GiB",
        bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64
    );
}
