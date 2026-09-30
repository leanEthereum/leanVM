//! The generic class witness: the gate list walked one instance at a time, against 64 at a time.
//!
//! ```text
//! BENCH_REPEAT=5 BENCH_COOLDOWN=0 cargo bench -p leanvm_core --bench class_witness
//! ```

use bench::Plan;
use primitives::test_rng::Rng;

fn main() {
    // One batch of 2^16 instances per class, the size of a mid-sized run's table.
    let n_log = bench::env_usize("WITNESS_N_LOG", 16);
    let plan = Plan::from_env();
    leanvm_core::init_prover();

    println!(
        "{:<6} {:>5} {:>10} {:>10} {:>8}",
        "class", "k_log", "walk", "64 lanes", "speedup"
    );
    // Every class without a word-level witness of its own.
    for spec in leanvm_core::tables::CLASSES
        .iter()
        .filter(|spec| spec.witness.is_none())
    {
        let circuit = (spec.circuit)();

        // Random input words: the walk costs the same on any input.
        let mut rng = Rng::new(0xC1A55);
        let rows: Vec<Vec<u64>> = (0..1 << n_log)
            .map(|_| (0..circuit.n_input_words()).map(|_| rng.next_u64()).collect())
            .collect();

        // Each pass is one proof's worth of arena, reclaimed by the next.
        let (_, walk) = plan.warm_then_measure(|_| {
            let _phase = zk_alloc::enter_phase();
            circuit.generate_witness_with(&rows, &rows[0], n_log, |row, z, az, bz| {
                circuit.witness_instance(row, z, az, bz)
            });
        });
        let (_, sliced) = plan.warm_then_measure(|_| {
            let _phase = zk_alloc::enter_phase();
            circuit.generate_witness_from(&rows, &rows[0], n_log, |row, words| words.copy_from_slice(row));
        });

        // Wall time per instance, all threads.
        let per_instance = |secs: f64| secs * 1e9 / (1 << n_log) as f64;
        println!(
            "{:<6} {:>5} {:>7.1} ns {:>7.1} ns {:>7.1}x",
            spec.name,
            circuit.k_log(),
            per_instance(walk.mean()),
            per_instance(sliced.mean()),
            walk.mean() / sliced.mean(),
        );
    }
}
