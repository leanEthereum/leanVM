use backend::*;
use lean_vm::*;

const WIDTH: usize = 8;

fn xorshift(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

#[test]
fn deferred_aux_fill_equals_scalar() {
    let mut seed = 0xDEADBEEF_u64;
    let n = 1003;
    let n_cols = num_cols_total_poseidon_8();
    let aux_start = POSEIDON_8_COL_ROUND_START;
    let aux_end = aux_start + (num_cols_poseidon_8() - POSEIDON_8_COL_ROUND_START);
    let mut trace: Vec<ArenaVec<F>> = (0..n_cols).map(|_| ArenaVec::new()).collect();
    for (c, col) in trace.iter_mut().enumerate() {
        if (aux_start..aux_end).contains(&c) {
            continue;
        }
        for _ in 0..n {
            col.push(F::from_u64(xorshift(&mut seed)));
        }
    }
    fill_trace_poseidon_8(&mut trace);

    assert!(trace.iter().all(|col| col.len() == n));
    for i in 0..n {
        let input: [F; WIDTH] = std::array::from_fn(|j| trace[POSEIDON_8_COL_INPUT_START + j][i]);
        let (aux, _) = compute_poseidon8_witness(input);
        for (k, v) in aux.iter().enumerate() {
            assert_eq!(trace[aux_start + k][i], *v, "aux[{k}] row {i}");
        }
    }
}

#[test]
#[ignore]
fn mds_witness_microbench() {
    let mut seed = 1u64;
    let inputs: Vec<[F; 8]> = (0..10_000)
        .map(|_| std::array::from_fn(|_| F::from_u64(xorshift(&mut seed))))
        .collect();
    let t = std::time::Instant::now();
    let mut sink = F::ZERO;
    for inp in &inputs {
        let (_aux, out) = compute_poseidon8_witness(*inp);
        sink += out[0];
    }
    let dt = t.elapsed();
    println!(
        "compute_poseidon8_witness: {:?} for 10k perms ({:.0} ns/perm), sink={sink:?}",
        dt,
        dt.as_nanos() as f64 / 10_000.0
    );
}

#[test]
#[ignore]
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
fn packed_witness_microbench() {
    const BATCHES: usize = 16_384;

    let mut seed = 0xC0FFEE_u64;
    let inputs: Vec<[[F; WIDTH]; WITNESS_LANES]> = (0..BATCHES)
        .map(|_| std::array::from_fn(|_| std::array::from_fn(|_| F::from_u64(xorshift(&mut seed)))))
        .collect();

    let n_aux = num_cols_poseidon_8() - POSEIDON_8_COL_ROUND_START;

    for batch in inputs.iter().take(64) {
        let (aux_p, out_p) = compute_poseidon8_witness_x8(batch);
        for l in 0..WITNESS_LANES {
            let (aux_s, out_s) = compute_poseidon8_witness(batch[l]);
            for (k, a) in aux_s.iter().enumerate().take(n_aux) {
                assert_eq!(aux_p[k].0[l], *a, "aux[{k}] lane {l}");
            }
            for j in 0..WIDTH {
                assert_eq!(out_p[j].0[l], out_s[j], "out[{j}] lane {l}");
            }
        }
    }

    let mut scalar_best = std::time::Duration::MAX;
    let mut packed_best = std::time::Duration::MAX;
    let mut sink = F::ZERO;
    for _ in 0..3 {
        let t = std::time::Instant::now();
        for batch in &inputs {
            for inp in batch {
                let (aux, out) = compute_poseidon8_witness(*inp);
                sink += out[0] + aux[n_aux - 1];
            }
        }
        scalar_best = scalar_best.min(t.elapsed());

        let t = std::time::Instant::now();
        for batch in &inputs {
            let (aux, out) = compute_poseidon8_witness_x8(batch);
            sink += out[0].0[0] + aux[n_aux - 1].0[WITNESS_LANES - 1];
        }
        packed_best = packed_best.min(t.elapsed());
    }

    let n_perms = (BATCHES * WITNESS_LANES) as f64;
    println!(
        "scalar {:?} ({:.0} ns/perm) | packed {:?} ({:.0} ns/perm) | speedup {:.2}x | sink={sink:?}",
        scalar_best,
        scalar_best.as_nanos() as f64 / n_perms,
        packed_best,
        packed_best.as_nanos() as f64 / n_perms,
        scalar_best.as_secs_f64() / packed_best.as_secs_f64(),
    );
}
