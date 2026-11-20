//! ML-DSA verification in the guest (`guests/ml_dsa.py`): `n` signatures under one parameter set, each from its own
//! key, proven in one run and verified.

use bench_harness::Plan;
use isa::{Prover, pretty_f64, pretty_integer};
use ml_dsa::{Keypair, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, SigningKey};
use ml_dsa_guest::{Claim, Params, fips};

fn sign<P: MlDsaParams>(seed: [u8; 32], msg: &[u8]) -> Claim {
    let sk = SigningKey::<P>::from_seed(&seed.into());
    let pk = sk.verifying_key().encode().to_vec();
    let sig = sk
        .expanded_key()
        .sign_deterministic(msg, b"")
        .expect("an empty context")
        .encode()
        .to_vec();
    Claim {
        mu: fips::mu(&pk, msg, b""),
        pk,
        sig,
    }
}

/// Prove `n` ML-DSA verifications under `p` in one run, then verify the proof, and print the report.
pub fn run_ml_dsa<P: Prover>(p: Params, n: usize, log_inv_rate: usize, plan: Plan) {
    let trace_span = tracing::info_span!("ML-DSA", set = p.name, n, log_inv_rate).entered();
    let claims: Vec<Claim> = (0..n)
        .map(|i| {
            let (seed, msg) = ([i as u8; 32], format!("message {i}"));
            match p.k {
                4 => sign::<MlDsa44>(seed, msg.as_bytes()),
                6 => sign::<MlDsa65>(seed, msg.as_bytes()),
                _ => sign::<MlDsa87>(seed, msg.as_bytes()),
            }
        })
        .collect();
    let program = ml_dsa_guest::program(&p, n);
    let witness = ml_dsa_guest::witness(&p, &claims).expect("valid signatures have a witness");
    let pi = ml_dsa_guest::public_input(&claims);
    let public_input = verifier::Digest::from_halves(pi[0], pi[1]).0;

    let ((proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench_harness::suppress_tracing);
        P::prove(&program, &witness, pi, log_inv_rate).expect("the ML-DSA guest proves")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench_harness::suppress_tracing);
        verifier::verify_execution(program.bytecode(), &public_input, &proof).unwrap()
    });
    drop(trace_span);

    println!("{} verification, {} signature(s)", p.name, pretty_integer(n));
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    println!(
        "    details                   : {}",
        crate::report::details(&stats, program.code_len())
    );
    crate::report::print_proof_size(proof.to_bytes().len());
    let cycles_per_second = (stats.cycles as f64 / prove_time.mean()).round() as u64;
    println!(
        "  proving                     : {} s{}   {} cycles/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_integer(cycles_per_second),
        crate::report::peak_gib()
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}
