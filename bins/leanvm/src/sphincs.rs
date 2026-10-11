//! leanSPHINCS signatures verified on the recursion machine: the circuit's cost, then a proof of the batch, timed and
//! verified.

use crate::refuse;
use bench::Plan;
use leansphincs_host::{LayerSignature, MESSAGE};
use leanvm::{Rate, SphincsBatch, SphincsClaim, SphincsFtsOpening, SphincsLayer, SphincsProof, SphincsSignature};
use primitives::{pretty_f64, pretty_integer};

/// A guest layer as the circuit's.
fn layer<const HEIGHT: usize>(l: &LayerSignature<HEIGHT>) -> SphincsLayer<HEIGHT> {
    SphincsLayer {
        counter: l.counter,
        ots: l.ots,
        path: l.path,
    }
}

/// `n` honest signers' claims and signatures, those of `cargo leanvm leansphincs`.
pub fn signed(n: usize) -> (Vec<SphincsClaim>, Vec<SphincsSignature>) {
    (leansphincs_host::signers(n).into_iter())
        .map(|(pk, s)| {
            let claim = SphincsClaim {
                root: pk.root,
                public_param: pk.public_param,
                message: MESSAGE,
            };
            let signature = SphincsSignature {
                randomizer: s.randomizer,
                fts: s.fts.map(|o| SphincsFtsOpening {
                    secret: o.secret,
                    path: o.path,
                }),
                layer0: layer(&s.layer0),
                layer1: layer(&s.layer1),
                layer2: layer(&s.layer2),
            };
            (claim, signature)
        })
        .unzip()
}

/// Prove and verify `n` signatures at `rate`, and print the report; with `tamper`, show instead that a batch whose last
/// signature has one chain element changed has no proof.
pub fn run(n: usize, rate: Rate, tamper: bool, plan: Plan) {
    let (claims, mut signatures) = signed(n);
    let batch = SphincsBatch::new(n, rate).unwrap_or_else(|e| refuse(format_args!("{e}")));
    if tamper {
        signatures[n - 1].layer0.ots[0][0] ^= 1;
        match batch.prove(&claims, &signatures) {
            Ok(_) => panic!("a tampered signature was proven"),
            Err(e) => println!("a batch with one tampered chain element is refused: {e}"),
        }
        return;
    }

    let (proof, prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        batch.prove(&claims, &signatures).expect("honest signatures")
    });
    let bytes = proof.to_bytes();
    let (key, setup_time) = Plan::new(1, 0).measure_quiet(|_| SphincsBatch::new(n, rate).expect("the prover's key"));
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        let proof = SphincsProof::from_bytes(&bytes).expect("the proof's bytes");
        key.verify(&claims, &proof).expect("the proof verifies");
    });

    let stats = batch.stats();
    let rows: Vec<String> = (stats.tables.iter())
        .map(|t| format!("{} {} (2^{})", t.name, pretty_integer(&t.rows), t.height_log))
        .collect();
    let seconds = prove_time.mean();
    println!(
        "leanSPHINCS verification on the recursion machine, {n} signatures, log-inv-rate {}",
        rate.log_inv_rate()
    );
    println!("  rows                        : {}", rows.join("  "));
    println!(
        "  committed words             : {} (2^{:.3})",
        pretty_integer(&stats.committed),
        (stats.committed as f64).log2()
    );
    println!("  proof size                  : {:.1} KiB", bytes.len() as f64 / 1024.0);
    println!(
        "  proving                     : {} s{}   {} signatures/s      peak memory {} GiB",
        pretty_f64(seconds),
        prove_time.spread(),
        pretty_f64(n as f64 / seconds),
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifier key (circuit)      : {} ms",
        pretty_f64(setup_time.mean() * 1000.0)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}
