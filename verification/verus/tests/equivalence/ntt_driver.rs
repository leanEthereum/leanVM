//! Permission-erased driver refinement against the actual production encoder.
//! Each child initializes the real fixed pool with its own worker configuration.
use leanvm_verus::gf2_64::F64 as VerifiedWord;
use leanvm_verus::ntt::{forward_scalar_from_layer, AdditiveNttF64 as Verified};
use pcs::ntt::AdditiveNttF64 as Production;
use primitives::field::F64;
use primitives::test_util::Rng;

fn case(rng: &mut Rng, dim: usize, log_d: usize, lanes: usize, start: usize, plans: &[(usize, usize)]) {
    let len = lanes << log_d;
    let message: Vec<_> = (0..(len >> start)).map(|_| F64(rng.next_u64())).collect();
    let mut production = vec![F64(u64::MAX); len];
    production[..message.len()].copy_from_slice(&message);
    Production::standard(dim).encode_interleaved_in_place(&mut production, lanes, start);
    let input: Vec<_> = message.iter().map(|x| VerifiedWord(x.0)).cycle().take(len).collect();
    let ntt = Verified::standard(dim);
    let mut reference = input.clone();
    forward_scalar_from_layer(&ntt, &mut reference, lanes, start);
    assert_eq!(
        production.iter().map(|x| x.0).collect::<Vec<_>>(),
        reference.iter().map(|x| x.0).collect::<Vec<_>>(),
        "production/reference dim={dim} log_d={log_d} lanes={lanes} start={start}"
    );
    for &(deep, width) in plans {
        let mut actual = input.clone();
        ntt.transform(&mut actual, log_d, lanes, start, deep, width);
        assert_eq!(
            actual.iter().map(|x| x.0).collect::<Vec<_>>(),
            production.iter().map(|x| x.0).collect::<Vec<_>>(),
            "driver/production dim={dim} log_d={log_d} lanes={lanes} start={start} deep={deep} width={width}"
        );
    }
}

#[test]
fn driver_matches_production_across_plans_and_threads() {
    if std::env::var_os("VERUS_DRIVER_CHILD").is_none() {
        for workers in [1, 2, 4] {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "ntt_driver::driver_matches_production_across_plans_and_threads",
                    "--nocapture",
                ])
                .env("VERUS_DRIVER_CHILD", "1")
                .env("LEANVM_NUM_THREADS", workers.to_string())
                .status()
                .unwrap();
            assert!(status.success(), "driver child with {workers} workers failed");
        }
        return;
    }
    let mut rng = Rng::new(0xD215_EE77);
    for log_d in 0..=8 {
        for lanes in [1, 3, 8] {
            for start in 0..=log_d {
                let plans: Vec<_> = (start..=log_d)
                    .flat_map(|deep| [1, 2, 3, 7].map(|width| (deep, width)))
                    .collect();
                // A nonempty table also covers the zero-layer domain.
                case(&mut rng, (log_d + 2).max(1), log_d, lanes, start, &plans);
            }
        }
    }
    for (log_d, lanes, start) in [(12, 1, 0), (12, 3, 2), (13, 56, 1), (16, 3, 3)] {
        case(
            &mut rng,
            log_d,
            log_d,
            lanes,
            start,
            &[(start, 3), ((start + log_d) / 2, 3), (log_d, 5)],
        );
    }
}
