use field::*;
use fiat_shamir::*;
use koala_bear::{KoalaBear, PackedQuinticExtensionFieldKB, QuinticExtensionFieldKB};
use poly::*;
use sumcheck::*;

type EFKb = QuinticExtensionFieldKB;
type PFKb = <KoalaBear as Field>::Packing;
const DIM_KB: usize = 5;

struct XorShift(u64);
impl XorShift {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

// ---- base_ext_packed kernel tests ----

fn reference_base_ext_packed<
    const DIM: usize,
    F: PrimeField64,
    PF: PackedField<Scalar = F>,
    EFP: BasedVectorSpace<PF> + Copy + Send + Sync,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[PF],
    pol_1: &[EFP],
    sum: EF,
) -> DensePolynomial<EF> {
    assert_eq!(DIM, EF::DIMENSION);
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let half = n / 2;
    let mut c0_acc = [F::ZERO; DIM];
    let mut c2_acc = [F::ZERO; DIM];
    for i in 0..half {
        let x0_lanes = pol_0[i].as_slice();
        let x1_lanes = pol_0[half + i].as_slice();
        let y0_coords = pol_1[i].as_basis_coefficients_slice();
        let y1_coords = pol_1[half + i].as_basis_coefficients_slice();
        for j in 0..DIM {
            let y0_j = y0_coords[j].as_slice();
            let y1_j = y1_coords[j].as_slice();
            for lane in 0..PF::WIDTH {
                let x0 = x0_lanes[lane];
                let x1 = x1_lanes[lane];
                let y0 = y0_j[lane];
                let y1 = y1_j[lane];
                c0_acc[j] += y0 * x0;
                c2_acc[j] += (y1 - y0) * (x1 - x0);
            }
        }
    }
    let c0 = EF::from_basis_coefficients_fn(|j| c0_acc[j]);
    let c2 = EF::from_basis_coefficients_fn(|j| c2_acc[j]);
    let c1 = sum - c0.double() - c2;
    DensePolynomial::new(vec![c0, c1, c2])
}

fn random_kernel_inputs(seed: u64, log_n: usize) -> (Vec<PFKb>, Vec<PackedQuinticExtensionFieldKB>) {
    let mut rng = XorShift(seed | 1);
    let n = 1 << log_n;
    let base: Vec<PFKb> = (0..n)
        .map(|_| PFKb::from_fn(|_| KoalaBear::from_u64(rng.next_u64())))
        .collect();
    let ext: Vec<PackedQuinticExtensionFieldKB> = (0..n)
        .map(|_| {
            PackedQuinticExtensionFieldKB::from_basis_coefficients_fn(|_| {
                PFKb::from_fn(|_| KoalaBear::from_u64(rng.next_u64()))
            })
        })
        .collect();
    (base, ext)
}

#[test]
fn rewritten_kernel_matches_reference_randomized() {
    for (seed, log_n) in [(1u64, 1usize), (2, 2), (3, 4), (4, 7), (5, 11), (6, 12)] {
        let (base, ext) = random_kernel_inputs(seed, log_n);
        let sum = EFKb::from_basis_coefficients_fn(|j| KoalaBear::from_u64(seed + j as u64));
        let new = compute_product_sumcheck_polynomial_base_ext_packed::<DIM_KB, _, _, _, EFKb>(
            &base, &ext, sum,
        );
        let reference = reference_base_ext_packed::<DIM_KB, _, _, _, EFKb>(&base, &ext, sum);
        assert_eq!(new.coeffs, reference.coeffs, "seed={seed} log_n={log_n}");
    }
}

#[test]
fn rewritten_kernel_matches_reference_boundary() {
    let n = 1 << 8;
    let mut rng = XorShift(0xDEAD_BEEF);
    let base: Vec<PFKb> = (0..n)
        .map(|i| match i % 4 {
            0 => PFKb::ZERO,
            1 => PFKb::ONE,
            2 => PFKb::from_fn(|_| KoalaBear::from_u64(u64::MAX)),
            _ => PFKb::from_fn(|_| KoalaBear::from_u64(rng.next_u64())),
        })
        .collect();
    let ext: Vec<PackedQuinticExtensionFieldKB> = (0..n)
        .map(|i| match i % 3 {
            0 => PackedQuinticExtensionFieldKB::ZERO,
            1 => PackedQuinticExtensionFieldKB::ONE,
            _ => PackedQuinticExtensionFieldKB::from_basis_coefficients_fn(|_| {
                PFKb::from_fn(|_| KoalaBear::from_u64(rng.next_u64()))
            }),
        })
        .collect();
    let sum = EFKb::ONE;
    let new = compute_product_sumcheck_polynomial_base_ext_packed::<DIM_KB, _, _, _, EFKb>(
        &base, &ext, sum,
    );
    let reference = reference_base_ext_packed::<DIM_KB, _, _, _, EFKb>(&base, &ext, sum);
    assert_eq!(new.coeffs, reference.coeffs);
}

// ---- full path equality tests ----

struct RecordingFs {
    rng: XorShift,
    polys: Vec<Vec<EFKb>>,
    challenges: Vec<EFKb>,
}

impl RecordingFs {
    fn new(seed: u64) -> Self {
        Self {
            rng: XorShift(seed | 1),
            polys: vec![],
            challenges: vec![],
        }
    }
}

impl ChallengeSampler<EFKb> for RecordingFs {
    fn sample_vec(&mut self, len: usize) -> Vec<EFKb> {
        (0..len)
            .map(|_| {
                let c = EFKb::from_basis_coefficients_fn(|_| KoalaBear::from_u64(self.rng.next_u64()));
                self.challenges.push(c);
                c
            })
            .collect()
    }
    fn sample_in_range(&mut self, _bits: usize, _n_samples: usize) -> Vec<usize> {
        unimplemented!("not used by run_product_sumcheck")
    }
}

impl FSProver<EFKb> for RecordingFs {
    fn state(&self) -> String {
        format!("recording[{}]", self.polys.len())
    }
    fn add_base_scalars(&mut self, _scalars: &[KoalaBear]) {}
    fn observe_scalars(&mut self, _scalars: &[KoalaBear]) {}
    fn duplex(&mut self) {}
    fn pow_grinding(&mut self, _bits: usize) {}
    fn hint_merkle_paths_base(&mut self, _paths: Vec<MerklePath<KoalaBear, KoalaBear>>) {}
    fn add_sumcheck_polynomial(&mut self, coeffs: &[EFKb], _eq_alpha: Option<EFKb>) {
        self.polys.push(coeffs.to_vec());
    }
}

fn random_full_inputs(seed: u64, n_vars: usize) -> (Vec<PFKb>, Vec<PackedQuinticExtensionFieldKB>) {
    let mut rng = XorShift(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let n_packed = (1usize << n_vars) / PFKb::WIDTH;
    let base: Vec<PFKb> = (0..n_packed)
        .map(|_| PFKb::from_fn(|_| KoalaBear::from_u64(rng.next_u64())))
        .collect();
    let ext: Vec<PackedQuinticExtensionFieldKB> = (0..n_packed)
        .map(|_| {
            PackedQuinticExtensionFieldKB::from_basis_coefficients_fn(|_| {
                PFKb::from_fn(|_| KoalaBear::from_u64(rng.next_u64()))
            })
        })
        .collect();
    (base, ext)
}

fn true_sum(base: &[PFKb], ext: &[PackedQuinticExtensionFieldKB]) -> EFKb {
    let mut acc = PackedQuinticExtensionFieldKB::ZERO;
    for (b, e) in base.iter().zip(ext.iter()) {
        acc += *e * *b;
    }
    <PackedQuinticExtensionFieldKB as PackedFieldExtension<KoalaBear, EFKb>>::to_ext_iter([acc]).sum::<EFKb>()
}

fn mle_owned_to_ext_vec(m: &MleOwned<EFKb>) -> Vec<EFKb> {
    match m {
        MleOwned::Base(v) => v.iter().map(|&x| EFKb::from(x)).collect(),
        MleOwned::Extension(v) => v.to_vec(),
        MleOwned::BasePacked(v) => v.iter().flat_map(|p| p.as_slice().to_vec()).map(EFKb::from).collect(),
        MleOwned::ExtensionPacked(v) => {
            <PackedQuinticExtensionFieldKB as PackedFieldExtension<KoalaBear, EFKb>>::to_ext_iter(v.iter().copied())
                .collect()
        }
    }
}

#[test]
fn eager_full_path_deterministic_under_mock() {
    for (seed, n_vars, n_rounds) in [(1u64, 8usize, 2usize), (2, 10, 3), (3, 12, 6)] {
        let (base, ext) = random_full_inputs(seed, n_vars);
        let sum = true_sum(&base, &ext);

        let mut fs_a = RecordingFs::new(seed);
        let out_a = run_product_sumcheck_base_eager::<DIM_KB, EFKb>(&base, &ext, &mut fs_a, sum, n_rounds, 0);
        let mut fs_b = RecordingFs::new(seed);
        let out_b = run_product_sumcheck_base_eager::<DIM_KB, EFKb>(&base, &ext, &mut fs_b, sum, n_rounds, 0);

        assert_eq!(fs_a.polys, fs_b.polys, "seed={seed}");
        assert_eq!(fs_a.challenges, fs_b.challenges, "seed={seed}");
        assert_eq!(out_a.0.0, out_b.0.0, "challenge points seed={seed}");
        assert_eq!(out_a.1, out_b.1, "final sum seed={seed}");
        assert_eq!(mle_owned_to_ext_vec(&out_a.2), mle_owned_to_ext_vec(&out_b.2));
        assert_eq!(mle_owned_to_ext_vec(&out_a.3), mle_owned_to_ext_vec(&out_b.3));
    }
}

#[test]
fn eager_full_path_final_claim_consistent() {
    for (seed, n_vars, n_rounds) in [(7u64, 9usize, 2usize), (8, 11, 4)] {
        let (base, ext) = random_full_inputs(seed, n_vars);
        let sum = true_sum(&base, &ext);
        let mut fs = RecordingFs::new(seed);
        let (_point, final_sum, pol_a, pol_b) =
            run_product_sumcheck_base_eager::<DIM_KB, EFKb>(&base, &ext, &mut fs, sum, n_rounds, 0);
        let a = mle_owned_to_ext_vec(&pol_a);
        let b = mle_owned_to_ext_vec(&pol_b);
        let recomposed: EFKb = a.iter().zip(b.iter()).map(|(&x, &y)| x * y).sum();
        assert_eq!(recomposed, final_sum, "seed={seed} n_vars={n_vars} n_rounds={n_rounds}");
    }
}

// ---- lazy path equality tests ----

fn ef_from(seed: u64, salt: u64) -> EFKb {
    EFKb::from_basis_coefficients_fn(|j| KoalaBear::from_u64(seed.wrapping_mul(salt + 1 + j as u64) | 1))
}

#[test]
fn e1_lazy_round1_matches_eager_oracle() {
    for (seed, n_vars) in [(11u64, 6usize), (12, 7), (13, 9), (14, 11), (15, 14)] {
        let (base, ext) = random_full_inputs(seed, n_vars);
        let r1 = ef_from(seed, 0xA5);
        let sum = ef_from(seed, 0x5A);

        let (poly_lazy, w_lazy) =
            fold_weights_and_compute_lazy_round1::<DIM_KB, _, _, _, EFKb>(&base, &ext, r1, sum);
        let (poly_eager, folded_eager) = fold_and_compute_product_sumcheck_polynomial(&base, &ext, r1, sum, |e| {
            <PackedQuinticExtensionFieldKB as PackedFieldExtension<KoalaBear, EFKb>>::to_ext_iter([e])
                .collect::<Vec<EFKb>>()
        });

        assert_eq!(poly_lazy.coeffs, poly_eager.coeffs, "seed={seed} n_vars={n_vars}");
        assert_eq!(
            w_lazy.as_slice(),
            folded_eager[1].as_slice(),
            "W' seed={seed} n_vars={n_vars}"
        );
    }
}

#[test]
fn e2_fused_round2_entry_matches_fold_twice_oracle() {
    for (seed, n_vars) in [(21u64, 8usize), (22, 9), (23, 10), (24, 13)] {
        let (base, ext) = random_full_inputs(seed, n_vars);
        let r1 = ef_from(seed, 0x11);
        let r2 = ef_from(seed, 0x22);
        let sum = ef_from(seed, 0x33);

        let (_p1, folded1) = fold_and_compute_product_sumcheck_polynomial(&base, &ext, r1, sum, |e| {
            <PackedQuinticExtensionFieldKB as PackedFieldExtension<KoalaBear, EFKb>>::to_ext_iter([e])
                .collect::<Vec<EFKb>>()
        });
        let (p2_oracle, folded2) = fold_and_compute_product_sumcheck_polynomial(
            folded1[0].as_slice(),
            folded1[1].as_slice(),
            r2,
            sum,
            |e| {
                <PackedQuinticExtensionFieldKB as PackedFieldExtension<KoalaBear, EFKb>>::to_ext_iter([e])
                    .collect::<Vec<EFKb>>()
            },
        );

        let (_p1_lazy, w_folded) =
            fold_weights_and_compute_lazy_round1::<DIM_KB, _, _, _, EFKb>(&base, &ext, r1, sum);
        let (p2_lazy, e2, w2) = materialize_double_fold_and_compute_round2::<DIM_KB, _, _, _, EFKb>(
            &base,
            &w_folded,
            r1,
            r2,
            sum,
            true,
            |e| {
                <PackedQuinticExtensionFieldKB as PackedFieldExtension<KoalaBear, EFKb>>::to_ext_iter([e])
                    .collect::<Vec<EFKb>>()
            },
        );

        assert_eq!(
            p2_lazy.unwrap().coeffs,
            p2_oracle.coeffs,
            "poly seed={seed} n_vars={n_vars}"
        );
        assert_eq!(e2.as_slice(), folded2[0].as_slice(), "E'' seed={seed} n_vars={n_vars}");
        assert_eq!(w2.as_slice(), folded2[1].as_slice(), "W'' seed={seed} n_vars={n_vars}");

        let (none_poly, e2b, w2b) = materialize_double_fold_and_compute_round2::<DIM_KB, _, _, _, EFKb>(
            &base,
            &w_folded,
            r1,
            r2,
            sum,
            false,
            |e| {
                <PackedQuinticExtensionFieldKB as PackedFieldExtension<KoalaBear, EFKb>>::to_ext_iter([e])
                    .collect::<Vec<EFKb>>()
            },
        );
        assert!(none_poly.is_none());
        assert_eq!(e2b.as_slice(), e2.as_slice());
        assert_eq!(w2b.as_slice(), w2.as_slice());
    }
}

#[test]
fn e3_full_lazy_vs_eager_transcript_identical() {
    for n_vars in [8usize, 9, 11, 14] {
        for n_rounds in [2usize, 3, 6] {
            if n_rounds > n_vars {
                continue;
            }
            let seed = (n_vars * 100 + n_rounds) as u64;
            let (base, ext) = random_full_inputs(seed, n_vars);
            let sum = true_sum(&base, &ext);

            let mut fs_eager = RecordingFs::new(seed);
            let out_eager =
                run_product_sumcheck_base_eager::<DIM_KB, EFKb>(&base, &ext, &mut fs_eager, sum, n_rounds, 0);
            let mut fs_lazy = RecordingFs::new(seed);
            let out_lazy =
                run_product_sumcheck_base_lazy::<DIM_KB, EFKb>(&base, &ext, &mut fs_lazy, sum, n_rounds, 0);

            assert_eq!(
                fs_lazy.polys, fs_eager.polys,
                "polys n_vars={n_vars} n_rounds={n_rounds}"
            );
            assert_eq!(
                fs_lazy.challenges, fs_eager.challenges,
                "challenges n_vars={n_vars} n_rounds={n_rounds}"
            );
            assert_eq!(out_lazy.0.0, out_eager.0.0, "point n_vars={n_vars} n_rounds={n_rounds}");
            assert_eq!(out_lazy.1, out_eager.1, "sum n_vars={n_vars} n_rounds={n_rounds}");
            assert_eq!(
                mle_owned_to_ext_vec(&out_lazy.2),
                mle_owned_to_ext_vec(&out_eager.2),
                "fold A n_vars={n_vars} n_rounds={n_rounds}"
            );
            assert_eq!(
                mle_owned_to_ext_vec(&out_lazy.3),
                mle_owned_to_ext_vec(&out_eager.3),
                "fold B n_vars={n_vars} n_rounds={n_rounds}"
            );
        }
    }
}
