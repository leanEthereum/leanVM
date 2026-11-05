//! The parallel `eq` table must be bit-identical to the serial one.
use primitives::field::F192;
use primitives::multilinear::{eq_table, eq_table_serial, fill_eq_table};
use primitives::test_rng::Rng;

/// Sizes on both sides of the parallel threshold, plain and seeded.
#[test]
fn parallel_eq_table_matches_serial() {
    let mut rng = Rng::new(21);
    for n in [0usize, 1, 6, 15, 16, 17] {
        let point: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
        let serial = eq_table_serial(&point);
        assert_eq!(eq_table(&point), serial, "mismatch at n={n}");
        let g = rng.ext();
        let mut seeded = vec![F192::ZERO; 1 << n];
        fill_eq_table(&point, g, &mut seeded);
        let scaled: Vec<F192> = serial.iter().map(|&e| g * e).collect();
        assert_eq!(seeded, scaled, "seeded mismatch at n={n}");
    }
}
