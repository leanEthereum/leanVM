use super::*;

// Independent bit-serial K product, including reduction by x^64+x^4+x^3+x+1.
fn scalar_mul(mut a: u64, mut b: u64) -> u64 {
    let mut product = 0;
    for _ in 0..64 {
        if b & 1 != 0 {
            product ^= a;
        }
        let carry = a >> 63;
        a <<= 1;
        if carry != 0 {
            a ^= 0x1b;
        }
        b >>= 1;
    }
    product
}
#[test]
#[ignore = "requires ARM_ATTRIBUTION_BASIS_DIR from a non-timed staged production proof"]
fn captured_basis_components() {
    use std::hint::black_box;
    use std::io::{BufReader, Read, Seek, SeekFrom};
    use std::time::Instant;

    const SAMPLE_ROWS: usize = 64;
    const ROWS_PER_GROUP: usize = SAMPLE_ROWS / 2;
    struct Input {
        k: [[u64; ROW]; GROUP],
        e: [[F192; ROW]; GROUP],
    }
    struct Expanded {
        k: [[u64; ROW]; GRID],
        e: [WeightRow; GRID],
    }

    fn read_window<const N: usize>(file: &mut BufReader<std::fs::File>, offset: usize) -> [u8; N] {
        file.seek(SeekFrom::Start(offset as u64)).expect("seek captured row");
        let mut bytes = [0; N];
        file.read_exact(&mut bytes).expect("read captured row");
        bytes
    }
    fn word(bytes: &[u8]) -> u64 {
        u64::from_le_bytes(bytes.try_into().expect("eight-byte coefficient"))
    }
    fn unpack(row: &WeightRow, x: usize) -> F192 {
        let pair = if x.is_multiple_of(2) { &row.lo } else { &row.hi };
        F192::new(pair[x & !1], pair[x | 1], row.c2[x])
    }

    #[inline(never)]
    fn pack_k(inputs: &[Input], expanded: &mut [Expanded]) {
        for (input, grid) in inputs.iter().zip(expanded) {
            for (lane, &at) in LANE_IN_GRID.iter().enumerate() {
                for (dst, &src) in grid.k[at].iter_mut().zip(&input.k[lane]) {
                    *dst = src;
                }
            }
        }
    }
    #[inline(never)]
    fn pack_e(inputs: &[Input], expanded: &mut [Expanded]) {
        for (input, grid) in inputs.iter().zip(expanded) {
            for (lane, &at) in LANE_IN_GRID.iter().enumerate() {
                grid.e[at] = WeightRow::pack(&input.e[lane]);
            }
        }
    }
    #[inline(never)]
    fn extend_k(expanded: &mut [Expanded]) {
        for grid in expanded {
            extend_grid::<_, PRECOMPUTED_ROUNDS>(&mut grid.k, |a, b| std::array::from_fn(|i| a[i] ^ b[i]));
        }
    }
    #[inline(never)]
    fn extend_e(expanded: &mut [Expanded]) {
        for grid in expanded {
            extend_grid::<_, PRECOMPUTED_ROUNDS>(&mut grid.e, WeightRow::add);
        }
    }
    #[inline(never)]
    fn products(expanded: &[Expanded], acc: &mut [ProductRow; GRID]) {
        for grid in expanded {
            for (acc, (k, e)) in acc.iter_mut().zip(grid.k.iter().zip(&grid.e)) {
                acc.mul_acc(e, k);
            }
        }
    }
    #[inline(never)]
    fn sums(acc: &[ProductRow; GRID], out: &mut [F192; GRID]) {
        for (out, acc) in out.iter_mut().zip(acc) {
            *out = acc.sum();
        }
    }
    fn measure(label: &str, iterations: usize, units: usize, unit: &str, mut run: impl FnMut()) {
        for _ in 0..8 {
            run();
        }
        for sample in 0..5 {
            let start = Instant::now();
            for _ in 0..iterations {
                run();
            }
            let elapsed_ns = start.elapsed().as_nanos();
            let ns_per_sweep = elapsed_ns as f64 / iterations as f64;
            eprintln!(
                "basis_component phase={label} sample={sample} iterations={iterations} elapsed_ns={elapsed_ns} \
                 ns_per_sweep={ns_per_sweep:.3} units_per_sweep={units} unit={unit} ns_per_unit={:.3}",
                ns_per_sweep / units as f64,
            );
        }
    }

    let directory = std::path::PathBuf::from(
        std::env::var_os("ARM_ATTRIBUTION_BASIS_DIR").expect("captured production Basis directory"),
    );
    let shape = std::fs::read(directory.join("shape.bin")).expect("read Basis shape");
    assert_eq!(shape.len(), 24, "three little-endian u64 shape words");
    let (n, block, initial_k) = (
        word(&shape[..8]) as usize,
        word(&shape[8..16]) as usize,
        word(&shape[16..]) as usize,
    );
    assert_eq!(PRECOMPUTED_ROUNDS, 4);
    assert!(initial_k >= PRECOMPUTED_ROUNDS);
    assert!(block.is_power_of_two() && block / ROW >= ROWS_PER_GROUP);
    assert!(
        n.is_multiple_of(block) && n / block >= 2 * GROUP,
        "two complete real lane groups"
    );
    let witness_file = std::fs::File::open(directory.join("witness.bin")).expect("open Basis witness");
    let weight_file = std::fs::File::open(directory.join("weight.bin")).expect("open Basis weight");
    assert_eq!(witness_file.metadata().unwrap().len(), (n * size_of::<F64>()) as u64);
    assert_eq!(weight_file.metadata().unwrap().len(), (n * size_of::<F192>()) as u64);
    let (mut witness, mut weight) = (BufReader::new(witness_file), BufReader::new(weight_file));
    let mut inputs = Vec::with_capacity(SAMPLE_ROWS);
    let mut offsets = Vec::with_capacity(SAMPLE_ROWS);
    for group in 0..2 {
        for sample in 0..ROWS_PER_GROUP {
            let x = sample * (block / ROW - 1) / (ROWS_PER_GROUP - 1) * ROW;
            offsets.push((group, x));
            let mut input = Input {
                k: [[0; ROW]; GROUP],
                e: [[F192::ZERO; ROW]; GROUP],
            };
            for lane in 0..GROUP {
                let at = (group * GROUP + lane) * block + x;
                let ks = read_window::<{ ROW * 8 }>(&mut witness, at * 8);
                let es = read_window::<{ ROW * 24 }>(&mut weight, at * 24);
                for i in 0..ROW {
                    input.k[lane][i] = word(&ks[i * 8..(i + 1) * 8]);
                    let e = &es[i * 24..(i + 1) * 24];
                    input.e[lane][i] = F192::new(word(&e[..8]), word(&e[8..16]), word(&e[16..]));
                }
            }
            inputs.push(input);
        }
    }
    drop((witness, weight));
    let mut expanded: Vec<_> = inputs
        .iter()
        .map(|_| Expanded {
            k: [[0; ROW]; GRID],
            e: [WeightRow::default(); GRID],
        })
        .collect();
    pack_k(&inputs, &mut expanded);
    pack_e(&inputs, &mut expanded);
    // Reconstruct each Boolean lane's ternary index without LANE_IN_GRID.
    for (input, grid) in inputs.iter().zip(&expanded) {
        for lane in 0..GROUP {
            let at = (0..PRECOMPUTED_ROUNDS)
                .map(|bit| ((lane >> bit) & 1) * 3usize.pow(bit as u32))
                .sum::<usize>();
            assert_eq!(grid.k[at], input.k[lane]);
            for x in 0..ROW {
                assert_eq!(unpack(&grid.e[at], x), input.e[lane][x]);
            }
        }
    }
    extend_k(&mut expanded);
    extend_e(&mut expanded);
    let mut expected = [F192::ZERO; GRID];
    for (input, grid) in inputs.iter().zip(&expanded) {
        for (point, expected_sum) in expected.iter_mut().enumerate() {
            let mut point_sum = F192::ZERO;
            for x in 0..ROW {
                let (mut k, mut e) = (0u64, F192::ZERO);
                for lane in 0..GROUP {
                    let included = (0..PRECOMPUTED_ROUNDS).all(|bit| {
                        let digit = point / 3usize.pow(bit as u32) % 3;
                        digit == 2 || digit == (lane >> bit) & 1
                    });
                    if included {
                        k ^= input.k[lane][x];
                        e += input.e[lane][x];
                    }
                }
                assert_eq!(grid.k[point][x], k, "K extension point={point}, offset={x}");
                assert_eq!(unpack(&grid.e[point], x), e, "E extension point={point}, offset={x}");
                point_sum += F192::new(scalar_mul(e.c0, k), scalar_mul(e.c1, k), scalar_mul(e.c2, k));
            }
            let mut product = ProductRow::default();
            product.mul_acc(&grid.e[point], &grid.k[point]);
            assert_eq!(product.sum(), point_sum, "mixed products and reduction point={point}");
            *expected_sum += point_sum;
        }
    }
    let mut acc = [ProductRow::default(); GRID];
    let mut output = [F192::ZERO; GRID];
    products(&expanded, &mut acc);
    sums(&acc, &mut output);
    assert_eq!(output, expected, "aggregate across captured rows");
    eprintln!(
        "basis_component_reference checked=true words={n} block={block} initial_k={initial_k} rows={SAMPLE_ROWS} \
         input_bytes={} expanded_bytes={} accumulator_bytes={} offsets={offsets:?}",
        inputs.len() * size_of::<Input>(),
        expanded.len() * size_of::<Expanded>(),
        size_of_val(&acc),
    );
    // The expanded batch intentionally changes cache/scheduling from the fused production loop.
    // All buffers are allocated before measurement; product accumulation is XOR, so odd repeats retain the sum.
    measure("pack_k", 513, SAMPLE_ROWS, "input_row", || {
        pack_k(black_box(&inputs), black_box(&mut expanded));
    });
    measure("pack_e", 513, SAMPLE_ROWS, "input_row", || {
        pack_e(black_box(&inputs), black_box(&mut expanded));
    });
    measure("extend_k", 513, SAMPLE_ROWS, "input_row", || {
        extend_k(black_box(&mut expanded));
    });
    measure("extend_e", 513, SAMPLE_ROWS, "input_row", || {
        extend_e(black_box(&mut expanded));
    });
    acc.fill(ProductRow::default());
    measure("products", 513, SAMPLE_ROWS * GRID, "grid_point", || {
        products(black_box(&expanded), black_box(&mut acc));
    });
    sums(&acc, &mut output);
    assert_eq!(
        output, expected,
        "odd timed product repetitions preserve the reference sum"
    );
    measure("final_sums", 4097, GRID, "grid_point", || {
        sums(black_box(&acc), black_box(&mut output));
    });
    assert_eq!(output, expected, "timed final reductions preserve the reference sum");
    #[inline(never)]
    fn fused(inputs: &[Input], grid: &mut Expanded, acc: &mut [ProductRow; GRID]) {
        for input in inputs {
            for (lane, &at) in LANE_IN_GRID.iter().enumerate() {
                grid.k[at] = input.k[lane];
                grid.e[at] = WeightRow::pack(&input.e[lane]);
            }
            #[cfg(all(leanvm_grid_candidate, target_arch = "aarch64", target_feature = "aes"))]
            accumulate_grid::<4>(&mut grid.k, &mut grid.e, acc);
            #[cfg(not(all(leanvm_grid_candidate, target_arch = "aarch64", target_feature = "aes")))]
            {
                extend_grid::<_, 4>(&mut grid.k, |a, b| std::array::from_fn(|i| a[i] ^ b[i]));
                extend_grid::<_, 4>(&mut grid.e, WeightRow::add);
                for (a, (k, e)) in acc.iter_mut().zip(grid.k.iter().zip(&grid.e)) {
                    a.mul_acc(e, k);
                }
            }
        }
    }
    acc.fill(ProductRow::default());
    fused(&inputs, &mut expanded[0], &mut acc);
    sums(&acc, &mut output);
    assert_eq!(output, expected, "fused captured grid");
    acc.fill(ProductRow::default());
    measure("fused", 513, SAMPLE_ROWS, "input_row", || {
        fused(black_box(&inputs), black_box(&mut expanded[0]), black_box(&mut acc));
    });
    sums(&acc, &mut output);
    assert_eq!(output, expected, "timed fused captured grid");
    black_box(output);
}

#[test]
#[ignore = "requires captured production witness and weights"]
fn captured_dense_pass() {
    let directory = std::path::PathBuf::from(std::env::var_os("ARM_ATTRIBUTION_BASIS_DIR").unwrap());
    let shape = std::fs::read(directory.join("shape.bin")).unwrap();
    let word = |b: &[u8]| u64::from_le_bytes(b.try_into().unwrap()) as usize;
    let (n, block, initial_k) = (word(&shape[..8]), word(&shape[8..16]), word(&shape[16..]));
    let f: Vec<_> = std::fs::read(directory.join("witness.bin"))
        .unwrap()
        .chunks_exact(8)
        .map(|b| F64(u64::from_le_bytes(b.try_into().unwrap())))
        .collect();
    let b = Basis::Dense(
        std::fs::read(directory.join("weight.bin"))
            .unwrap()
            .chunks_exact(24)
            .map(|b| F192::new(word(&b[..8]) as u64, word(&b[8..16]) as u64, word(&b[16..]) as u64))
            .collect(),
    );
    assert_eq!(f.len(), n);
    let tail3 = std::env::var_os("GRID_TAIL3").is_some();
    if tail3 {
        assert_eq!(n / block, 39, "the production opening has a seven-lane R3 tail");
        let Basis::Dense(weights) = &b else { unreachable!() };
        for sample in 0..64 {
            let x = sample * (block / ROW - 1) / 63 * ROW;
            let mut ks = Vec::with_capacity(7 * ROW);
            let mut es = Vec::with_capacity(7 * ROW);
            for lane in 32..39 {
                ks.extend_from_slice(&f[lane * block + x..lane * block + x + ROW]);
                es.extend_from_slice(&weights[lane * block + x..lane * block + x + ROW]);
            }
            let actual = grid_pass_with::<3>(&ks, ROW, &Basis::Dense(es), 0..7, None);
            for (point, &actual) in actual.iter().enumerate() {
                let mut expected = F192::ZERO;
                for offset in 0..ROW {
                    let (mut k, mut e) = (0, F192::ZERO);
                    for lane in 0..7 {
                        if (0..3).all(|bit| {
                            let digit = point / 3usize.pow(bit) % 3;
                            digit == 2 || digit == (lane >> bit) & 1
                        }) {
                            let at = (32 + lane) * block + x + offset;
                            k ^= f[at].0;
                            e += weights[at];
                        }
                    }
                    expected += F192::new(scalar_mul(e.c0, k), scalar_mul(e.c1, k), scalar_mul(e.c2, k));
                }
                assert_eq!(actual, expected, "captured R3 tail sample={sample}, point={point}");
            }
        }
        eprintln!("captured_R3_tail_reference checked=true sampled_rows=64");
    }
    let mut result = None;
    for sample in 0..6 {
        let start = std::time::Instant::now();
        let grid = if tail3 {
            grid_pass_with::<3>(std::hint::black_box(&f), block, std::hint::black_box(&b), 32..39, None)
        } else {
            initial_rounds(std::hint::black_box(&f), block, initial_k, std::hint::black_box(&b)).grid
        };
        eprintln!(
            "dense_pass sample={sample} elapsed_ns={} grid={grid:?}",
            start.elapsed().as_nanos()
        );
        if let Some(expected) = &result {
            assert_eq!(&grid, expected);
        }
        result = Some(grid);
    }
    if let Some(path) = std::env::var_os("GRID_RESULT") {
        let bytes: Vec<u8> = result
            .unwrap()
            .iter()
            .flat_map(|e| [e.c0, e.c1, e.c2].into_iter().flat_map(u64::to_le_bytes))
            .collect();
        std::fs::write(path, bytes).unwrap();
    }
}
