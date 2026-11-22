# 24. The DEEP fold's point evaluations, measured

Researcher 24 (measurement). Scope: the prover time of the point evaluations that Protocol D (note 14) and its ladder schedule (note 15) add, which notes 11 and 15 only estimated ("3 to 10 percent of proving time at rate 1/2", from formula counts and one traced `OOD` span). Statuses: **[measured]** (wall time on this machine, conditions stated), **[derived]** (arithmetic on measured numbers), **[estimate]**. No file of the repository was changed. The benchmark is a scratch cargo project outside the repository (section 9) that links the experimental tree's `primitives` and `parallel` by path, with the workspace's flags (`-C target-cpu=native`, thin LTO, one codegen unit) and the benchmark CLI's allocator.

Notation: $K = \mathrm{GF}(2^{64})$, $E = \mathrm{GF}(2^{128})$, a stack of $2^\mu$ words of $K$ in $2^\ell = 64$ lanes of $2^\kappa$ words (lane $u$ is words $u2^\kappa$ to $(u+1)2^\kappa - 1$, the layout `whir::commit` takes). The benchmark's stack (`aggregate --xmss 900`) is $\kappa = 20$ with 40 data lanes, $2^{25.3}$ words, 320 MiB; the other 24 lanes are zero and cost nothing. **One OOD evaluation** means one call of `mle_eval_par` on that stack, which is what today's `OOD` span is. It is the unit of this note, written `a`, because it can be measured both in the scratch benchmark and inside the real prover.

## 0. Summary

1. **Twelve points in one batch cost about 2.3 percent of `Prove` at rate 1/2, net of today's OOD evaluation, which disappears (2.7 percent gross).** **[derived]** from measured ratios: other agents kept the machine saturated for the whole session, so the number is assembled from load-robust ratios and has a wide spread, 1.0 to 3.3 percent. The ladder of note 15: 2.1 percent net. A hypothetical 6-point design: 1.1 percent. A 3-point design: 0.4 percent. Section 6 has the table and what each range is made of. The estimate of notes 11 and 15 was 3 to 10 percent, so the truth is at or below its lower end.
2. **The fused pass is bound by the carry-less multiplier, not by memory.** A point costs two `PMULL` per word of the stack and nothing can lower that count (section 5.3). One performance core of the M4 does 7.6 G `PMULL` per second **[measured]**, and the best kernel reaches 7.4 G. So twelve points in one pass cost 9.1 OOD evaluations on one thread and 6.3 at all threads, against 12.0 as twelve separate passes: fusing halves the cost at all threads, it does not make it "one pass". The lead's expectation that $s$ accumulators cost much less than $s$ passes holds only up to this factor of two on this machine.
3. **Best kernel** (section 5): rows of 256 words of one lane, read once; the points in groups of four, each group one walk of the row with its eight accumulators in registers; the low weights (256 per point) stored interleaved in the order of the walk, as coefficient pairs, so one 128-bit load of data meets one point with four `PMULL` and two `EOR3` and no shuffle; one reduction per row and point; one unreduced accumulator per lane and point. It takes 24 percent less time per point than today's `dot_base` on one thread (11.4 against 15.0 ms) because the portable `dot_base` loop is two dependency chains, not because of memory.
4. **The carried scalars are free, provided the pass returns the per-lane evaluations** $P_u(\zeta_m)$ and not only $y_m$: all 72 scalars of a 12-point batch take 21 microseconds from the 64 lane values per point **[measured]**, identity **[checked]** against real affine folds. Computed as passes of their own they would cost 12.9 OOD evaluations, twice the answers themselves. This confirms note 11 section 3.4 and is not optional.
5. **The ladder saves less time than its multiplication count says.** Its six late points are answered on the folded lanes, which are $E$-valued: 2.2 OOD evaluations as five passes of their own, against 2.8 saved on the first batch. At all threads the ladder's answers cost 5.7 against 6.3 for the single batch (10 percent less), on one thread 6.3 against 9.6 (34 percent less, which is what the count of note 15 predicts). The ladder's saving in scalars is unaffected.
6. **One cost nobody counted: the conversion.** At the level's end the $s$ point claims join the next level's weight as dense tensors over $2^\kappa$ coefficients. For 12 points at level 0 that is 1.0 OOD evaluation as I implemented it (0.6 by multiplication count), an eighth of the total. It is in the totals above.
7. **Not measured:** the verifier, the guest, the transcript, the real integration, any x86 machine, and the real prover at other stack sizes (section 8).

## 1. What the prover computes, as passes over memory

**The answer of a point is one tensor-weighted inner product over the stack.** For a point $z_m = (\theta_m, \zeta_m)$, note 14 Definition E gives $y_m = \sum_u \theta_m^{e(u)} P_u(\zeta_m)$, and in the novel basis $P_u(\zeta) = \sum_c f(u, c)\,\mathcal{X}_c(\zeta)$ with $\mathcal{X}_c(\zeta) = \prod_{k: c_k = 1} \widehat W_k(\zeta)$ (`def:enc`, `lem:colweight`, at a point that need not be in the domain). So the weight of word $(u, c)$ is a product of one factor per bit of $c$ and one per bit of $u$: the same shape as the `eq` weights of today's OOD evaluation, with factors $(1, \widehat W_k(\zeta))$ instead of $(1 + r_k, r_k)$. The $\kappa + 1$ values $\widehat W_k(\zeta_m)$ are one squaring and two mixed products each (`Subspace::at` of `crates/verifier/src/whir.rs` with the argument in $E$), nanoseconds.

**The split.** With $c = h\,2^L + l$: $P_u(\zeta_m) = \sum_h \mathrm{high}_m[h] \sum_l \mathrm{low}_m[l]\, f(u, h2^L + l)$, where $\mathrm{low}_m$ has $2^L$ weights and $\mathrm{high}_m$ has $2^{\kappa - L}$. The inner sum is $2^L$ products $K \times E$, accumulated unreduced (two `PMULL` each), then one reduction and one product $E \times E$ per row and point. The lane weights $\theta^{e(u)}$ are applied to 64 numbers at the end. All points of a batch are known together (one verifier message), so one pass over the stack can serve them all.

**Per-lane values.** The pass should return the $2^\ell s$ values $P_u(\zeta_m)$, not only the $s$ sums. Then (note 14, Lemma E, E1 to E3) every later scalar of these points is arithmetic on 64 numbers per point: round $j$'s carried scalar is $\varphi^{(j)}_m = \sum_{u'} \theta_m^{e_j(u')} v_{(0,u')}$ on the current lane values $v$, and the fold maps them to $v'_{u'} = v_{(1,u')} + (\alpha_j + \beta_j\zeta_m)\,v_{(0,u')}$. It is the verifier's `fold_row` at $\zeta_m$ instead of a domain point. **[checked]** in the benchmark's self-test: lanes of $2^5$ coefficients, three real affine folds $P = G + \alpha F + \beta XF$ with multiplication by $X$ in the novel basis (the verifier's test helper `times_x`), $\zeta \in E$; the scalars derived from the lane values equal the direct evaluations of the folded coefficient vectors, high coefficients included, in every round, and the carried value follows the update of step 1(c).

**Where the ladder's data lives.** The ladder answers a point sampled with challenge $j$ on the tuple after $j$ rounds. Today's prover does hold that tuple: `whir_lanes.rs` writes each round's folded pairs (`Pairs::Stored`, separate `f` and `g` arrays of $E$) inside the next round's table pass. After $j$ rounds it has $\lceil 40/2^j \rceil$ lanes (20, 10, 5, 3, 2) of $2^\kappa + j$ coefficients. A product $E \times E$ accumulated unreduced is four `PMULL` (with the weight stored as $(b_0, b_1 \mid b_1, b_0 + x b_1)$ so that no shift is left in the loop), so a pass over the tuple after one round costs exactly as many multiplications as a pass over the stack, and halves each round after.

**The conversion.** At the level's end (note 14, step 2(e)) each point claim becomes a weighted claim with weight $W_{i,\zeta_m}(c) = \mathcal{X}_c(\zeta_m)$ on the $2^{\kappa}$ low coefficients, scaled by $\lambda^m$ and added to the weight the next level's rounds run on. A query's weight is induced by a transposed NTT today, which does not apply to a point outside the domain, so this is $s$ dense tensors: $s\,2^\kappa$ products $E \times E$ in one pass over the weight.

## 2. Setup, load, and method

**Machine.** Apple M4 Max, 12 performance and 4 efficiency cores, 48 GB, macOS (Darwin 27.0.0), rustc 1.100.0. The experimental pool's default: 15 threads, 11 on performance cores and 4 on efficiency cores. One thread is `set_num_threads(1)`, strictly sequential. The allocator is `allocator::Jemalloc` as in the benchmark CLI.

**Load.** Other agents of the swarm ran computations on the same machine for the whole session, and from 18:08 on they saturated it. `uptime` load averages (16 cores): 11.6 at 17:53, 9.0 at 18:02, 6.8 at 18:05 (the quietest minutes of the session), 21 at 18:08, 24 at 18:13, 32 at 18:19, 35 at 18:24, 44 at 18:32, 59 at 18:39, 36 at 18:42. Idle CPU (one-second `top` samples): 24 percent at 18:09, a median of 17 percent over 40 seconds at 18:31, often zero. Another checkout's `leanvm-bench` ran in the same minutes. The real prover's `Prove`, 450 ms in the lead's run, took between 0.85 and 9.9 seconds in mine. I waited twice for a quiet window (four and six minutes, threshold 65 to 70 percent idle) and none came. Consequences:

- Absolute all-thread times of this note are not quiet-machine times. I give the best observed, the median, and the load.
- A loaded scheduler serves a short burst faster than sustained work (twelve back-to-back passes cost 20 to 25 times one isolated pass in my first runs, not 12). Every comparison below is therefore a **round robin**: each round runs every item for about the same duration (an item is repeated 2 to 24 times back to back and its mean taken), with today's OOD evaluation `a` run before and after each item; the ratio of an item to the mean of its two neighbouring `a` is taken per round, and I report the median and the quartiles over rounds.
- The ratio to `a` is converted to a share of `Prove` through the `OOD` span of traced runs of the real prover: the span is `a` under exactly the conditions of that run, so share = ratio times `OOD`/`Prove` of the same trace. This `OOD`/`Prove` is the weakest link under load (section 6).
- One-thread numbers are much more stable. The run at 18:05 (load 6.8) had its best, median and worst repetition within 1 percent of each other for most items, which says the thread kept a performance core to itself; I use it as the clean one-thread reference and confirm its ratios with later round robins under load.
- Process CPU time (`CLOCK_PROCESS_CPUTIME_ID`) undercounts short multi-threaded bursts on macOS and is not used.

**Data.** The stack is pseudo-random words of $K$; the folded lanes are pseudo-random elements of $E$ of the right sizes (no kernel here is data dependent; real folds are used only in the self-test). Points are random in $E^2$ with the real $\widehat W_k(\zeta)$. Every timed item includes building its weight tables.

## 3. One thread

**[measured]** at 18:05, load average 6.8, stack $\kappa = 20$, 40 lanes; best of 3, and the spread between best and worst was under 1 percent except where noted.

| item | ms | per point, ms | G `PMULL`/s |
| --- | --- | --- | --- |
| (a) today's OOD evaluation, `mle_eval_par` | 15.05 | 15.05 | 5.6 |
| (b) 1 point as a pass, today's kernel shape (rows of $2^{10}$, `dot_base`) | 14.87 | 14.87 | 5.6 |
| (b) 12 points as 12 such passes | 179.7 | 15.0 | 5.6 |
| (c) 12 points fused, same portable kernel | 181.8 | 15.1 | 5.5 |
| (c) 12 points fused, best kernel (groups of 4, rows of $2^8$) | 137.9 | 11.5 | 7.3 |
| (c) same, groups of 3 / of 12 | 137.8 / 136.6 | 11.4 | 7.4 |
| (c) 6 points fused, best kernel | 68.9 | 11.5 | 7.3 |
| (c) 3 points fused | 34.7 | 11.6 | 7.2 |
| (c) 2 points fused | 23.4 | 11.7 | 7.2 |
| (c) 12 points fused, fold-style (each row folded variable by variable per point) | 710 | 59 | |
| one point on the lanes after one round ($E$-valued, same bytes as the stack) | 11.7 | 11.7 | 7.2 |
| 12 points fused on the same lanes | 150.9 | 12.6 | 6.7 |
| single-core `PMULL` ceiling (microbenchmark, 8 or more independent chains, L1 data) | | | 7.6 |
| same with 1 / 2 / 4 chains | | | 2.85 / 5.67 / 6.95 |

On one thread fusing by itself buys nothing (179.7 against 181.8 ms with the same kernel): one core is nowhere near memory bandwidth (320 MiB in 15 ms). All of the gain is the kernel reaching the multiplier's throughput.

Round robins under load, one thread, 8 rounds (18:29 to 18:32, load above 40, where `a` itself took 27 to 60 ms), ratios to `a`, median and quartiles **[measured]**: 12 fused 9.6 (7.9 to 10.3), against 9.1 in the clean run; 6 fused 4.4 (3.5 to 5.2), clean 4.6; 3 fused 2.3 (2.1 to 2.8), clean 2.3; 1 point 0.84 (0.79 to 1.02); the ladder's five late passes together 1.92 (1.79 to 1.99); 12 separate passes of today's kernel 12.0 (10.4 to 14.2); 12 fused with the portable kernel 11.9 (11.1 to 12.5).

The remaining items come from one run under heavy load (18:41, `a` at 23.8 ms instead of 15.0), so I give them as ratios to that run's `a` **[measured, loaded]**: the ladder's late passes one by one (1 point on the lanes after round 1; 1 after round 2; 2 after round 3; 1 after round 4; 1 after round 5) 0.92, 0.42, 0.39, 0.13, 0.09, sum 1.95; the carried scalars as passes of their own, batch of 12: 17.3 (round 1 alone, a fused pass over the even lanes of the stack: 6.1); the same for the ladder: 10.8; the conversion of 12 points: 1.02, of 6 points: 0.52; level 1's answers (a message of $2^{20}$ elements of $E$ in 16 lanes), 9 points: 0.34, 6 points: 0.23; level 2's, 9 points: 0.02; the carried scalars derived from the lane values, 12 points, all six rounds: 0.021 ms.

## 4. All threads

**[measured]**, 15 threads, same stack, 68 rounds pooled from four round robins between 18:23 and 18:35 (load averages 27 to 44). "Best" is the least mean of a back-to-back group; the lead's traced run had `OOD` at 1.55 ms, so even the best `a` here (2.09 ms) is 35 percent above a quiet machine.

| item | best ms | median ms | ratio to `a`, median | quartiles |
| --- | --- | --- | --- | --- |
| (a) today's OOD evaluation | 2.09 | 10.8 | 1 | |
| (c) 1 point, best kernel | 2.07 | 9.6 | 0.99 | 0.69 to 1.40 |
| (c) 3 points fused | 4.38 | 19.5 | 1.82 | 1.51 to 2.28 |
| (c) 6 points fused | 9.02 | 34.7 | 3.50 | 2.60 to 4.79 |
| (c) 12 points fused | 16.2 | 65.3 | 6.34 | 5.17 to 8.96 |
| (c) 12 points fused, portable `dot_base` kernel | 20.3 | 80.7 | 8.22 | 6.06 to 11.3 |
| (b) 12 points as 12 passes, today's kernel | 26.9 | 136.5 | 12.0 | 9.5 to 17.4 |
| (d) ladder, the five late passes (1, 1, 2, 1, 1 points on the folded lanes) | 4.83 | 25.0 | 2.21 | 1.77 to 3.18 |
| (d) ladder, all answers: 6 fused, then the late passes **[derived]** | 13.9 | | 5.7 | |
| (e) carried scalars as passes of their own, batch of 12 (16 rounds) | 94 | 150 | 12.9 | 8.8 to 18.7 |
| (e) carried scalars from the lane values, batch of 12 | 0.021 | 0.021 | | |
| later levels: level 1's answers, 9 points (16 rounds) | 2.46 | 5.9 | 0.47 | 0.30 to 0.74 |
| conversion of 12 point claims at the end of level 0 (9 repetitions, not in the round robin) | 4.2 | 5.8 | 1.0 | |

The per-round medians of the four round robins for "12 points fused" were 5.7, 6.5, 5.9 and 6.9, so the pooled 6.3 is stable to about 10 percent even though single rounds scatter by a factor of two.

Reading: at all threads the cost is close to $0.4 + 0.5 s$ OOD evaluations for $s$ fused points. The constant is the one read of the stack; the slope is the multiplications, and it is lower than on one thread (0.76 per point) because `a` itself scales worse than the fused pass (it is short, and partly bound by memory at 15 threads).

**Quiet-machine value [estimate].** Three routes agree on 11 to 14 ms for the twelve fused answers on a quiet machine, against 1.55 ms for today's evaluation: the ratio 6.3 to 9.1 times 1.55 ms gives 9.8 to 14.1 ms; the best observed 16.2 ms scaled by 1.55/2.09 gives 12.0 ms; the one-thread 136.6 ms divided by the parallel speedup the lead's trace implies for `a` (15.05/1.55 = 9.7) gives 14.1 ms, and divided by 12.5 performance-core equivalents 10.9 ms.

## 5. Kernels

### 5.1 What was tried

All on the $2^{25.3}$ stack, 12 points fused, one thread, clean run (ms); the all-thread ordering is the same where I could resolve it (the best three are within the noise of each other).

| kernel | ms | comment |
| --- | --- | --- |
| rows of $2^{10}$, per point one `primitives::dot_base` against a packed low table (what a first integration would write) | 181.8 | the low tables of 12 points are 196 KB, beyond L1; the aarch64 `dot_base` is two chains |
| the same with rows of $2^8$ | 250.8 | not understood; the tables fit L1 |
| rows of $2^{10}$, per point one hand-written walk with 4 chains | 165.2 | tables beyond L1 |
| rows of $2^8$, same walk | 158.7 | |
| rows of $2^{10}$, all 12 points interleaved | 159.0 | tables beyond L1 |
| rows of $2^8$, all 12 points interleaved, 24 accumulators | 136.6 | |
| **rows of $2^8$, groups of 4 points, 8 accumulators** | **137.9** | the choice: same speed, and nothing depends on 24 live registers |
| rows of $2^8$, groups of 3 / of 2 | 137.8 / 139.0 | |
| rows of $2^8$, one point at a time with only 2 chains | 167.6 | latency bound; with 8 chains a single point runs at the grouped rate |
| rows of $2^7$, groups of 4 | 140.4 | |
| fold-style: each row of $2^{10}$ folded one variable at a time per point | 710 | one mixed product per two words in the first layer, but every later layer is full products with reductions |
| $E$-valued lanes: schoolbook with the twist in the weight (4 `PMULL`) | 12.6 per point | the choice for the folded lanes |
| $E$-valued lanes: three products per element (Karatsuba form) | slower by 10 to 40 percent | measured only under load; the extra accumulator and XORs cost more than the saved `PMULL` |

A weight table split three ways (low, middle, lane) was not needed: with rows of $2^8$ the high table is $2^{12}$ entries per point, 786 KB for 12 points, read once per lane from L2, 10 percent of the data traffic.

### 5.2 The kernel

The inner walk, for a group of `G` points (`U` separate accumulator sets for consecutive loads, used only when `G` is 1 or 2 so that at least 8 chains are live):

```rust
/// One walk of a row for a group of `G` points: every 128-bit load of the row meets the group's `G` weights, and
/// the accumulators stay in registers, each its own dependency chain.
///
/// `row` is 64-bit words: two words of K, or the two limbs of one element of E, per load. `wts` holds four words
/// per load and point, `[load][point]`:
///
///     K:  [w_2i.c0, w_2i+1.c0 | w_2i.c1, w_2i+1.c1]      load = (k_2i, k_2i+1)
///     E:  [w.c0,    w.c1      | w.c1,    w.c0 + x w.c1]  load = (a.c0, a.c1)
///
/// Either way the y^0 coefficient of the sum is the two half products against the first pair and the y^1
/// coefficient the two against the second: four PMULL and two EOR3 per load and point, no shuffle.
#[inline(always)]
unsafe fn group_dots<const G: usize, const U: usize>(row: &[u64], wts: *const u64, out: &mut [F128]) {
    unsafe {
        let zero = vdupq_n_u64(0);
        let (mut a0, mut a1) = ([[zero; G]; U], [[zero; G]; U]);
        let (mut k, mut w) = (row.as_ptr(), wts);
        for _ in 0..row.len() / (2 * U) {
            for u in 0..U {
                let kk = vld1q_u64(k.add(2 * u));
                for m in 0..G {
                    let at = w.add(4 * (u * G + m));
                    let (w0, w1) = (vld1q_u64(at), vld1q_u64(at.add(2)));
                    a0[u][m] = xor3_u64(a0[u][m], clmul_lo(kk, w0), clmul_hi(kk, w0));
                    a1[u][m] = xor3_u64(a1[u][m], clmul_lo(kk, w1), clmul_hi(kk, w1));
                }
            }
            k = k.add(2 * U);
            w = w.add(4 * G * U);
        }
        for m in 0..G {
            let (mut d0, mut d1) = (a0[0][m], a1[0][m]);
            for u in 1..U {
                d0 = veorq_u64(d0, a0[u][m]);
                d1 = veorq_u64(d1, a1[u][m]);
            }
            // One reduction modulo x^64 + x^4 + x^3 + x + 1 per coefficient, row and point.
            out[m] = F128::new(reduce128(transmute(d0)), reduce128(transmute(d1)));
        }
    }
}
```

`clmul_lo` and `clmul_hi` are `PMULL` and `PMULL2` on the two registers, `xor3_u64` is `primitives::field::neon::xor3_u64`. The pass around it, on the experimental pool, one task per row as `mle_eval_par` does, with one unreduced accumulator per lane and point in each worker:

```rust
// low_m = tensor(What_0..What_{L-1} at zeta_m), laid out by `inter_weights`: [group][load][point of the group];
// high[h * s + m] = tensor(What_L..What_{kappa-1} at zeta_m)[h];  L = 8, groups of 4.
let acc = parallel::map_reduce_with_state(
    n_lanes << (kappa - L),
    || (),
    || vec![F128Unreduced::ZERO; n_lanes * s],
    |_, acc, r| {
        let (u, h) = (r >> (kappa - L), r & ((1 << (kappa - L)) - 1));
        let row = &stack[r << L..(r + 1) << L];
        let mut d = [F128::ZERO; S_MAX];
        // SAFETY: the weights were laid out for rows of 2^L words and s points.
        unsafe { row_dots_inter(row, &wts, s, 4, false, &mut d) };   // group_dots::<4, 1> per group of four points
        for m in 0..s {
            acc[u * s + m] ^= high[h * s + m].mul_unreduced(d[m]);
        }
    },
    |mut a, b| { a.iter_mut().zip(b).for_each(|(a, b)| *a ^= b); a },
);
let lane_values: Vec<F128> = acc.into_iter().map(F128Unreduced::reduce).collect();   // P_u(zeta_m) at [u * s + m]
// y_m = sum_u theta_m^{e(u)} lane_values[u * s + m]; every carried scalar of the level folds these 64 values.
```

The same two functions serve the $E$-valued folded lanes (the load is one element, the weight layout is the second line of the comment) with rows of $2^7$ elements.

### 5.3 Why it cannot be much faster here

A point's answer is a generic $K$-linear form $K^{2^\mu} \to E = K^2$ of the stack, and with deferred reduction a product $K \times E$ is exactly two carry-less multiplications, so $s$ points need $2s$ `PMULL` per word whatever the loop order. The tensor structure only helps build the weights. Folding first (the fold-style row) trades half of the mixed products for full products and reductions and loses by a factor of five. On this stack 12 points are $1.007 \cdot 10^9$ `PMULL`, 132 ms of one performance core at its measured 7.6 G per second, and the kernel takes 137 ms. So on Apple silicon the only levers left are fewer points and a smaller stack. A machine with a wider multiplier (AVX-512 `VPCLMULQDQ`) would sit closer to the memory bound, where fusing pays more; I did not measure one.

## 6. In context: share of `Prove`

### 6.1 The real prover on this machine

`cargo leanvm-bench --prover experimental aggregate --xmss 900 --log-inv-rate 1 --tracing`, run 21 times at all threads between 17:56 and 18:43 as the load allowed (`--repeat 1`; with `--repeat 3` the CLI prints one span tree and the mean time). Spans in ms.

| run | `Prove` | `Commit` | `NTT` (level 0) | `OOD` | `PCS open` | `OOD`/`Prove` |
| --- | --- | --- | --- | --- | --- | --- |
| the lead's, earlier that day | 450 | 93.9 | 92.2 | 1.55 | 91.9 | 0.344 % |
| 17:56, load 9 | 1130 | 157 | 154 | 1.96 | 315 | 0.173 % |
| 18:24, three runs, load 35 | 942, 854, 951 | 179, 149, 168 | 174, 146, 165 | 4.21, 2.89, 3.05 | 179, 160, 172 | 0.447, 0.338, 0.321 % |
| 18:27 to 18:43, sixteen runs, load 35 to 59 | 1820 to 9850 | 357 to 3120 | 350 to 3100 | 4.4 to 33.8 | 343 to 2350 | 0.104 to 0.718 %, median 0.18 % |
| one thread, 18:19 and 18:29 | 13500, 16000 | 2610, 3170 | 2570, 3130 | 33.2, 31.7 | 2780, 3580 | 0.246, 0.198 % |

(One further run, at 18:26 while my own benchmark was compiling, is left out.) The four least loaded runs (`Prove` under one second) have `OOD`/`Prove` at 0.32, 0.34, 0.34 and 0.45 percent; I use **0.34 percent** as the central value, which is also the lead's run. Over all twenty of my all-thread runs the median is 0.19 percent (quartiles 0.15 to 0.32): when the machine is saturated the long phases slow down more than the two-millisecond `OOD` burst. With that value every all-thread percentage below is multiplied by 0.56; I take it as the low end of the range, not as the value a quiet machine would show. The one-thread value is 0.20 to 0.25 percent.

### 6.2 The designs

Units of `a` (one OOD evaluation), all threads, medians of section 4; "later levels" is level 1's answers plus a sixteenth for each further level and the later conversions; the hypothetical 6-point and 3-point designs are given proportionally fewer points at later levels. Net subtracts today's OOD evaluations (1.0 at level 0, 0.05 at later levels), which Protocol D removes.

| design | level-0 answers | conversion | later levels | total | share of `Prove`, gross | net |
| --- | --- | --- | --- | --- | --- | --- |
| 12 points, one batch (Protocol D, list $2^{40}$) | 6.3 | 1.0 | 0.55 | 7.9 | **2.7 %** | **2.3 %** |
| ladder 6+1+1+2+1+1 (note 15, list $2^{40}$) | 3.5 + 2.2 | 1.0 | 0.4 | 7.1 | **2.4 %** | **2.1 %** |
| 6 points, one batch (hypothetical) | 3.5 | 0.5 | 0.3 | 4.3 | **1.5 %** | **1.1 %** |
| 3 points, one batch (hypothetical) | 1.8 | 0.26 | 0.15 | 2.2 | **0.75 %** | **0.4 %** |
| for comparison: 12 points as 12 passes of today's kernel | 12.0 | 1.0 | 0.55 | 13.6 | 4.6 % | 4.3 % |
| for comparison: 12 fused, carried scalars as passes | 6.3 + 12.9 | 1.0 | 0.55 | 20.8 | 7.1 % | 6.7 % |

**Spread.** Three sources, all from the load. (i) The ratio to `a`: quartiles of 5.2 to 9.0 around 6.3 for the twelve fused answers, and a quiet machine is more likely at the upper end (9.1 on one thread, where nothing is bound by memory; section 4's estimate of 11 to 14 ms is 7 to 9 units). (ii) `OOD`/`Prove`: 0.34 percent in the least loaded runs, 0.19 percent as the median of all. (iii) The conversion as implemented (1.0 for 12 points) against its multiplication count (0.6). Taking the low quartile, the count and 0.19 percent on one side, and the high quartile, the implementation and 0.34 percent on the other, the net shares are **[derived]**:

| design | net share of `Prove`, central | low | high |
| --- | --- | --- | --- |
| 12 points, one batch | 2.3 % | 1.0 % | 3.3 % |
| ladder | 2.1 % | 0.8 % | 2.8 % |
| 6 points | 1.1 % | 0.4 % | 1.5 % |
| 3 points | 0.4 % | 0.1 % | 0.6 % |

**One thread [derived].** Totals of 11.0 (12 points), 7.6 (ladder: 4.4 + 1.9 + 1.0 + 0.3), 5.1 (six) and 2.7 (three) units, times 0.20 to 0.25 percent: 2.2 to 2.7, 1.5 to 1.9, 1.0 to 1.3 and 0.5 to 0.7 percent of the one-thread `Prove`, gross; subtract 0.2 for net.

**Against the estimate.** Note 11 argued from the multiplication count (12 points equal the level-0 NTT's at rate 1/2) and guessed 3 to 10 percent. The count is right and the comparison is not: the level-0 `NTT` span is 92 ms in the lead's run and the twelve fused answers are 11 to 14 ms, a seventh of it, because the encode is several passes of full products, stores and Merkle hashing while this is one accumulate-only pass at the multiplier's throughput. Note 15's "point work 0.637 of the level-0 NTT" for the ladder likewise overstates the time by the same factor, and its 36 percent saving of the ladder over the single batch is 10 percent at all threads here.

### 6.3 Rate 1/4 and other stack sizes

**Rate 1/4.** The point work does not depend on the rate (same stack, and the level-0 point counts of notes 11 and 15 hold for every rate), only `Prove` grows. Traced runs at `--log-inv-rate 2` and `1`, alternating, four pairs at 18:42 under load 37 to 44 **[measured, loaded]**: `Prove` 5230, 6070, 4180 and 5740 ms at rate 1/4 against 5020, 3090, 4390 and 3490 ms at rate 1/2, a ratio of medians of 1.39 (pair by pair 0.95 to 1.96). `OOD`/`Prove` over the nine rate-1/4 runs of the session has median 0.16 percent, against 0.19 percent for the rate-1/2 runs. Both say the shares at rate 1/4 are 0.7 to 0.85 of those at rate 1/2 **[derived]**: about 1.8 percent net for the 12-point batch, 1.6 for the ladder, 0.9 for six points and 0.3 for three. This is the noisiest number of the note; one pair of runs on a quiet machine would settle it.

**Other stack sizes, kernels only.** Round robins on stacks of $2^{24}$ ($\kappa = 18$, 64 lanes), $2^{26}$ ($\kappa = 20$, 64 lanes) and $2^{28}$ words ($\kappa = 22$, 64 lanes, 2 GiB, with 4 GiB of folded lanes beside it; memory was not a limit), ratios to `a` on the same stack, one thread / all threads **[measured, loaded]** (one thread: 1 or 2 rounds, 18:43 to 18:45; all threads: 12, 10 and 6 rounds, 18:35 to 18:39, load 33 to 59):

| stack | `a`, best ms, one thread / all | 12 fused | 6 fused | 3 fused | ladder's late passes | 12 separate passes |
| --- | --- | --- | --- | --- | --- | --- |
| $2^{24}$ | 10.1 / 1.53 | 9.4 / 4.8 | 4.8 / 3.4 | 2.7 / 2.0 | 1.9 / 2.3 | 12.0 / 9.3 |
| $2^{25.3}$ (the benchmark's) | 15.05 (clean) / 2.09 | 9.1 to 9.6 / 6.3 | 4.4 to 4.8 / 3.5 | 2.3 to 2.4 / 1.8 | 1.9 to 2.2 / 2.2 | 12.0 / 12.0 |
| $2^{26}$ | 38.8 / 9.4 | 9.2 / 8.1 | 4.9 / 3.4 | 2.2 / 1.5 | 1.9 / 2.6 | 12.5 / 17.0 |
| $2^{28}$ | 179 / 33.9 | 9.0 / 5.8 | 4.6 / 3.4 | 2.3 / 1.7 | 2.3 / 1.9 | 11.4 / 10.8 |

On one thread the ratios do not move with the size (9.0 to 9.4 for the twelve fused answers over a factor of 16), as a multiplier-bound kernel must behave; the clean per-word cost is 0.36 ns for `a` and 0.27 ns per point for the fused kernel. At all threads the three extra sizes were measured in the worst minutes of the session and scatter between 4.8 and 8.1 with quartiles as wide as 2.7 to 10.5; they are compatible with the 6.3 of the benchmark's stack and I read nothing more into them. The times of `a` at $2^{24}$, $2^{26}$ and $2^{28}$ are loaded values (a clean machine would show about 6, 24 and 96 ms on one thread).

I did not run the real prover at other stack sizes, so there is no percentage for them. The answers are linear in the number of data words of the stack and so is most of `Prove`, so the same share is the natural guess **[estimate]**.

## 7. What a real integration would change

- **The ladder's late answers could ride in passes the prover already makes.** Round $j + 1$'s table pass writes the lanes after round $j$; evaluating the fresh points in that pass saves the separate reads I measured (the constant 0.4 of section 4, five times, scaled by the sizes), not the multiplications. The late passes would fall from 2.2 units towards their multiplication count at the fused pass's rate, about 1.2 units **[estimate]**, which would bring the ladder to 1.7 percent net.
- **The twelve answers cannot ride in the encode**: the points are sampled after the root.
- **Zero lanes are free and the prover already knows them**; the benchmark reads only the 40 data lanes, like `ood_sample`. The stack's repeated blocks, which the fold rounds skip (`Repeats`), could be skipped here too; not measured.
- **The conversion** would be written with the kernel of section 5 (the weight is the tensor itself) and should cost its count, 0.6 units for 12 points.
- **Today's OOD claim leaves the opening**: it is a `StackClaim::Point` over the whole stack whose terms the level-0 rounds project. I did not measure what that saves, so the net figures are conservative on this side.

## 8. What the measurement does not include

1. **The verifier and the guest**: the chains $\widehat W_k(\zeta_m)$, the carried updates, the terminal weights, the squeezes; guest cycles and the recursion's size. Notes 11 and 15 estimate them; nothing here measures them.
2. **The transcript**: $2s$ squeezes and $s$ absorbed answers per commitment, $s$ more scalars per fold round (72 at level 0 for a batch of 12), the point grind. A few hundred field elements through the sponge, microseconds for the native prover, but the grind is not free and was not timed.
3. **Later levels beyond level 1's answers and level 2's**, which I measured in isolation (0.47 and 0.02 units for 9 points) and extrapolated by sixteenths; the later levels' carried scalars and conversions are scaled, not measured.
4. **The real integration**: the benchmark is standalone passes over buffers of the right sizes and types. The folded lanes are random data of $2^\kappa$ coefficients per lane (the real ones have $j$ more after $j$ rounds, and live in two arrays); nothing is interleaved with the rest of the prover, so cache state, the pool's wake-up cost between phases and memory pressure are those of a microbenchmark.
5. **A quiet machine.** Every all-thread number was taken while 12 to 16 other threads were busy. The ratios should survive; the absolute times and the `OOD`/`Prove` conversion are the uncertain parts, as section 6.2 says.
6. **Other machines.** One Apple M4 Max. On x86 the carry-less multiplier, the vector width and the memory system differ and the split between multiplier-bound and memory-bound will too. The stable prover was not measured.
7. **Peak memory**: the fused pass allocates under 2 MB of tables; not an issue, not measured against the real prover's peak.
8. **Proof size and soundness**: not this note's subject.

## 9. Reproduction

The scratch project is at `/private/tmp/claude-501/-Users-e-Documents-leanVM/f2f13f78-f152-4a76-84f4-26a466d43373/scratchpad/bench24/` (session-specific; it is not in the repository and will not survive a cleanup): `src/main.rs` (kernels, self-test, the items of sections 3 and 4), `src/bin/pmull.rs` (the multiplier's throughput), `rr.py` and `table.py` (the round-robin statistics), `traces.py` (the span tables), `batch2.sh` to `batch4.sh` (the runs), `out/` (every raw output quoted here). Build: `cargo build --release --offline` in that directory. Run: `target/release/bench24 <threads> <kappa> <lanes> <reps> <K kernel> <E kernel> <mode>`, for example `bench24 0 20 40 16 i8.4 i7.4 rr` (round robin, all threads, the benchmark's stack), `bench24 1 20 40 3 i8.4 i7.4 sweep` (kernel sweep, one thread), `bench24 0 20 40 9 i8.4 i7.4 main` (every item, best of 9). Kernel names: `p<L>` portable `dot_base` with rows of $2^L$; `n<L>.<b>` one point at a time in blocks of `b` words; `i<L>.<g>` groups of `g` points (the kernel of section 5.2); `k<L>.<g>` the three-product form for $E$; `f<L>` fold-style. The program starts with a self-test: every kernel against the definition on $K$ and $E$ data, with and without lane stride, and the carried scalars against real affine folds.
