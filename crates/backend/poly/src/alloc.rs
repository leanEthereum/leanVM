//! Explicit arena allocation for proof buffers.
//!
//! [`ArenaVec`] is [`zk_alloc::ArenaVec`]: an owning vector that bumps from the proving arena inside a
//! phase and falls back to the system allocator outside one. `Deref<Target = [T]>` lets it drop
//! into slice-based APIs unchanged. Construct one with its inherent constructors — `ArenaVec::new`,
//! `with_capacity`, `filled`, `zeroed`, `from_slice`, `from_iter`, `par_collect`, `uninitialized`.

pub use zk_alloc::{ArenaVec, OwnedBuffer, PhaseGuard, enter_phase};

#[cfg(test)]
mod bench {
    use std::hint::black_box;
    use std::time::{Duration, Instant};

    use field::PrimeCharacteristicRing;
    use koala_bear::QuinticExtensionFieldKB;
    use zk_alloc::enable_arena;

    use super::ArenaVec;
    use crate::EFPacking;

    type EF = QuinticExtensionFieldKB;
    type Packing = EFPacking<EF>;

    /// Run `f` `iters` times and return the summed wall-clock spent strictly inside `f` (the phase
    /// reset and timer plumbing stay outside the measured region).
    fn time_arena_alloc(iters: usize, mut f: impl FnMut() -> Duration) -> Duration {
        (0..iters).map(|_| f()).sum()
    }

    /// Compares the three ways to obtain a zero-initialized `EFPacking<EF>` buffer used by the
    /// proving hot paths (whir::open / sumcheck split-eq fold):
    ///   A. `ArenaVec::filled(Packing::ZERO, n)` — arena bump + element-wise clone fill.
    ///   B. `ArenaVec::zeroed(n)`                 — arena bump + single `write_bytes` memset.
    ///   C. `Packing::zero_vec(n)`                — system `alloc_zeroed`/`calloc`.
    ///
    /// A and B run inside an arena phase (re-entered each iteration so the bump pointer resets and
    /// the slab is not exhausted); the phase enter/exit is excluded from the timed region. C uses
    /// the system allocator regardless of phase.
    ///
    /// NOTE: this isolates the allocate+zero cost only. At the real call sites the whole buffer is
    /// then summed into across its full length, so `alloc_zeroed`'s deferred OS zeroing (C) does not
    /// actually save the first-touch page faults — keep that in mind when reading the C column.
    ///
    /// cargo test --release --package mt-poly --lib -- alloc::bench::bench_arena_zero_init --exact --nocapture --ignored
    #[test]
    #[ignore]
    fn bench_arena_zero_init() {
        enable_arena();

        let elem_bytes = size_of::<Packing>();
        println!("EFPacking<EF> = {elem_bytes} bytes/element\n");
        println!(
            "{:>12} {:>10} {:>14} {:>14} {:>14}   {:>10}",
            "n (elems)", "buf", "A filled", "B zeroed", "C zero_vec", "A/B"
        );

        for log_n in [10usize, 14, 16, 18, 20, 21] {
            let n = 1 << log_n;
            let buf_bytes = n * elem_bytes;
            // Aim for ~4 GiB of total memset traffic per method, clamped to a sane iteration count.
            let iters = ((4usize << 30) / buf_bytes).clamp(20, 4000);
            let warmup = (iters / 10).max(3);

            // ---- warmup (touches the arena slab pages so steady-state hits warm memory) ----
            for _ in 0..warmup {
                let _g = super::enter_phase();
                let v = ArenaVec::filled(Packing::ZERO, n);
                black_box(v.as_ptr());
            }

            // ---- A: ArenaVec::filled (element-wise clone fill) ----
            let dur_a = time_arena_alloc(iters, || {
                let _g = super::enter_phase();
                let t = Instant::now();
                let v = ArenaVec::filled(Packing::ZERO, n);
                black_box(v.as_ptr());
                t.elapsed()
            });

            // ---- B: ArenaVec::zeroed (single memset) ----
            let dur_b = time_arena_alloc(iters, || {
                let _g = super::enter_phase();
                let t = Instant::now();
                // SAFETY: all-zero bytes is a valid `EFPacking<EF>` (Montgomery zero == 0 bits).
                let v = unsafe { ArenaVec::<Packing>::zeroed(n) };
                black_box(v.as_ptr());
                t.elapsed()
            });

            // ---- C: zero_vec (system alloc_zeroed) ----
            let dur_c = time_arena_alloc(iters, || {
                let t = Instant::now();
                let v = Packing::zero_vec(n);
                black_box(v.as_ptr());
                t.elapsed()
            });

            let per = |d: Duration| d.as_secs_f64() / iters as f64 * 1e6; // µs / call
            let (a, b, c) = (per(dur_a), per(dur_b), per(dur_c));
            println!(
                "{:>12} {:>9}M {:>11.2}µs {:>11.2}µs {:>11.2}µs   {:>9.2}x",
                n,
                buf_bytes >> 20,
                a,
                b,
                c,
                a / b,
            );
        }
    }
}
