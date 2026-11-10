//! What a case costs: its peak heap and its time. The `leanvm-fuzz` binary installs [`Counting`] as its global
//! allocator; without it (libFuzzer, a library user) every measured peak is zero and only time is real.
//!
//! The peak is the campaign's resource signal twice over. [`crate::run_case`] notes the bucket a case's peak falls in,
//! so a case that allocates more than any before joins the corpus and the fuzzer climbs toward expensive inputs
//! (PerfFuzz's idea), and targets that take input from a peer hold the code under test to a budget with [`measure`].

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use std::time::{Duration, Instant};

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static INSTALLED: AtomicBool = AtomicBool::new(false);

/// The system allocator, counting live and peak bytes across the process.
pub struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: forwarded unchanged.
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            grew(layout.size());
        }
        p
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: forwarded unchanged.
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            grew(layout.size());
        }
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: forwarded unchanged.
        unsafe { System.dealloc(ptr, layout) };
        LIVE.fetch_sub(layout.size(), Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: forwarded unchanged.
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            if new_size >= layout.size() {
                grew(new_size - layout.size());
            } else {
                LIVE.fetch_sub(layout.size() - new_size, Relaxed);
            }
        }
        p
    }
}

fn grew(bytes: usize) {
    INSTALLED.store(true, Relaxed);
    let live = LIVE.fetch_add(bytes, Relaxed) + bytes;
    PEAK.fetch_max(live, Relaxed);
}

/// Whether [`Counting`] is the global allocator, so peaks mean something.
pub fn installed() -> bool {
    INSTALLED.load(Relaxed)
}

/// What a closure cost.
#[derive(Clone, Copy, Debug, Default)]
pub struct Usage {
    /// The most heap it held at once beyond what was live when it started, every thread included.
    pub peak_bytes: usize,
    pub elapsed: Duration,
}

impl Usage {
    /// `2^k`, the power of two at or above the peak: what a note records, so a case that allocates a few bytes more
    /// is no new behaviour.
    pub fn peak_bucket(&self) -> u32 {
        self.peak_bytes.max(1).next_power_of_two().trailing_zeros()
    }
}

/// Run `f` and measure it. Measurements nest: an outer one still sees an inner one's peak.
pub fn measure<T>(f: impl FnOnce() -> T) -> (T, Usage) {
    let start_live = LIVE.load(Relaxed);
    let outer_peak = PEAK.swap(start_live, Relaxed);
    let t = Instant::now();
    let out = f();
    let elapsed = t.elapsed();
    let peak = PEAK.load(Relaxed);
    PEAK.fetch_max(outer_peak, Relaxed);
    (
        out,
        Usage {
            peak_bytes: peak.saturating_sub(start_live),
            elapsed,
        },
    )
}

/// A budget the code under test must stay within on input a peer chose: a verifier, a decoder, a replay. Over it is
/// a denial of service, a Medium finding keyed by `what`.
pub fn within(what: &str, usage: Usage, max_bytes: usize, max_time: Duration) -> crate::Outcome {
    if installed() && usage.peak_bytes > max_bytes {
        return Err(crate::Finding::medium(
            format!(
                "resource: {what} allocates past its budget of 2^{} bytes",
                max_bytes.next_power_of_two().trailing_zeros()
            ),
            format!("peaked at {} bytes in {:?}", usage.peak_bytes, usage.elapsed),
        ));
    }
    if usage.elapsed > max_time {
        return Err(crate::Finding::medium(
            format!("resource: {what} runs past its budget of {max_time:?}"),
            format!("took {:?}, peaked at {} bytes", usage.elapsed, usage.peak_bytes),
        ));
    }
    Ok(())
}
