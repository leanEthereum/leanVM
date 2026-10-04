//! The global allocator of the CLI and the proving benchmarks.
//!
//! A proof allocates gigabytes of short-lived buffers and frees them before it returns.
//!
//! An allocator that returns freed pages to the kernel makes the next proof fault each page in again.
//!
//! With dirty pages that never decay, jemalloc keeps them instead:
//!
//! ```text
//!     proof 1: pages faulted in, then freed  ->  kept mapped in jemalloc's cache
//!     proof 2: pages served from the cache   ->  no fault
//! ```
//!
//! The cost is resident memory: the process holds its peak until it exits.

pub use tikv_jemallocator::Jemalloc;

/// jemalloc's configuration, which it reads before its first allocation.
///
/// - Dirty pages never decay, so freed memory never returns to the kernel.
/// - jemalloc reads a C string pointer here.
/// - A reference to a byte array is that pointer, with no length beside it.
#[unsafe(export_name = "_rjem_malloc_conf")]
static MALLOC_CONF: &[u8; 18] = b"dirty_decay_ms:-1\0";
