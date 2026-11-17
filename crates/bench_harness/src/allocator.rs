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
//!
//! Linux gives transparent huge pages only to ranges that ask for them (`madvise` mode), so jemalloc
//! asks for its extents: a pass over a large table then walks 2 MiB pages, with fewer TLB misses and
//! one first-touch fault per huge page.

pub use tikv_jemallocator::Jemalloc;

/// jemalloc's configuration, which it reads before its first allocation.
///
/// - Dirty pages never decay, so freed memory never returns to the kernel.
/// - On Linux, its extents are advised as huge pages, and so is its own metadata once that grows large;
///   elsewhere jemalloc rejects `thp`.
/// - jemalloc reads a C string pointer here.
/// - A reference to a byte array is that pointer, with no length beside it.
#[cfg(target_os = "linux")]
#[unsafe(export_name = "_rjem_malloc_conf")]
static MALLOC_CONF: &[u8; 47] = b"dirty_decay_ms:-1,thp:always,metadata_thp:auto\0";

#[cfg(not(target_os = "linux"))]
#[unsafe(export_name = "_rjem_malloc_conf")]
static MALLOC_CONF: &[u8; 18] = b"dirty_decay_ms:-1\0";
