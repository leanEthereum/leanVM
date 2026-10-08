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
//! On Linux every mapping also asks for transparent huge pages, so the first proof faults one 2 MiB page where it would fault 512 small ones, and the buffers take fewer TLB entries.

pub use tikv_jemallocator::Jemalloc;

/// jemalloc's configuration, which it reads before its first allocation.
///
/// - Dirty pages never decay, so freed memory never returns to the kernel.
/// - On Linux every mapping, metadata included, asks for transparent huge pages (`MADV_HUGEPAGE`); the kernel's mode decides: `madvise` honours it, `always` already backs every mapping, `never` refuses it.
/// - Elsewhere, 32-bit ARM Linux included, jemalloc has no huge page support and would print a warning for `thp`, so the string is the first option alone.
/// - jemalloc reads a C string pointer here.
/// - A reference to a byte array is that pointer, with no length beside it.
#[cfg(all(target_os = "linux", not(target_arch = "arm")))]
#[unsafe(export_name = "_rjem_malloc_conf")]
static MALLOC_CONF: &[u8; 49] = b"dirty_decay_ms:-1,thp:always,metadata_thp:always\0";

/// jemalloc's configuration on targets without transparent huge pages (see the Linux one).
#[cfg(not(all(target_os = "linux", not(target_arch = "arm"))))]
#[unsafe(export_name = "_rjem_malloc_conf")]
static MALLOC_CONF: &[u8; 18] = b"dirty_decay_ms:-1\0";
