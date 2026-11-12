//! The channel file: header, two SPSC rings, arena. All of the crate's `unsafe`.
//!
//! The peer is another process writing the same pages. Nothing read from the mapping is trusted:
//! ring counters only select a slot inside the ring, and arena regions are bounds-checked and
//! copied out before any decoding.

use crate::wire::MSG_SIZE;
use leanvm::lean_xmss::{MESSAGE_LEN, PUB_KEY_SIZE, SIG_SIZE};
use std::fs::OpenOptions;
use std::io;
use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

const MAGIC: u64 = u64::from_le_bytes(*b"LEANVMSH");
const VERSION: u64 = 1;
const PAGE: usize = 4096;

// Header: u64 words at these offsets. `H_EPOCH` is the only one written after creation.
const H_MAGIC: usize = 0;
const H_VERSION: usize = 8;
const H_EPOCH: usize = 16;
const H_RING_CAP: usize = 24;
const H_TOTAL: usize = 32;
const H_REQ_RING: usize = 40;
const H_RESP_RING: usize = 48;
const H_ARENA_OFF: usize = 56;
const H_ARENA_LEN: usize = 64;
const H_PUB_KEY_SIZE: usize = 72;
const H_MESSAGE_LEN: usize = 80;
const H_SIG_SIZE: usize = 88;

// Ring: consumer and producer counters on separate cache lines, then the slots.
const R_HEAD: usize = 0;
const R_TAIL: usize = 64;
const R_SLOTS: usize = 128;

/// Fault the whole file in at `mmap`: tmpfs allocates its pages then, not under the first requests.
#[cfg(target_os = "linux")]
const POPULATE: libc::c_int = libc::MAP_POPULATE;
#[cfg(not(target_os = "linux"))]
const POPULATE: libc::c_int = 0;

/// Wait between polls of a full ring.
const FULL_POLL: Duration = Duration::from_micros(100);

#[derive(Clone, Copy)]
pub enum Ring {
    /// Client produces, server consumes.
    Request,
    /// Server produces, client consumes.
    Response,
}

pub struct Channel {
    base: *mut u8,
    total: usize,
    ring_cap: u64,
    req_ring: usize,
    resp_ring: usize,
    arena_off: usize,
}

impl Channel {
    /// Map the channel at `path`, creating it if needed, and start a new epoch.
    ///
    /// A file whose header already describes this geometry keeps its rings, so requests queued
    /// across a restart are served. Any other file is reinitialized; a client still mapping the
    /// old geometry has to reopen.
    pub fn create(path: &Path, ring_cap: u32, arena_len: usize) -> io::Result<Self> {
        if !ring_cap.is_power_of_two() {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "ring capacity is not a power of two"));
        }
        let ring_bytes = (R_SLOTS + ring_cap as usize * MSG_SIZE).next_multiple_of(PAGE);
        let (req_ring, resp_ring) = (PAGE, PAGE + ring_bytes);
        let arena_off = resp_ring + ring_bytes;
        let total = arena_off + arena_len;

        // A new channel is built under a staging name and renamed into place below, so a client
        // that finds `path` finds its header written and its pages faulted in.
        let mut staging = path.as_os_str().to_owned();
        staging.push(".init");
        let fresh = !path.exists();
        let open_at = if fresh { Path::new(&staging) } else { path };
        let file = OpenOptions::new().read(true).write(true).create(true).truncate(false).open(open_at)?;
        if file.metadata()?.len() != total as u64 {
            file.set_len(total as u64)?;
        }
        // SAFETY: a new shared mapping of `total` bytes of a file of that length, unmapped in `drop`.
        let base = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                total,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED | POPULATE,
                file.as_raw_fd(),
                0,
            )
        };
        if base == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        let chan = Self {
            base: base.cast(),
            total,
            ring_cap: u64::from(ring_cap),
            req_ring,
            resp_ring,
            arena_off,
        };

        let header = [
            (H_MAGIC, MAGIC),
            (H_VERSION, VERSION),
            (H_RING_CAP, chan.ring_cap),
            (H_TOTAL, total as u64),
            (H_REQ_RING, req_ring as u64),
            (H_RESP_RING, resp_ring as u64),
            (H_ARENA_OFF, arena_off as u64),
            (H_ARENA_LEN, arena_len as u64),
            (H_PUB_KEY_SIZE, PUB_KEY_SIZE as u64),
            (H_MESSAGE_LEN, MESSAGE_LEN as u64),
            (H_SIG_SIZE, SIG_SIZE as u64),
        ];
        let epoch = chan.word(H_EPOCH).load(Ordering::Relaxed);
        if !header.iter().all(|&(at, value)| chan.word(at).load(Ordering::Relaxed) == value) {
            // SAFETY: `[0, arena_off)` is inside the mapping.
            unsafe { std::ptr::write_bytes(chan.base, 0, arena_off) };
            for (at, value) in header {
                chan.word(at).store(value, Ordering::Relaxed);
            }
        }
        // Survives reinitialization, so a client never sees an epoch repeat.
        chan.word(H_EPOCH).store(epoch.wrapping_add(1), Ordering::Release);
        if fresh {
            std::fs::rename(&staging, path)?;
        }
        Ok(chan)
    }

    fn word(&self, at: usize) -> &AtomicU64 {
        assert!(at.is_multiple_of(8) && at + 8 <= self.total);
        // SAFETY: in bounds and 8-aligned (the mapping is page-aligned). An `AtomicU64` is valid
        // for any bit pattern and for concurrent writes by the peer.
        unsafe { &*self.base.add(at).cast::<AtomicU64>() }
    }

    fn ring(&self, ring: Ring) -> usize {
        match ring {
            Ring::Request => self.req_ring,
            Ring::Response => self.resp_ring,
        }
    }

    fn slot(&self, ring: usize, index: u64) -> *mut u8 {
        let slot = (index & (self.ring_cap - 1)) as usize;
        // SAFETY: `slot < ring_cap`, and each ring spans `R_SLOTS + ring_cap * MSG_SIZE` bytes of the mapping.
        unsafe { self.base.add(ring + R_SLOTS + slot * MSG_SIZE) }
    }

    /// The oldest unconsumed message of `ring`. Only its one consumer may call this.
    pub fn pop(&self, ring: Ring) -> Option<[u8; MSG_SIZE]> {
        let ring = self.ring(ring);
        let head = self.word(ring + R_HEAD).load(Ordering::Relaxed);
        if self.word(ring + R_TAIL).load(Ordering::Acquire) == head {
            return None;
        }
        let mut msg = [0; MSG_SIZE];
        // SAFETY: the slot is `MSG_SIZE` bytes inside the mapping. The producer published it with
        // its Release store of the tail; a producer that breaks the protocol only garbles the bytes.
        unsafe { std::ptr::copy_nonoverlapping(self.slot(ring, head), msg.as_mut_ptr(), MSG_SIZE) };
        self.word(ring + R_HEAD).store(head.wrapping_add(1), Ordering::Release);
        Some(msg)
    }

    /// Append `msg` to `ring`, waiting while it is full. Only its one producer may call this.
    pub fn push(&self, ring: Ring, msg: &[u8; MSG_SIZE]) {
        let ring = self.ring(ring);
        let tail = self.word(ring + R_TAIL).load(Ordering::Relaxed);
        while tail.wrapping_sub(self.word(ring + R_HEAD).load(Ordering::Acquire)) >= self.ring_cap {
            std::thread::sleep(FULL_POLL);
        }
        // SAFETY: as in `pop`; the consumer does not read this slot before the tail moves past it.
        unsafe { std::ptr::copy_nonoverlapping(msg.as_ptr(), self.slot(ring, tail), MSG_SIZE) };
        self.word(ring + R_TAIL).store(tail.wrapping_add(1), Ordering::Release);
    }

    /// `[off, off + len)` as indices into the mapping, if it lies inside the arena. `off` is from the file's start.
    fn region(&self, off: u64, len: u64) -> Option<(usize, usize)> {
        let end = off.checked_add(len)?;
        (off >= self.arena_off as u64 && end <= self.total as u64).then_some((off as usize, len as usize))
    }

    pub fn in_arena(&self, off: u64, len: u64) -> bool {
        self.region(off, len).is_some()
    }

    /// A private copy of an arena region. The peer can still write to the arena, so nothing is decoded in place.
    pub fn read(&self, off: u64, len: u64) -> Option<Vec<u8>> {
        let (off, len) = self.region(off, len)?;
        let mut out = Vec::with_capacity(len);
        // SAFETY: the source is inside the mapping and `out` has capacity `len`. A concurrent write
        // by the peer yields arbitrary bytes, which the decoders treat as any other input.
        unsafe {
            std::ptr::copy_nonoverlapping(self.base.add(off), out.as_mut_ptr(), len);
            out.set_len(len);
        }
        Some(out)
    }

    /// Copy `bytes` into the arena at `off`. Panics on a region the caller did not check with [`Self::in_arena`].
    pub fn write(&self, off: u64, bytes: &[u8]) {
        let (off, len) = self.region(off, bytes.len() as u64).expect("region outside the arena");
        // SAFETY: the destination is inside the mapping.
        unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), self.base.add(off), len) };
    }
}

impl Drop for Channel {
    fn drop(&mut self) {
        // SAFETY: the mapping `create` made; no reference into it outlives `self`.
        unsafe { libc::munmap(self.base.cast(), self.total) };
    }
}
