//! Client of the `leanvm-sidecar` service: [`Client::send`] a request, [`Client::try_recv`] its response.
//!
//! Links nothing of the prover. Payloads and response bodies are raw bytes in the encodings of
//! `bins/leanvm-sidecar/PROTOCOL.md`; the Go and Java clients beside that file mirror this one.
//!
//! One `Client` per channel. Open it while no request of an earlier client is outstanding: the
//! server would write that request's response into arena space this client hands out again.

use std::collections::VecDeque;
use std::fs::OpenOptions;
use std::io;
use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

pub const OP_AGGREGATE: u32 = 1;
pub const OP_RECURSE: u32 = 2;
pub const OP_VERIFY: u32 = 3;
pub const OP_VERIFY_NARROW: u32 = 4;
pub const OP_EXTEND: u32 = 5;

/// `OP_RECURSE`, `OP_EXTEND`: verify every child natively before proving.
pub const FLAG_VERIFY_CHILDREN: u32 = 1;
/// A proving op: the server keeps the proof it returns, in place of any it held.
pub const FLAG_KEEP_PROOF: u32 = 2;
/// `OP_RECURSE`, `OP_EXTEND`: the kept proof is one more child, and is no longer kept.
pub const FLAG_USE_KEPT: u32 = 4;

pub const ST_OK: u32 = 0;
pub const ST_BAD_REQUEST: u32 = 1;
pub const ST_RESP_TOO_SMALL: u32 = 2;
pub const ST_INVALID_PROOF: u32 = 3;
pub const ST_AGGREGATION_FAILED: u32 = 4;

const MAGIC: u64 = u64::from_le_bytes(*b"LEANVMSH");
const VERSION: u64 = 1;
const MSG_SIZE: usize = 64;

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
const HEADER_SIZE: usize = 96;

/// Map every page at `mmap`, so no request takes this process's first-touch faults on the arena.
#[cfg(target_os = "linux")]
const POPULATE: libc::c_int = libc::MAP_POPULATE;
#[cfg(not(target_os = "linux"))]
const POPULATE: libc::c_int = 0;

const R_HEAD: usize = 0;
const R_TAIL: usize = 64;
const R_SLOTS: usize = 128;

/// The request ring or the arena has no room. Receive a response and retry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Full;

impl std::fmt::Display for Full {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "no room in the request ring or the arena")
    }
}

impl std::error::Error for Full {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Response {
    /// What [`Client::send`] returned for the request.
    pub id: u64,
    pub status: u32,
    pub detail: u32,
    /// The body's length, or under [`ST_RESP_TOO_SMALL`] the response capacity the request needed.
    pub resp_len: u64,
    /// The op's response under [`ST_OK`], UTF-8 text for a human on a failure, empty under [`ST_RESP_TOO_SMALL`].
    pub body: Vec<u8>,
}

/// A request's arena block: its payload, then its response region, both offsets from the arena's start.
struct Block {
    id: u64,
    off: usize,
    payload_len: usize,
    resp_cap: usize,
}

impl Block {
    fn end(&self) -> usize {
        self.off + self.payload_len + self.resp_cap
    }
}

/// Where a block of `len` bytes goes, from the arena's start, given the blocks still held.
fn place(live: &VecDeque<Block>, arena_len: usize, len: usize) -> Option<usize> {
    let (Some(first), Some(last)) = (live.front(), live.back()) else {
        return (len <= arena_len).then_some(0);
    };
    let end = last.end();
    if last.off < first.off {
        // Wrapped: the gap up to the oldest block.
        (len <= first.off - end).then_some(end)
    } else if len <= arena_len - end {
        Some(end)
    } else {
        // Wrap into the space before the oldest block. `first.off > 0` keeps `last.off < first.off` meaning wrapped.
        (first.off > 0 && len <= first.off).then_some(0)
    }
}

pub struct Client {
    base: *mut u8,
    total: usize,
    ring_cap: u64,
    req_ring: usize,
    resp_ring: usize,
    arena_off: usize,
    arena_len: usize,
    next_id: u64,
    /// Blocks of requests not yet answered, oldest first. The server answers in order, so the arena
    /// is a circular buffer of them: allocated at the back, freed at the front.
    live: VecDeque<Block>,
}

// SAFETY: the mapping is owned by the `Client` and not tied to a thread.
unsafe impl Send for Client {}

impl Client {
    /// Map the channel the server created at `path`. Responses left by an earlier client are discarded.
    pub fn open(path: &Path) -> io::Result<Self> {
        let invalid = |what: &'static str| io::Error::new(io::ErrorKind::InvalidData, what);
        let file = OpenOptions::new().read(true).write(true).open(path)?;
        let total = usize::try_from(file.metadata()?.len()).map_err(|_| invalid("channel too large"))?;
        if total < HEADER_SIZE {
            return Err(invalid("not a leanvm-sidecar channel"));
        }
        // SAFETY: a new shared mapping of the whole file, unmapped in `drop`.
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
        let mut client = Self {
            base: base.cast(),
            total,
            ring_cap: 0,
            req_ring: 0,
            resp_ring: 0,
            arena_off: 0,
            arena_len: 0,
            next_id: 0,
            live: VecDeque::new(),
        };
        let field = |at: usize| client.word(at).load(Ordering::Relaxed);
        if field(H_MAGIC) != MAGIC || field(H_VERSION) != VERSION {
            return Err(invalid("not a leanvm-sidecar channel of this version"));
        }
        let (ring_cap, req_ring, resp_ring) = (field(H_RING_CAP), field(H_REQ_RING), field(H_RESP_RING));
        let (arena_off, arena_len) = (field(H_ARENA_OFF), field(H_ARENA_LEN));
        // Every later access is in bounds given these: the rings sit below the arena, the arena inside the file.
        let ring_bytes = ring_cap.checked_mul(MSG_SIZE as u64).and_then(|slots| slots.checked_add(R_SLOTS as u64));
        let ring_fits = |ring: u64| {
            let end = ring_bytes.and_then(|bytes| ring.checked_add(bytes));
            ring.is_multiple_of(8) && end.is_some_and(|end| end <= arena_off)
        };
        if !ring_cap.is_power_of_two()
            || field(H_TOTAL) != total as u64
            || !ring_fits(req_ring)
            || !ring_fits(resp_ring)
            || arena_off.checked_add(arena_len) != Some(total as u64)
        {
            return Err(invalid("inconsistent channel header"));
        }
        client.ring_cap = ring_cap;
        client.req_ring = req_ring as usize;
        client.resp_ring = resp_ring as usize;
        client.arena_off = arena_off as usize;
        client.arena_len = arena_len as usize;
        let stale = client.word(client.resp_ring + R_TAIL).load(Ordering::Acquire);
        client.word(client.resp_ring + R_HEAD).store(stale, Ordering::Release);
        Ok(client)
    }

    fn word(&self, at: usize) -> &AtomicU64 {
        assert!(at.is_multiple_of(8) && at + 8 <= self.total);
        // SAFETY: in bounds and 8-aligned (the mapping is page-aligned). An `AtomicU64` is valid
        // for any bit pattern and for concurrent writes by the server.
        unsafe { &*self.base.add(at).cast::<AtomicU64>() }
    }

    fn slot(&self, ring: usize, index: u64) -> *mut u8 {
        let slot = (index & (self.ring_cap - 1)) as usize;
        // SAFETY: `slot < ring_cap`, and `open` checked that the ring's slots are inside the mapping.
        unsafe { self.base.add(ring + R_SLOTS + slot * MSG_SIZE) }
    }

    /// Incremented each time the server starts. A request in flight across a restart gets no response.
    pub fn epoch(&self) -> u64 {
        self.word(H_EPOCH).load(Ordering::Acquire)
    }

    pub fn pub_key_size(&self) -> usize {
        self.word(H_PUB_KEY_SIZE).load(Ordering::Relaxed) as usize
    }

    pub fn message_len(&self) -> usize {
        self.word(H_MESSAGE_LEN).load(Ordering::Relaxed) as usize
    }

    pub fn sig_size(&self) -> usize {
        self.word(H_SIG_SIZE).load(Ordering::Relaxed) as usize
    }

    /// Queue a request and return its id. `resp_cap` bytes of arena are reserved for the response:
    /// a proof that does not fit is discarded by the server ([`ST_RESP_TOO_SMALL`]).
    pub fn send(
        &mut self,
        op: u32,
        flags: u32,
        log_inv_rate: u32,
        payload: &[u8],
        resp_cap: usize,
    ) -> Result<u64, Full> {
        let tail = self.word(self.req_ring + R_TAIL).load(Ordering::Relaxed);
        if tail.wrapping_sub(self.word(self.req_ring + R_HEAD).load(Ordering::Acquire)) >= self.ring_cap {
            return Err(Full);
        }
        let len = payload.len().checked_add(resp_cap).ok_or(Full)?;
        let off = place(&self.live, self.arena_len, len).ok_or(Full)?;
        let req_off = self.arena_off + off;
        // SAFETY: `place` returned a block inside the arena that no live request holds.
        unsafe { std::ptr::copy_nonoverlapping(payload.as_ptr(), self.base.add(req_off), payload.len()) };

        self.next_id += 1;
        let id = self.next_id;
        let mut msg = [0u8; MSG_SIZE];
        msg[0..8].copy_from_slice(&id.to_le_bytes());
        msg[8..12].copy_from_slice(&op.to_le_bytes());
        msg[12..16].copy_from_slice(&flags.to_le_bytes());
        msg[16..24].copy_from_slice(&(req_off as u64).to_le_bytes());
        msg[24..32].copy_from_slice(&(payload.len() as u64).to_le_bytes());
        msg[32..40].copy_from_slice(&((req_off + payload.len()) as u64).to_le_bytes());
        msg[40..48].copy_from_slice(&(resp_cap as u64).to_le_bytes());
        msg[48..52].copy_from_slice(&log_inv_rate.to_le_bytes());
        // SAFETY: the slot is inside the mapping, and the server does not read it before the tail moves past it.
        unsafe { std::ptr::copy_nonoverlapping(msg.as_ptr(), self.slot(self.req_ring, tail), MSG_SIZE) };
        self.word(self.req_ring + R_TAIL).store(tail.wrapping_add(1), Ordering::Release);
        self.live.push_back(Block {
            id,
            off,
            payload_len: payload.len(),
            resp_cap,
        });
        Ok(id)
    }

    /// The next response, if the server has produced one. Frees the request's arena block, and
    /// those of earlier requests that a server restart left unanswered.
    pub fn try_recv(&mut self) -> Option<Response> {
        let head = self.word(self.resp_ring + R_HEAD).load(Ordering::Relaxed);
        if self.word(self.resp_ring + R_TAIL).load(Ordering::Acquire) == head {
            return None;
        }
        let mut msg = [0u8; MSG_SIZE];
        // SAFETY: the slot is inside the mapping; the server published it with its store of the tail.
        unsafe { std::ptr::copy_nonoverlapping(self.slot(self.resp_ring, head), msg.as_mut_ptr(), MSG_SIZE) };
        self.word(self.resp_ring + R_HEAD).store(head.wrapping_add(1), Ordering::Release);

        let mut response = Response {
            id: u64::from_le_bytes(msg[0..8].try_into().unwrap()),
            status: u32::from_le_bytes(msg[8..12].try_into().unwrap()),
            detail: u32::from_le_bytes(msg[12..16].try_into().unwrap()),
            resp_len: u64::from_le_bytes(msg[16..24].try_into().unwrap()),
            body: Vec::new(),
        };
        while self.live.pop_front_if(|block| block.id < response.id).is_some() {}
        // The body is read only for the request this answers, and only from inside its own block.
        if let Some(block) = self.live.pop_front_if(|block| block.id == response.id)
            && response.status != ST_RESP_TOO_SMALL
            && response.resp_len <= block.resp_cap as u64
        {
            let len = response.resp_len as usize;
            let resp_off = self.arena_off + block.off + block.payload_len;
            response.body.reserve_exact(len);
            // SAFETY: `len <= resp_cap`, inside the block; `body` has capacity `len`.
            unsafe {
                std::ptr::copy_nonoverlapping(self.base.add(resp_off), response.body.as_mut_ptr(), len);
                response.body.set_len(len);
            }
        }
        Some(response)
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        // SAFETY: the mapping `open` made; no reference into it outlives `self`.
        unsafe { libc::munmap(self.base.cast(), self.total) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Random sends and in-order frees: a placed block is inside the arena and overlaps no live one.
    #[test]
    fn blocks_never_overlap() {
        const ARENA_LEN: usize = 100;
        let mut live = VecDeque::new();
        let mut state = 1u64;
        let mut placed = 0;
        for id in 0..10_000 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let len = (state >> 33) as usize % 40;
            match place(&live, ARENA_LEN, len) {
                Some(off) => {
                    assert!(off + len <= ARENA_LEN);
                    assert!(live.iter().all(|b: &Block| off + len <= b.off || b.end() <= off));
                    live.push_back(Block { id, off, payload_len: len, resp_cap: 0 });
                    placed += 1;
                }
                None => assert!(live.pop_front().is_some()),
            }
            if state >> 63 == 1 {
                live.pop_front();
            }
        }
        assert!(placed > 1000);
    }
}
