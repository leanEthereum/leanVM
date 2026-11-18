//! A node's database I/O for a block, on a file standing in for its state database: a 4 KiB page read at a random
//! place for each account and slot the block touches that the node's cache misses, a page written for each the block
//! changes, and an fsync to commit, past the page cache on Linux as a database bigger than memory is.

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::FileExt;
use std::sync::atomic::{AtomicU64, Ordering};

const PAGE: usize = 4096;

/// A page, aligned as direct I/O requires.
#[repr(C, align(4096))]
struct Page([u8; PAGE]);

pub struct Db {
    file: File,
    pages: u64,
    miss: f64,
}

impl Db {
    /// The file at `path`, of `gib` GiB of data, written once and kept: a sparse file's reads would not reach the disk.
    pub fn open(path: &str, gib: u64, miss: f64) -> Self {
        let bytes = gib << 30;
        if std::fs::metadata(path).map_or(true, |m| m.len() != bytes) {
            let mut file = File::create(path).unwrap();
            let mut chunk = vec![0u8; 64 << 20];
            let mut x = 0x9e37_79b9_7f4a_7c15;
            for _ in 0..bytes / chunk.len() as u64 {
                for word in chunk.chunks_mut(8) {
                    word.copy_from_slice(&xorshift(&mut x).to_le_bytes());
                }
                file.write_all(&chunk).unwrap();
            }
            file.sync_all().unwrap();
        }
        let mut options = OpenOptions::new();
        options.read(true).write(true);
        #[cfg(target_os = "linux")]
        std::os::unix::fs::OpenOptionsExt::custom_flags(&mut options, libc::O_DIRECT);
        Self { file: options.open(path).unwrap(), pages: bytes / PAGE as u64, miss }
    }

    /// A block's I/O: `touched` accounts and slots, of which the cache misses a `miss` share, and `changed` written back.
    pub fn block(&self, touched: usize, changed: usize) {
        static SEED: AtomicU64 = AtomicU64::new(1);
        let mut x = SEED.fetch_add(0x9e37_79b9, Ordering::Relaxed) | 1;
        let mut page = Box::new(Page([0; PAGE]));
        for _ in 0..(touched as f64 * self.miss).round() as usize {
            let at = xorshift(&mut x) % self.pages * PAGE as u64;
            self.file.read_exact_at(&mut page.0, at).unwrap();
        }
        for _ in 0..changed {
            let at = xorshift(&mut x) % self.pages * PAGE as u64;
            self.file.write_all_at(&page.0, at).unwrap();
        }
        self.file.sync_data().unwrap();
    }
}

fn xorshift(x: &mut u64) -> u64 {
    *x ^= *x << 13;
    *x ^= *x >> 7;
    *x ^= *x << 17;
    *x
}
