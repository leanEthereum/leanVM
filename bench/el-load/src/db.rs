//! A node's database I/O for a block, on a 16 GiB file standing in for its state database: a 4 KiB page read at a
//! random place for each account and slot the block touches, as a cold cache misses them, a page written for each the
//! block changes, and an fsync to commit, past the page cache on Linux as a database bigger than memory is.

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::FileExt;
use std::sync::atomic::{AtomicU64, Ordering};

const PAGE: usize = 4096;
const BYTES: u64 = 16 << 30;

/// A page, aligned as direct I/O requires.
#[repr(C, align(4096))]
struct Page([u8; PAGE]);

pub struct Db(File);

impl Db {
    /// The file at `path`, written once and kept: a sparse file's reads would not reach the disk.
    pub fn open(path: &str) -> Self {
        if std::fs::metadata(path).map_or(true, |m| m.len() != BYTES) {
            let mut file = File::create(path).unwrap();
            let mut chunk = vec![0u8; 64 << 20];
            let mut x = 0x9e37_79b9_7f4a_7c15;
            for _ in 0..BYTES / chunk.len() as u64 {
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
        Self(options.open(path).unwrap())
    }

    /// A block's I/O: `touched` accounts and slots read, `changed` written back.
    pub fn block(&self, touched: usize, changed: usize) {
        static SEED: AtomicU64 = AtomicU64::new(1);
        let mut x = SEED.fetch_add(0x9e37_79b9, Ordering::Relaxed) | 1;
        let mut page = Box::new(Page([0; PAGE]));
        let mut at = || xorshift(&mut x) % (BYTES / PAGE as u64) * PAGE as u64;
        for _ in 0..touched {
            self.0.read_exact_at(&mut page.0, at()).unwrap();
        }
        for _ in 0..changed {
            self.0.write_all_at(&page.0, at()).unwrap();
        }
        self.0.sync_data().unwrap();
    }
}

fn xorshift(x: &mut u64) -> u64 {
    *x ^= *x << 13;
    *x ^= *x >> 7;
    *x ^= *x << 17;
    *x
}
