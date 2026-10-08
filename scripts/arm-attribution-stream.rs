use std::{hint::black_box, time::Instant};

fn main() {
    for bytes in [64 << 10, 2 << 20, 256 << 20] {
        let source = vec![0x5au8; bytes];
        let mut dest = vec![0u8; bytes];
        let reps = ((512 << 20) / bytes).max(2);
        for kind in ["copy", "fill"] {
            for sample in 0..6 {
                let start = Instant::now();
                for _ in 0..reps {
                    if kind == "copy" {
                        black_box(&mut dest).copy_from_slice(black_box(&source));
                    } else {
                        black_box(&mut dest).fill(black_box(0x5a));
                    }
                    black_box(&dest);
                }
                let ns = start.elapsed().as_nanos();
                assert!(dest.iter().all(|&b| b == 0x5a));
                println!("{{\"kind\":\"{kind}\",\"bytes\":{bytes},\"reps\":{reps},\"sample\":{sample},\"warmup\":{},\"ns\":{ns}}}", sample == 0);
            }
        }
    }
}
