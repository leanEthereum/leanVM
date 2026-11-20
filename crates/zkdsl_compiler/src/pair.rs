//! Two cell-mode `DEREF`s through one pointer cell in one block, merged into one instruction's two links.
//!
//! A `DEREF` is an equality between two cells, which the runner settles whichever side is written first, linking
//! them while neither is. So the second of the two can run where the first does: the pointer cell they share is
//! written by then, the first reading it.

use super::*;

/// Every function's pairs merged, then the jump tables' `KVal::At` targets moved with the instructions dropped.
pub(crate) fn pair_derefs(lowered: &mut [Lowered], tables: &mut JumpTables) {
    let mut remaps: HashMap<String, Vec<u32>> = HashMap::new();
    for l in lowered.iter_mut() {
        let targets: Vec<u32> = (tables.slots.iter())
            .filter_map(|k| match k {
                KVal::At(n, i) if *n == l.name => Some(*i),
                _ => None,
            })
            .collect();
        if let Some(remap) = pair_fn(l, &targets) {
            remaps.insert(l.name.clone(), remap);
        }
    }
    for k in &mut tables.slots {
        if let KVal::At(n, i) = k
            && let Some(remap) = remaps.get(n.as_str())
        {
            *i = remap[*i as usize];
        }
    }
}

/// The function's pairs merged; the old-to-new instruction index when instructions went.
fn pair_fn(l: &mut Lowered, at_targets: &[u32]) -> Option<Vec<u32>> {
    let n = l.code.len();
    let mut starts = vec![false; n + 1];
    starts[0] = true;
    for &t in at_targets {
        starts[t as usize] = true;
    }
    for (i, ins) in l.code.iter().enumerate() {
        match &ins.op {
            LOp::Set { k: KVal::Local(t), .. } => starts[*t as usize] = true,
            LOp::Jump { .. } => starts[i + 1] = true,
            _ => {}
        }
    }
    let mut dead = vec![false; n];
    // Per pointer cell, the unpaired cell-mode DEREF of this block through it.
    let mut open: HashMap<Off, usize> = HashMap::new();
    for i in 0..n {
        if starts[i] {
            open.clear();
        }
        let LOp::Deref {
            o1,
            o2,
            o3,
            mode: DerefMode::Cell,
            pair: None,
        } = l.code[i].op
        else {
            continue;
        };
        match open.get(&o1) {
            Some(&j) if l.code[i].hints.is_empty() => {
                if let LOp::Deref { pair, .. } = &mut l.code[j].op {
                    *pair = Some((o2, o3));
                }
                dead[i] = true;
                open.remove(&o1);
            }
            _ => {
                open.insert(o1, i);
            }
        }
    }
    if !dead.iter().any(|&d| d) {
        return None;
    }
    // Old index to new; a dropped instruction maps to the next kept one.
    let mut remap = vec![0u32; n + 1];
    let mut k = 0u32;
    for i in 0..n {
        remap[i] = k;
        k += u32::from(!dead[i]);
    }
    remap[n] = k;
    let code = std::mem::take(&mut l.code);
    l.code = (code.into_iter().zip(&dead))
        .filter(|(_, d)| !**d)
        .map(|(mut ins, _)| {
            if let LOp::Set { k: KVal::Local(t), .. } = &mut ins.op {
                *t = remap[*t as usize];
            }
            ins
        })
        .collect();
    Some(remap)
}
