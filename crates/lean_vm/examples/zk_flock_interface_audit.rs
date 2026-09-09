//! A small-frame valid witness pair and its disclosed chaining-value invariant.

use std::collections::HashMap;

use lean_vm::{
    cpu::{DerefMode, Op, Program, hints::RHint, layout, prove, verify},
    hash_flock::{IV, IV_CELLS},
    leaf, tables,
};
use primitives::field::{F64, F192, g_pow};

const FRAME: u32 = 1280;

fn program() -> Program {
    let mut code = vec![Op::Jump { oc: 0, od: 0, of: 1 }];
    for offset in 0..4 {
        code.push(Op::Set {
            o: offset,
            k: F192::ZERO,
        });
    }
    code.extend([
        Op::Set {
            o: 12,
            k: F192::new(64, u32::MAX as u64, 0),
        },
        Op::Set {
            o: 14,
            k: F192::from(g_pow(31)),
        },
        Op::Set { o: 15, k: F192::ONE },
        Op::Set {
            o: 18,
            k: F192::from(g_pow(FRAME as usize)),
        },
        Op::Xor { a: 0, b: 0, c: 16 },
        Op::Mul { a: 0, b: 0, c: 17 },
        Op::Deref {
            o1: 18,
            o2: 0,
            o3: 19,
            mode: DerefMode::Cell,
        },
    ]);
    code.extend(std::iter::repeat_n(
        Op::Blake2s {
            ins: [0, 1, 2, 3],
            cv: 8,
            out: 10,
            md: 12,
        },
        8,
    ));
    code.push(Op::Jump { oc: 14, od: 14, of: 15 });
    assert!(code.len() < 32);
    code.resize(32, Op::Set { o: 16, k: F192::ZERO });
    let hints = HashMap::from([(
        1,
        vec![RHint::WitnessStack {
            name: "cv".into(),
            base: 8,
            len: 2,
        }],
    )]);
    Program::assemble(code, hints, FRAME + 256)
}

fn gkr_scalars(depth: usize) -> usize {
    let mut count = 2;
    let mut layer = depth;
    if layer % 2 == 1 {
        count += 6;
        layer -= 1;
    }
    while layer > 0 {
        count += 4 * (depth - layer) + 12;
        layer -= 2;
    }
    count
}

fn main() {
    lean_vm::init_prover_pool();
    let mut program = program();
    let public_input = [F192::from(g_pow(1)), F192::from(g_pow(FRAME as usize))];
    let mut common = None;
    for bit in 0..=1 {
        let mut cv = IV_CELLS;
        cv[0].c0 ^= bit;
        program.set_witness("cv", vec![cv.to_vec()]);
        let execution = program.execute(public_input);
        assert_eq!(execution.base_counts, [1, 1, 8, 1, 2, 8]);
        assert!(execution.unconstrained_reads.is_empty());
        assert_eq!(execution.mem.len(), 1 << 16);
        assert_eq!(&execution.mem[FRAME as usize + 8..FRAME as usize + 10], &cv);
        assert!(execution.mem.iter().enumerate().all(|(address, &value)| {
            address < 2 || (FRAME as usize..FRAME as usize + 256).contains(&address) || value == F192::ZERO
        }));
        let (proof, stats) = prove(&program, public_input, 1);
        verify(&program, &public_input, &proof).expect("complete valid VM proof");
        let heights = stats.counts.map(|count| count.ilog2() as usize);
        let layout = layout(&program.prog, stats.log_mem, heights, public_input);
        assert_eq!(layout.shape.mu, stats.log_mem + 3);
        assert_eq!(stats.counts, execution.base_counts);
        if let Some(previous) = common {
            assert_eq!(previous, (stats.log_mem, heights, layout.shape.mu));
        }
        common = Some((stats.log_mem, heights, layout.shape.mu));
        let before_blake: usize = tables::tables()[..5]
            .iter()
            .map(|table| table.n_committed_columns())
            .sum();
        let start =
            8 + 2 + gkr_scalars(leaf::layout(&layout.push).mu) + 5 + 3 * heights.iter().max().unwrap() + before_blake;
        let first_cv = tables::BLAKE2S_VALUE_COLS[12];
        let values = &proof.stream[start + first_cv..start + first_cv + 6];
        assert_eq!(
            values,
            [
                F192::new(cv[0].c0, 0, 0),
                F192::from(IV[1]),
                F192::from(IV[2]),
                F192::from(IV[3]),
                F192::new(64, 0, 0),
                F192::new(u32::MAX as u64, 0, 0)
            ]
        );
        let disclosed = F192::from(IV[1]) * values[0] + F192::from(IV[0]) * values[1];
        assert_eq!(disclosed, F192::from(IV[1] * F64(bit)));
        println!(
            "Valid bit-{bit} proof: the disclosed table-column invariant equals the predicted private-bit multiple."
        );
    }
    println!(
        "Both witnesses use one 256-cell payload slot, public bootstrap cells and the same public heights; no filler rows or verifier changes are needed."
    );
    println!(
        "These concrete Fiat-Shamir runs certify the wire disclosure, not an honest-query probability theorem for Fiat-Shamir."
    );
}
