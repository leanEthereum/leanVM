//! Native execution of a public wrapper with reservation-aware witness allocation.

use std::ops::Range;

use lean_compiler::{Ast, compile, parse};
use lean_vm::cpu::{Execution, MIN_LOG_MEM, Program, allocation::AllocationLayout, prove, verify};
use primitives::field::{F64, F192, g_pow};

const PREFIX: u32 = 1 << MIN_LOG_MEM;
const MASK: u32 = 1280;
const SLOT: u32 = 256;

fn wrapped(mut ast: Ast) -> Ast {
    assert!(ast.funcs.iter().all(|f| f.name != "zk_private_entry"));
    let main = ast.funcs.iter_mut().find(|f| f.name == "main").expect("main");
    assert!(main.params.is_empty() && main.n_ret == 0 && !main.inline);
    main.name = "zk_private_entry".into();
    let bootstrap = parse(
        r#"
def main():
    masks = GEN ** 65536
    hint_witness(masks[0:1280], "zk_masks")
    zk_private_entry()
    return
"#,
    )
    .expect("public wrapper");
    ast.funcs.extend(bootstrap.funcs);
    ast
}

fn candidate_capacity() {
    let lane = 1 << 22;
    let runs = vec![
        PREFIX + MASK + 2688 * SLOT..PREFIX + MASK + 8191 * SLOT,
        PREFIX + MASK + 8192 * SLOT..PREFIX + MASK + 16123 * SLOT,
        lane + MASK + 7201 * SLOT..lane + MASK + 16379 * SLOT,
        2 * lane + MASK + 12288 * SLOT..2 * lane + MASK + 16379 * SLOT,
    ];
    assert_eq!(runs.iter().map(|r| (r.end - r.start) / SLOT).sum::<u32>(), 26703);
    for largest in [1, 2, 25, 64, 256, 4091] {
        let layout = AllocationLayout::new(runs.clone(), SLOT);
        let mut cursor = 0;
        let mut remaining = 26703 - 3 * (largest - 1);
        while remaining != 0 {
            let slots = remaining.min(largest);
            let base = layout
                .allocate(&mut cursor, slots * SLOT)
                .expect("proved next-fit capacity");
            assert!(runs.iter().any(|r| r.start <= base && cursor <= r.end));
            remaining -= slots;
        }
    }
    println!("The actual allocator meets the candidate's four-run capacity guarantee, including multi-slot requests.");
}

fn audit_execution(execution: &Execution, runs: &[Range<u32>], masks: &[F192]) {
    assert!(execution.unconstrained_reads.is_empty());
    assert_eq!(&execution.mem[PREFIX as usize..(PREFIX + MASK) as usize], masks);
    let counts = execution.memory_read_counts();
    assert!(
        counts[PREFIX as usize..(PREFIX + MASK) as usize]
            .iter()
            .all(|c| *c == F64::ONE)
    );
    let mut end = 0;
    for &(base, size, reserved) in &execution.allocations {
        assert!(base >= end && reserved == size.max(1).div_ceil(SLOT) * SLOT);
        end = base + reserved;
        assert!(runs.iter().any(|r| r.start <= base && end <= r.end));
    }
    assert!(execution.allocations.iter().any(|&(_, size, _)| size > SLOT));
    assert!(execution.allocations.iter().any(|&(_, size, _)| size == 0));
    assert!(execution.allocations.iter().any(|&(base, _, _)| base >= runs[1].start));
    for (address, count) in counts.iter().enumerate().skip(PREFIX as usize) {
        if !runs.iter().any(|r| r.contains(&(address as u32))) {
            assert_eq!(*count, F64::ONE, "reserved address {address} was accessed");
        }
        if *count != F64::ONE {
            assert!(
                execution
                    .allocations
                    .iter()
                    .any(|&(base, size, _)| { base as usize <= address && address < (base + size) as usize }),
                "address {address} lies outside every requested object"
            );
        }
    }
}

fn main() {
    lean_vm::init_prover_pool();
    candidate_capacity();
    let source = r#"
from snark_lib import *

def process(seed, count):
    large = StackBuf(300)
    large[299] = seed
    chain = HeapBuf(count * GEN)
    chain[1] = large[299]
    for index in mul_range(1, count):
        chain[index * GEN] = chain[index] + 1
    return chain

def main():
    secret = hint_witness("secret")
    count = hint_witness("count")
    choice = hint_witness("choice")
    assert log(count) < 8
    digest = StackBuf(2)
    blake2s([secret, secret], [secret, secret], digest)
    empty = HeapBuf(0)
    value = HeapBuf(1)
    if choice == 0:
        result = process(secret, count)
        value[1] = result[count]
    else:
        result = process(secret + 1, count)
        value[1] = result[count] + 1
    public = GEN ** 0
    public[1] = value[1] + secret
    public[GEN] = secret + secret
    return
"#;
    let mut program: Program = compile(&wrapped(parse(source).expect("fixture")));
    let runs = vec![PREFIX + MASK..PREFIX + MASK + 3 * SLOT, 1 << 17..(1 << 17) + 128 * SLOT];
    program.set_allocation_layout(AllocationLayout::new(runs.clone(), SLOT));
    let inputs = [F192::ZERO; 2];
    let mut prefix = None;
    let mut proof_shape = None;
    for (secret, count, choice) in [(17, 0, 0), (29, 4, 0), (53, 4, 1), (71, 6, 1)] {
        let masks: Vec<_> = (0..MASK)
            .map(|i| F192::new(u64::from(i) + secret, u64::from(i), 1))
            .collect();
        program.set_witness("secret", vec![vec![F192::new(secret, 0, 0)]]);
        program.set_witness("count", vec![vec![F192::from(g_pow(count))]]);
        program.set_witness("choice", vec![vec![F192::new(choice, 0, 0)]]);
        program.set_witness("zk_masks", vec![masks.clone()]);
        let execution = program.execute(inputs);
        audit_execution(&execution, &runs, &masks);
        let current_prefix = execution.mem[..PREFIX as usize].to_vec();
        if let Some(expected) = &prefix {
            assert_eq!(&current_prefix, expected, "private choices changed the public prefix");
        }
        prefix = Some(current_prefix);
        println!(
            "Count {count}, branch {choice}: {} fresh allocations, no reserved address accessed.",
            execution.allocations.len()
        );
        if count == 4 {
            let (proof, stats) = prove(&program, inputs, 1);
            verify(&program, &inputs, &proof).expect("native reserved-allocation proof");
            let shape = (stats.log_mem, stats.counts);
            if let Some(expected) = proof_shape {
                assert_eq!(shape, expected);
            }
            proof_shape = Some(shape);
        }
    }
    println!("Two same-statement native proofs pass; the complete wrapper prefix is fixed across all private cases.");
    println!(
        "This checks allocation and legality, not a full ZK sampler, fixed candidate table heights or transcript simulation."
    );
}
