//! Allocation feasibility checks, not a ZK prover or a program-wide certificate.

use std::collections::{BTreeMap, BTreeSet};

use lean_vm::cpu::{Execution, Op, allocation::AllocationLayout};

use super::*;

const PREFIX: u32 = 1 << lean_vm::cpu::MIN_LOG_MEM;
const MASK: u32 = 1280;
const SLOT: u32 = 256;

fn candidate_runs() -> Vec<Range<u32>> {
    let lane = 1 << 22;
    vec![
        PREFIX + MASK + 2688 * SLOT..PREFIX + MASK + 8191 * SLOT,
        PREFIX + MASK + 8192 * SLOT..PREFIX + MASK + 16123 * SLOT,
        lane + MASK + 7201 * SLOT..lane + MASK + 16379 * SLOT,
        2 * lane + MASK + 12288 * SLOT..2 * lane + MASK + 16379 * SLOT,
    ]
}

fn wrapped_guest() -> Program {
    let mut ast = parse_with_replacements(include_str!("../../guests/aggregate.py"), &placeholder_map(19))
        .expect("aggregation source");
    assert!(ast.funcs.iter().all(|f| f.name != "zk_private_entry"));
    let main = ast.funcs.iter_mut().find(|f| f.name == "main").expect("main");
    assert!(main.params.is_empty() && main.n_ret == 0 && !main.inline);
    main.name = "zk_private_entry".into();
    ast.funcs.extend(
        lean_compiler::parse(
            r#"
def main():
    masks = GEN ** 65536
    hint_witness(masks[0:1280], "zk_masks")
    zk_private_entry()
    return
"#,
        )
        .expect("public wrapper")
        .funcs,
    );
    let program = compile(&ast);
    assert_eq!(program.prog.len(), 1 << 19, "wrapped code fixed point changed");
    let first_code = (1 << 19) - (1 << 11) + 1024;
    let last_code = first_code + 127;
    let emitted_end = program
        .fn_ranges
        .iter()
        .map(|(_, pc, size)| pc + size)
        .max()
        .expect("function ranges");
    assert!(emitted_end <= first_code);
    assert!(program.filler.iter().all(|b| b.pc + b.size < first_code));
    assert!(
        program.prog[first_code as usize..=last_code as usize]
            .iter()
            .all(|op| matches!(op, Op::Set { o: 0, k } if *k == F192::ZERO))
    );
    let mut maximum = 0;
    for (_, pc, size) in &program.fn_ranges {
        let mut loads = BTreeMap::<u32, usize>::new();
        for address in *pc..pc + size {
            if program.filler.iter().any(|b| (b.pc..=b.pc + b.size).contains(&address)) {
                continue;
            }
            if let Some(cells) = blake_cells(&program.prog[address as usize]) {
                for cell in cells {
                    *loads.entry(cell).or_default() += 1;
                }
            }
        }
        maximum = maximum.max(loads.values().copied().max().unwrap_or(0));
    }
    assert!(maximum <= 256, "static per-cell BLAKE2s load cap exceeded");
    println!("Wrapped code: log 19, emitted end {emitted_end}, static BLAKE2s load cap {maximum}.");
    program
}

fn blake_cells(op: &Op) -> Option<[u32; 9]> {
    match *op {
        Op::Blake2s { ins, cv, out, md } => Some([ins[0], ins[1], ins[2], ins[3], cv, cv + 1, out, out + 1, md]),
        _ => None,
    }
}

fn check_accesses(execution: &Execution, runs: &[Range<u32>], masks: &[F192]) {
    assert!(execution.unconstrained_reads.is_empty());
    assert_eq!(&execution.mem[PREFIX as usize..(PREFIX + MASK) as usize], masks);
    let mut end = 0;
    for &(base, size, reserved) in &execution.allocations {
        assert!(base >= end && reserved == size.max(1).div_ceil(SLOT) * SLOT);
        end = base + reserved;
        assert!(runs.iter().any(|r| r.start <= base && end <= r.end));
    }
    let mut object = 0;
    for (address, count) in execution.memory_read_counts().iter().enumerate().skip(PREFIX as usize) {
        let address = address as u32;
        while object < execution.allocations.len()
            && execution.allocations[object].0 + execution.allocations[object].1 <= address
        {
            object += 1;
        }
        if *count != F64::ONE {
            let &(base, size, _) = execution.allocations.get(object).expect("access past all objects");
            assert!(
                base <= address && address < base + size,
                "access outside requested object at {address}"
            );
        }
        if !runs.iter().any(|r| r.contains(&address)) {
            assert_eq!(*count, F64::ONE, "mask reservation accessed at {address}");
        }
    }
}

fn compare_relocations(program: &Program, dense: &Execution, reserved: &Execution) {
    assert_eq!(dense.base_counts, reserved.base_counts);
    assert_eq!(dense.allocations.len(), reserved.allocations.len());
    assert_eq!(&dense.mem[..PREFIX as usize], &reserved.mem[..PREFIX as usize]);
    let mut renaming = BTreeMap::from([(0, 0)]);
    for (&(old, size, _), &(new, new_size, _)) in dense.allocations.iter().zip(&reserved.allocations) {
        assert_eq!(size, new_size, "allocation request depends on relocation");
        renaming.insert(old, new);
    }
    let mut sites = BTreeSet::new();
    let mut loads = BTreeMap::<u32, usize>::new();
    for ((pc, old), (new_pc, new)) in dense.instruction_sites().zip(reserved.instruction_sites()) {
        assert_eq!(pc, new_pc, "instruction choices depend on relocation");
        assert_eq!(
            renaming.get(&old),
            Some(&new),
            "frame does not follow allocation renaming"
        );
        assert!(sites.insert((pc, new)), "instruction repeats within one frame");
        if let Some(cells) = blake_cells(&program.prog[pc as usize]) {
            for cell in cells {
                assert_eq!(dense.mem[(old + cell) as usize], reserved.mem[(new + cell) as usize]);
                *loads.entry(new + cell).or_default() += 1;
            }
        }
    }
    let maximum = loads.values().copied().max().expect("signature compressions");
    assert!(maximum <= 256, "actual per-cell BLAKE2s load cap exceeded");
    println!("Actual BLAKE2s load {maximum}; compression data and instruction choices agree after relocation.");
}

/// Execute a real leaf witness with dense and reservation-aware allocation.
/// This does not exercise recursive children or construct the common ZK padding.
pub fn audit_leaf(n_xmss: usize, n_sphincs: usize, native_proof: bool) {
    use crate::signers_cache::{XMSS_EPOCH_A, get_signers, get_sphincs_signers, message};

    assert!(n_xmss + n_sphincs > 0);
    let raw_xmss = get_signers(n_xmss)
        .into_iter()
        .map(|(key, signature)| (key, XMSS_EPOCH_A, message(), signature))
        .collect();
    let mut prepared = prepare_aggregate(&[], raw_xmss, get_sphincs_signers(n_sphincs), None, MIN_LOG_INV_RATE)
        .expect("prepare real leaf witness");
    let mut program = wrapped_guest();
    let mut defer = prepared.defer;
    defer.bytecode_value = F192::from(lean_vm::cpu::layout::bytecode_table(&program.prog)[0]);
    let seed = lean_vm::cpu::fs_seed(&program);
    assert_ne!(seed, lean_vm::cpu::fs_seed(unified_guest()));
    let public_input = statement_digest_for(
        &program,
        signers_hash(&prepared.xmss_signers, &prepared.sphincs_signers),
        &defer,
    );
    for (name, entries) in &mut prepared.hints.0 {
        match name.as_str() {
            "fs_seed" => *entries = vec![seed.to_vec()],
            "leaf_defer" => *entries = vec![vec![defer.bytecode_value, defer.matrix_a_value, defer.matrix_b_value]],
            _ => {}
        }
    }
    prepared.hints.install(&mut program);
    let masks: Vec<_> = (0..MASK).map(|i| F192::new(i as u64 + 1, i as u64, 1)).collect();
    program.set_witness("zk_masks", vec![masks.clone()]);
    let runs = candidate_runs();
    let mut dense = program.clone();
    dense.set_allocation_layout(AllocationLayout::new(
        std::iter::once(runs[0].start..1 << 25).collect(),
        1,
    ));
    let dense = dense.execute(public_input);
    program.set_allocation_layout(AllocationLayout::new(runs.clone(), SLOT));
    let reserved = program.execute(public_input);
    check_accesses(&reserved, &runs, &masks);
    compare_relocations(&program, &dense, &reserved);
    let slots: u32 = reserved.allocations.iter().map(|&(_, _, n)| n / SLOT).sum();
    let largest = reserved
        .allocations
        .iter()
        .map(|&(_, _, n)| n / SLOT)
        .max()
        .expect("allocations");
    let budget = 26703u32
        .checked_sub(3 * (largest - 1))
        .expect("no worst-case capacity guarantee");
    assert!(
        slots <= budget,
        "execution fits, but the sufficient next-fit budget is exceeded"
    );
    println!(
        "Leaf: {n_xmss} XMSS, {n_sphincs} SPHINCS; {} allocations, {slots}/{budget} guaranteed slots, largest {largest} slots.",
        reserved.allocations.len()
    );
    println!(
        "Real opcode counts [XOR, MUL, SET, DEREF, JUMP, BLAKE2s]: {:?}.",
        reserved.base_counts
    );
    assert!(reserved.base_counts[5] <= 65536, "real BLAKE2s padding budget exceeded");
    println!("Mask bank untouched; all accesses belong to requested objects or the public prefix.");
    drop(dense);
    drop(reserved);
    if native_proof {
        let (proof, _) = prove(&program, public_input, MIN_LOG_INV_RATE);
        verify(&program, &public_input, &proof).expect("wrapped leaf proof verifies");
        println!("A native proof verifies against the wrapped bytecode and its own statement digest.");
    }
    println!("These are finite leaf execution checks, not a universal relocation theorem or a ZK proof.");
}
