//! Allocation feasibility checks, not a ZK prover or a program-wide certificate.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use lean_vm::cpu::{Execution, Op, allocation::AllocationLayout};

use super::*;

mod range;

const PREFIX: u32 = 1 << lean_vm::cpu::MIN_LOG_MEM;
const MASK: u32 = 1280;
const SLOT: u32 = 256;
const LOCAL_DIGIT_CHECK: &str = r#"
@inline
def zk_digit_check(digit):
    product = digit + 1
    for k in unroll(1, 8):
        product = product * (digit + GEN ** k)
    assert product == 0
    return
"#;

fn candidate_runs() -> Vec<Range<u32>> {
    let lane = 1 << 22;
    vec![
        PREFIX + MASK + 2688 * SLOT..PREFIX + MASK + 8191 * SLOT,
        PREFIX + MASK + 8192 * SLOT..PREFIX + MASK + 16123 * SLOT,
        lane + MASK + 7201 * SLOT..lane + MASK + 16379 * SLOT,
        2 * lane + MASK + 12288 * SLOT..2 * lane + MASK + 16379 * SLOT,
    ]
}

fn wrapped_guest(local_digits: bool, local_ranges: bool, ordinary_children: bool) -> Program {
    let mut source = include_str!("../../guests/aggregate.py").to_string();
    if local_ranges {
        for (old, new) in [
            (
                "zeta = HeapBuf(g_bus_mu)",
                "zeta = HeapBuf(g_bus_mu * GEN ** YR_LOG_CAP)",
            ),
            (
                "point_fold = HeapBuf(GEN ** (n_folds + YR_LOG_CAP))",
                "point_fold = HeapBuf(SIZE_BITS + SLOT_STRIDE_LOG)",
            ),
        ] {
            assert_eq!(source.matches(old).count(), 1);
            source = source.replace(old, new);
        }
    }
    if ordinary_children {
        let [seed0, seed1] = lean_vm::cpu::fs_seed(unified_guest()).map(dsl_u128);
        for (old, new) in [
            (
                "pi_0, pi_1 = statement_digest(seed_0, seed_1, sub_hash, carried)",
                format!("pi_0, pi_1 = statement_digest({seed0}, {seed1}, sub_hash, carried)"),
            ),
            (
                "verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, child_fresh * xc ** DEFER_SIZE)",
                format!(
                    "verify_sub(pi_0, pi_1, {seed0}, {seed1}, g_logs_pow2, g_squares, child_fresh * xc ** DEFER_SIZE)"
                ),
            ),
        ] {
            assert_eq!(source.matches(old).count(), 1);
            source = source.replace(old, &new);
        }
    }
    if local_digits && !local_ranges {
        for check in [
            "assert log(digit) < CHAIN_LENGTH",
            "assert log(digit) < SP_CHAIN_LENGTH",
        ] {
            assert_eq!(source.matches(check).count(), 1);
            source = source.replace(check, "zk_digit_check(digit)");
        }
        source.push_str(LOCAL_DIGIT_CHECK);
    }
    let mut ast = parse_with_replacements(&source, &placeholder_map(19)).expect("aggregation source");
    if local_ranges {
        let sites = range::eliminate_probes(&mut ast);
        println!("Replaced {sites} source range-check sites by local exponent checks.");
    }
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
    let mut program = compile(&ast);
    let original_seed = lean_vm::cpu::fs_seed(&program);
    program.use_local_deref_fillers();
    assert_ne!(lean_vm::cpu::fs_seed(&program), original_seed);
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
    let mut priority_caps = [[0usize; 3]; 5];
    let mut local_caps = [[0usize; 3]; 5];
    for (_, pc, size) in &program.fn_ranges {
        let mut loads = BTreeMap::<u32, usize>::new();
        let mut local_loads = BTreeMap::<u32, [usize; 13]>::new();
        for address in *pc..pc + size {
            if program.filler.iter().any(|b| (b.pc..=b.pc + b.size).contains(&address)) {
                continue;
            }
            if let Some(cells) = blake_cells(&program.prog[address as usize]) {
                for cell in cells {
                    *loads.entry(cell).or_default() += 1;
                    local_loads.entry(cell).or_default()[0] += 1;
                }
            } else if let Some((table, cells)) = noncompression_cells(&program.prog[address as usize]) {
                for (column, cell) in cells.into_iter().enumerate() {
                    if let Some(cell) = cell {
                        local_loads.entry(cell).or_default()[local_priority(table, column)] += 1;
                    }
                }
            }
        }
        maximum = maximum.max(loads.values().copied().max().unwrap_or(0));
        for address in *pc..pc + size {
            if program.filler.iter().any(|b| (b.pc..=b.pc + b.size).contains(&address)) {
                continue;
            }
            let Some((table, cells)) = noncompression_cells(&program.prog[address as usize]) else {
                continue;
            };
            for (column, cell) in cells.into_iter().enumerate() {
                if let Some(cell) = cell {
                    priority_caps[table][column] = priority_caps[table][column].max(*loads.get(&cell).unwrap_or(&0));
                    local_caps[table][column] = local_caps[table][column].max(
                        local_loads[&cell][..=local_priority(table, column)]
                            .iter()
                            .sum::<usize>()
                            - 1,
                    );
                }
            }
        }
    }
    assert!(maximum <= 256, "static per-cell BLAKE2s load cap exceeded");
    println!("Wrapped code: log 19, emitted end {emitted_end}, static BLAKE2s load cap {maximum}.");
    priority_caps[3][1] = maximum;
    if local_ranges && ordinary_children {
        let certificate = [[2, 16, 16], [2, 2, 1], [213, 0, 0], [0, 213, 182], [16, 1, 2]];
        assert!(
            priority_caps
                .iter()
                .flatten()
                .zip(certificate.iter().flatten())
                .all(|(actual, cap)| actual <= cap),
            "the local-range wrapper exceeds its BLAKE-priority shift certificate"
        );
        assert!(
            local_caps[4]
                .into_iter()
                .zip([517, 1, 350])
                .all(|(actual, cap)| actual <= cap)
        );
    }
    println!("Static BLAKE-priority shift caps per memory role (X/M/S/D/J): {priority_caps:?}.");
    println!(
        "These are public incidence bounds under fresh-frame single-visit execution; the indirect DEREF role uses the global cap."
    );
    println!("Static local-first label caps per memory role (X/M/S/D/J): {local_caps:?}; indirect DEREF excluded.");
    program
}

fn noncompression_cells(op: &Op) -> Option<(usize, [Option<u32>; 3])> {
    Some(match *op {
        Op::Xor { a, b, c } => (0, [Some(a), Some(b), Some(c)]),
        Op::Mul { a, b, c } => (1, [Some(a), Some(b), Some(c)]),
        Op::Set { o, .. } => (2, [Some(o), None, None]),
        Op::Deref { o1, o3, .. } => (3, [Some(o1), None, Some(o3)]),
        Op::Jump { oc, od, of } => (4, [Some(oc), Some(od), Some(of)]),
        Op::Blake2s { .. } => return None,
    })
}

fn local_priority(table: usize, column: usize) -> usize {
    match (table, column) {
        (4, column) => 1 + column,
        (2, 0) => 4,
        (1, 1 | 2) => 4 + column,
        (0, column) => 7 + column,
        (3, 0) => 10,
        (3, 2) => 11,
        (1, 0) => 12,
        _ => panic!("not a local noncompression role"),
    }
}

fn blake_cells(op: &Op) -> Option<[u32; 9]> {
    match *op {
        Op::Blake2s { ins, cv, out, md } => Some([ins[0], ins[1], ins[2], ins[3], cv, cv + 1, out, out + 1, md]),
        _ => None,
    }
}

fn check_accesses(program: &Program, execution: &Execution, runs: &[Range<u32>], masks: &[F192]) {
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
            if !(base <= address && address < base + size) {
                let mut sites = BTreeSet::new();
                for (pc, fp) in execution.instruction_sites() {
                    let op = &program.prog[pc as usize];
                    let cells = match *op {
                        Op::Xor { a, b, c } | Op::Mul { a, b, c } => vec![a, b, c],
                        Op::Set { o, .. } => vec![o],
                        Op::Deref { o1, o3, .. } => vec![o1, o3],
                        Op::Jump { oc, od, of } => vec![oc, od, of],
                        Op::Blake2s { .. } => blake_cells(op).unwrap().to_vec(),
                    };
                    let indirect = if let Op::Deref { o1, o2, .. } = *op {
                        let ptr = execution.mem[(fp + o1) as usize];
                        ptr.c1 == 0 && ptr.c2 == 0 && F64(ptr.c0) * g_pow(o2 as usize) == g_pow(address as usize)
                    } else {
                        false
                    };
                    if indirect || cells.iter().any(|&cell| fp + cell == address) {
                        sites.insert(format!("{}; fp={fp}, {op:?}", program.site_at(pc)));
                    }
                }
                panic!(
                    "access at {address} before object {base}..{}, sites {sites:?}",
                    base + size
                );
            }
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

fn public_leaf_probes(group_sizes: &[usize], sphincs: usize) -> Vec<usize> {
    let mut counts = vec![0; PREFIX as usize];
    let mut check = |value: usize, bound: usize| {
        assert!(value < bound && bound <= PREFIX as usize);
        counts[value] += 1;
        counts[bound - 1 - value] += 1;
    };
    for value in [group_sizes.len(), 0, group_sizes.len()] {
        check(value, MAX_EPOCHS + 1);
    }
    for value in [sphincs, 0, sphincs] {
        check(value, MAX_KEYS);
    }
    check(0, MAX_RECURSIONS + 1);
    for &size in group_sizes {
        for value in [size, 0, size] {
            check(value, MAX_KEYS);
        }
        check(size % 2, 2);
        check(size / 2, MAX_KEYS);
    }
    check(group_sizes.iter().sum::<usize>() + sphincs, MAX_KEYS);
    for blocks in group_sizes
        .iter()
        .map(|size| size.div_ceil(2))
        .chain((sphincs != 0).then_some(sphincs))
        .chain(std::iter::once(2 + 2 * group_sizes.len()))
    {
        check((blocks - 1) % SIGNERS_WINDOW, SIGNERS_WINDOW);
        check((blocks - 1) / SIGNERS_WINDOW, SIGNERS_MAX_WINDOWS);
    }
    counts[0] += 1;
    counts[1] += 1;
    counts
}

fn audit_prefix_probes(
    program: &Program,
    execution: &Execution,
    group_sizes: &[usize],
    sphincs: usize,
    local_digits: bool,
    local_ranges: bool,
) {
    use lean_vm::cpu::filler::{NO_FLOORS, filled, solve};

    let source = include_str!("../../guests/aggregate.py");
    let line_of = |needle: &str| {
        let matches: Vec<_> = source
            .lines()
            .enumerate()
            .filter(|(_, line)| line.trim() == needle)
            .collect();
        assert_eq!(matches.len(), 1, "probe source anchor {needle}");
        matches[0].0 as u32 + 1
    };
    let digits = [
        line_of("assert log(digit) < CHAIN_LENGTH"),
        line_of("assert log(digit) < SP_CHAIN_LENGTH"),
    ];
    let coverage = [
        line_of("assert log(idx) < log(slots)"),
        line_of("assert log(off_hint) < log(sphincs_slots_g)"),
    ];
    let addresses: HashMap<_, _> = (0..PREFIX as usize).map(|j| (g_pow(j).0, j)).collect();
    let mut profiles: [Vec<usize>; 4] = std::array::from_fn(|_| vec![0; PREFIX as usize]);
    let mut other_sources = BTreeMap::<u32, usize>::new();
    let mut bootstrap_pcs = BTreeSet::new();
    for (pc, fp) in execution.instruction_sites() {
        let line = program.src_lines[pc as usize];
        let kind = if fp == 0 {
            0
        } else if digits.contains(&line) {
            1
        } else if coverage.contains(&line) {
            2
        } else {
            3
        };
        if fp == 0 {
            assert_eq!(program.fn_at(pc), "main");
            assert!(bootstrap_pcs.insert(pc));
        } else {
            assert!(fp >= PREFIX);
        }
        let mut count = |address: usize| {
            if address < PREFIX as usize {
                profiles[kind][address] += 1;
                if kind == 3 {
                    *other_sources.entry(line).or_default() += 1;
                }
            }
        };
        let op = &program.prog[pc as usize];
        if fp == 0 {
            let cells = match *op {
                Op::Xor { a, b, c } | Op::Mul { a, b, c } => vec![a, b, c],
                Op::Set { o, .. } => vec![o],
                Op::Deref { o1, o3, .. } => vec![o1, o3],
                Op::Jump { oc, od, of } => vec![oc, od, of],
                Op::Blake2s { .. } => blake_cells(op).unwrap().to_vec(),
            };
            for cell in cells {
                count(cell as usize);
            }
        }
        if let Op::Deref { o1, o2, .. } = *op {
            let pointer = execution.mem[(fp + o1) as usize];
            assert_eq!((pointer.c1, pointer.c2), (0, 0));
            if let Some(&address) = addresses.get(&(F64(pointer.c0) * g_pow(o2 as usize)).0) {
                count(address);
            }
        }
    }
    let (_, main_pc, main_len) = program.fn_ranges.iter().find(|(name, _, _)| name == "main").unwrap();
    let main_pcs = (*main_pc..main_pc + main_len)
        .filter(|pc| {
            !program
                .filler
                .iter()
                .any(|block| (block.pc..=block.pc + block.size).contains(pc))
        })
        .collect();
    assert_eq!(bootstrap_pcs, main_pcs);
    let expected_other = if local_ranges {
        let mut fixed = vec![0; PREFIX as usize];
        fixed[0] = 1;
        fixed[1] = 1;
        fixed
    } else {
        public_leaf_probes(group_sizes, sphincs)
    };
    let differences: Vec<_> = expected_other
        .iter()
        .zip(&profiles[3])
        .enumerate()
        .filter(|(_, (a, b))| a != b)
        .collect();
    assert!(
        differences.is_empty(),
        "public probe remainder differs: {differences:?}; sources {other_sources:?}"
    );
    let mut expected_coverage = vec![0; PREFIX as usize];
    for size in group_sizes
        .iter()
        .copied()
        .chain(std::iter::once(sphincs))
        .filter(|_| !local_ranges)
    {
        for count in &mut expected_coverage[..size] {
            *count += 2;
        }
    }
    assert_eq!(profiles[2], expected_coverage);
    assert!(profiles[1][8..].iter().all(|&count| count == 0));
    assert_eq!(
        profiles[1].iter().sum::<usize>(),
        if local_digits {
            0
        } else {
            2 * xmss::V * group_sizes.iter().sum::<usize>() + 2 * sphincs::V * sphincs::D * sphincs
        }
    );
    assert!((0..8).all(|j| profiles[1][j] == profiles[1][7 - j]));
    const _: () = assert!(xmss::V == 42 && xmss::CHAIN_LENGTH == 8 && xmss::TARGET_SUM == 195);
    const _: () = assert!(sphincs::V == 42 && sphincs::CHAIN_LEN == 8 && sphincs::TARGET_SUM == 191 && sphincs::D == 3);
    let xmss = group_sizes.iter().sum::<usize>();
    let caps: Vec<_> = [41, 41, 42, 33, 33, 42, 41, 41]
        .into_iter()
        .zip([41, 41, 41, 34, 34, 41, 41, 41])
        .map(|(x, s)| x * xmss + s * sphincs::D * sphincs)
        .collect();
    assert!((0..8).all(|j| profiles[1][j] <= caps[j]));
    let topups = (0..8).map(|j| caps[j] - profiles[1][j]).sum::<usize>();
    if !local_digits {
        assert_eq!(topups, 230 * (xmss + sphincs::D * sphincs));
    }
    let padded = filled(execution.base_counts, &solve(execution.base_counts, NO_FLOORS).unwrap());
    let filler = padded[3] - execution.base_counts[3];
    for j in 0..PREFIX as usize {
        let count = profiles.iter().map(|part| part[j]).sum::<usize>();
        assert_eq!(execution.memory_read_counts()[j], g_pow(count));
    }
    println!(
        "Prefix probes: {} digit reads, {} coverage reads, {} public remainder reads; {filler} local filler rows leave the prefix unchanged.",
        profiles[1].iter().sum::<usize>(),
        profiles[2].iter().sum::<usize>(),
        profiles[3].iter().sum::<usize>()
    );
    if local_ranges {
        println!("All range probes are local; prefix counts depend only on the public bootstrap and two input reads.");
    } else if local_digits {
        println!("Local digit membership eliminates all private prefix-count contributions on this canonical leaf.");
    } else {
        println!(
            "All private prefix-count contributions are confined to indices 0..7 on this leaf; public geometry predicts the other 65528 counts exactly."
        );
        println!(
            "Eight-address completion would add {topups} DEREF/JUMP cycles; those cycles are not installed by this audit."
        );
    }
}

/// Execute a real leaf witness with dense and reservation-aware allocation.
/// This does not exercise recursive children or construct the common ZK padding.
pub fn audit_leaf(n_xmss: usize, n_sphincs: usize, native_proof: bool, local_digits: bool, local_ranges: bool) {
    use crate::signers_cache::{XMSS_EPOCH_A, get_signers, get_sphincs_signers, message};

    assert!(n_xmss + n_sphincs > 0);
    let raw_xmss = get_signers(n_xmss)
        .into_iter()
        .map(|(key, signature)| (key, XMSS_EPOCH_A, message(), signature))
        .collect();
    let mut prepared = prepare_aggregate(&[], raw_xmss, get_sphincs_signers(n_sphincs), None, MIN_LOG_INV_RATE)
        .expect("prepare real leaf witness");
    let mut program = wrapped_guest(local_digits, local_ranges, false);
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
    check_accesses(&program, &reserved, &runs, &masks);
    compare_relocations(&program, &dense, &reserved);
    let group_sizes: Vec<_> = prepared.xmss_signers.iter().map(|(_, _, keys)| keys.len()).collect();
    audit_prefix_probes(
        &program,
        &reserved,
        &group_sizes,
        prepared.sphincs_signers.len(),
        local_digits || local_ranges,
        local_ranges,
    );
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
    check_opcode_budget(&program, &reserved);
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

/// Audit an optional outer wrapper that verifies ordinary non-ZK children.
/// Its child program identity is public and separate from the wrapper's identity.
pub fn audit_recursion(n_xmss: usize, n_sphincs: usize, children: usize, native_proof: bool) {
    use crate::signers_cache::{XMSS_EPOCH_A, get_signers, get_sphincs_signers, message};

    assert!((1..=MAX_RECURSIONS).contains(&children) && n_xmss + n_sphincs > 0);
    let raw = get_signers(n_xmss)
        .into_iter()
        .map(|(key, signature)| (key, XMSS_EPOCH_A, message(), signature))
        .collect();
    let child = aggregate(&[], raw, get_sphincs_signers(n_sphincs), None, MIN_LOG_INV_RATE).expect("ordinary child");
    child.verify().expect("complete ordinary child verifies");
    let mut prepared = prepare_aggregate(&vec![child; children], vec![], vec![], None, MIN_LOG_INV_RATE)
        .expect("prepare recursive witness");
    assert_eq!(
        DeferredClaim::recompute(
            prepared.defer.bytecode_point.clone(),
            prepared.defer.matrix_point.clone()
        )
        .unwrap(),
        prepared.defer
    );
    let mut program = wrapped_guest(false, true, true);
    let seed = lean_vm::cpu::fs_seed(&program);
    let public_input = statement_digest_for(
        &program,
        signers_hash(&prepared.xmss_signers, &prepared.sphincs_signers),
        &prepared.defer,
    );
    for (name, entries) in &mut prepared.hints.0 {
        if name == "fs_seed" {
            *entries = vec![seed.to_vec()];
        }
    }
    prepared.hints.install(&mut program);
    let masks: Vec<_> = (0..MASK).map(|i| F192::new(i as u64 + 1, i as u64, 1)).collect();
    program.set_witness("zk_masks", vec![masks.clone()]);
    let runs = candidate_runs();
    let mut dense_program = program.clone();
    dense_program.set_allocation_layout(AllocationLayout::new(
        std::iter::once(runs[0].start..1 << 25).collect(),
        1,
    ));
    let dense_execution = dense_program.execute(public_input);
    program.set_allocation_layout(AllocationLayout::new(runs.clone(), SLOT));
    let execution = program.execute(public_input);
    check_accesses(&program, &execution, &runs, &masks);
    compare_relocations(&program, &dense_execution, &execution);
    drop(dense_execution);
    let groups: Vec<_> = prepared.xmss_signers.iter().map(|(_, _, keys)| keys.len()).collect();
    audit_prefix_probes(
        &program,
        &execution,
        &groups,
        prepared.sphincs_signers.len(),
        true,
        true,
    );
    let slots: u32 = execution.allocations.iter().map(|&(_, _, n)| n / SLOT).sum();
    let largest = execution.allocations.iter().map(|&(_, _, n)| n / SLOT).max().unwrap();
    let budget = 26703u32.checked_sub(3 * (largest - 1)).expect("allocation bound");
    assert!(slots <= budget);
    println!(
        "Recursive wrapper: {children} ordinary children, {slots}/{budget} guaranteed slots, largest {largest} slots."
    );
    println!("Real opcode counts: {:?}.", execution.base_counts);
    check_opcode_budget(&program, &execution);
    drop(execution);
    if native_proof {
        let (proof, _) = prove(&program, public_input, MIN_LOG_INV_RATE);
        verify(&program, &public_input, &proof).expect("recursive wrapper proof");
        println!(
            "Native wrapper proof verifies; its carried claims on the ordinary child program were discharged separately."
        );
    }
    println!(
        "This is a recursive execution certificate, not a self-recursive ZK construction or a joint privacy proof."
    );
}

fn local_count_profile(program: &Program, execution: &Execution, original: &[Vec<(u64, u32)>]) {
    let mut phases: [Vec<(u32, usize, usize)>; 13] = std::array::from_fn(|_| Vec::new());
    let mut indirect = Vec::new();
    for (pc, fp) in execution.instruction_sites() {
        let op = &program.prog[pc as usize];
        if let Some(cells) = blake_cells(op) {
            for (column, cell) in cells.into_iter().enumerate() {
                phases[0].push((fp + cell, 5, column));
            }
        } else if let Some((table, cells)) = noncompression_cells(op) {
            for (column, cell) in cells.into_iter().enumerate() {
                if let Some(cell) = cell {
                    phases[local_priority(table, column)].push((fp + cell, table, column));
                }
            }
        }
        if let Op::Deref { o1, o2, .. } = *op {
            let pointer = execution.mem[(fp + o1) as usize];
            assert_eq!((pointer.c1, pointer.c2), (0, 0));
            indirect.push((F64(pointer.c0) * g_pow(o2 as usize)).0);
        }
    }
    let mut profile: Vec<_> = original.iter().map(|row| vec![(0u64, 0u32); row.len() - 1]).collect();
    let mut counts = HashMap::<u32, u32>::new();
    for phase in phases {
        for (address, table, column) in phase {
            let count = counts.entry(address).or_default();
            let output = &mut profile[table][column];
            output.0 += u64::from(*count);
            output.1 = output.1.max(*count);
            *count += 1;
        }
    }
    let mut encoded: HashMap<_, _> = counts
        .into_iter()
        .map(|(address, count)| (g_pow(address as usize).0, count))
        .collect();
    for address in indirect {
        let count = encoded.entry(address).or_default();
        profile[3][1].0 += u64::from(*count);
        profile[3][1].1 = profile[3][1].1.max(*count);
        *count += 1;
    }
    let old_sum: u64 = original
        .iter()
        .flat_map(|row| &row[..row.len() - 1])
        .map(|entry| entry.0)
        .sum();
    let new_sum: u64 = profile.iter().flatten().map(|entry| entry.0).sum();
    assert_eq!(
        old_sum, new_sum,
        "local-first routing changed the total memory exponent"
    );
    assert_eq!(
        new_sum,
        encoded
            .values()
            .map(|&count| u64::from(count) * u64::from(count - 1) / 2)
            .sum::<u64>()
    );
    let mut address = F64::ONE;
    for actual in execution.memory_read_counts() {
        if let Some(count) = encoded.remove(&address.0) {
            assert_eq!(
                *actual,
                g_pow(count as usize),
                "a reconstructed real chain has the wrong final count"
            );
        }
        if encoded.is_empty() {
            break;
        }
        address = primitives::field::mul_by_g(address);
    }
    assert!(
        encoded.is_empty(),
        "a reconstructed indirect address is outside native memory"
    );
    for (table, row) in profile.iter().enumerate() {
        println!("Private local-first count profile {table} (sum, max): {row:?}.");
    }
    println!(
        "This reconstructs legal count labels only; it does not emit a padded native proof or certify guest-wide resource bounds."
    );
}

fn check_opcode_budget(program: &Program, execution: &Execution) {
    let caps = [1 << 19, 1 << 19, 1 << 19, 1 << 19, 1 << 20, 1 << 16];
    for (table, (actual, cap)) in execution.base_counts.iter().zip(caps).enumerate() {
        assert!(
            *actual <= cap,
            "real table {table} exceeds the candidate's private row budget"
        );
    }
    let profile = execution.real_count_profile();
    let mut sites = execution.instruction_sites();
    for (table, rows) in execution.base_counts.iter().enumerate() {
        let mut visits = HashMap::<u32, u64>::new();
        for (pc, _) in sites.by_ref().take(*rows) {
            *visits.entry(pc).or_default() += 1;
        }
        let bytecode_sum: u64 = visits.values().map(|count| count * (count - 1) / 2).sum();
        let bytecode_max = visits.values().max().copied().unwrap_or(1) - 1;
        assert_eq!(*profile[table].last().unwrap(), (bytecode_sum, bytecode_max as u32));
        println!(
            "Private real count profile {table} (sum, max; bytecode last): {:?}.",
            profile[table]
        );
    }
    assert!(sites.next().is_none());
    local_count_profile(program, execution, &profile);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_digit_membership_rejects_nonroots() {
        let source = format!(
            "{LOCAL_DIGIT_CHECK}\ndef main():\n    digit = hint_witness(\"digit\")\n    zk_digit_check(digit)\n    return\n"
        );
        let mut program = compile(&lean_compiler::parse(&source).unwrap());
        for digit in 0..8 {
            program.set_witness("digit", vec![vec![F192::from(g_pow(digit))]]);
            let execution = program.execute([F192::ZERO; 2]);
            assert!(execution.unconstrained_reads.is_empty());
            assert_eq!(execution.base_counts[3], 0);
        }
        for value in [
            F192::ZERO,
            F192::from(g_pow(8)),
            F192::from(G.inv()),
            F192::new(0, 1, 0),
        ] {
            program.set_witness("digit", vec![vec![value]]);
            assert!(std::panic::catch_unwind(|| program.execute([F192::ZERO; 2])).is_err());
        }
    }
}
