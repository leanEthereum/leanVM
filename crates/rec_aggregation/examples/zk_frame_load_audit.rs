use std::collections::BTreeMap;

use lean_vm::cpu::{DerefMode, Op, Program};
use primitives::field::F192;

struct FunctionLoad<'a> {
    name: &'a str,
    compressions: usize,
    max_load: usize,
    max_cell: u32,
    local_extent: u32,
}

fn inspect(program: &Program) -> Vec<FunctionLoad<'_>> {
    let mut result = Vec::new();
    for (name, entry, length) in &program.fn_ranges {
        let mut loads = BTreeMap::<u32, usize>::new();
        let mut compressions = 0;
        let mut extent = 0;
        for pc in *entry..entry + length {
            if program
                .filler
                .iter()
                .any(|block| (block.pc..=block.pc + block.size).contains(&pc))
            {
                continue;
            }
            let cells = match program.prog[pc as usize] {
                Op::Blake2s { ins, cv, out, md } => {
                    let cells = vec![ins[0], ins[1], ins[2], ins[3], cv, cv + 1, out, out + 1, md];
                    compressions += 1;
                    for &cell in &cells {
                        *loads.entry(cell).or_default() += 1;
                    }
                    cells
                }
                Op::Xor { a, b, c } | Op::Mul { a, b, c } => vec![a, b, c],
                Op::Set { o, .. } => vec![o],
                Op::Deref { o1, o3, mode, .. } => {
                    if mode == DerefMode::Cell {
                        vec![o1, o3]
                    } else {
                        vec![o1]
                    }
                }
                Op::Jump { oc, od, of } => vec![oc, od, of],
            };
            extent = extent.max(cells.into_iter().max().unwrap() + 1);
        }
        if let Some((&max_cell, &max_load)) = loads.iter().max_by_key(|(cell, count)| (**count, **cell)) {
            result.push(FunctionLoad {
                name,
                compressions,
                max_load,
                max_cell,
                local_extent: extent,
            });
        }
    }
    result.sort_by_key(|row| std::cmp::Reverse((row.max_load, row.compressions, row.name)));
    result
}

fn main() {
    let alias_source = r#"
from snark_lib import *

def main():
    word = StackBuf(1)
    hint_witness(word, "word")
    digests = StackBuf(32)
    for i in unroll(0, 16):
        blake2s([word[0], word[0]], [word[0], word[0]], digests[2*i:2*i+2])
    return
"#;
    let mut alias =
        lean_compiler::compile_without_filler(&lean_compiler::parse(alias_source).expect("parse alias example"));
    let profile = inspect(&alias);
    assert_eq!(profile.len(), 1);
    assert_eq!((profile[0].compressions, profile[0].max_load), (16, 64));
    assert!(profile[0].local_extent <= 256);
    alias.set_witness("word", vec![vec![F192::ONE]]);
    let execution = alias.execute([F192::ZERO; 2]);
    assert_eq!(execution.base_counts[5], 16);
    assert!(execution.mem_used <= 256);
    assert!(execution.unconstrained_reads.is_empty());
    println!(
        "A native straight-line small-frame execution reads its aliased message cell 64 times in 16 compressions."
    );

    let arguments: Vec<_> = std::env::args().skip(1).collect();
    let supplied;
    let program = if arguments.is_empty() {
        rec_aggregation::aggregation::unified_guest()
    } else {
        assert_eq!(
            arguments.len(),
            1,
            "pass a zkDSL source path, or no argument for the aggregation guest"
        );
        let source = std::fs::read_to_string(&arguments[0]).expect("read source");
        supplied = lean_compiler::compile(&lean_compiler::parse(&source).expect("parse source"));
        &supplied
    };
    let functions = inspect(program);
    if arguments.is_empty() {
        assert!(
            functions.iter().all(|row| row.max_load <= 256),
            "the aggregation guest exceeds the current static BLAKE2s load budget"
        );
    }
    println!("Public bytecode log: {}", program.prog.len().trailing_zeros());
    println!("Functions containing BLAKE2s: {}", functions.len());
    println!(
        "Static per-cell load above 16: {}",
        functions.iter().filter(|row| row.max_load > 16).count()
    );
    println!(
        "Used local extent above 256: {}",
        functions.iter().filter(|row| row.local_extent > 256).count()
    );
    println!("name compressions max_load cell used_extent");
    for row in functions.iter().take(20) {
        println!(
            "{} {} {} {} {}",
            row.name, row.compressions, row.max_load, row.max_cell, row.local_extent
        );
    }
    println!(
        "Incidence bounds assume each instruction executes at most once per fresh frame; this does not certify arbitrary hinted traces or relocation."
    );
}
