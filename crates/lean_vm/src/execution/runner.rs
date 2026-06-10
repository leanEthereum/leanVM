//! VM execution runner

use backend::ArenaVec;

use crate::core::{DIMENSION, F, PUBLIC_INPUT_LEN};
use crate::diagnostics::{ExecutionMetadata, ExecutionResult, RunnerError};
use crate::execution::memory::MemoryAccess;
use crate::execution::{ExecutionHistory, Memory};
use crate::isa::Bytecode;
use crate::isa::hint::{DiagnosticState, Hint, HintState};
use crate::isa::instruction::{InstructionContext, InstructionCounts};
use crate::{
    ALL_TABLES, CodeAddress, HintExecutionContext, MAX_LOG_MEMORY_SIZE, MemOrConstant, N_TABLES, STARTING_PC, Table,
    TableTrace,
};
use backend::*;
use std::collections::{BTreeMap, BTreeSet};

use super::memory::SegmentMemory;

#[derive(Debug, Clone, Copy)]
pub struct ExecutionOptions {
    /// Include VM profiling metadata in the execution result.
    pub profiling: bool,
    /// Print a source-level stack trace to stderr when execution fails.
    pub stack_trace: bool,
}

impl ExecutionOptions {
    /// Preserve the legacy boolean profiler API while allowing `LEANVM_STACK_TRACE=0`
    /// to disable stack traces without changing callers.
    pub fn from_profiling(profiling: bool) -> Self {
        Self {
            profiling,
            stack_trace: stack_trace_enabled_from_env(true),
        }
    }
}

impl Default for ExecutionOptions {
    fn default() -> Self {
        Self {
            profiling: false,
            stack_trace: true,
        }
    }
}

struct ExecutionFailure {
    err: RunnerError,
    stack_trace: Option<String>,
}

impl ExecutionFailure {
    fn new<M: MemoryAccess>(
        bytecode: &Bytecode,
        memory: &M,
        pc: CodeAddress,
        fp: usize,
        err: RunnerError,
        stack_trace: bool,
    ) -> Self {
        let stack_trace = stack_trace.then(|| crate::diagnostics::pretty_stack_trace(bytecode, pc, fp, memory, &err));
        Self { err, stack_trace }
    }
}

fn stack_trace_enabled_from_env(default: bool) -> bool {
    match std::env::var("LEANVM_STACK_TRACE") {
        Ok(value) => match value.trim().to_ascii_lowercase().as_str() {
            "0" | "false" | "off" | "no" => false,
            "1" | "true" | "on" | "yes" => true,
            _ => default,
        },
        Err(_) => default,
    }
}

#[derive(Debug, Default)]
pub struct ExecutionWitness {
    /// Length of the program's "preamble memory" — a region between public
    /// memory and runtime memory that the runner leaves unset, that is filled
    /// manually by the program at startup.
    pub preamble_memory_len: usize,
    pub hints: Hints,
    /// testing purpose
    pub min_table_log_n_rows: BTreeMap<Table, usize>,
}

#[derive(Debug, Default)]
pub struct HintData {
    pub name: &'static str,
    pub entries: ArenaVec<ArenaVec<F>>,
}

#[derive(Debug, Default)]
pub struct Hints(Vec<HintData>);

impl Hints {
    pub fn insert(&mut self, bytecode: &Bytecode, name: &'static str, entries: ArenaVec<ArenaVec<F>>) {
        let slot = bytecode.hint_slot(name);
        if slot >= self.0.len() {
            self.0.resize_with(slot + 1, HintData::default);
        }
        self.0[slot] = HintData { name, entries };
    }

    pub fn entries(&self, slot: usize) -> &[ArenaVec<F>] {
        self.0.get(slot).map_or(&[], |h| &h.entries)
    }

    pub fn name(&self, slot: usize) -> &str {
        self.0.get(slot).map_or("", |h| h.name)
    }
}

pub fn try_execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    profiling: bool,
) -> Result<ExecutionResult, RunnerError> {
    try_execute_bytecode_with_options(
        bytecode,
        public_input,
        witness,
        ExecutionOptions::from_profiling(profiling),
    )
}

pub fn try_execute_bytecode_with_options(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    options: ExecutionOptions,
) -> Result<ExecutionResult, RunnerError> {
    let mut std_out = String::new();
    let mut instruction_history = ExecutionHistory::new();
    execute_bytecode_helper(
        bytecode,
        public_input,
        witness,
        &mut std_out,
        &mut instruction_history,
        options,
    )
    .map_err(|failure| {
        if let Some(stack_trace) = failure.stack_trace {
            eprintln!("\n{stack_trace}");
        }
        if !std_out.is_empty() {
            eprintln!("╔══════════════════════════════════════════════════════════════╗");
            eprintln!("║                         STD-OUT                              ║");
            eprintln!("╚══════════════════════════════════════════════════════════════╝\n");
            eprint!("{std_out}");
        }
        failure.err
    })
}

pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    profiling: bool,
) -> ExecutionResult {
    try_execute_bytecode(bytecode, public_input, witness, profiling)
        .unwrap_or_else(|err| panic!("Error during bytecode execution: {err}"))
}

struct Trace {
    pcs: ArenaVec<usize>,
    fps: ArenaVec<usize>,
    tables: BTreeMap<Table, TableTrace>,
    counts: InstructionCounts,
    pending_deref_hints: Vec<(usize, usize)>, // (target_addr, src_addr) constraints to resolve at end
}

impl Trace {
    fn new() -> Self {
        Self {
            pcs: ArenaVec::new(),
            fps: ArenaVec::new(),
            tables: BTreeMap::from_iter((0..N_TABLES).map(|i| (ALL_TABLES[i], TableTrace::new(&ALL_TABLES[i])))),
            counts: InstructionCounts::default(),
            pending_deref_hints: Vec::new(),
        }
    }

    fn merge(&mut self, other: Self) {
        self.pcs.extend_from_slice(&other.pcs);
        self.fps.extend_from_slice(&other.fps);
        self.counts += other.counts;
        self.pending_deref_hints.extend(other.pending_deref_hints);
        for (table, other_t) in other.tables {
            let mine = self.tables.get_mut(&table).unwrap();
            for (col, new_data) in mine.columns.iter_mut().zip(&other_t.columns) {
                col.extend_from_slice(new_data);
            }
        }
    }
}

enum LoopExit {
    Halted,
    LoopBack,
    ParallelBatch(ParallelBatchInfo),
}

struct ParallelBatchInfo {
    batch_pc: usize,
    batch_fp: usize,
    frame_size: usize,
    n_args: usize,
    end_value: MemOrConstant,
    /// Per-name cursor indices at the moment iteration 0 started consuming
    /// hints. Diffed against the post-iteration-0 state to learn per-name
    /// consumption.
    hint_indices_at_start: Vec<usize>,
}

struct ParallelSegmentFailure {
    segment_id: usize,
    pc: CodeAddress,
    fp: usize,
    err: RunnerError,
}

#[allow(clippy::too_many_arguments)]
fn run_loop<M: MemoryAccess>(
    bytecode: &Bytecode,
    memory: &mut M,
    trace: &mut Trace,
    pc: &mut usize,
    fp: &mut usize,
    ap: &mut usize,
    hints: &mut HintState<'_>,
    hint_data: &Hints,
    stop_pc: Option<usize>,
) -> Result<LoopExit, RunnerError> {
    let mut parallel_batch: Option<ParallelBatchInfo> = None;

    loop {
        if *pc == bytecode.ending_pc() {
            return Ok(LoopExit::Halted);
        }
        if *pc >= bytecode.size() {
            return Err(RunnerError::PCOutOfBounds);
        }
        trace.pcs.push(*pc);
        trace.fps.push(*fp);
        if let Some(diag) = &mut hints.diagnostics {
            *diag.cpu_cycles_before_new_line += 1;
        }

        let entry = &bytecode.code()[*pc];

        for hint in entry.hints.iter() {
            if let Hint::ParallelBatchStart { n_args, end_value } = hint {
                if parallel_batch.is_none() {
                    parallel_batch = Some(ParallelBatchInfo {
                        batch_pc: *pc,
                        batch_fp: *fp,
                        frame_size: *ap - *fp,
                        n_args: *n_args,
                        end_value: *end_value,
                        hint_indices_at_start: hints.indices.to_vec(),
                    });
                }
                continue;
            }
            let mut ctx = HintExecutionContext {
                hints,
                hint_data,
                memory,
                fp: *fp,
                ap,
                cpu_cycles: trace.pcs.len(),
                pending_deref_hints: &mut trace.pending_deref_hints,
            };
            hint.execute_hint(&mut ctx)?;
        }

        let instruction = &entry.instruction;
        let mut ctx = InstructionContext {
            memory,
            fp,
            pc,
            pcs: &trace.pcs,
            traces: &mut trace.tables,
            counts: &mut trace.counts,
        };
        instruction.execute_instruction(&mut ctx)?;

        if stop_pc == Some(*pc) {
            // we are at the end of a parallel batch segment
            return Ok(LoopExit::LoopBack);
        }

        // Parallel batch ready: we have run the first iteration, so we know the memory usage and
        // can spawn parallel execution for the remaining iterations.
        if let Some(ref batch) = parallel_batch
            && *pc == batch.batch_pc
        {
            return Ok(LoopExit::ParallelBatch(parallel_batch.take().unwrap()));
        }
    }
}

/// Resolve pending deref hints in correct order
///
/// Each constraint has form: memory[target_addr] = memory[memory[src_addr]]
/// Order matters because some src addresses might point to targets of other hints.
/// We iteratively resolve constraints until no more progress, then fill remaining with 0.
fn resolve_deref_hints(memory: &mut Memory, pending: &[(usize, usize)]) -> Result<(), RunnerError> {
    let mut resolved: BTreeSet<usize> = BTreeSet::new();
    loop {
        let mut made_progress = false;
        for &(target_addr, src_addr) in pending {
            if resolved.contains(&target_addr) {
                continue;
            }
            let addr = memory
                .get(src_addr)
                .map_err(|_| RunnerError::ImpossibleDerefResolution)?;
            let Some(value) = memory.0.get(addr.to_usize()).copied().flatten() else {
                continue;
            };
            memory.set(target_addr, value)?;
            resolved.insert(target_addr);
            made_progress = true;
        }
        if !made_progress {
            break;
        }
    }
    // Fill any remaining unresolved targets with 0 (this can happen in case of cycles)
    for &(target_addr, _src_addr) in pending {
        if !resolved.contains(&target_addr) {
            memory.set(target_addr, F::ZERO)?;
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    options: ExecutionOptions,
) -> Result<ExecutionResult, ExecutionFailure> {
    let n_slots = bytecode.n_hint_slots();
    let hint_data = &witness.hints;
    let mut hint_indices = vec![0usize; n_slots];

    let public_memory = public_input.to_vec();
    let mut memory = Memory::new(public_memory);
    let mut fp = PUBLIC_INPUT_LEN + witness.preamble_memory_len;
    fp = fp.next_multiple_of(DIMENSION);
    let initial_ap = fp + bytecode.starting_frame_memory();
    let mut pc = STARTING_PC;
    let mut ap = initial_ap;
    let mut trace = Trace::new();
    let mut cpu_cycles_before_new_line = 0;
    let mut last_checkpoint_cpu_cycles = 0;
    let mut checkpoint_ap = initial_ap;

    loop {
        let mut hints = HintState {
            diagnostics: Some(DiagnosticState {
                std_out,
                instruction_history,
                cpu_cycles_before_new_line: &mut cpu_cycles_before_new_line,
                last_checkpoint_cpu_cycles: &mut last_checkpoint_cpu_cycles,
                checkpoint_ap: &mut checkpoint_ap,
            }),
            indices: &mut hint_indices,
        };
        match run_loop(
            bytecode,
            &mut memory,
            &mut trace,
            &mut pc,
            &mut fp,
            &mut ap,
            &mut hints,
            hint_data,
            None,
        )
        .map_err(|e| ExecutionFailure::new(bytecode, &memory, pc, fp, e, options.stack_trace))?
        {
            LoopExit::Halted => break,
            LoopExit::ParallelBatch(batch) => {
                handle_parallel_batch(
                    bytecode,
                    &mut memory,
                    &mut trace,
                    &mut hints,
                    hint_data,
                    &mut pc,
                    &mut fp,
                    &mut ap,
                    &batch,
                    options.stack_trace,
                )?;
            }
            LoopExit::LoopBack => unreachable!("main loop has no stop_pc"),
        }
    }

    resolve_deref_hints(&mut memory, &trace.pending_deref_hints)
        .map_err(|e| ExecutionFailure::new(bytecode, &memory, pc, fp, e, options.stack_trace))?;
    assert_eq!(pc, bytecode.ending_pc());
    for (slot, hint) in hint_data.0.iter().enumerate() {
        if hint_indices[slot] != hint.entries.len() {
            return Err(ExecutionFailure::new(
                bytecode,
                &memory,
                pc,
                fp,
                RunnerError::InvalidHintWitness(format!(
                    "not all entries of named hint '{}' were consumed ({} of {} used)",
                    hint.name,
                    hint_indices[slot],
                    hint.entries.len(),
                )),
                options.stack_trace,
            ));
        }
    }
    trace.pcs.push(pc);
    trace.fps.push(fp);

    let no_vec_runtime_memory = ap - initial_ap;
    let profiling_report = if options.profiling {
        Some(crate::diagnostics::profiling_report(
            instruction_history,
            &bytecode.debug_info().function_locations,
        ))
    } else {
        None
    };
    let runtime_memory_size = memory.0.len() - PUBLIC_INPUT_LEN - witness.preamble_memory_len;
    let used_memory_cells = parallel::map_reduce(
        memory.0.len(),
        || 0usize,
        |i| usize::from(memory.0[i].is_some()),
        |a, b| a + b,
    );
    let metadata = ExecutionMetadata {
        cycles: trace.pcs.len(),
        memory: memory.0.len(),
        n_poseidons: trace.tables[&Table::poseidon16()].columns[0].len(),
        n_extension_ops: trace.tables[&Table::extension_op()].columns[0].len(),
        bytecode_size: bytecode.size(),
        public_input_size: PUBLIC_INPUT_LEN,
        runtime_memory: runtime_memory_size,
        memory_usage_percent: used_memory_cells as f64 / memory.0.len() as f64 * 100.0,
        stdout: std::mem::take(std_out),
        profiling_report,
    };
    Ok(ExecutionResult {
        runtime_memory_size: no_vec_runtime_memory,
        memory,
        pcs: trace.pcs,
        fps: trace.fps,
        traces: trace.tables,
        metadata,
    })
}

fn write_call_frame(
    memory: &mut Memory,
    fp: usize,
    return_pc: usize,
    saved_fp: usize,
    iterator_val: usize,
    args: &[F],
) -> Result<(), RunnerError> {
    memory.set(fp, F::from_usize(return_pc))?;
    memory.set(fp + 1, F::from_usize(saved_fp))?;
    memory.set(fp + 2, F::from_usize(iterator_val))?;
    for (j, &v) in args.iter().enumerate().skip(1) {
        memory.set(fp + 2 + j, v)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn handle_parallel_batch(
    bytecode: &Bytecode,
    memory: &mut Memory,
    trace: &mut Trace,
    hints: &mut HintState<'_>,
    hint_data: &Hints,
    pc: &mut usize,
    fp: &mut usize,
    ap: &mut usize,
    batch: &ParallelBatchInfo,
    stack_trace: bool,
) -> Result<(), ExecutionFailure> {
    let start_value = memory
        .get(batch.batch_fp + 2)
        .map_err(|e| ExecutionFailure::new(bytecode, memory, *pc, *fp, e, stack_trace))?
        .to_usize();
    let end_value = batch
        .end_value
        .read_value(memory, batch.batch_fp)
        .map_err(|e| ExecutionFailure::new(bytecode, memory, *pc, *fp, e, stack_trace))?
        .to_usize();
    let n_iters = end_value.saturating_sub(start_value);
    if n_iters <= 1 {
        return Ok(());
    }

    let stride = *fp - batch.batch_fp;
    let return_pc = memory
        .get(*fp)
        .map_err(|e| ExecutionFailure::new(bytecode, memory, *pc, *fp, e, stack_trace))?
        .to_usize();
    let saved_fp = memory
        .get(*fp + 1)
        .map_err(|e| ExecutionFailure::new(bytecode, memory, *pc, *fp, e, stack_trace))?
        .to_usize();
    let args: Vec<F> = (0..batch.n_args)
        .map(|i| {
            memory
                .get(batch.batch_fp + 2 + i)
                .map_err(|e| ExecutionFailure::new(bytecode, memory, *pc, *fp, e, stack_trace))
        })
        .collect::<Result<_, _>>()?;

    let named_per_iter: Vec<usize> = hints
        .indices
        .iter()
        .enumerate()
        .map(|(slot, &index)| index - batch.hint_indices_at_start[slot])
        .collect();
    let base_indices: Vec<usize> = hints.indices.to_vec();

    for i in 1..=n_iters {
        let iter_val = if i < n_iters { start_value + i } else { end_value };
        write_call_frame(
            memory,
            batch.batch_fp + i * stride,
            return_pc,
            saved_fp,
            iter_val,
            &args,
        )
        .map_err(|e| ExecutionFailure::new(bytecode, memory, *pc, *fp, e, stack_trace))?;
    }

    let max_addr = batch.batch_fp + (n_iters + 1) * stride;
    if max_addr > 1 << MAX_LOG_MEMORY_SIZE {
        return Err(ExecutionFailure::new(
            bytecode,
            memory,
            *pc,
            *fp,
            RunnerError::OutOfMemory,
            stack_trace,
        ));
    }
    if max_addr > memory.0.len() {
        memory.0.resize(max_addr, None);
    }

    let n_par = n_iters - 1;

    // Split memory into a shared read-only region and per-segment mutable slices.
    // Iteration 0 has already been executed and wrote into [batch_fp, batch_fp + stride).
    // Iterations 1..n_par each get their own [batch_fp + (i+1)*stride, batch_fp + (i+2)*stride).
    let split_at = batch.batch_fp + stride; // end of iteration 0's frame
    let (left, right) = memory.0.split_at_mut(split_at);
    let shared: &[Option<F>] = &*left;
    let mut segment_slices: Vec<&mut [Option<F>]> = right.chunks_mut(stride).take(n_par).collect();

    type SegResult = Result<(Trace, Vec<(usize, F)>), ParallelSegmentFailure>;

    let seg_info: Vec<(parallel::SendPtr<Option<F>>, usize)> = segment_slices
        .iter_mut()
        .map(|s| (parallel::SendPtr(s.as_mut_ptr()), s.len()))
        .collect();
    drop(segment_slices);

    let results: Vec<SegResult> = parallel::par_map_collect(n_par, |i| {
        let (seg_ptr, seg_len) = &seg_info[i];
        let seg_slice: &mut [Option<F>] = unsafe { std::slice::from_raw_parts_mut(seg_ptr.0, *seg_len) };
        let seg_start = split_at + i * stride;
        let mut seg_mem = SegmentMemory::new(shared, seg_slice, seg_start);
        let fp_i = batch.batch_fp + (i + 1) * stride;
        let mut seg_trace = Trace::new();
        let mut seg_pc = batch.batch_pc;
        let mut seg_fp = fp_i;
        let mut seg_ap = fp_i + batch.frame_size;
        let mut seg_indices = base_indices.clone();
        for (slot, index) in seg_indices.iter_mut().enumerate() {
            *index += i * named_per_iter[slot];
        }
        let mut seg_hints = HintState {
            diagnostics: None,
            indices: &mut seg_indices,
        };
        run_loop(
            bytecode,
            &mut seg_mem,
            &mut seg_trace,
            &mut seg_pc,
            &mut seg_fp,
            &mut seg_ap,
            &mut seg_hints,
            hint_data,
            Some(batch.batch_pc),
        )
        .map_err(|err| ParallelSegmentFailure {
            segment_id: i + 1,
            pc: seg_pc,
            fp: seg_fp,
            err,
        })?;
        for slot in 0..seg_indices.len() {
            let delta = named_per_iter[slot];
            // Before `run_loop` this segment was at `base_indices[slot] + i*delta`.
            let consumed = seg_indices[slot] - (base_indices[slot] + i * delta);
            if consumed != delta {
                let name = hint_data.name(slot);
                return Err(ParallelSegmentFailure {
                    segment_id: i + 1,
                    pc: seg_pc,
                    fp: seg_fp,
                    err: RunnerError::InvalidHintWitness(format!(
                        "hint '{name}' consumed {consumed} entries in a parallel iteration but {delta} in iteration 0; parallel iterations must consume hints uniformly"
                    )),
                });
            }
        }
        let deferred = seg_mem.into_deferred_writes();
        Ok((seg_trace, deferred))
    });

    for result in results {
        let (seg_trace, deferred) = result.map_err(|failure| {
            ExecutionFailure::new(
                bytecode,
                memory,
                failure.pc,
                failure.fp,
                RunnerError::ParallelSegmentFailed(failure.segment_id, Box::new(failure.err)),
                stack_trace,
            )
        })?;
        trace.merge(seg_trace);
        for (addr, val) in deferred {
            memory
                .set(addr, val)
                .map_err(|e| ExecutionFailure::new(bytecode, memory, *pc, *fp, e, stack_trace))?;
        }
    }

    for (slot, &delta) in named_per_iter.iter().enumerate() {
        hints.indices[slot] += n_par * delta;
    }

    *pc = batch.batch_pc;
    *fp = batch.batch_fp + n_iters * stride;
    *ap = *fp + batch.frame_size;
    Ok(())
}
