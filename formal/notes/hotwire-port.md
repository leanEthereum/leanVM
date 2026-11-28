# Porting formal/ to Hotwire

The link (`crates/verifier/src/link.rs`) replaced the bus and the table sumcheck. The proofs of the protocol before it are at tag `formal-bus-archive`. This note keeps what the port decided, what must change together, what it found and what is open. Files are under `formal/lean_vm/LeanVM/` unless said otherwise; the full working log is in this file's history.

## Summary

**Proved**, in `Statement.Theorems`, by `LeanVM.theorems_hold` (`lean_vm/LeanVM.lean`) at the extractor `LeanVM.Cost.compiledKnowledgeExtractor` and the decoder `LeanVM.Cost.compiledGuestWitnessDecoder`, on Lean's three axioms. `LeanVM.corollaries_hold` and `LeanVM.aggregateSound_holds` take no hypothesis.

| field | theorem | file | section |
| ----- | ------- | ---- | ------- |
| `leanVmKnowledgeSoundness` | `LeanVM.knowledgeSoundness_compiled` | `Protocol/KnowledgeSoundnessCompiled.lean` | M2-KS |
| `leanVmCompleteness` | `LeanVM.completeness_holds` | `Prover/Complete.lean` | M2-C |
| `guestKnowledgeSoundness` | `LeanVM.Cost.guestKnowledgeSoundness_holds` | `Cost/GuestKnowledgeHolds.lean` | M2-guest |
| `statementDigestBinds` | `LeanVM.Guest.Binding.digest_binds` | `Guest/Binding.lean` | |
| `guestExecutionComplete` | `LeanVM.Guest.Complete.guestExecutionComplete_of_routed` | `Guest/Complete/Holds.lean` | M2-guest complete |
| `batchingSound` | `LeanVM.Guest.Batch.batch_sound_holds` | `Guest/Batch/Rpm.lean` | M2-F |
| leanXMSS, leanSPHINCS, LeanDA | their projects' end theorems | `lean_xmss/`, `lean_sphincs/`, `lean_da/` | unchanged by the port |

**Statement changes**, each breaking (`!`):

- `Theorems` takes the extractor and decoder programs and holds every field; `OpenStatements` is deleted.
- `leanVmKnowledgeExtractorSizeBound` is `23975`: the compiled extractor's `23855` (`asProgram_size_le`) and a slack of `120` (the final formal review).
- `guestWitnessDecoderSizeBound` is `257906`: the decoder's `257768` (pinned in `tests/LeanVMTests/Cost/DecoderSize.lean`) and a slack of `138`.
- `NodeWitness.memoryBudget` is at counted coefficients: `66` a claim, `457265` a child, `41297` fixed (M2-guest complete, the budget's verdict).
- `LeanVM.Completeness` assumes `Execution.pointerWidth ≤ maxPointerWidth` and `Execution.KeccakBlocksInWindows`, which `GuestExecutionComplete` concludes. `Execution.committedSize` is the whole-column stack's size, so `≤ 2^30` is the prover's `MAX_STACKED_LOG` cap (`Execution.committedSize_le_iff_stackLog_le`, `Facts/Stack.lean`).
- The deferring verifier's theorem is weaker than the bus era's. A fresh claim's values reach the verifier only through the link's terminal check, a linear form, so the verifier accepts a true claim and possibly other claims at the same point. `freshClaim_holds_of_leanVmVerifier` has no deterministic Hotwire form, and `statement.tex`'s honest-children remark says so (`Protocol/Verifier/{Deferred, Defers}.lean`, `LeanVM.leanVmVerifier_iff_verifyDeferred`).

**Findings.** No soundness bug in the Rust verifier or the guest. Found and fixed:

- The memory budget's child coefficient was false: a child whose opening draws a zero challenge takes the slow residual sum (the budget's verdict).
- The Rust executors covered `DEREF`'s third cell in pc and fp mode only by bounds-checking `o3`, so a far `o3` gave a smaller memory and a prover panic. Both trees now cover it (`deref_covers_its_third_cell_in_every_mode`, `bench/tests/identical_proofs.rs`); compiled programs have `o3 = 0` there.
- `candidate`'s step count must be `firstFinal`, not the cycle count (M2-A).
- The lite extractor priced a packed read by the whole stream (M2-P).
- The extractor's size bound had a slack of `1525` (the final formal review).
- Proof-side statements that were false or vacuous, each restated: `GuestRestAt.framesWithin`, `CallAtA`'s unbounded end, `OpenStackedCompleteA`'s capacity and pops, `LqA`'s `λ ≠ 0`, `HandFact`, the floors `k` (M2-guest complete).

**Open.**

- A kernel replay of the end theorems' closure in the gate (`tools/escape-scan.py` cites it; the final formal review).
- The memory budget covers a 16-child node only up to `142722` claims in its children's lists, `(2^24 − 41297 − 16·457265)/66`, while the Rust aggregates about twice that within `2^24` words (`statement.tex`, "What is not proved").
- `encodeValue_decoded_injective` is archived, not restored: injectivity is read off the encodings.

## What must change together

Beyond `formal/AGENTS.md`'s "Changing the spec":

- **A guest change that leaves a function off the core route** stops `frame_gen.py`, which names it; were it left off, the `rfl` in `theorems_hold` (`CoreMode.offSigs = []`) would fail (The core route).
- **`verify_sub` or a callee's body.** `regen-guest.sh` regenerates the certificates, walks and windows, but much is written against fixed statement and value numbers of the core IR: the soundness templates of `Guest/B1/VerifySub/` (`vsSeedT`, `vsOodT`, `vsLkVanishT`, `vsOpenT`), `Guest/B1/Link/Arith/IR.lean`'s `linkSec`, the Keccak layer's `layer_body264`, `layer_body265`, `IRReads`, the `VsC` proofs (`.n 42`, `w 3991`), and the core route's rule files and `CoreMode/Fn/<f>/` (in `verify_sub`, `120`, `408`, `409`, `1076`, `2920`, `4009`). A change fails their kernel checks (`stmtsEqb`), and they are rewritten from the new core IR; `scripts/guest-changes` lists them, and `val%` (`scripts/val-names`) is the stable form.
- **`main`'s or `aggregate_claims`' body** renumbers `mOrc`, `MainCounts.bufs`, `MainEval.lean`'s `chk_*` cut points, `Agg/Hon.lean`'s `aOrc`, `Agg/Layout.lean`'s `aBufs` and the windows `aW0` to `aW10`. Regenerate `MainWinData.lean`, then update them by hand.
- **The deployed specializations** the proofs quantify over follow the constants: `open_stacked`'s `15` arms (stack logs `16` to `30`, rates `1` to `4`), the link's widths `19` to `24`, `column_selector`'s `155`. `open_stacked`'s per-arm files (`Os/CHonStatic{0,1,2,3}.lean`, `CHonNames*`, `CHonAlloc*`) and theorems (`osCallsOk_*`, `qx_*`) are committed with no generator, so a change of `LIG_N_LOG_SIZES` or of the rates rewrites them. A constant the guest reads is `guest_const% NAME` in the Lean (`childStreamCap := guest_const% STREAM_CAP`).
- **Nonzero `ROUND2_GRIND_BITS` or `ROUND3_GRIND_BITS`** make `layer_rounds_placed`, `plain60_placed` and `plain41_placed` read the window tables.
- **The verifier's transcript** (a phase's reads, a packed message): `leanVmStream` (`Wire/HonestShape.lean`), `leanVmQueryBound_eq`, `PackedPos` (every packed read and draw has `n ≥ 1`, `Protocol/Verifier/PackedPos.lean`), the grinds' bound (`Protocol/Verifier/Grinds.lean`), the costs (`Protocol/Verifier/Cost.lean`, `Prover/Complete/Cost*.lean`), the lite skeleton (`Protocol/EndToEnd/Sound/Skel*`), and `Protocol/Link/Skeleton.lean`, whose `linkSkeleton` copies `verifyLink`'s `let`s (`verifyLink_eq_linkSkeleton` by `rfl`).
- **The tables** (`tables()`, links, constraints): the decided facts `lkt_*` (`Relation/Link/GroupLinksTables.lean`), `tables_ok` (`Relation/Link/RowDeg.lean`), `tableOK_all` (`Prover/Complete/Link/TailRowFacts.lean`), and the compiled extractor's literals (`keccakInLit`, `globalColumnBasesLit`, `stackLit`, in `Cost/AS/Top.lean`, each a `decide +kernel` rewrite).
- **The compiled chain** (extractor or decoder): an on-demand function is named by its index (`Auto.<head>.c<i>`), so a change early in the chain renames every later one; `scripts/renumber-chain` renames the bounds. The decoder's chain extends the extractor's (`Cost/Decoder/Lib.lean` imports `Cost/AS/Top.lean`), and the decoder's program holds `.position 0` at the extractor's indices it does not call (`ofListPos`, `Cost/DecoderProgram.lean`).
- **The guest's memory per item**: `regen-guest.sh`'s `memory` and `complete` steps regenerate the counts; then recheck by hand `Budget/HandCount.lean` (`iterSum`, `iterZero`, `Coefs.checker`, `Coefs.checkerZero`), `Budget/CycleCount.lean`, `Coefs.deployed` (`Budget/Count.lean`), `NodeWitness.memoryBudget`, `statement.tex`'s budget paragraph, and `memory_budget` in `crates/aggregation/src/tests.rs` (its ignored test `guest_memory_within_its_budget`).
- **The executor** (`cpu/execute.rs`): `Statement/Prover/Execute.lean`, compared on runs and faults with both Rust trees (`scripts/executor-faults`, `leanvm-execute`); the advice parser (`Prover/Advice.lean`) reads `leanvm-advice 2` (and `1`).
- **A family of the core route added or removed**: its soundness is joined by hand, in the registry's order, in `EndExecOwnA.fams_okA`, `EndExecCoreGhostD.stLoops_okA`, `EndExecResNzD.nzs_okA`, `EndExecExpW.expFacts_okW` or `dimFacts_okW`. A new caller of a function whose facts are carried down (`column_selector/CsChain`, `verify_sub/VkCarry`, `hint_stream/HsCarry`, `keccak_layer/KlCarry`) breaks `Res.termCallers_all` (`termcall.py`).

## H4

`Protocol/Link/` proves `verify_link`'s two chained sum-checks sound in the sample model (`Sample.lean`: `win W P`, challenges uniform, each prover message the supremum over its values, grinds and commitments free: interactive soundness against an unbounded adaptive prover). `verifyLink_sound` (`Sound.lean`) bounds `win` by `(max(D_A, D_B + 2W) + 1 + m·(rc − 1) + m_Q·(cc − 1))/|E|` from hypotheses that are the link's arithmetization:

- `hidx`: the index summand's partial sums, degree `2`;
- `hrow`: the row summand's, totalling `idx + Σ_i fresh_i·B_i`;
- `htail`: the terminal value is the row summand at `(χ, q*)`;
- `hA`: the not-one-hot count (`card_mirrorTables_le`);
- `hB`: the failing-link count (`card_linkError_le`, `D_B = max(W + 1, m + 3 + BYTECODE_SLOT_BITS)`, the numerator `verify_link` grinds for).

Against the paper's theorem it adds one `1/|E|`: `verify_link` shares the row rounds with `JUMP`'s constraint sum-check, and failing `JUMP` constraints can cancel a false index claim. It has no `ε_chunk`: the bit-slices are an output claim that ring switching's soundness reads. The end proof does not instantiate `verifyLink_sound`: M2-A discharges the same facts round by round, reusing `Skeleton.lean` and `Sumcheck.lean`.

## M2-A

The link's relation is `LinkRel` (`PointersOneHot`, `StateHolds`, `MemoryHolds`, `ProgramHolds`, `ConstraintsHold`) and its round-by-round specification `linkSpecOf`, in `Protocol/Relation/Link.lean` and `Relation/Link/`, ending in `linkIface := linkIfaceOfLinks card_notDoom_of_links` (`GroupLinksEnd.lean`). `thm:link`'s three cases are a pointer not one-hot (`card_notDoom_of_not_oneHot`), a link failing (`card_notDoom_of_links`, through a nonzero draw of `groupF`, `exists_groupF_ne`, by the state, program and memory cases), and every link holding with a `JUMP` constraint failing (`card_notDoom_of_not_constraints`, `GroupJump.lean`).

- The drawn group (`θ_0` and the packed draw) is one group under `grindingBits(linkGroupError)`, `linkGroupError = max(m + 3 + BYTECODE_SLOT_BITS, W + 1)`, exactly `verify_link`'s grind. The not-one-hot case uses the per-drawn-variable count `m + 3`, not H4's joint `m + 3 + 2·w_max`, which exceeds the grind when `2·w_max > BYTECODE_SLOT_BITS`.
- Doom is a disjunction, so a round's error is the larger of its causes, not the sum. The Keccak defect rides each round as a carried fact (`KeccakCarry`).
- `candidate` (`Link/Rel.lean`) runs `firstFinal` steps, to the first executed row in the final state. The state link accepts a chain that passes through `(pcFinal, 1)` before `T` and returns to it (a taken `JUMP` to the final state, then the prover's self-loop rows), while leanISA's `run` halts at the first visit. This is not a soundness bug: the prefix is a valid execution.
- `VerifierProgram.Returns`' packed cases carry the list's length (`Verifier/PackedLength.lean`), which `LinkShape` needs. The wire's cost calculus quantifies over every list, as `Script.alongside` does, and uses `ReturnsAny`.
- The index summand has degree at most `2` per index variable whether or not the pointers are one-hot (`Good` is `True`). The row summand's degree bound holds for every chunk count `d` (`Link/RowDeg.lean`).

## M2-KS

`LeanVM.knowledgeSoundness_compiled` is `knowledgeSoundness_of linkIface extractorOf_extractorProgram transcriptExtractorL_of` (`Protocol/KnowledgeSoundness.lean`). It composes the agreement-set extractor's random-oracle bound (M2-X), its transfer to the random permutation (M2-E), the link's interface (M2-A), WHIR, ring switching and the Keccak GKR as phase interfaces (M2-W), and the compiled extractor (M2-P). The phases' vocabulary is `Protocol/Relation/{Stack, Iface}.lean` (`StackRel := LinkRel ∧ PubRel ∧ KeccakRel`); the round-by-round certificate is `Relation/Whole.lean`'s `leanVmCert` and `Relation/Statements.lean`'s `anyCert`.

- **M2-W.** WHIR's soundness is the archive's level loop. What changed is that ring switching draws the batching challenge `λ` in its packed message, so `verifyStackedOpeningG` and `ringOpenSpec` take it: the whole packed draw is one group under the `13`-bit grind, paid by the parameter row `lambda_row`. `KeccakIface.keccakSpec` takes `LinkShape`: `keccakValidity` reads each output lane's first claim (`find?`), so a duplicate or misplaced claim would otherwise escape the reduction.
- **M2-F.** A packed message is one event in the framework (`Ev.readPacked`, `Ev.samplePacked`, `avgPk`). The random-oracle decoder (`Rom/Decode.lean`) tells an untagged packed chunk from tagged scalars by the program's position (`Pos.rpk`, `Pos.spk`), which is why `RootOk` asks `PackedPos`. The `packed_pos` tactic applies its lemmas at reducible transparency and splits conditionals first; the Keccak reduction's blocks go step by step, since failed attempts on their terms exhaust the elaborator. The batching (`BatchingSound`, `Guest/Batch/`) draws `λ` and the column challenges as one group under a `3`-bit grind.
- **M2-X, M2-E.** `extractAS` (`Relation/ExtractorDef.lean`) replays the cut verifier, reads each root's word, runs the compiled descent (`descendTraceC`) and returns `candidate`, with no halting search. The compiled extractor is related to it by `hmono`, not equality: it replays without the checks, so it may return where `extractAS` fails, which no break can use.
- **M2-P.** The lite extractor's packed read checks the prefix it reads, `(s.stream.take n).length = n`: checking `n ≤ s.stream.length` costs the whole stream, which no budget bounds, so a padded proof would have broken `extractorOf_extractorProgram`. `extractL` binds `fwdIndex qs` once, or the compiler rebuilds it in every closure. `cost_calls` at a proof's top level cannot name a variable a tactic introduced; after `rcases` use `limbs_bound`.

## M2-C

The honest prover is the statement's own (`LeanVM.Prover.prove`: `witness?`, then `honestScript` against `leanVmVerifierProgram`), so completeness is proved of the script directly, with no specification strategy. `Wins` (`Prover/Complete/Wins.lean`) says a script plays the program whatever the challenges, and `runProof_of_wins`, `romComplete`, `rpmComplete` compile it. The link's four identities on the honest witness (`linkIndexIdentity_honest`, `rowIdentity_of`, `columnSplit_of`, `linkTailHolds_honest`, `Prover/Complete/Link/`) are the honest side of M2-A's `LinkArith`. `CostCalc`'s cases are conjunctions, never a bare `∀`: a `∀`-headed case makes the elaborator unfold the program.

## M2-guest

`guestKnowledgeSoundness_holds` is B2 (the compiled guest against its core IR, kernel-checked certificates, `Guest/EndSound.lean`), B1 (each function's core IR against its meaning, `Guest/B1/`), and `verify_sub`'s soundness assembled phase by phase (`B1/VerifySub/Phases.lean`, `subSoundW_of_phases`), at the compiled decoder (`Cost/Decoder*`).

- **Children** (`Guest/Child/`): an accepted child's stream is at most `leanVmStream` (`Wire/HonestRun.lean`'s `Wired` calculus), its stack log at least `minChildStackLog`, and its caps agree or its openings collide (`acceptableChildren_or_collide`). These hold on every bytecode.
- **The decoded proof** (`B1/VerifySub/Proof.lean`, `vsPiOf`) is the stream up to the cursor handed to `open_stacked`, then `open_stacked`'s words and openings. `open_stacked`'s returned cursor is unconstrained (`OpenOutW`): only the stream bound reads it.
- **Kernel cost.** A section of `verify_sub` is a template checked against a slice `(vsPre.drop a).take n` (`stmtsEqb`); searching the whole body for single statements (`membB`) is too heavy for the kernel. One `kernel_eq` across a whole table fold recursed too deep, so the link's arithmetic (`B1/Link/Arith/`, a reflected normalizer `Ex.norm`) chains three, and the forms' coefficients are read as literal limbs (`tablesL`). A grind then a packed draw is stated at a variable permutation (`runsTo_grindPacked`), so the kernel never unfolds Keccak-f.
- **The compiler's folding.** `verify_sub` passes `tabs = g_squares·g^WIN_TAB_AT` and the compiler folds the offset into each load, so inlined grinds are `gcInlineAt` with the offset as a parameter. `link_terminal`'s template is built from the statement's `Chunks.new`, so the guest's chunk tables are kernel-checked to be the verifier's.
- **B2's checker** gained a shift tag (a dispatch selector bounded through a `MUL` by `g^-d`, as `check_stack_terminal`'s `gmv·g^-16`), window `0` knowing the memory its precondition bounds, and an `if` joining through the segment one arm ends at (`passTo`). `Expand` drops a product by the compiler's cell for `1`, as the compiler does. `index_mle` has one proof, the link's (`Link.index_mle_holds`), which the Keccak family reuses.

## M2-guest complete

`GuestExecutionComplete` is `guestExecutionComplete_of_routed` (`Guest/Complete/Holds.lean`), applied in `LeanVM.lean` with `CoreMode.offSigs = []` by `rfl`. The chain:

1. `guestExecutionComplete_of_routed h` is `guestExecutionComplete_of_left ⟨off_of_routed h⟩`; `GuestLeft` holds only `off`.
2. `guestRest_of_left` (`Complete/Left.lean`) fills every field of `GuestRestAt alW 17 exA alignA true` from a proved lemma; the core route's is `route_alW`.
3. `guestExecutionComplete_of_rest` applies `guestExecutionComplete_of_open` at `Coefs.deployed`, whose coefficient fields hold by `deployed_above_checker` (`decide`) and `fits_deployed`.
4. Inside `_of_open` (`Complete/Open.lean`), on a node: `acceptableChildren_or_collide`; `vsComplete_of_calleesA` and `MainFromVsA`, which place `main` at the root; `refX_of_callAtA`, B2's reference run; `ref_of_open`, a `Ref` with `RefH` and `Ref.Ok`, its bounds from the checker's counts (`bounds_main`); then `ExecGaps.ofHintsAlloc`, `execute_ref` and `guestExecutionComplete_of_runsWithin`.

The references are `R := RefOf al`, the honest data `D := refD al`, a `Classical.epsilon` over `RefH`. Because `D` is a choice, whatever a field needs of the honest data is a field of `RefH` (`exact`: every computed hint exact on `rd0`; `extra`: the hint-only cells' values).

**The reduction.** `guestExecutionComplete_of_runsWithin` needs every covered node to run with `logMemorySize ≤ 24`, `stepCount < 2^24` and `committedSize ≤ 2^30`, or some child's openings to collide. Validity comes from `execute_sound`. The pointer width stays at most `24` because a valid run's table rows sum to its steps (`tableRows_sum`); the `KECCAK` windows come from `execute_keccakBlocksInWindows` (`Prover/ExecuteWindows.lean`). Memory and steps do not bound `q_keccak`'s `2^slot_bits` words per `KECCAK` row, so `committedSize_eq_sum` and `two_pow_height_le` (`Complete/Committed.lean`) bound the committed size by rows weighted by each table's columns.

### The budget's verdict

The memory budget (`NodeWitness.memoryBudget`, `Statement/LeanVmGuestCompleteness.lean`) uses proved coefficients: `66` per claim of the children's lists, `457265` per child, `1400` per raw leanXMSS signature, `7500` per raw leanSPHINCS signature, `131072` plus `122000` per row for a blob matrix, and `41297` fixed. The bus era's child coefficient, `310000`, was measured and was false. When a child's stacked opening draws a zero tail challenge (an outcome Keccak-256 can produce, which the deferring verifier accepts), every non-final level of `open_stacked` takes `level_residual_slow`'s slow sum `level_residual_sum`, about `84000` more words at stack `2^30`, rate `1`. A node of sixteen such children plus raw leanSPHINCS signatures fits `310000` but needs a memory of `2^25`, so `GuestExecutionComplete` was false as stated. The statement changed rather than exclude zero challenges: the coefficients are the static checker's count with the zero sum counted (`Coefs.checker`, `Budget/HandCount.lean`), and no hypothesis on challenges remains.

The checker is context-insensitive: it bounds each callee once over all its callers, every `dispatch`, `match` and `ite` at its costliest arm, so it exceeds the lowered count. A tighter count would need per-shape certificates (a callee specialized at a constant selector, the stack log and rate threaded from `verify_sub` into `open_stacked`). The words decide every coefficient: the rows fit below each, and each item's weighted rows within `31` times them, so `cycles_committed_of_count` gives `2^25 + 2 (31 · 2^24 - 2^15) + 2^16 = 2^30` (`Budget/CycleCount.lean`, `Budget/CheckerCount.lean`).

- **Aligned words.** The checker (`Memory/Static*.lean`, mirrored by `scripts/count/checker.py`) runs at padded frame weights `fsPad fsW alW`: `15` cells per allocation of an aligned frame (`Memory/WordsA.lean`). `alW` is a superset of the compiler's aligned frames: a function holding a `KECCAK`, or an arm of a `dispatch` with such an arm.
- **Hand functions.** A function whose size or loop end comes from hinted bits or a load is checked over virtual parameters (`Hand`, `CheckedH`, `chk_soundH`, `Memory/StaticSound.lean`; `hand.py` finds them from the checker's failures), its callers seeing an outer certificate. The children's loop `__loop4_main` is a loop hand (`LoopRun`). Every `callIf` guard is kept (`guardAtom`), so a loop may run no iteration.
- **Per-node obligations.** The facts each hand needs on its node (`HandFact`) are proved from the honest valuation in `Complete/Hand*.lean` and `Complete/Cyc*.lean`, one proof per hand function feeding the words and every opcode's count. `HandFact` reads virtual parameters through a re-valuation (`SameOnPath`): off the path nothing pins a value. Range-checked values come from the pops, never from memory: a `rangeCheck` passes vacuously on a memory of at least `2^64` cells.
- **Audit tools.** `scripts/count/{lowered, words2, cyc, shape, dyn, grid}.py` and `Budget/Count.lean`'s `nodeWords` are not on the end theorem's path. They read a `DBG_LOWER` dump with each instruction's hints, which `zkdsl_compiler`'s debug print emits only with a local patch (`ins.op, ins.hints`).

### Statement forms of a callee's completeness

- `CallCompletes k f args rets Pre Post` (`Complete/CallComplete.lean`) is layout-free; `CallCompletes0` (`Complete/Call0.lean`) is that for a call with no words of its own, its valuation chosen per memory. `CallAtA fs al cert k f args rets R D Out Pre Post B fp c e` (`Complete/ComposeA.lean`) is placed: frame `fp`, cursor `c`, end `e`, loads and heap hints in the region `R`, claimed data `D`, `Out` what its words give later callees.
- `CallCompletes` cannot give B2's premise `MainB1`: it asks for `HeapBuf` pointers and `frameAddr`s at the aligned allocator's positions, and pointers cannot be moved after the fact (a counter `g^n` may equal an address, and some buffers hold pointers). So a callee owning a `HeapBuf`, or returning a `frameAddr` or a buffer pointer, is stated placed, composed by `callAtA_node` (`KidsAtF`), `callAtA_nodeL` (`KidsAtL`) for loop helpers, and their `Rd` twins (`Complete/ComposeRd.lean`) when range checks or touches read memory (`σ0` fixed first, one valuation per memory agreeing with it on the calls' words). A callee with no words of its own is proved `CallCompletes0` and placed by `callAtA_of_callCompletes0`.
- Hotwire's executor starts a frame holding `KECCAK` blocks at the next multiple of `16` (`allocBase`), so `Memory/AllocA` places a tree as the executor does (`Tree.instsA fs lp al`, `Tree.endA`, `Tree.wordsA`), `al` a function of the callee. The bus era's placed completeness assumed the unaligned allocator and is not restored.
- **Ends are bounded.** A `CallAtA` holds vacuously at an end past `2^64`: own words `2^64 - 1` apart share an address, so no memory holds them (`callAtA_wrap`, `Agg/Wrap.lean`). Every field therefore bounds its end below a cursor bound `T` with `T + β < 2^64 - 1` (`AtEveryB … (2^60) (2^40)`, `MainCalleesA.lean`; `VsCalleesEndA`, `B1/VsC/CalleesB.lean`; `OpenStackedEndA` at `2^36`; `MainEndWithin`, `within_deployed`). Each bound is a twin beside the unbounded statement (`…AE`, `…AB`, `.toA` forgets it). `fs_lt16` (`Complete/FsSmall.lean`) keeps frames small.
- Callee statements hold at every frame past a floor and every cursor past their block (`AtEvery`), since those positions depend on earlier callees' ends. Ends are existential, chosen inside each producer and fixed before the caller's valuation (`HonRun.osChain`, `osChain_choose`).
- Pointers are `ptrAt i = ofK (addressOfIndex i)`. `argRegion` and `ptrRegion` are closed under the address period `2^64 - 1`, so no index-interval region contains them: use `argRegionAt`, an explicit region, or narrow with `CallAtA.idxR`. Address `0` is never an `addressOfIndex i`, hence `cur ≠ 0` in `LinkRoundsCompleteA` and `LinkRowSideCompleteA`.
- The memory floor is `17 ≤ k`: `main`'s range check `n_children < 2^16` reads the word at `2^16 - n`, which `LowDef k` defines only from `k = 17`. A range check whose touched word may lie above `2^k` needs that word defined on the admitted memories (`count_def`, `read_def`, `kid_def`).
- Template facts are kernel decisions, one `decide +kernel` per specialization or table entry (`lr_checks_{k}`, `lq_checks`, `cselOk_all`, `osCallsOk_0` to `osCallsOk_14`, `qx_0` to `qx_14`). A single decision over a whole table runs the kernel out of memory.

### vsc: `verify_sub` and its callees

`vsComplete_of_calleesA` gives `VsCompleteHypA` from `VsC.vsWindows_alW` (`B1/VsC/VsHonDone.lean`) and `vsCalleesCompleteA_of_rest`: the link callees at every floor `k ≥ 11` (`vsLinkCalleesA_complete`), `certify_stack`, `check_stack_terminal`, `ring_switch_target`, `verify_keccak` and `open_stacked` (`openStackedCompleteA_17`, `openStackedEndA_17`).

- **Windows generated.** `scripts/vs-windows` writes the gitignored `B1/VsC/VsWinData.lean` and `VsRunData.lean`: `verify_sub`'s body cut into maximal runs and calls (`wA`, `wB`, `wC`), checked by the kernel (`flatW`, `winsOk`). `runHyp_bufs` (`RunBufs.lean`) reduces a run to per-buffer facts; the phase lemmas `vsPh*_wins` chain by `winsHyp_append`.
- **Callee ends pinned.** `certify_stack`'s and `open_stacked`'s returns point into their frames, so the oracle depends on the chain of ends and a statement taken at every end is false. The ends are chosen once, from native closed forms that read neither `ret` nor `ec` (`VsCtx.ecOf`, `VsHonEc.lean`), breaking the cycle `ret` → point buffers → end → earlier ends → `ret`.
- **The honest oracle and memory.** `w` is a causal fixpoint (`OrcFix.lean`: `vsVal_causal`, `fixW_eq`). `rd0` holds each own buffer's honest words in closed form, not from the stores, which would need store forwarding over the whole body. The one exception, `.n 19` (the link terminal's sums), is an overlay (`rdSet`, `VsAvoid`). The honest values are functions of what the native verifier read (`natOpen`, `LinkNat`, `VsNat*.lean`).
- **`open_stacked`** (`B1/VsC/Os/`): its honest data are the accepting run read backwards (`honRun_of`), tied to the run's openings (`osHonest_of_openOs`). `merkleHints_open` splits `Prover.merkleHints true qs os` level by level, and each `level_queries` pops `levelHints` (`HonRun.lqPops_os`). The Merkle collision is no disjunct inside: `open_stacked` assumes agreeing openings and `capsAgree_or_collide` gives `OpeningsCollide` once, at the top.
- **keccak.** Only `keccak_layer`'s `s` grind reads the window tables: `layer_rounds` and `keccak_plain_rounds` take none because `ROUND2_GRIND_BITS` and `ROUND3_GRIND_BITS` are `0`. `KeccakLayerCompleteA` assumes `c.point.length = y` and `InRegion` (a layer reads earlier layers' buffers, above `verify_keccak`'s frame); `VerifyKeccakCompleteA` assumes a carried capacity. `readPacked` and `samplePacked` have no carried semantics on `Fs` (a draw after a grind reads the grind's whole permutation), so the carried run `runT` rejects them and those lemmas take `NoPacked p` or `PackedFree p`.
- **Statements fixed.** `OpenStackedCompleteA` held of every capacity list (with no sponge carrying it, `RunsWith` is vacuous); it assumes `∃ sp, (⟨fsv, []⟩ : Fs).Carries sp`. Its pops were an equality, false at every level with a query (`level_queries` pops the cap before its callee pops the queries, while `levelHints` pushes it after); it is `SameStreams`. `LqA` assumed `λ ≠ 0`, but `open_stacked` passes `0, 1` at a level with `λ = 0`; `LqAG` takes the second argument free. `CertifyStackCompleteA` and `CheckStackTerminalCompleteA` assume `layout.stackLog ≤ 30` (a Keccak table of log height `30` has block kappa `36`, past `certify_stack`'s `SIZE_BITS = 34`), which `VsShape` supplies.
- Every range check of `verify_sub` and its callees was compared with the verifier's accepted range (stream cap, row counts, pointer width `19 ..= 24`, chunk count `6 ..= 9`, packed challenges, the link grind, `certify_stack`'s keys, all `60` WHIR shapes). Six of its computed hints are `inverse`s pinned by the next `assertNe`; the other nine are exact on the honest valuation (`vsXs_exact`).

### b1c: `main` and the functions outside `verify_sub`

The callees' fields (`mainCalleesOpenA`, `Complete/MainCalleesHonest.lean`) and `main`'s window (`mainWindowFromCallees`, `Complete/MainFinal.lean`) are proved.

- `MainCalleesAt al k s w cover` has one `AtEveryB` field per callee, at `main`'s honest arguments (`mOrc`). Each posts its share of `honestPushes` (`PopsPost`) and claims no data. One coverage table, `honestCover`, carries the raw loops' marks (`RawMarks`) and the children's (`KidCover`).
- `main`'s body is a list of windows over temporaries read per memory (`over mTL σ0`, `Complete/MainWinGen.lean`); `scripts/main-windows` writes the gitignored `Complete/MainWinData.lean`. `main` has two branches, so its pops go by a skeleton (`Complete/PopSkel.lean`), and blocks with disjoint stream names swap (`main_reorder`, `sameStreams_append_comm`) because `main` pops `da_verify`'s entries before the children's while `honestPushes` lists them last.
- A claim walk's index and gap hints are free in a valid tree, so its pops ride the constructed tree (`loopFHP_callAtA`, `loopFH_callAtA`). The fresh claims' shape (`ClaimCells`) comes from the deferring verifier's acceptance (`fresh_shape_of_verifyDeferred`). The honest prover hints `g^0`, not `0`, for the walk by indices; the guest branches on `child_mono + g`, so either is sound.

### The core route

`CoreMode.offSigs = []` means every compiled function has a kernel-checked `CertE`: its static facts, its `FnSpecC` at its core data, `TermOk`, and residuals that are only listed nonzero values (`Res.NzOnly FnReg.nzs`). `scripts/core-mode/certs.py` writes `CoreMode/Gen/Certs/List.lean` (gitignored): `corePacks`, one `core_cert%` per routed function, and `offSigs`, every compiled function with a signature but no routed certificate. `OffOk` then asks nothing (`offOk_nil`, `EndExecOffNil.lean`); the off-route machinery exists only so that a partial route still states a theorem.

`route_alW` (`EndExecRouteG.lean`): certificates `coreAssembled`; frames `frame_core` (`CoreHonAll` from `coreHonAll_ghost … ghostOk_guest`, `UsedNextAll` from `usedNextAll_of` over `allocTrack_ofHint`); residuals `res_of_track`; termination `term_of_nodeA` over the loops' check `Res.termAll` (`loopcheck.py`). `GhostOk` (`EndExecCoreGhost.lean`) is discharged by `ghostOk_guest` (`EndExecCoreGhostD.lean`). Each function's own facts and families live in `CoreMode/Fn/<f>/{Data, Fam, SoundA}.lean`, concatenated by `fnreg.py` into `Gen/FnData` and `Gen/FnFams`.

**The generators.** `regen-guest.sh`'s `core-mode` step (`scripts/core-mode/run.sh` is `regen-guest.sh --from core-mode`) runs `bridge-cert/align.py` and `progal.py`; then in parallel the bridge checks (`jumpcells.py`, `alloc.py`, `pair.py`, `wit.py`, `fral.py`) and the registries (`fnreg`, `anylink`, `carry` with `carrynz`, `termcall`, `monocall`, `pows`, `glue`, `sigc --minimal`); then in order `callc.py`, `loopcc.py`, `heap.py`, `pair.py`, `frame_gen.py`, `core.py`, `loopcheck.py`, `certs.py`. Everything it writes is gitignored. `scripts/windows.py` holds the sizes the checks are cut at, kept under the per-module memory cap; a function too large for them gets its own in its rule file (`FRAME_WIN`, `CORE_WIN`, `PAIR_WIN`).

- A function no check takes stops `frame_gen.py`; a function with no contract written or in its rule file gets its frame layout's cells and no heap facts (`sigc.py --minimal`). Diagnose with `callc.py --why`, `loopcc.py --why` or `callc.infer_one`.
- A function's contract is the first of its rule file `scripts/core-mode/fn/<f>.py` (`CONTRACTS`, written with `sigseed.py`), the local `CoreMode/Sig/` as already written, and the bus era's `scripts/core-mode/contracts/P*.lean`. A contract stays once written into a local `CoreMode/Sig/`, so removing it from a rule file does not revert it (`--fresh NAME` does): a tree with a stale `CoreMode/Sig/` can route differently from a clean checkout.
- Rule files hold everything else per function (`RES_EQ`, `FEATURES`, `EXP_FACTS`, `ST_LOOPS`, `SPLITS`, the hooks `fam`, `arg_bound`, `sel_bound`, `merged_runs`, `merged_cell`, `arm_path`, `split`, and `OWN`, checked by `fnreg.own_files`).
- A memo directory (`CORE_MEMO`) keys its inputs by absolute path, so a copied tree reusing one reads the original's results: start a copy with an empty memo.

**Lessons of the route.**

- `Mode.Idx` is only `.num n` or `.ex base c`, with no `k·e(x)`, so a run of `k·e(x)` cells is `k` residue runs of stride `k` (`hint_stream` `256`, `squeeze_packed` `8`, `ring_rows` `64`, `link_rounds` `W`, `verify_keccak`'s stream `24`), merged back for reads (`merged_runs`). `Mode.Sig` has no `postQ`.
- `verify_keccak` reads `24·(h - 3) + 1106` words of the stream and `open_stacked` may end the stream after them, so no constant stream bound is sound: it is closed by residue runs over `e(tau_g) + 44`, the exact advance (`vk_retCur`), and `open_stacked`'s returned cursor (`open_stacked_sound_cur`).
- A cursor returned after a runtime count (`cursor·count_g^W`) needs an equation residual, `CRes.eq`, and `seedEnv` (`HeapC.lean`, mirrored in `heapc.py`) to name the value by it, since the heap pass compares cells syntactically. Conversely, a later `mul` can give a load a different monomial between two dispatches; `verify_sub`'s `RES_EQ` `[120] = [120]` names that load by itself.
- `HeapK` requires `Cf.H.ders = []`, so a callee's run over a word its caller never loads is a cursor-run family instead (`stLoops`). The bus era's stream family has no instance on Hotwire: the proof stream is `verify_sub`'s `HeapBuf`, its callees carry only `cursor`, and a ghost link reaches one caller up.
- A symbolic run inside a constant run is `subRS` (`CoreResS.lean`, mirrored in `subrs.py`). A split's arm is checked under its selector (`heapOkC1P`, `selReach`, `arm_path`), never in windows.
- Solver pitfalls: a contract run whose base mixes a frame cell with a word at a cell lists the frame cells first (`callc.own_sig` sorts the bases, `rngL` keeps their order); `drv` can make up a wrong run and state a false `subR`, which fails in the kernel, so merged runs go first (`drv_merged`); point-witness runs check their cells with `ptOkD`, not `ptOk`.

**The hint bridge and the allocation track.** `ExecGaps.ofHintsAlloc` takes `HintHyps` (`ProgAl`, `JumpCellsAt`, `AlLayout`, `AdvAl`, `WitCells`, `CompRef`, `CellsAl`) and the allocation track's `CurHyps`, `BufHint`, `FrameHint`, `AddrReady`, each discharged at `alignA` by per-function Boolean checks the kernel decides, written by `scripts/bridge-cert/` (`alloc.py`: `allocFnChk`, `addrFnChk`, `bufFnChk`, `frChk`; `pair.py`: `pairChk`; `wit.py`: `witChk`; `fral.py`: `frAlChk`; `jumpcells.py`). The cursor is a fold (`curF`), since `allocBase` does not commute with addition; the order of an offset's hints is checked (`ordHints`), not derived. The four heap witness pointers no spine pins come from the carried facts (`witPtrK_carryA`) at `pinDepth = 9`. `RefFrames` is stated through `JumpCellsV`, which breaks a cycle through `r.Ok`, and `refFrames_core` follows from the kernel checks `LastSelf`, `LoopFsAl` and `KecAl`.

**Fixed in these parts.** `ExecuteCompleteHint` asked `0 < ndigits`, but the compiled guest has digit hints with no digit (`column_selector__L{4..7}_L{16..30}`): `runHint_complete`. `pairChk` rejected a computed hint into a buffer the caller allocates (`table_size`'s `bits`): `bufOk` accepts a buffer loaded through on the spine. The hint-only table is fixed at `exA` (`extraOk_exA`). The bus era's signatures of `statement_digest` and `exponent_tables` were false on Hotwire's bodies; they have their own contracts (`fn/{statement_digest, exponent_tables, main, aggregate_claims}.py`).

## Lean pitfalls

Besides `formal/AGENTS.md`'s:

- Checking a term against a type that names a symbolic template's calls (`KidsValid … (calls …)`, `KidsAtF`) at default transparency times out in `whnf` or hits the recursion limit: use `with_reducible exact`, generalize the calls first, or keep the valuation abstract. A `set` local holding a symbolic template unfolds under `rw` and `whnf`; `obtain ⟨es, hes⟩ : ∃ es, es = … := ⟨_, rfl⟩` keeps it opaque.
- `rfl` between argument lists under two valuations makes the kernel compare the valuations (through Keccak or `statementDigest`) before reducing: state each argument by an evaluation lemma. `clear_value σ` before a `rfl` that would otherwise evaluate `vsVal`.
- A recursive predicate over a verifier program makes `exact` reduce the program by `whnf`: make it inductive (`Plain`).
- `congr 1` on powers of `gen`, `subst` of a cursor equation, a `+ 0` in an index, and `simp` membership in a long window hit the recursion limit: rewrite, or find atoms by index (`mem_of_getElem?'`). `xs[k]` in a large context sends `get_elem_tactic` into a timeout: write `xs[k]'hk`. `omega` with large literal coefficients on two atoms: name the constants.
- `linter.constructorNameAsVariable` can time out on a large context: turn it off locally.
- A `?_` inside `obtain … := f (fun … => ?_)` is not left as a goal: state the step as a `have`.
- Two files declaring the same global name cannot be imported together: check for a clash before adding a helper in a new file, and prefix helpers by family (`tail`, `tailRow`, `sk`).
- `B2C/Cells` reads names' sizes through `names_eq`: the kernel's `String.length` over every name is too costly.

## The archive

Tag `formal-bus-archive` holds the bus-era proofs, and each archived family was proved again: the bus, the table sumcheck and `Arithmetization/*` by the link (H4, M2-A); `Compile/*`, `Rpm/*` restored with packed messages (M2-F); `Guest/Batch/*` by the batching's proof (M2-F); `Protocol/Verifier/{Deferred, Defers}` restated (the deferring verifier, Summary), `DeferredShape` and the honest `Guest/Child/*` not restored; the honest prover's wire facts (`Wire/Honest*.lean`) restated for Hotwire's prover; the walk, WHIR, Keccak and extractor families by M2-KS; `EndToEnd/Complete/*`, `Prover/*` by M2-C; `Cost/*` by M2-P and M2-guest (the decoder); the guest's B1, B2, core route and budget by M2-guest and M2-guest complete.

## The final formal review

Four adversarial reviewers (the trusted statement, Lean against Rust, proof hygiene, the guest's end statements) found no vacuity, bound mismatch or Lean/Rust mismatch. A kernel replay of `theorems_hold`'s closure into an empty environment found no mismatch and no axiom beyond Lean's three, except for `lean_xmss` and `lean_sphincs` constants it could not replay within its memory. The review tightened `leanVmKnowledgeExtractorSizeBound` to the extractor's size and a slack of `120`: a slack of `1525` would leave room for a table of about five leanXMSS signatures' encodings, which the bound exists to exclude. It added `executor-faults` to the gate and fixtures at pointer widths `9` and `13` (a five-bit chunk). The kernel replay is not in the gate (Summary, Open).
