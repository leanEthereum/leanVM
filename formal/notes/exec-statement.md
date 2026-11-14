# The executor's end statement: the prepared `Statement/` change

Status: the final chain is proved in `lean_vm` modulo one structure, `ExecGaps` (`lean_vm/LeanVM/Guest/EndExec.lean`), and pinned in `LeanVM.lean` (axioms Lean's three). The `Statement/` change below is prepared, not applied: `Theorems` can take the field only once `ExecGaps` is discharged, since `theorems_hold` takes no hypothesis.

## What is proved

- `EndExec.execute_guest_complete (G : ExecGaps Ks Km E0 X Pro)`: for every `seed s w` with `NodeRelation bytecode seed s w`, `GuestLimits s w`, `ChildrenOk bytecode seed w` and the deployed budget's size within `2^30`, `execute guestProgram (publicInputOf (statementDigest seed s)) (guestAdvice seed s w) = .ok t`, `t` valid, `t.committedSize ≤ 2^30`. `guestExecution_complete` is the same with `guestExecution`.
- `EndExec.guestExecution_complete_on_honest_children (G) : GuestExecutionComplete guestAdvice` (`EndExecHonest.lean`): the proposed field, on honest children under the deployed seed.
- `EndExec.aggregate_complete_exec (G)`: `End.aggregate_complete_of`'s random-permutation bound for the executor's execution. `EndExec.guest_prover_complete (G)`: the composed prover (generator, executor, `leanVmHonestProver`) at `ρ ∈ [1, 4]`, `2^35` nonces: rejected with probability at most `2^-256` (`Completeness`), refused by `verifierRefusingZero` or not made with probability at most `2^-100` (`HonestProofRarelyRefused`).

The chain: `ref_exists` (`EndExecRef.lean`: `refX_valid_of_main` and `honest_of_mainP` on one tree, under `mainCompletePE_deployed`), then `execute_complete_guest` (`inv_rule`) with `ProgOk` from the certificates (`progOk_of`, through `certOk_fn`), `κ ≤ 28` and `n ≤ maxSteps` from the committed size (`logMemorySize_le_28`, `stepCount_le_maxSteps`), every slot decoding (`guest_decodable`, one kernel check, `ExecDecodable.lean`), `main`'s frame below `maxCells`; `Prem` is assembled from the fields below.

`guestAdvice` is now built from the advice's data (`Data.adviceMainFrame`, `Data.adviceHints`, the data the mode certificates are checked against) with the honest streams, a total function `Digest → NodeStatement → NodeWitness → Advice` (`Guest/Executor.lean`); `tests/LeanVMTests/Guest/AdviceData.lean` keeps checking the data against the text's parse.

## `ExecGaps`: the shortest list

Each field is read at a node's reference run `r` (`Ref.Ok`: the honest tree exact on its memory, its pops the honest pushes, its memory a valid execution within `2^30`) and the executor's tables `C` for `guestAdvice`; `X` is the other tracks' invariant, `Pro` the prologue's states, both chosen by the tracks.

| field | proposition | track |
| --- | --- | --- |
| `certs` | `ModeCerts Ks Km E0`: every certificate a guest function's, its walk accepting, operands small, hints the advice's, and `ProgOk`'s structural facts | the mode walk closed (remaining root failures, heavy functions' checks, assembly by `gen.py`) |
| `mainExact` | `Budget.MainExactHyp` | exactness: `mainExactHyp_of_l5`, the children's loop's E form |
| `hintAlloc` | `HintOk` of each allocation hint | the allocation track: `AllocInv`, reservation order, `Tree.heapPops` against `heap_sizes` |
| `hintWitness` | `HintOk` of each witness hint | the hint bridge (alignment soundness) and the tree track's cursor (`witness_next`) |
| `hintComputed` | `HintOk` of each computed hint | the hint bridge with `Ref.Ok`'s exactness |
| `res` | `ResRef guestProgram r.img r.n Ks (X r)` | residuals by family (`ResFam`) |
| `term` | the termination facts at each entry | loop exits, table calls' arms, through the frame-to-instance map |
| `ref` | `RefOk` of each instruction | the reference step (as `ref_mul`) |
| `keepHint`, `keepOp` | `X` kept by each hint and instruction | the tree track along the run (`RefTrace`), the allocation track |
| `pro`, `init` | the prologue's steps; `X`, `Pro` initially | the prologue (`__jump_tables`) |
| `used` | `X r s → s.mem.used ≤ 2^r.κ` | the allocation track |

Discharged here, so not fields: the reference run but its exactness, `κ ≤ 28`, `n ≤ maxSteps`, `Decodable`, `main`'s frame, `ProgOk`'s tie to the executor, the honest-children reduction, the budget.

## The `Statement/` diff

`Statement/LeanVmGuestCompleteness.lean`, in `namespace Completeness` after `GuestCompleteOnHonestChildren` (and `public import Statement.Prover.Execute`, which imports only `LeanIsa`):

```lean
/-- The guest program's run on a node: the executor on the statement's digest, with the advice
the generator makes from the statement and the witness. -/
def guestRun (advice : Digest → NodeStatement → NodeWitness → Prover.Exec.Advice)
    (statement : NodeStatement) (witness : NodeWitness) :
    Except (ℕ × Prover.Exec.Fault) (Execution guestProgram) :=
  Prover.Exec.execute guestProgram
    (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement))
    (advice (deployedSeed guestProgram) statement witness)

/-- **The executor runs the guest program to completion on the advice**, within `2^30` committed
cells, on every node `GuestCompleteOnHonestChildren` admits. Nothing about the advice is trusted:
every execution the executor returns is valid whatever its advice. -/
def GuestExecutionComplete (advice : Digest → NodeStatement → NodeWitness → Prover.Exec.Advice) :
    Prop :=
  ∀ statement witness,
    NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness →
    DeployedLimits statement witness → (∀ child ∈ witness.children, HonestChild child) →
    ∃ execution, guestRun advice statement witness = .ok execution ∧
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) execution ∧
      execution.committedSize ≤ 2 ^ 30
```

`Statement/Theorems.lean`: a third parameter and one field; the docstring's "two programs" paragraph gains the generator.

```lean
structure Theorems
    (leanVmKnowledgeExtractor guestWitnessDecoder : LeanVM.Cost.MachineProgram)
    (guestAdvice : Digest → LeanVM.Node.NodeStatement → LeanVM.Node.NodeWitness →
      LeanVM.Prover.Exec.Advice) : Prop where
  ...
  /-- The executor (`Prover/Execute.lean`) runs the leanISA guest program to completion on the
  advice `guestAdvice` makes from a node's statement and witness, within `2^30` committed cells, on
  every node `guestCompleteOnHonestChildren` covers (`LeanVmGuestCompleteness.lean`). The advice is
  untrusted: whatever it is, an execution the executor returns is valid. -/
  guestExecutionComplete : LeanVM.Guest.Completeness.GuestExecutionComplete guestAdvice
```

`guestCompleteOnHonestChildren` stays a field in this change (removing it is a second step: it follows from the new field, `EndExec.guestCompleteOnHonestChildren_of_exec`, and would move to `Corollaries.lean`, which then takes the third parameter too). `Statement/Corollaries.lean` otherwise only passes the parameter: `Corollaries (leanVmKnowledgeExtractor guestWitnessDecoder)` is unchanged and `corollaries_of_theorems` takes `Theorems _ _ guestAdvice` for any `guestAdvice`.

`lean_vm/LeanVM.lean`: `theorems_hold : Statement.Theorems (leanVmKnowledgeExtractor := …) (guestWitnessDecoder := …) (guestAdvice := LeanVM.Guest.guestAdvice)`, its field `guestExecutionComplete := LeanVM.Guest.EndExec.guestExecution_complete_on_honest_children G` for the discharged `G : ExecGaps …`; `theorems_of_decoderSpec` and `theorems_hold_of_decode` gain the field the same way, and the final `example` names the parameter.

## The `statement.tex` text

Entry point (the sentence naming the programs): "`Statement.Theorems` (its programs named, `leanVmKnowledgeExtractor := P`, `guestWitnessDecoder := D`, and its advice generator, `guestAdvice := LeanVM.Guest.guestAdvice`)", the `theorems_hold` display gaining `(guestAdvice := LeanVM.Guest.guestAdvice)`.

Table row, after `guestCompleteOnHonestChildren`:

```latex
\lean{guestExecutionComplete} & \lean{LeanVM.Guest.Completeness.GuestExecutionComplete A} & \ref{sec:guest}\\
```

File list: "\item \lean{LeanVmGuestCompleteness.lean}: the deployed limits, honest children, the guest's completeness, the executor's run of it on the generator's advice, and \lean{BatchingSound}."

Section on the guest's completeness, after "The theorems." (one line):

```latex
\paragraph{The prover from the witness} (\lean{GuestExecutionComplete}). \lean{Theorems} takes a third parameter, the advice generator $A$: a function from the seed, a statement and a witness to the executor's advice (\texttt{main}'s frame size, the compiler's hints by pc, the witness streams). \lean{lean_vm/LeanVM.lean} instantiates it with \lean{LeanVM.Guest.guestAdvice}, a computable definition (the compiler's hints as generated data, the honest streams computed from the statement and the witness) that CI runs against the Rust on real aggregations (\lean{lake exe guest-run}). The field states that on every node \lean{GuestCompleteOnHonestChildren} admits, the executor \lean{LeanVM.Prover.Exec.execute} run on the guest program, the statement's digest and that advice returns a valid execution of committed size at most $2^{30}$. Nothing about the advice is trusted: every execution the executor returns is valid whatever its advice (\lean{LeanVM.Prover.Exec.execute\_sound}); the field says this advice makes it return one. With \lean{Completeness} and \lean{HonestProofRarelyRefused}, the prover that runs the generator, the executor and \lean{LeanVM.leanVmHonestProver} on a statement and a witness makes a proof the verifier rejects with probability at most $2^{-256}$, and that the verifier refusing every zero challenge rejects, or that it fails to make, with probability at most $2^{-100}$, in the RPM (\lean{guest\_prover\_complete} in \lean{lean_vm}).
```

"What is not proved", the witness-generation item, replaced by (one line):

```latex
\item Witness generation's speed: the executor \lean{LeanVM.Prover.Exec.execute} (\lean{Statement/Prover/Execute.lean}) runs the guest on the generator's advice as leanVM's Rust interpreter does, and gives the Rust's memory and step count, byte for byte, on the prover differential's programs and on real aggregations; no complexity bound is proved.
```

The `\lean{aggregate\_complete\_of}` item gains: "and \lean{aggregate\_complete\_exec}, the same for the executor's execution."
