# Wave 1a: the low layers' class-A functions, and the small ones without proofs

Worktree: /home/devops/leanEthereum/leanVM-t-comb (branch formal/rv64mc-total-w1a, head e8794dc66a). Lake project formal/rv64mc, warm.

## Deliverables, in order

1. Total contracts, by port or `of_holds_code`, of the class-A functions of heights 0 to 2 (waves.md) not yet total: `clmul_low`, `clmul`, `base_mul`, `E as Mul::mul`, `E::sum::<Copied<…>>`, `grinding_bits`, `bus_grinding_bits`, `Layout::committed`, `Transcript::finish`, `Transcript::next`, `whir_queries`, `qkeccak_slot`, `is_output_lane`, the two one-instruction drops (68, 73), `frobenius_8`, `Digest::words`, `memcpy`/`memmove` C wrappers (227, 228: over a total contract of `compiler_builtins`' `memcpy`/`memmove` taken as a hypothesis, which wave 1b proves, stated as the `HoldsT` the wave-1b task names: `Proof/Runtime/MemcpyT.lean`'s `MemcpySpecT` and `MemmoveT.lean`'s `MemmoveSpecT`; coordinate by stating your wrapper over a hypothesis of a contract of that shape), `finish_grow` (over memcpy's and alloc's total contracts).
2. The small class-C and class-D ones of heights 0 to 2: 206 (one instruction), the drops 69, 71, 72 (their loops), both `try_allocate_in` (3, 37), `Input::digest` (5).
3. `Table` instances (`Rv64mc/Table/<Family>T.lean`) for every function total so far whose callees all are, including the earlier ones (`halt`, panics, `alloc`, `Input::word`, `memset` wrapper, `reduce`, `spread`, `E::square`, `Digest::from_halves`, `memcmp`).
4. A new `notes/total-status.md`: per function reachable from `main`, whether it has a total contract (template proof, `Table` instance), its module, and its open hypotheses; and the summary counts (functions and instructions) like `notes/status.md`'s. Link it from README.md.

## Context (common to wave 1)

The campaign proves `main`'s total contract `MainSpecT` (`Final/MainSpecT.lean`) bottom-up: a `HoldsT` (`Core/HoldsT.lean`) for each of the 229 functions `main` reaches. The call graph, by height (0 = leaf) with each function's partial-proof class from `notes/status.md` (A: partial proof at the image; C: spec only; D: nothing), is formal/rv64mc/campaign/waves.md; each function's callees are in cg.json next to it. Already total: `halt` and the panic chain (`Aborts`, HaltT/PanicsT), `alloc`, `Input::word`, `memset` and its C wrapper, `reduce`, `spread`, `E::square`, `Digest::from_halves`, `memcmp`.

Read first: formal/rv64mc/README.md, notes/total-correctness.md (the two recipes: port a partial proof with `rv_autoT`/`rv_symT`, or prove a safety-only total contract and combine it with the partial proof by `HoldsT.of_holds_code`/`of_holds_post`), notes/how-to-prove-a-function.md, Tactic/SymT.lean's header, and the existing total proofs Proof/Field/{ReduceT,ESquareT}.lean, Proof/Hash/DigestFromHalvesT.lean, Proof/Runtime/{MemcmpT,AllocT,MemsetT,PanicsT}.lean.

What the end needs, and so what each contract must give:
* `MainSpecT` asks only safety and termination: a panic or the allocator's failure ending the run with `a0 = 2` is allowed. Take `Stop` uniformly as `Core/AbortStop.lean`'s `AbortStop` (`a0 = 2`, which is `main`'s `MainStopT`) for every function that may abort, weakening a finer callee stop (`AllocStop`) by `HoldsT.mono_stop`; `False` (the default) for one that never aborts.
* Postconditions: a function with a partial proof keeps its partial postcondition and memory frame (port, or `of_holds_code`). A function without one states what its callers need for their own safety and termination: the memory frame (`Out`), and the representation facts of what it returns or writes (a vector's pointer, capacity and length in a window and aligned, contents where a caller's later safety reads them, e.g. a copied pointer). Prefer the existing spec in `Spec/` when it has a contract (class C), adding window facts.
* Preconditions: each pointer argument's bytes in a window (`InWin`) and aligned for the widest access through it, plus what the partial spec has. **Every `Pre` must hold at every call site in the image** (else the contract is vacuous where it is used): check each call site in the callers' templates (`Rv64mc/Gen/Tmpl/`), and say in the defence which call-site fact discharges each conjunct.
* Each loop: `Total.loop` with a measure (see `MemcmpT`, `MemsetT`).
* At the image: for every function made total in this wave whose callees all have total contracts at the image, a `Table` instance in a new `Rv64mc/Table/<Family>T.lean` (as `Table/Runtime.lean` instantiates the partial ones: `liftProg Gen.fns`, `Gen.Idx`, `Gen.Needs`, the generated `tmpl_eq`, `link`, `wf`), including the functions already total above, with the callees' `Table` instances as arguments, so that no hypothesis is left but environment facts. This is how the campaign composes toward `main`.

Constraints:
- No existing statement changes (`Holds`, `HoldsT`, `TContract`, `Total`, `MainSpec*`, end theorems, `EndStatement.lean`, existing specs and partial proofs). New modules for new proofs.
- Build only what you changed: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build <module names>`; one `lake build` of your own at a time; check `free -g` first (another agent builds in a sibling worktree; keep at least 10 GB available). Never `lake clean`, never delete `.lake` or `Rv64mc/Gen`, never run `scripts/regen.sh`. A `timeout` on every Lean command.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`; no raised `maxHeartbeats` without a stated reason. A `#guard_msgs in #print axioms` block pinning `[propext, Classical.choice, Quot.sound]` (or fewer) for each `Table` theorem.
- Style (formal/AGENTS.md, the repo AGENTS.md): header docstring per module; comments only where necessary; no measurements in comments; no em-dashes or en-dashes; one symbol one meaning.
- Stop when the next function's gain is marginal or the budget is spent, and list in the defence what is done and what is left, per function, with the obstacle.
- Commit on the branch with conventional messages (`feat(formal): …`) ending with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`; do not push.

Module names: the sibling wave (1b) writes `Rv64mc/Table/MemT.lean`, `HashT.lean`, `Proof/Runtime/MemcpyT.lean`, `MemmoveT.lean`, and total contracts of `xor_block`, `keccak_f`, `keccak_cell_lanes` and `E::sum::<Chain<…>>`: do not create those.
