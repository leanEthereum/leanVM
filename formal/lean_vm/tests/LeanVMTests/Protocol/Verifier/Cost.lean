import LeanVM.Protocol.Verifier.Cost

/-!
# The query cost of verifier programs

Regression and negative tests for `LeanVM.Protocol.Compile.Cost` and
`LeanVM.Protocol.Verifier.Cost`.

* The calculus: a small program with a commitment and an opening has the cost the accounting
  gives, and the conditions doing the work are load-bearing: a commitment taller than the
  height bound, an opening charged per position and level, and a budget one short are refuted.
* The leanVM constants: the bound is `13213`; the WHIR bound and the height bound are attained
  by an admissible ladder (`μ = 28` at rates `1` and `4`), so they are not slack in the ladder
  table.
* The seed: the leanVM seeding chain has two steps after the bytecode's hash.
* An executed run: the compiled leanVM verifier, its hash counting its calls, rejects a garbage
  proof at the first GKR layer after exactly the hashes the accounting charges, within the
  bound.
-/

namespace LeanVMTests.Protocol.Verifier.Cost

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Blake2sHash

/-! ## The calculus -/

/-- A read, a commitment of height `3`, and an opening of two positions. -/
def small : Prog Bool := do
  let _ ← Prog.readE
  Prog.commitP 3 1
  let _ ← Prog.queryP 0 [5, 6]
  return true

/-- Its cost at height `3`: `1 + 2 + 2 · (1 + 3) = 11`. -/
theorem small_cost : small.CostLE 3 11 :=
  Prog.Costs.seq Prog.Costs.readE (fun _ _ ↦ Prog.Costs.seq (Prog.Costs.commitP 1 le_rfl)
    (fun _ _ ↦ Prog.Costs.seq (Prog.Costs.queryP 0 _) (fun _ _ ↦ trivial) (by decide))
    (by decide)) (by decide)

/-- Its query bound against the random oracle, with a seed of one step. -/
example (π : Proof) :
    OracleComp.IsTotalQueryBound (verifierComp ⟨[], [([], [])]⟩ small π) (1 + 1 + 11) :=
  isTotalQueryBound_verifierComp small_cost _ π

/-- One short of the budget is refuted. -/
example : ¬ small.CostLE 3 10 := by
  intro h
  obtain ⟨-, h⟩ := h
  obtain ⟨-, -, h⟩ := h 0
  exact absurd (h.1) (by decide)

/-- A commitment taller than the height bound is refuted, whatever the budget. -/
example (n : ℕ) : ¬ (Prog.commitP 5 1).CostLE 4 n := fun h ↦ absurd h.1 (by decide)

/-- An opening is charged one leaf and one level per position: two positions at height `3` cost
`8`, not `7`. -/
example : ¬ (Prog.queryP 0 [0, 1]).CostLE 3 7 := fun h ↦ absurd h.1 (by decide)

/-! ## The leanVM constants -/

example : leanVmQueryBound = 13213 := leanVmQueryBound_eq

/-- The WHIR bound is attained by the ladder at `μ = 28`, rate `1`. -/
example : whirCost costHeight 28 ((Whir.ladder 28 1).getD []) = whirBound := by decide +kernel

/-- The height bound is attained: the stack's commitment at `μ = 28`, rate `4`, has height
`28 - 6 + 4 = 26`. -/
example : stackHeightLE (costHeight - 1) 28 ((Whir.ladder 28 4).getD []) = false := by
  decide +kernel

/-- The bus depth bound: `37` blocks of `2^32` rows. -/
example : gkrCost 38 0 = gkrBound := by decide

/-- The seed has `1 + 2` hashes. -/
example (bytecode : List K) (publicInput : Digest) :
    1 + (leanVmSeed bytecode publicInput).steps.length = 3 := rfl

/-! ## An executed run -/

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its three limbs. -/
def e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)

/-- The bytecode: 32 words. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The public input. -/
def samplePublicInput : Digest := Vector.ofFn fun j : Fin 8 ↦ (fw j 10 % 2 ^ 32).toUInt32

/-- The sizes (memory `2^16`, small tables, rate `4`), two canonical root halves, then `n`
scalars. -/
def stream (n : ℕ) : List E :=
  [eOfNat 16] ++ [2, 1, 1, 2, 2, 3].map eOfNat ++ [eOfNat 4] ++
    [e (fw 8 0) (fw 8 1) 0, e (fw 9 0) (fw 9 1) 0] ++
    (List.range n).map fun k ↦ e (fw (10 + k) 0) (fw (10 + k) 1) (fw (10 + k) 2)

/-- BLAKE2s, counting its calls. -/
def countingHash (x : Bytes) : StateM ℕ Digest := do
  modify (· + 1)
  return blake2sBytes x

/-- The verdict and the number of hashes of the compiled verifier on a stream. -/
def countedRun (n : ℕ) : Bool × ℕ :=
  (verifyWith countingHash sampleBytecode samplePublicInput ⟨stream n, []⟩).run 0

-- Rejected at the first GKR layer (the depth is odd, so one level), after `3` seeding hashes,
-- `8` sizes, `2` for the root, `4 + 1` bus challenges, `2` for the GKR roots, `1` for the first
-- layer's combiner, and the `3 · 2` children; the failed check itself hashes nothing.
#guard countedRun 100 = (false, 3 + 8 + 2 + 5 + 3 + 6)
#guard (countedRun 100).2 ≤ leanVmQueryBound

end LeanVMTests.Protocol.Verifier.Cost
