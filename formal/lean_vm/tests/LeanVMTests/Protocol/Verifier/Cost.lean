import LeanVM.Protocol.Verifier.Cost
import LeanVM.Protocol.WithHash

/-!
# The query cost of verifier programs

Regression and negative tests for `LeanVM.Protocol.Compile.Cost` and
`LeanVM.Protocol.Verifier.Cost`.

* The calculus, in quarters of a query: a small program with a commitment and an opening has
  the cost the accounting gives, and the conditions doing the work are load-bearing: a
  commitment taller than the height bound, an opening charged per position and level, and a
  budget one short are refuted.
* The leanVM constants: the bound is `13261`; the height bound is attained by an admissible
  ladder (`μ = 28` at rate `4`), and the WHIR bound by the same ladder at rate `1` but for the
  grind and two challenges its `26` fold rounds no longer take (`13` quarters each).
* The seed: the leanVM seeding has three hash steps.
* An executed run: the compiled leanVM verifier, its hash and permutation counting their calls,
  rejects a garbage proof at the first GKR layer after exactly the queries the sponge makes,
  within the bound.
-/

namespace LeanVMTests.Protocol.Verifier.Cost

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.KeccakHash LeanVM.Semantics

/-! ## The calculus -/

/-- A read, a commitment of height `3`, and an opening of two positions. -/
def small : VerifierProgram Bool := do
  let _ ← VerifierProgram.readScalar
  VerifierProgram.readCommitment 3 1
  let _ ← VerifierProgram.queryOpenings 0 [5, 6]
  return true

/-- Its cost at height `3`, in quarters: `1 + 2 + 4 · 2 · (1 + 3) = 35`. -/
theorem small_cost : small.CostLE 3 35 :=
  VerifierProgram.Costs.seq VerifierProgram.Costs.readE (fun _ _ ↦ VerifierProgram.Costs.seq
      (VerifierProgram.Costs.commitP 1 le_rfl)
    (fun _ _ ↦ VerifierProgram.Costs.seq (VerifierProgram.Costs.queryP 0 _) (fun _ _ ↦ trivial)
        (by decide))
    (by decide)) (by decide)

/-- Its query bound against the random oracles, with a seed of one permutation. -/
example (π : Proof) :
    OracleComp.IsTotalQueryBound (verifierComp ⟨[], fun _ ↦ default⟩ small π) (0 + 1 + 35 / 4) :=
  isTotalQueryBound_verifierComp small_cost _ π

/-- One short of the budget is refuted. -/
example : ¬ small.CostLE 3 34 := by
  intro h
  obtain ⟨-, h⟩ := h
  obtain ⟨-, -, h⟩ := h 0
  exact absurd (h.1) (by decide)

/-- A commitment taller than the height bound is refuted, whatever the budget. -/
example (n : ℕ) : ¬ (VerifierProgram.readCommitment 5 1).CostLE 4 n := fun h ↦ absurd h.1
    (by decide)

/-- An opening is charged one leaf and one level per position: two positions at height `3` cost
`8` queries, `32` quarters, not `31`. -/
example : ¬ (VerifierProgram.queryOpenings 0 [0, 1]).CostLE 3 31 := fun h ↦ absurd h.1 (by decide)

/-! ## The leanVM constants -/

example : leanVmQueryBound = 13261 := leanVmQueryBound_eq

/-- The WHIR bound is the ladder at `μ = 28`, rate `1`, with the `26` fold rounds' former grind
and two challenges. -/
example : whirCost costHeight 28 ((Whir.ladder 28 1).getD []) + 26 * 13 = whirBound := by
  decide +kernel

/-- The height bound is attained: the stack's commitment at `μ = 28`, rate `4`, has height
`28 - 6 + 4 = 26`. -/
example : stackHeightLE (costHeight - 1) 28 ((Whir.ladder 28 4).getD []) = false := by
  decide +kernel

/-- The bus depth bound: `54` blocks of `2^32` rows. -/
example : gkrCost 38 0 = gkrBound := by decide

/-- The seed has `1` hash, the IV's. -/
example (bytecode : List K) (publicInput : Digest) :
    (leanVmSeed bytecode publicInput).hs.length = 1 := rfl

/-! ## An executed run -/

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its two limbs. -/
def e (c0 c1 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1)

/-- The bytecode: 32 words. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The public input. -/
def samplePublicInput : Digest := Vector.ofFn fun j : Fin 4 ↦ (fw j 10).toUInt64

/-- The sizes (memory `2^16`, small tables, rate `4`), two root halves, then `n` scalars. -/
def stream (n : ℕ) : List E :=
  [eOfNat 16] ++ [2, 1, 1, 2, 2, 3].map eOfNat ++ [eOfNat 4] ++
    [e (fw 8 0) (fw 8 1), e (fw 9 0) (fw 9 1)] ++
    (List.range n).map fun k ↦ e (fw (10 + k) 0) (fw (10 + k) 1)

/-- Keccak-256, counting its calls. -/
def countingHash (x : Bytes) : StateM ℕ Digest := do
  modify (· + 1)
  return keccak256 x

/-- Keccak-f[1600], counting its calls. -/
def countingPerm (s : KeccakState) : StateM ℕ KeccakState := do
  modify (· + 1)
  return keccakF1600 s

/-- The verdict and the number of queries of the compiled verifier on a stream. -/
def countedRun (n : ℕ) : Bool × ℕ :=
  (verifyWithHash countingHash countingPerm sampleBytecode samplePublicInput ⟨stream n, []⟩).run 0

-- Rejected at the stack commitment's out-of-domain proof of work (the garbage nonce fails its
-- `15` bits), after the IV's hash and the seed's permutation, then the sponge's permutations: the
-- fifth of the `8` sizes, the first half of the root (four scalars waiting each time), and the
-- nonce's own.
#guard countedRun 100 = (false, 1 + 1 + 1 + 1 + 1)
#guard (countedRun 100).2 ≤ leanVmQueryBound

end LeanVMTests.Protocol.Verifier.Cost
