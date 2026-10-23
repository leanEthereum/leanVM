import LeanVM.Protocol.EndToEnd.Complete.Assemble
import LeanVM.Protocol.EndToEnd.Complete.Sumcheck

/-!
# Completeness of the verifier program: the wire rounds, the sizes, the public input

* **Statement locks** of the generic wire sumcheck (`follows_sumcheck`), the announcement
  (`follows_readSizes`), the public-input step (`follows_publicInputPhase`) and the assembly
  (`follows_verifyExecution`, `runI_leanVmProgram_of`): a change of a hypothesis or of the
  conclusion fails here.
* **The wire round** (`#guard`, compiled): fed the honest wire (`wire`) of a coefficient list, the
  verifier's `sumcheckRoundPoly` rebuilds the list exactly when the round's check holds, in both
  modes; with the claim off by one it rebuilds a different list (the check is load-bearing).
* **The announcement**: the theorem `follows_readSizes` at a concrete program and admissible
  sizes (an inhabitant of its hypotheses), and the rate `5`, outside `validRate`, rejected.
* **The public digest**: `publicDigest` inverts the digest's halves on a concrete input.
-/

namespace LeanVMTests.Protocol.EndToEnd.Complete.Basic

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Blake2sHash

/-! ## Statement locks -/

example : ∀ (count : ℕ), 2 ≤ count → ∀ (claimOf : List E → E) (modes : List (Option E))
    (pre : List E) (cs : Commits),
    (∀ ext : List E, ext.length < modes.length →
      PolyLE (count - 1) fun x ↦ claimOf (pre ++ ext ++ [x])) →
    (∀ ext : List E, (h : ext.length < modes.length) →
      RoundSplit modes[ext.length] (claimOf (pre ++ ext)) (claimOf (pre ++ ext ++ [0]))
        (claimOf (pre ++ ext ++ [1]))) →
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.1.length = modes.length ∧
        b.2 = claimOf (pre ++ b.1))
      (hSumcheck count claimOf modes pre) (sumcheck (claimOf pre) count modes) cs :=
  follows_sumcheck

example : ∀ (prog : Program) {s : Sizes}, s.Admissible prog → ∀ {ρ : ℕ}, validRate ρ →
    ∀ (cs : Commits), Follows (fun cs' _ b ↦ cs' = cs ∧ b = (verifierLayout prog s, ρ))
      (Script.sendList (announce s ρ)) (readSizes (bytecodeWords prog)) cs :=
  follows_readSizes

example : ∀ {prog : Program} {s : Sizes} {input : PublicInput} {q : Column (leanIsaμ prog s)},
    M3Holds (inst prog s) input q → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b) (hPub prog s q)
      (Verifier.publicInputPhase (verifierLayout prog s) (publicDigest input)) cs :=
  follows_publicInputPhase

example : ∀ {prog : Program} {s : Sizes} {input : PublicInput} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)}, s.Admissible prog → validRate ρ →
    M3Holds (inst prog s) input q → ∀ (P : Phases), P.Honest prog s q →
    ∀ (chal : List Ev → E),
      runI (leanVmProgram (bytecodeWords prog) (publicDigest input))
          (honestStrategy prog s ρ q P) chal = some true ∧
        shapedI (leanVmProgram (bytecodeWords prog) (publicDigest input))
          (honestStrategy prog s ρ q P) chal :=
  runI_leanVmProgram_of

/-! ## The wire round -/

/-- Run a program that only reads, on a list of scalars. -/
def feed {α : Type} : Prog α → List E → Option α
  | .ret a, _ => some a
  | .read k, x :: xs => feed (k x) xs
  | _, _ => none

/-- A field element from three words. -/
def eK (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c)

/-- A pseudo-random coefficient list of `n` entries. -/
def coeffs (seed n : ℕ) : List E :=
  (List.range n).map fun i ↦ eK (i * 0x9E3779B97F4A7C15 + seed) (i * i + 3 * seed) (seed + 7 * i)

/-- The claim a round's check accepts for a coefficient list. -/
def claimFor (mode : Option E) (c : List E) : E :=
  match mode with
  | none => polyEval c 0 + polyEval c 1
  | some r => (1 + r) * polyEval c 0 + r * polyEval c 1

-- Fed the honest wire, the verifier rebuilds the coefficient list, in both modes and for the
-- counts the deployed program uses (`3` for the Flock and WHIR rounds, `4` for the table
-- sumcheck, `2^step + 1 ∈ {3, 5}` for the GKR layers).
#guard [3, 4, 5].all fun count ↦
  [none, some (eK 11 12 13)].all fun mode ↦
    let c := coeffs count count
    feed (sumcheckRoundPoly count (claimFor mode c) mode) (wire mode c) == some c

-- Negative: with the claim off by one, the rebuilt list is not the coefficient list.
#guard [none, some (eK 11 12 13)].all fun mode ↦
  let c := coeffs 7 4
  feed (sumcheckRoundPoly 4 (claimFor mode c + 1) mode) (wire mode c) != some c

/-! ## The announcement -/

/-- Four `XOR` instructions. -/
def prog4 : Program := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- Row counts with a table as tall as the memory, and others not powers of two: heights
`2^16, 2^3, 2^16, 2^4, 2^16, 2^16`. -/
def s₁ : Sizes := ⟨16, by decide, ![65536, 5, 40000, 9, 65536, 50000]⟩

/-- The sizes are admissible for the program (their stacked size is `25 ≤ 28`). -/
theorem admissible_s₁ : s₁.Admissible prog4 := by
  refine ⟨by decide, by decide, by decide, max_le ?_ (by decide)⟩
  refine Nat.clog_le_of_le_pow ?_
  have hsum : (blocks prog4 s₁).total =
      (committedColumns.map fun c ↦ 2 ^ kappa prog4 s₁ c).sum := by
    rw [Blocks.total_eq_sum, ← ((List.mergeSort_perm committedColumns fun a b ↦
      decide (kappa prog4 s₁ b ≤ kappa prog4 s₁ a)).map _).sum_eq, ← List.sum_ofFn]
    exact congrArg List.sum
      (List.ofFn_getElem_eq_map (stackOrder prog4 s₁) fun c ↦ 2 ^ kappa prog4 s₁ c)
  rw [hsum]
  decide +kernel

/-- The announcement's completeness at a concrete program, sizes and rate. -/
example : Follows (fun cs' _ b ↦ cs' = [] ∧ b = (verifierLayout prog4 s₁, 2))
    (Script.sendList (announce s₁ 2)) (readSizes (bytecodeWords prog4)) [] :=
  follows_readSizes prog4 admissible_s₁ ⟨by decide, by decide⟩ []

-- The honest announcement returns the verifier's layout; the rate `5` is rejected.
#guard (feed (readSizes (bytecodeWords prog4)) (announce s₁ 2)).map (·.2) == some 2
#guard (feed (readSizes (bytecodeWords prog4)) (announce s₁ 5)).isNone

/-! ## The public digest -/

/-- A public input. -/
def input₀ : PublicInput :=
  ⟨![K.ofBits 0x0123456789ABCDEF, K.ofBits 0xFEDCBA9876543210, K.ofBits 42,
    K.ofBits 0xFFFFFFFFFFFFFFFF]⟩

#guard digestScalars (publicDigest input₀) == (input₀.word0, input₀.word1)

end LeanVMTests.Protocol.EndToEnd.Complete.Basic
