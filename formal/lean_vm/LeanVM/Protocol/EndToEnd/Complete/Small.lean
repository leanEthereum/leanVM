/-
  LeanVM.Protocol.EndToEnd.Complete.Small

  Completeness in the ISA's terms: a valid execution whose committed size the verifier admits has a
  witness at admissible sizes, and the honest prover's proof of it is accepted.
-/

module

public import LeanVM.Protocol.EndToEnd.Completeness
public import LeanVM.Spec.Statement

/-!
# Completeness for executions within the budget

The completeness theorems of `EndToEnd.Completeness` start from a witness at admissible sizes
(`Sizes.Admissible`), an arithmetization notion. This file closes the gap to the ISA: a valid
execution (`ValidExecution`) whose committed size (`Trace.committedSize`, stated in the ISA's
terms in `Spec/Statement.lean`) is at most `2^maxMu = 2^28` has a witness representing it at
admissible sizes (`exists_admissible_witness`), and the honest proof of that witness
(`honestProofOf`) is accepted (`verify_honestProofOf`), and exists as soon as the proof-of-work
searches succeed (`honestProofOf_isSome`).

## The sizes of the witness

The witness is `constraintCompleteness_rows`'s: its memory is the trace's, `2^κ` words, and each
opcode table holds the run's rows of its opcode, as many as the instructions of that opcode the
execution executes (`Trace.count_eq_runRows`). The stacked size counts every committed column at
its table's height (`blocks_total_eq`):

  `4·2^logMem + 2^logSize + 2^(8 + τ₅) + 15·2^τ₀ + 15·2^τ₁ + 8·2^τ₂ + 15·2^τ₃ + 14·2^τ₄ + 19·2^τ₅`

(the four memory columns, `BFCNT`, the Flock region of `2^8` rows per `BLAKE2S` row, and the
committed columns of `XOR`, `MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `BLAKE2S`, the last
without its eighteen limbs), `τ_j = ⌈log₂ rows_j⌉`. At the witness's sizes it is the execution's
committed size, so it is within the verifier's cap exactly when that is at most `2^28`.

## Wrong readings excluded

* The budget bounds the tables, not the steps: a run of many steps fits when few are `BLAKE2S`
  steps, whose table is the costly one (`tests/LeanVMTests/Protocol/EndToEnd/Complete/Small.lean`
  proves a run of `2^20` steps complete).
* The honest prover is a specification: `honestProofOf` chooses its witness classically, and is
  `none` only for an invalid rate, an execution without an admissible witness, or a proof-of-work
  search that finds no nonce below the fuel.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open Air.Flat (EnsembleWitness)

@[expose] public section

/-! ## The stacked size -/

/-- The committed columns, by table: four of the memory, `BFCNT`, `QFLOCK`, then those of the six
opcode tables (`15, 15, 8, 15, 14` and `19` for `BLAKE2S`, whose eighteen limbs are read off the
Flock region). -/
theorem committedColumns_tables : committedColumns.map (fun c ↦ c.1) =
    List.replicate 4 0 ++ [1, 2] ++ List.replicate 15 3 ++ List.replicate 15 4 ++
      List.replicate 8 5 ++ List.replicate 15 6 ++ List.replicate 14 7 ++ List.replicate 19 8 := by
  decide +kernel

/-- **The stacked size**: every committed column at its table's height. -/
theorem blocks_total_eq (prog : Program) (s : Sizes) : (LeanIsa.blocks prog s).total =
    4 * 2 ^ s.logMem + 2 ^ prog.logSize + 2 ^ (8 + s.τ 5) + 15 * 2 ^ s.τ 0 + 15 * 2 ^ s.τ 1 +
      8 * 2 ^ s.τ 2 + 15 * 2 ^ s.τ 3 + 14 * 2 ^ s.τ 4 + 19 * 2 ^ s.τ 5 := by
  rw [Blocks.total_eq_sum]
  have h1 : ∑ b : Fin (LeanIsa.blocks prog s).n, 2 ^ (LeanIsa.blocks prog s).size b =
      ((LeanIsa.stackOrder prog s).map fun c ↦ 2 ^ kappa prog s c).sum :=
    Fin.sum_univ_fun_getElem (LeanIsa.stackOrder prog s) (fun c ↦ 2 ^ kappa prog s c)
  rw [h1, LeanIsa.stackOrder, ((List.mergeSort_perm _ _).map _).sum_eq]
  have h2 : (committedColumns.map fun c ↦ 2 ^ kappa prog s c) =
      (committedColumns.map fun c ↦ c.1).map fun j ↦ 2 ^ LeanIsa.height prog s j := by
    rw [List.map_map]
    rfl
  rw [h2, committedColumns_tables]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, smul_eq_mul, LeanIsa.height,
    Nat.add_zero, ← Nat.add_assoc]
  rfl

/-- The stacked size is within the cap when the blocks fit on `2^maxMu` cells. -/
theorem leanIsaμ_le_of_total_le {prog : Program} {s : Sizes}
    (h : (LeanIsa.blocks prog s).total ≤ 2 ^ maxMu) : leanIsaμ prog s ≤ maxMu :=
  max_le (Nat.clog_le_of_le_pow h) (by decide)

/-! ## The admissible witness -/

/-- **An admissible witness, under the budget.** A valid execution whose committed size is at most
`2^28` has a witness representing it that satisfies leanISA's constraint system at sizes the
verifier admits. -/
theorem exists_admissible_witness {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu) :
    ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧
      Sizes.ofWitness w = some s ∧ s.Admissible prog := by
  have hcount : ∀ op, t.count op = t.runRows op := Trace.count_eq_runRows hv.2
  -- A table's rows fit in its height, which the committed size counts.
  have hheight : ∀ op, 2 ^ Nat.clog 2 (t.count op) ≤ t.committedSize := by
    intro op
    -- `omega` takes `2 ^ x` for an atom without its sign: the bound it needs, stated.
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    simp only [Trace.committedSize]
    cases op <;> omega
  have hcap : (2 : ℕ) ^ maxMu ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  have hrows : ∀ op, t.runRows op ≤ 2 ^ maxLogRows := fun op ↦ by
    rw [← hcount]
    exact (Nat.le_pow_clog (by norm_num) _).trans (((hheight op).trans hbudget).trans hcap)
  obtain ⟨w, hw, hrep, hlen⟩ := constraintCompleteness_rows hv hrows
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hw
  refine ⟨w, s, hw, hrep, hs, ?_⟩
  obtain ⟨hpos, rfl⟩ := eq_of_ofWitness hs
  -- The sizes: the trace's memory, and each table's row count that of the run.
  have hmem : (witnessSizes w hpos).logMem = t.κ := hrep.κ_eq
  have hr : ∀ j : Fin 6, (witnessSizes w hpos).rows j = t.count (tableOpcode j) := fun j ↦
    (hlen j).trans (hcount _).symm
  have htotal : (LeanIsa.blocks prog (witnessSizes w hpos)).total = t.committedSize := by
    have e : tableOpcode 0 = .xor ∧ tableOpcode 1 = .mulNative ∧ tableOpcode 2 = .setConstant ∧
        tableOpcode 3 = .deref ∧ tableOpcode 4 = .jump ∧ tableOpcode 5 = .blake2s := by decide
    rw [blocks_total_eq, hmem, pow_add 2 8]
    simp only [Sizes.τ, hr, e, Trace.committedSize]
    ring
  refine ⟨?_, ?_, fun j ↦ (hr j).trans_le (by rw [hcount]; exact hrows _), ?_⟩
  · rw [hmem]
    exact hv.1.1
  · rw [hmem]
    exact hv.1.2.1
  · exact leanIsaμ_le_of_total_le (htotal ▸ hbudget)

/-! ## The honest proof of an execution -/

/-- The honest prover's witness for an execution `t` at rate `ρ`: the rate is valid, and `w`
satisfies leanISA's constraint system at sizes `s` the verifier admits and represents `t`. -/
def HonestFor (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog)) (s : Sizes) : Prop :=
  validRate ρ ∧ SatisfiedBy prog input w ∧ Sizes.ofWitness w = some s ∧ s.Admissible prog ∧
    AssignmentRepresents w t

open Classical in
/-- **The honest proof of an execution**: the compiled honest prover's proof, with the hash `H`, of
a witness for `t` at rate `ρ` (`HonestFor`, chosen classically); `none` when there is none, or
when a proof-of-work search finds no nonce below `fuel`. A specification. -/
noncomputable def honestProofOf (H : Bytes → Digest) (prog : Program) (input : PublicInput)
    (t : Trace prog) (ρ fuel : ℕ) : Option Proof :=
  if h : ∃ w s, HonestFor prog input t ρ w s then
    prove H (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (leanVmProver prog h.choose_spec.choose ρ
        (stackOf Blake2sFlock.blake2sFlockSpec prog h.choose_spec.choose h.choose))
      (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel
  else none

/-- **The honest proof is accepted**, for every hash function: whenever the honest prover outputs
a proof, the verifier accepts it. -/
theorem verify_honestProofOf (H : Bytes → Digest) {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ fuel : ℕ} {proof : Proof}
    (h : honestProofOf H prog input t ρ fuel = some proof) :
    verifyWith (m := Id) H (bytecodeWords prog) (publicDigest input) proof = true := by
  unfold honestProofOf at h
  split_ifs at h with hc
  obtain ⟨hρ, hw, hs, hadm, -⟩ := hc.choose_spec.choose_spec
  have hq := m3Honest_stackOf (F := Blake2sFlock.blake2sFlockSpec) hw hs padLimbs_compress
  have hrun := runI_leanVmProgram hadm hρ hq walkFaithful_blake2sFlockSpec
  exact runProof_prove H _ _ _ fuel (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2) h

/-- **The honest prover succeeds within the budget.** For a valid execution whose committed size is
at most `2^28`, at a valid rate, the honest proof exists as soon as every
proof-of-work search the verifier program asks for finds a nonce below `fuel`. -/
theorem honestProofOf_isSome {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) (H : Bytes → Digest) (fuel : ℕ)
    (hpow : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist =
          some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    (honestProofOf H prog input t ρ fuel).isSome := by
  obtain ⟨w, s, hw, hrep, hs, hadm⟩ := exists_admissible_witness hv hbudget
  have hex : ∃ w s, HonestFor prog input t ρ w s := ⟨w, s, hρ, hw, hs, hadm, hrep⟩
  unfold honestProofOf
  split_ifs
  exact Option.isSome_iff_ne_none.mpr (prove_ne_none H _ _ _ fuel hpow)

/-- **Completeness within the budget.** A valid execution whose committed size is at most `2^28`, at
a valid rate: when every proof-of-work search succeeds below `fuel`, the honest prover outputs a
proof, and the verifier accepts it, for every hash function. -/
theorem complete_of_budget {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) (H : Bytes → Digest) (fuel : ℕ)
    (hpow : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist =
          some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    ∃ proof, honestProofOf H prog input t ρ fuel = some proof ∧
      verifyWith (m := Id) H (bytecodeWords prog) (publicDigest input) proof = true := by
  obtain ⟨proof, h⟩ := Option.isSome_iff_exists.mp
    (honestProofOf_isSome hv hbudget hρ H fuel hpow)
  exact ⟨proof, h, verify_honestProofOf H h⟩

end
end LeanVM.Protocol.EndToEnd.Complete
