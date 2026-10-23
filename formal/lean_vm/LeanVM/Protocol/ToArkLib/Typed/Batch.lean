/-
  LeanVM.Protocol.ToArkLib.Typed.Batch

  Batching by powers as a typed component: the verifier draws one challenge and combines the
  claimed values by its powers. Completeness and round-by-round knowledge soundness at
  `(k - 1) / |F|`. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.SampleChallenge
public import LeanVM.Protocol.ToCompPoly.PowerBatching

/-!
# Batching by powers

`Typed.batch O F value out` is batching by powers as a typed component: the statement `s`
claims the values `value s : Fin k → F`, the verifier draws `ρ`, and the output statement is
`out s ρ (Σ_j value_j · ρ^j)` (`powerBatch`).

Completeness (`batchComplete`): the input relation is carried into the output relation at every
challenge. Knowledge soundness (`batchSecurity`, at `(k - 1) / |F|`, with the extractor that keeps
the witness): when every statement has true values `a`, fixed before the challenge and the
witness, such that a challenge carrying it with a witness outside the input relation into the
output relation makes the combined claim the combination of `a`, and `a` differs from the claimed
values, at most `k - 1` challenges are bad (`card_badBatch_le`, from `card_false_batch_le`).
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped NNReal

@[expose] public section

variable {ι : Type} (O : ι → Type) {S T W : Type}
  (F : Type) [Field F] [SampleableType F] {k : ℕ} (value : S → Fin k → F) (out : S → F → F → T)

/-- Batching by powers: draw `ρ`, combine the claimed values by its powers. -/
def batch : Def O S W T W (drawSlot F) :=
  sampleChallenge O F (fun _ ↦ true) fun s ρ ↦ out s ρ (powerBatch (value s) ρ)

variable {O F value out}
variable {relIn : Set ((S × ∀ i, O i) × W)} {relOut : Set ((T × ∀ i, O i) × W)}

/-- Its completeness, whenever the input relation is carried into the output relation at every
challenge. -/
theorem batchComplete
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ∀ ρ, ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut) :
    Complete (batch O F value out) relIn relOut :=
  sampleChallengeComplete fun s o w hin ↦ ⟨rfl, h s o w hin⟩

omit [SampleableType F] in
/-- **The count of bad combiners**: at most `k - 1`, whenever the statement has true values fixed
before the challenge and the witness, which every bad combiner makes the combined claim's and
which differ from the claimed values. -/
theorem card_badBatch_le [Finite F] (s : S) (o : ∀ i, O i)
    (h : ∃ a : Fin k → F, ∀ w ρ, ((s, o), w) ∉ relIn →
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut →
        a ≠ value s ∧ powerBatch (value s) ρ = powerBatch a ρ) :
    Nat.card {ρ // ∃ w, ((s, o), w) ∉ relIn ∧
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut} ≤ k - 1 := by
  have := Fintype.ofFinite F
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨a, ha⟩ := h
  by_cases hgood : ∃ ρ w, ((s, o), w) ∉ relIn ∧
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut
  · obtain ⟨ρ₀, w₀, hin₀, hρ₀⟩ := hgood
    refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans
      (card_false_batch_le (value s) a (Function.ne_iff.mp (ha w₀ ρ₀ hin₀ hρ₀).1.symm))
    obtain ⟨w', hw', hout⟩ := (Finset.mem_filter.mp hρ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ha w' ρ hw' hout).2⟩
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ρ - ⟨w', hw', hout⟩
    exact hgood ⟨ρ, w', hw', hout⟩

variable [Finite F]

/-- Its security at `(k - 1) / |F|`, whenever every statement has values `a`, fixed before the
challenge and the witness, such that a challenge carrying it, with a witness outside the input
relation, into the output relation makes the combined claim the combination of `a`, and `a` is
not the claimed values. -/
def batchSecurity
    (h : ∀ s o, ∃ a : Fin k → F, ∀ w ρ, ((s, o), w) ∉ relIn →
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut →
        a ≠ value s ∧ powerBatch (value s) ρ = powerBatch a ρ) :
    Security (batch O F value out) relIn relOut
      (drawErrors F (((k - 1 : ℕ) : ℝ≥0) / (Nat.card F : ℝ≥0))) :=
  sampleChallengeSecurity (k - 1) fun s o _ ↦ card_badBatch_le s o (h s o)

end
end LeanVM.Protocol.Typed
