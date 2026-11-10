module

public import Qrom.Sphincs.Bound.Defer

@[expose] public section

/-!
# Covered digests

On corresponding digests, the leaves a signing log reveals are among the leaves of all the
presampled digests (`Qrom.Sphincs.revealedLeaves_sub`), so a digest the log covers is covered by
them (`Qrom.Sphincs.leavesAll`). `Qrom.Sphincs.Bound.CoverCells` searches for such digests.
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

open Classical in
/-- The FORS leaves all the presampled digests open. -/
def leavesAll (δ : Fin signatureLimit → DigV) : Disclosures := fun index κ ↦
  Finset.univ.filter fun leaf ↦ ∃ i, digestIndex (truncateMessageDigest (δ i)) = index ∧
    digestLeaves (truncateMessageDigest (δ i)) κ = leaf

theorem revealedLeaves_sub (r : Data) {Dg : Message → DigV} {δ : Fin signatureLimit → DigV} {s : Log}
    (hc : OvGame.Corr (sig s) Dg δ) (index : Index) (κ : FTree) :
    revealedLeaves (withDig r Dg) s index κ ⊆ leavesAll δ index κ := by
  intro leaf hl
  simp only [revealedLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨e, he, hi, hk⟩ := hl
  have hm : e.1 ∈ sig s := mem_sig.mpr ⟨e, he, rfl⟩
  have hdg := dgOf_corr (length_sig_le s) hc hm
  have hq : (sig s).idxOf e.1 < signatureLimit :=
    lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hm) (length_sig_le s)
  rw [dgOf, dite_eq_left hq] at hdg
  have hD : digestH (hOf (withDig r Dg)) e.1 = truncateMessageDigest (δ ⟨_, hq⟩) := by
    rw [← hdg]
    rfl
  simp only [leavesAll, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hD] at hi hk
  exact ⟨_, hi, hk⟩

theorem covered_mono {R R' : Disclosures} (h : ∀ i κ, R i κ ⊆ R' i κ) {v : FullDigestView}
    (hv : Covered R v) : Covered R' v := fun κ ↦ h _ _ (hv κ)

open Classical in
/-- The covered event, with the data's public key. -/
def evA (r : Data) (G : Input → HashOutput) (Dg : Message → DigV)
    (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) (PublicKey × Forgery) u) (s : Log) : Bool :=
  evCov (withDig r Dg) s G p.2.2.2 && decide (p.2.2.1 = pkD (withDig r Dg))

theorem digestInput_mem_trace (f : Input → HashOutput) (d : Data) (F : Forgery) :
    digestInputX d F.message F.signature.randomness firstCall ∈
      outK (evalWithAnswerFn (QueryImpl.ofFn f) (verifier (pkD d, F))) := by
  rw [outK_verifier, mem_outOf, eval_verifier]
  exact digestInputs_mem' (QueryImpl.ofFn (extend f)) (pkD d) F.message F.signature firstCall

theorem card_ne_zero_enn (α : Type) [Fintype α] [Nonempty α] : (Fintype.card α : ℝ≥0∞) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

end Qrom.Sphincs
