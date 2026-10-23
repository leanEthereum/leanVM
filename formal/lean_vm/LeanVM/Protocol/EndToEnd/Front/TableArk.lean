/-
  LeanVM.Protocol.EndToEnd.Front.TableArk

  The table sumcheck's components, read off as statements about their relations: the batching
  challenge's escape from the bus seam, the rounds' family, and the final values' hand-over to
  the table seam.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.BusSpec
public import LeanVM.Protocol.TableSumcheck

/-!
# The table sumcheck's relations

The table sumcheck phase's security on the typed framework (`tableSumcheckSecurity`,
`LeanVM.Protocol.TableSumcheck`) appends three securities, the first and the last of them public
(`xiSecurity`, `finalValuesSecurity`). This module reads them as doom transitions:

* `xi_escape`: the batching challenge `ξ` escapes doom on the bus seam with probability at most
  `L₀ · (B + 2) / |E|`;
* `tableFamily_sound`: the rounds' family (`Sumcheck.family` of `tableSummand`) is sound, its
  invariant being the side condition no challenge changes;
* `finalValues_keep`: values that pass the final check carry doom on the rounds' last stage to doom
  on the table seam at `tableOut`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.TableSumcheck
open CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

variable (I : M3Instance)

/-- The error of the batching challenge over at most `L₀` candidates: `L₀ · (B + 2) / |E|`. -/
noncomputable def xiError (L₀ : ℕ) : ℝ≥0∞ :=
  L₀ * ((((I.B + 3 - 1 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)

open Classical in
/-- **The batching challenge escapes** doom on the bus seam with probability at most
`L₀ · (B + 2) / |E|`. -/
theorem xi_escape {L₀ : ℕ} {C : Set (∀ i, TheOracle I i)} (hfin : C.Finite)
    (hcard : C.ncard ≤ L₀) (s : I.Stmt × BusOut I) (hpre : RelDoom C (Seam.bus I) s) :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun ξ ↦ ¬ RelDoom C
      (Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I))
      (start I s ξ (powerBatch (claimed I s) ξ))).card : ℝ≥0∞) ≤ xiError I L₀ :=
  draw_escape_le (xiSecurity I) hfin hcard hpre rfl

/-- The rounds' family. -/
noncomputable abbrev tableFamily : SumcheckRound.Family E (Data I) (TheOracle I) Unit 3 :=
  Sumcheck.family (tableSummand I) Sumcheck.unitWeights nodes (side I)

/-- The rounds' family is consistent (the summand has degree at most three in each variable). -/
theorem tableFamily_consistent (hd : I.d ≤ 2) : (tableFamily I).Consistent I.τmax :=
  (Sumcheck.family_honest (tableSummand I) Sumcheck.unitWeights nodes (side I)
    (tableSummand_degree I hd) nodes_injective).toConsistent

/-- The rounds' family is sound: its invariant is the side condition, which no challenge
changes. -/
theorem tableFamily_sound : (tableFamily I).Sound I.τmax :=
  fun _ _ _ _ h ↦ (Nat.card_eq_zero.mpr (Or.inl ⟨fun x ↦ h x.2⟩)).trans_le (Nat.zero_le 3)

/-- **The final values keep doom**: values that pass the final check carry doom on the rounds'
last stage to doom on the table seam. -/
theorem finalValues_keep {C : Set (∀ i, TheOracle I i)}
    {s : SumcheckRound.Stmt (Data I) E I.τmax}
    (hpre : RelDoom C (SumcheckRound.rel (tableFamily I) I.τmax) s) (v : Vector E I.tableColumns)
    (hc : Sumcheck.finalCheck (tableSummand I) s v = true) :
    RelDoom C (Seam.table I) (tableOut I s v) :=
  say_keep (finalValuesSecurity I) hpre v hc

end
end LeanVM.Protocol.EndToEnd.Front
