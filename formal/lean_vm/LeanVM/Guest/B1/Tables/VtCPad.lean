/-
  LeanVM.Guest.B1.Tables.VtCPad

  `verify_tables`' pure callees: the selector, index and sumcheck loops and the padding weights
  are `PureIn`, and a dispatched `padding_weight` arm is complete, placed.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesFront
public import LeanVM.Guest.B1.Tables.StraightAt

/-!
# `verify_tables`' pure callees, placed

Every loop `verify_tables` calls and its 29 `padding_weight` arms have no `alloc`, `allocDyn` or
`frameAddr` in their call subtrees (`pure_sel`, `pure_idx`, `pure79`, `pure80`, `pure_pw`, by
kernel evaluation), so their completeness lifts through `completeAt_of_rel_lowD`. For the arms
that is `pw_completeAtD`: on a point holding at least `τ` words, `padding_weight__L{τ}` of
`n ≤ 2^τ` rows returns the padding weight over its first `τ` coordinates with `lead` and `rest`,
which the guest's assertions accept once `log2Ceil n = τ` (`pw_lead_rest`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The pure callees -/

/-- `PureIn` by evaluation. -/
private noncomputable def vtcPureCheck (S : List String) : Bool :=
  S.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList S fn.body
    | none => true

private theorem vtc_pureIn {S : List String} (h : vtcPureCheck S = true) : coreProgram.PureIn S := by
  intro g hg fn hfn
  have := List.all_eq_true.mp h g hg
  rw [hfn] at this
  exact this

set_option maxRecDepth 100000 in
theorem pure_sel : coreProgram.PureIn selNames := vtc_pureIn (by decide +kernel)

set_option maxRecDepth 100000 in
theorem pure_idx : coreProgram.PureIn ["__loop14", "__loop16"] := vtc_pureIn (by decide +kernel)

set_option maxRecDepth 100000 in
theorem pure79 : coreProgram.PureIn ["__loop79", "sumcheck_round4"] := vtc_pureIn (by decide +kernel)

set_option maxRecDepth 100000 in
theorem pure80 : coreProgram.PureIn ["__loop80"] := vtc_pureIn (by decide +kernel)

set_option maxRecDepth 100000 in
theorem pure_pw : coreProgram.PureIn pwNames := vtc_pureIn (by decide +kernel)

/-! ## The padding weights -/

/-- A dispatched `padding_weight` arm is complete. -/
theorem pw_dispatch_complete {rd : Reader} {rows zeta : E} {rets : List E} (j : ℕ)
    (hj : j < pwNames.length) (h : MeaningPaddingWeight j rd [rows, zeta] rets) :
    coreProgram.Rel rd (pwNames[j]'hj) [rows, zeta] rets := by
  have hj' : j < 29 := by simpa [pwNames] using hj
  interval_cases j
  · exact (padding_weight_L0_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L1_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L2_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L3_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L4_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L5_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L6_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L7_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L8_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L9_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L10_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L11_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L12_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L13_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L14_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L15_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L16_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L17_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L18_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L19_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L20_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L21_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L22_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L23_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L24_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L25_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L26_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L27_iff rd rows zeta rets).mpr h
  · exact (padding_weight_L28_iff rd rows zeta rets).mpr h

/-- **A dispatched `padding_weight` arm is complete, placed**: arm `j` on `n ≤ 2^j` rows and a
point `zeta` holding `zs`, `j ≤ |zs|`, on every memory holding `Lin`, returns the padding weight
over the point's first `j` coordinates, `lead` and `rest`. -/
theorem pw_completeAtD {fs : String → ℕ} {cert : String → V → ℕ} (j : ℕ) (hj : j < pwNames.length)
    {k : ℕ} {Lin : Main.Layout} {zeta : E} {zs : List E} {n : ℕ} (hn : n ≤ 2 ^ j) (hzl : j ≤ zs.length)
    (hz : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd zeta zs) :
    CompleteAtD fs cert k (pwNames[j]'hj) Lin [eOfNat n, zeta]
      (Returns [paddingWeight (zs.take j) n, pwLead j n, pwRest j n]) :=
  completeAt_of_rel_lowD pure_pw (List.getElem_mem hj) k fun rd hlow hL rd' hag =>
    pw_dispatch_complete j hj ⟨n, zs.take j, hn, rfl, by simp only [List.length_take]; omega,
      fun i hi => by
        simp only [List.length_take] at hi
        rw [List.getElem_take]
        exact loadHolds_agree hag (hz rd hlow hL i (by omega)) (addr_in_region hz hlow hL (by omega)),
      rfl⟩

/-- The guest's assertions on the arm's results, `lead = 1` and `rest ≠ 0`, hold once the rows'
`log2Ceil` is the arm's. -/
theorem pw_lead_rest {j n : ℕ} (hj : j < 29) (hl : log2Ceil n = j) : pwLead j n = 1 ∧ pwRest j n ≠ 0 :=
  (lead_rest_iff (by omega) (log2Ceil_le_iff.mp hl.le)).mpr hl

end
end LeanVM.Guest.B1.VerifySub
