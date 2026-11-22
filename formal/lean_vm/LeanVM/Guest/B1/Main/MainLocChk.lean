/-
  LeanVM.Guest.B1.Main.MainLocChk

  Where `main`'s evaluated block defines the values its completeness reads (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Main.MainCChk
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem mOrcStmts_ok : mOrcStmts.all (fun s => mFlatE.any (stmtEqb · s)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mDefAtoms_ok : mDefAtoms.all (fun a => (atomsIn mFlatE).any (atomEqb a)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mStores_eq : mStores = mStoresL := by decide +kernel

set_option maxRecDepth 100000 in
theorem mByte_ok : (List.range 256).all (fun v =>
    (atomsIn mFlatE).any (atomEqb (.const (.n ((val% «main» "s43.u0.s0#0") + v)) (word v 0)))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mLeafC_ok : (List.range 23).all (fun k =>
    (atomsIn mFlatE).any (atomEqb (.const (.n (420 + k)) (word 0 0)))) = true := by decide +kernel

/-- Membership in `mStoresL`, a load compared field by field (`atomEqb`), not by `DecidableEq Atom`. -/
def mStoreB : Atom → Bool
  | .load d p o => mStoresL.any (atomEqb (.load d p o))
  | _ => false

theorem mStoresL_loads : mStoresL.all (fun a => match a with | .load .. => true | _ => false) = true := by
  decide +kernel

theorem mStoreB_eq : (fun a => decide (a ∈ mStoresL)) = mStoreB := by
  funext a
  by_cases h : a ∈ mStoresL
  · have hl := List.all_eq_true.mp mStoresL_loads a h
    cases a <;> simp only [Bool.false_eq_true] at hl
    rename_i d p o
    simp only [h, decide_true, mStoreB]
    exact (List.any_eq_true.mpr ⟨_, h, by simp [atomEqb, vEqb_iff]⟩).symm
  · simp only [h, decide_false]
    cases a <;> simp only [mStoreB]
    rename_i d p o
    refine (Bool.eq_false_iff.mpr fun hb => h ?_).symm
    obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hb
    rwa [atomEqb_sound he]

set_option maxRecDepth 100000 in
/-- Each block's stores. -/
theorem mStoresIn :
    (atomsIn (mPre ++ mMid ++ mPost)).filter (fun a => decide (a ∈ mStoresL)) =
      (List.range 256).map (fun v => .load (.n ((val% «main» "s43.u0.s0#0") + v)) (.n (val% «main» "byte_bits")) v) ++ [.load (.n (val% «main» "s55#0")) (.n (val% «main» "written")) 0] ∧
    (atomsIn mDa).filter (fun a => decide (a ∈ mStoresL)) =
      [.load (.n (val% «main» "s50.t.s1#0")) (.n (val% «main» "own_da")) 0, .load (.n (val% «main» "s50.t.s1#0[1]")) (.n (val% «main» "own_da")) 1] ∧
    (atomsIn mDaZ).filter (fun a => decide (a ∈ mStoresL)) =
      [.load (.n (val% «main» "s50.e.s0#0")) (.n (val% «main» "own_da")) 0, .load (.n (val% «main» "s50.e.s1#0")) (.n (val% «main» "own_da")) 1] ∧
    (atomsIn mLeaf).filter (fun a => decide (a ∈ mStoresL)) =
      (List.range 23).map (fun k => .load (.n ((val% «main» "s63.t.s1.u0.s0#0") + k)) (.n (val% «main» "defer_stmt")) k) ++
        [.load (.n (val% «main» "leaf_value")) (.n (val% «main» "defer_stmt")) 23] ∧
    (atomsIn mAgg).filter (fun a => decide (a ∈ mStoresL)) = [] := by
  rw [mStoreB_eq]
  decide +kernel

theorem mem_storesIn {P : List Stmt} {L : List Atom}
    (h : (atomsIn P).filter (fun a => decide (a ∈ mStoresL)) = L) {a : Atom} (ha : a ∈ atomsIn P)
    (hs : a ∈ mStores) : a ∈ L := by
  rw [mStores_eq] at hs
  rw [← h]
  exact List.mem_filter.mpr ⟨ha, by simpa using hs⟩

set_option maxRecDepth 100000 in
theorem mDaZC_ok : (atomsIn mDaZ).any (atomEqb (.const (.n (val% «main» "s50.e.s0#0")) (word 0 0))) = true ∧
    (atomsIn mDaZ).any (atomEqb (.const (.n (val% «main» "s50.e.s1#0")) (word 0 0))) = true := by decide +kernel

/-- The own DA claim's digest, its chain on `mDa`'s atoms but the stores. -/
noncomputable def daSpec : ChainSpec := pairSpec (.n (val% «main» "root_0")) (.n (val% «main» "root_1")) (.n (val% «main» "z")) (.n (val% «main» "s50.t.s1#1[1]")) (noStores mDa)

set_option maxRecDepth 100000 in
theorem daSpec_ok : daSpec.check (noStores mDa) = true ∧
    daSpec.outV (daSpec.nb - 1) 0 = .n (val% «main» "s50.t.s1#0") ∧ daSpec.outV (daSpec.nb - 1) 1 = .n (val% «main» "s50.t.s1#0[1]") := by
  decide +kernel

end
end LeanVM.Guest.B1.Main
