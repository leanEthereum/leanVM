/-
  LeanVM.Guest.B1.Main.MainLocChk

  Where `main`'s evaluated block defines the values its completeness reads (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Main.MainCChk

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
    (atomsIn mFlatE).any (atomEqb (.const (.n (69 + v)) (word v 0)))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mLeafC_ok : (List.range 23).all (fun k =>
    (atomsIn mFlatE).any (atomEqb (.const (.n (441 + k)) (word 0 0)))) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Each block's stores. -/
theorem mStoresIn :
    (atomsIn (mPre ++ mMid ++ mPost)).filter (fun a => decide (a ∈ mStoresL)) =
      (List.range 256).map (fun v => .load (.n (69 + v)) (.n 68) v) ++ [.load (.n 420) (.n 419) 0] ∧
    (atomsIn mDa).filter (fun a => decide (a ∈ mStoresL)) =
      [.load (.n 399) (.n 387) 0, .load (.n 400) (.n 387) 1] ∧
    (atomsIn mDaZ).filter (fun a => decide (a ∈ mStoresL)) =
      [.load (.n 401) (.n 387) 0, .load (.n 402) (.n 387) 1] ∧
    (atomsIn mLeaf).filter (fun a => decide (a ∈ mStoresL)) =
      (List.range 23).map (fun k => .load (.n (441 + k)) (.n 437) k) ++
        [.load (.n 440) (.n 437) 23] ∧
    (atomsIn mAgg).filter (fun a => decide (a ∈ mStoresL)) = [] := by
  decide +kernel

theorem mem_storesIn {P : List Stmt} {L : List Atom}
    (h : (atomsIn P).filter (fun a => decide (a ∈ mStoresL)) = L) {a : Atom} (ha : a ∈ atomsIn P)
    (hs : a ∈ mStores) : a ∈ L := by
  rw [mStores_eq] at hs
  rw [← h]
  exact List.mem_filter.mpr ⟨ha, by simpa using hs⟩

set_option maxRecDepth 100000 in
theorem mDaZC_ok : (atomsIn mDaZ).any (atomEqb (.const (.n 401) (word 0 0))) = true ∧
    (atomsIn mDaZ).any (atomEqb (.const (.n 402) (word 0 0))) = true := by decide +kernel

/-- The own DA claim's digest, its chain on `mDa`'s atoms but the stores. -/
noncomputable def daSpec : ChainSpec := pairSpec (.n 390) (.n 391) (.n 392) (.n 394) (noStores mDa)

set_option maxRecDepth 100000 in
theorem daSpec_ok : daSpec.check (noStores mDa) = true ∧
    daSpec.outV (daSpec.nb - 1) 0 = .n 399 ∧ daSpec.outV (daSpec.nb - 1) 1 = .n 400 := by
  decide +kernel

end
end LeanVM.Guest.B1.Main
