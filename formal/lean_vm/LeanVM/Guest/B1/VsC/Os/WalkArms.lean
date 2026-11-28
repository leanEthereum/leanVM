/-
  LeanVM.Guest.B1.VsC.Os.WalkArms

  `open_stacked`'s body walks every statement, from its relational form.
-/

module

public import LeanVM.Guest.B1.VsC.Os.WalkD
public import LeanVM.Guest.B1.Whir.RateFree
public import LeanVM.Guest.B1.Whir.FinishSplit

/-!
# `open_stacked`'s walk

`flatBody_all`: every arm's body before its return is atoms, calls, `match`es of quiet arms and
dispatches, each with fewer than `2^64 - 1` arms (one `decide +kernel` an arm). `osBody_walk`:
where the bus era's relational form holds of the body at a rate (`AllOk`), the body walks every
statement to its return, the dispatches and `match`es taking the arms the selectors name, and
every event holds.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

/-- A body flat with `match`es and dispatches, its arms few. -/
def FlatBody (ss : List Stmt) : Bool := ss.all fun s ↦ s.flatD && s.armsShort

set_option maxRecDepth 100000 in
theorem flatBody_0 : FlatBody (osBodyA (osCfg 0)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_1 : FlatBody (osBodyA (osCfg 1)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_2 : FlatBody (osBodyA (osCfg 2)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_3 : FlatBody (osBodyA (osCfg 3)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_4 : FlatBody (osBodyA (osCfg 4)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_5 : FlatBody (osBodyA (osCfg 5)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_6 : FlatBody (osBodyA (osCfg 6)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_7 : FlatBody (osBodyA (osCfg 7)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_8 : FlatBody (osBodyA (osCfg 8)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_9 : FlatBody (osBodyA (osCfg 9)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_10 : FlatBody (osBodyA (osCfg 10)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_11 : FlatBody (osBodyA (osCfg 11)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_12 : FlatBody (osBodyA (osCfg 12)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_13 : FlatBody (osBodyA (osCfg 13)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem flatBody_14 : FlatBody (osBodyA (osCfg 14)) = true := by decide +kernel

theorem flatBody_all (m : ℕ) (hm : m < 15) : FlatBody (osBodyA (osCfg m)) = true := by
  interval_cases m
  · exact flatBody_0
  · exact flatBody_1
  · exact flatBody_2
  · exact flatBody_3
  · exact flatBody_4
  · exact flatBody_5
  · exact flatBody_6
  · exact flatBody_7
  · exact flatBody_8
  · exact flatBody_9
  · exact flatBody_10
  · exact flatBody_11
  · exact flatBody_12
  · exact flatBody_13
  · exact flatBody_14

theorem osBodyA_dropLast (c : OsCfg) : osBodyA c = (osBody c).dropLast := by
  rw [osBody_eq, List.dropLast_concat]

theorem osBodyA_rate (m ri : ℕ) : osBodyA (osCfg m) = osBodyA (osCfgR m ri) := by
  rw [osBodyA_dropLast, osBodyA_dropLast, osBody_rate m ri]

/-- A body whose selectors are all the rate's selector `.n osRate`. -/
def SelBody (ss : List Stmt) : Bool := ss.all fun s ↦ s.selV.all (· == .n osRate)

set_option maxRecDepth 100000 in
theorem selBody_0 : SelBody (osBodyA (osCfg 0)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_1 : SelBody (osBodyA (osCfg 1)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_2 : SelBody (osBodyA (osCfg 2)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_3 : SelBody (osBodyA (osCfg 3)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_4 : SelBody (osBodyA (osCfg 4)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_5 : SelBody (osBodyA (osCfg 5)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_6 : SelBody (osBodyA (osCfg 6)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_7 : SelBody (osBodyA (osCfg 7)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_8 : SelBody (osBodyA (osCfg 8)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_9 : SelBody (osBodyA (osCfg 9)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_10 : SelBody (osBodyA (osCfg 10)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_11 : SelBody (osBodyA (osCfg 11)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_12 : SelBody (osBodyA (osCfg 12)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_13 : SelBody (osBodyA (osCfg 13)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem selBody_14 : SelBody (osBodyA (osCfg 14)) = true := by decide +kernel

theorem selBody_all (m : ℕ) (hm : m < 15) : SelBody (osBodyA (osCfg m)) = true := by
  interval_cases m
  · exact selBody_0
  · exact selBody_1
  · exact selBody_2
  · exact selBody_3
  · exact selBody_4
  · exact selBody_5
  · exact selBody_6
  · exact selBody_7
  · exact selBody_8
  · exact selBody_9
  · exact selBody_10
  · exact selBody_11
  · exact selBody_12
  · exact selBody_13
  · exact selBody_14

/-- **The body's events are the same on valuations agreeing on the rate's selector.** -/
theorem osBody_evs_congr {m ri : ℕ} (hm : m < 15) {σ σ' : Val} (h : σ (.n osRate) = σ' (.n osRate)) :
    (osBodyA (osCfgR m ri)).flatMap (fdEvs σ) = (osBodyA (osCfgR m ri)).flatMap (fdEvs σ') := by
  have hs := selBody_all m hm
  rw [osBodyA_rate m ri] at hs
  refine flatMap_fdEvs_congr fun s hsm x hx ↦ ?_
  have := List.all_eq_true.mp hs s hsm
  rw [hx] at this
  simp only [Option.all_some, beq_iff_eq] at this
  rw [this]; exact h

/-- **The body walks**, from its relational form at the rate `ri`: every statement, to its return,
every event holding. -/
theorem osBody_walk {m ri : ℕ} (hm : m < 15) {C : CallRel} {rd : Reader} {σ : Val}
    (h : AllOk C rd σ (osBodyA (osCfgR m ri))) :
    walk σ (osBody (osCfg m)) = .ret ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ)) (osBodyRet (osCfgR m ri)) ∧
      ∀ e ∈ (osBodyA (osCfgR m ri)).flatMap (fdEvs σ), e.Holds rd σ := by
  have hf := flatBody_all m hm
  rw [osBodyA_rate m ri] at hf
  simp only [FlatBody, List.all_eq_true, Bool.and_eq_true] at hf
  have h1 : (osBodyA (osCfgR m ri)).all Stmt.flatD = true := List.all_eq_true.mpr fun s hs ↦ (hf s hs).1
  have h2 : (osBodyA (osCfgR m ri)).all Stmt.armsShort = true := List.all_eq_true.mpr fun s hs ↦ (hf s hs).2
  refine ⟨?_, fdEvs_holds_all h2 h⟩
  rw [osBody_rate m ri, osBody_eq]
  exact walk_flatD σ _ _ h1 (selOk_of_allOk h2 h)

end
end LeanVM.Guest.B1.Whir
