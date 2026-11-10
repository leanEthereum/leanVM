/-
  LeanVM.Guest.B1.VerifySub.C.Hon

  `verify_sub`'s honest valuation on a memory: its evaluation list evaluated from the arguments,
  loads read from the memory, allocations' and callees' words from an oracle.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Flat
public import LeanVM.Guest.B1.Fwd.FlatIte
public import LeanVM.Guest.B1.Fwd.NotStored
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.Basic
public import LeanVM.Guest.B1.Terminal.KidsDep

/-!
# The honest valuation

`vsσ rd w args`: `vsEvL` evaluated (`Fwd.ev`) on the memory `rd` and the oracle `w` from the
arguments `args` (`vs_chk'`: `1959` values). `verify_sub` has no `ite` and no `assertNe`, so each
statement of `vsCPre` satisfies its equations (`GoodS`) with the stores `vsSL` (`vs_goodS`); the
parameters are the arguments (`vsC_param`), an allocation's or a callee's value is the oracle's
(`vs_w`). `vs_goodL`: the equations of a slice, by its position.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables

@[expose] public section

/-- A statement other than an `assertNe`. -/
def vsNoNeB : Stmt → Bool
  | .atom (.assertNe _ _ _) => false
  | _ => true

theorem vs_fixNe_of_noNe {s : Stmt} (h : vsNoNeB s = true) : fixNe s = s := by
  cases s with
  | atom a => cases a <;> simp_all [vsNoNeB, fixNe]
  | _ => rfl

theorem vs_noNe : vsCPre.all vsNoNeB = true := by decide +kernel

theorem vs_notIte : vsCPre.all notIteB = true := by decide +kernel

/-- The stores of the evaluation list. -/
def vsSL : List Atom := storesOf 6 vsEvL

/-- The pointers of `verify_sub`'s stores: `table_rows`, `dims_g`, `kappa_base`, `fp_w`, the ring
map's challenges, `c_table`, the deferred claim's cells. -/
def vsStorePtrs : List ℕ := [26, 71, 83, 335, 847, 848, 5]

theorem vsSL_ptrs : vsSL.all (ptrInB vsStorePtrs) = true := by decide +kernel

/-- `a ∉ vsSL` by the read's numbers, its pointer first (`Fwd.notStoredB`). -/
instance (priority := high) instDecidableNotMemVsSL (a : Atom) : Decidable (a ∉ vsSL) :=
  decidable_of_iff _ (notStoredB_iff vsSL_ptrs a)

theorem vs_chk' : chk 6 vsEvL = some 1959 := by decide +kernel

/-- **The honest valuation** of `verify_sub`. -/
noncomputable def vsσ (rd : Reader) (w : ℕ → E) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd w args vsEvL)

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vs_good (hl : args.length = 6) : ∀ s ∈ vsEvL, GoodS rd vsSL w (vsσ rd w args) s := by
  have h := (ev_spec rd w vsEvL args (by rw [hl]; exact vs_chk')).2.2
  rw [hl] at h
  exact h

theorem vsC_param (hl : args.length = 6) {i : ℕ} (hi : i < 6) :
    vsσ rd w args (.n i) = args.getD i 0 :=
  ev_params rd w (by rw [hl]; exact vs_chk') (by rw [hl]; exact hi)

theorem vs_mem_slice {n : ℕ} {blk : List Stmt}
    (heq : tbStmtsEqb blk ((vsCPre.drop n).take blk.length) = true) {s : Stmt} (hs : s ∈ blk) :
    s ∈ vsCPre := by
  rw [tbStmtsEqb_sound heq] at hs
  exact List.mem_of_mem_drop (List.mem_of_mem_take hs)

/-- **A statement's equations.** -/
theorem vs_goodS (hl : args.length = 6) {s : Stmt} (hs : s ∈ vsCPre) :
    GoodS rd vsSL w (vsσ rd w args) s := by
  have hn := List.all_eq_true.mp vs_noNe s hs
  have hi := List.all_eq_true.mp vs_notIte s hs
  have h := vs_good (rd := rd) (w := w) hl (fixNe s)
    (List.mem_map_of_mem (mem_flatIte_of (fun c z n e ↦ by subst e; simp [notIteB] at hi) hs))
  rwa [vs_fixNe_of_noNe hn] at h

/-- The equations of a slice of the body, by its position. -/
theorem vs_goodL (hl : args.length = 6) {n : ℕ} {blk : List Stmt}
    (heq : tbStmtsEqb blk ((vsCPre.drop n).take blk.length) = true) :
    ∀ s ∈ blk, GoodS rd vsSL w (vsσ rd w args) s :=
  fun _ hs ↦ vs_goodS hl (vs_mem_slice heq hs)

/-- The values the oracle defines: an allocation's, a call's returns. -/
def vsDefW : Stmt → List V
  | .atom (.hint (.alloc d _)) => [d]
  | .atom (.hint (.allocDyn d _)) => [d]
  | .call _ _ r => r
  | .dispatch _ _ _ r => r
  | _ => []

/-- The values the oracle defines, in order: the allocations and the callees' returns. -/
def vsWVars : List ℕ :=
  [6, 25, 26, 64, 71, 72, 83, 253, 254, 274, 275, 276, 304, 305, 306, 307, 308, 309, 310, 313,
    314, 315, 316, 317, 318, 319, 320, 329, 335, 562, 563, 564, 565, 566, 567, 568, 569, 570, 573,
    574, 575, 576, 577, 578, 579, 580, 581, 582, 584, 585, 590, 591, 592, 593, 594, 595, 596, 847,
    848, 1361, 1931, 1932, 1933, 1934, 1935]

theorem vs_defW : vsCPre.flatMap vsDefW = vsWVars.map V.n := by decide +kernel

theorem vs_goodS_defW {s : Stmt} {σ : Val} (hg : GoodS rd vsSL w σ s) {v : V} (hv : v ∈ vsDefW s) :
    σ v = w v.idx := by
  cases s with
  | atom a =>
    cases a with
    | hint h =>
      cases h with
      | alloc d _ =>
        simp only [vsDefW, List.mem_singleton] at hv
        subst hv; exact hg
      | allocDyn d _ =>
        simp only [vsDefW, List.mem_singleton] at hv
        subst hv; exact hg
      | _ => simp [vsDefW] at hv
    | _ => simp [vsDefW] at hv
  | call f a r => exact hg v hv
  | dispatch x fs a r => exact hg v hv
  | _ => simp [vsDefW] at hv

/-- **An allocation's or a callee's value is the oracle's.** -/
theorem vs_w (hl : args.length = 6) {a : ℕ} (ha : a ∈ vsWVars) : vsσ rd w args (.n a) = w a := by
  have hm : V.n a ∈ vsCPre.flatMap vsDefW := by rw [vs_defW]; exact List.mem_map_of_mem ha
  obtain ⟨s, hs, hv⟩ := List.mem_flatMap.mp hm
  exact vs_goodS_defW (vs_goodS hl hs) hv

end

end
end LeanVM.Guest.B1.VerifySub
