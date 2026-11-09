/-
  LeanVM.Guest.B1.VerifySub.H.Vals

  The honest valuation on the oracle `vsW`: the allocations' values are the buffers' pointers,
  the calls' returns the callees' results.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Own

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- An allocation's value is the oracle's. -/
theorem vs_alloc_vals (hl : args.length = 6) :
    ∀ x ∈ vsCPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz, vsσ rd w args x.1 = w x.1.idx := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  have hg := vs_goodS (rd := rd) (w := w) hl hs
  cases s with
  | atom a =>
    cases a with
    | hint hk =>
      cases hk with
      | alloc d n =>
        simp only [LeanVM.Guest.Memory.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx; exact hg
      | allocDyn d n =>
        simp only [LeanVM.Guest.Memory.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx; exact hg
      | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx
    | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx
  | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx

theorem vs_alloc_fst : (vsCPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.1) =
    vsAllocVars.map V.n := by
  rw [vs_allocs, List.map_map]
  rfl

/-- An allocated value is the oracle's. -/
theorem vs_alloc_var (hl : args.length = 6) {v : ℕ} (hv : v ∈ vsAllocVars) :
    vsσ rd w args (.n v) = w v := by
  have : V.n v ∈ (vsCPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.1) := by
    rw [vs_alloc_fst]; exact List.mem_map.mpr ⟨v, hv, rfl⟩
  obtain ⟨x, hx, e⟩ := List.mem_map.mp this
  have := vs_alloc_vals (rd := rd) (w := w) hl x hx
  rw [e] at this
  exact this

/-- A statement returning the value `v`. -/
def retsHas (v : ℕ) : Stmt → Bool
  | .call _ _ rets => rets.contains (.n v)
  | .dispatch _ _ _ rets => rets.contains (.n v)
  | _ => false

theorem vs_retsHas : ∀ j < 13, ∀ k < (vsRetVars.getD j []).length,
    vsCPre.any (retsHas ((vsRetVars.getD j []).getD k 0)) = true := by decide +kernel

/-- A call's return is the oracle's. -/
theorem vs_ret_var (hl : args.length = 6) {v : ℕ} (hv : vsCPre.any (retsHas v) = true) :
    vsσ rd w args (.n v) = w v := by
  obtain ⟨s, hs, hr⟩ := List.any_eq_true.mp hv
  have hg := vs_goodS (rd := rd) (w := w) hl hs
  cases s with
  | call f a rets =>
    simp only [retsHas, List.contains_iff_mem] at hr
    exact hg _ hr
  | dispatch x fs a rets =>
    simp only [retsHas, List.contains_iff_mem] at hr
    exact hg _ hr
  | _ => simp [retsHas] at hr

/-- **The allocations' pointers.** -/
theorem vs_alloc_ptr (hl : args.length = 6) (bs : List ℕ) (outs : List (List E × Main.Layout))
    {i : ℕ} (hi : i < 13) :
    vsσ rd (vsW bs outs) args (.n (vsAllocVars.getD i 0)) = ofK (addressOfIndex (bs.getD i 0)) := by
  rw [vs_alloc_var hl (vsAllocVars_idx i hi).1, vsW_alloc bs outs hi]

/-- **The calls' returns.** -/
theorem vs_ret_val (hl : args.length = 6) (bs : List ℕ) (outs : List (List E × Main.Layout))
    {j k : ℕ} (hj : j < 13) (hk : k < (vsRetVars.getD j []).length) :
    vsσ rd (vsW bs outs) args (.n ((vsRetVars.getD j []).getD k 0)) =
      (outs.getD j ([], [])).1.getD k 0 := by
  rw [vs_ret_var hl (vs_retsHas j hj k hk), vsW_ret bs outs hj hk]

end
end LeanVM.Guest.B1.VerifySub
