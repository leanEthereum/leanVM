/-
  LeanVM.Guest.B1.Selectors.SharedWeight

  Every valid tree of `shared_selector_tables` on a length `g^n`, `n < 64`, weighs at most its
  frame's weight, `shared_selector_tables_loop0`'s `n / 4` iterations' bound and the partial
  nibble's bound.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTotal
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.Data.NameStrings

/-!
# `shared_selector_tables` within its weight

`ss_weightLeOn`: `ss_totalLeOn` for a weight `ω`, `shared_selector_tables_loop0` within `K9` an
iteration (`Budget.LoopW`) and the partial nibbles within `Ksp` (`WeightLe`): at most
`ω "shared_selector_tables" + max (ω "shared_selector_tables_loop0") (15·K9) + Ksp` (a loop not
entered weighs its frame).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Core.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **`shared_selector_tables` is within its weight**: every valid tree on a length `g^n`, `n < 64`. -/
theorem ss_weightLeOn (ω : String → ℕ) (K9 Ksp : ℕ) (h9 : Budget.LoopW ω
    name% «shared_selector_tables_loop0» K9)
    (hsp : ∀ j < 4, WeightLe coreProgram ω (lName "sel_partial_nibble" j) (fun _ ↦ Ksp)) :
    ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = "shared_selector_tables" →
      (∃ n < 64, args.getD 3 0 = gen ^ n) → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.weight ω ≤ ω "shared_selector_tables" + 15 * K9 + Ksp := by
  intro rd t args rets hname ⟨n, hn, h3⟩ hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hname
  subst hname
  obtain ⟨hcalls, -, e37, e51, e52⟩ := ss_node hv hb hn h3
  have hq15 : n / 4 ≤ 15 := by omega
  have hw' := Budget.node_weight_le ω
    (fun c ↦ if c.f = name% «shared_selector_tables_loop0» then n / 4 * K9 else Ksp) [fun _ ↦ True,
        fun _ ↦ True] hv hb hcalls (by simp [ssCalls]) (kidsT_true2 _ _)
    (fun c Q hc ht t rets' htn htv htb _ ↦ ?_)
  · refine hw'.trans ?_
    simp only [Budget.callsW, ssCalls, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      lName_sel_ne (show n % 4 < 4 by omega), ↓reduceIte, add_zero]
    have h1 : (if decide (σ (.n 51) ≠ 0) = true then n / 4 * K9 else 0) ≤ 15 * K9 := by
      split
      · have := Nat.mul_le_mul_right K9 hq15; omega
      · omega
    omega
  · simp only [ssCalls, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [decide_eq_true_eq] at ht
      have hq0 : n / 4 ≠ 0 := by
        intro h0
        apply ht; rw [e51, h0, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
      have := h9.at htn htv htb (e := n / 4)
        (by simp only [List.map_cons, List.map_nil, List.getD_cons_zero, e52])
        (by simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, e37])
        hq0 (by omega)
      simpa using this
    · have := hsp (n % 4) (by omega) rd t _ rets' htn htv htb
      simpa [lName_sel_ne (show n % 4 < 4 by omega)] using this

end
end LeanVM.Guest.B1.Tables
