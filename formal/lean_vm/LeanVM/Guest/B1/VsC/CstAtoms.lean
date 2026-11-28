/-
  LeanVM.Guest.B1.VsC.CstAtoms

  `check_stack_terminal`'s atoms before its assertion hold on an honest memory.
-/

module

public import LeanVM.Guest.B1.VsC.CstLoads
public import LeanVM.Guest.B1.VsC.LeafA

/-!
# `check_stack_terminal`'s atoms

`CstHyp.holds`: every atom before the final assertion holds. An atom needing no side condition by
its equation; a load that is not one of `eqtree`'s stores by `CstHyp.load`; `eqtree`'s stores by
`eqtreeAt_complete`, the slots' levels being `tq`'s own words (`tqW`), its reads not stores.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem cst_eqtree_eq : eqtreeT (.n 254) (.n 39) 0 255 6 = eqtreeAt (.n 254) (.n 39) 0 0 255 6 := rfl

theorem cst_eqReads : ∀ a ∈ eqReadsAt (.n 254) (.n 39) 0 0 255 6, a ∉ cstS := by
  have := cstAtomsOk_ok
  simp only [cstAtomsOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
  exact this.2

theorem mem_atomsB_eqtree {a : Atom} (h : Stmt.atom a ∈ eqtreeAt (.n 254) (.n 39) 0 0 255 6) : a ∈ cstAtomsB := by
  apply mem_atomsB; apply memB_ring
  rw [← cst_eqtree_eq] at h
  simp only [cstRing, List.mem_append, List.mem_cons]
  tauto

/-- `tq`'s word at `2^t - 2 + i`: level `t`'s entry `i`. -/
theorem tqEntry_level (layout : Layout) (x : List E) {t i : ℕ} (h1 : 1 ≤ t) (hi : i < 2 ^ t) :
    tqEntry layout x (2 ^ t - 2 + i) = (eqKernel (((x.drop (hgt layout 5)).take 6).take t)).getD i 0 := by
  have h2 : 2 ≤ 2 ^ t := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) h1
  have hlt : 2 ^ t + i < 2 ^ (t + 1) := by rw [pow_succ]; omega
  have hlog : Nat.log 2 (2 ^ t - 2 + i + 2) = t := by
    rw [show 2 ^ t - 2 + i + 2 = 2 ^ t + i by omega]
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt
  rw [tqEntry, hlog, show 2 ^ t - 2 + i + 2 - 2 ^ t = i by omega]

theorem holds_noSide {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a : Atom} (hg : Good rd S w σ a)
    (hn : needsSide a = false) : a.Holds rd σ :=
  atoms_holds (atoms := [a]) (fun b hb => by rw [List.mem_singleton.mp hb]; exact hg)
    (fun b hb hb' => by rw [List.mem_singleton.mp hb, hn] at hb'; cases hb') a List.mem_cons_self

section
variable {rd : Reader} {w : ℕ → E} {σ : Val} {layout : Layout} {link : LinkEnd}
  {chi r qPoint kOut kIn f g x z : List E} {rho lam rm : E} {outputs : List ColumnClaim} {c csel crow fp : ℕ}
variable (h : CstHyp rd w σ layout link chi r qPoint kOut kIn f g x z rho lam rm outputs c csel crow fp)
include h

/-- An atom before the assertion that is not a store holds. -/
theorem CstHyp.holdsNS {a : Atom} (ha : a ∈ cstAtomsB) (hS : a ∉ cstS) : a.Holds rd σ := by
  cases a with
  | load d p off => exact (h.load ha).2 (Or.inl hS)
  | _ =>
    have hA := cst_atomB ha
    simp only [cstAtomB, Bool.not_eq_true'] at hA
    exact holds_noSide (h.gB ha) hA

/-- **`eqtree`'s atoms hold.** -/
theorem CstHyp.eqHolds : ∀ a, Stmt.atom a ∈ eqtreeAt (.n 254) (.n 39) 0 0 255 6 → a.Holds rd σ := by
  obtain ⟨⟨bytecode, rows, hbl⟩, -, -, -, -, -, hchi24, hheights, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hxl, hpt, -⟩ := h.ctx
  have hL := h.hL
  have hq6 : hgt layout 5 + 6 ≤ layout.stackLog := by
    have := (block_placed hbl (b := 2) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 2) (by decide)).2.1, (blockKap_eq layout).2.2] at this
  have hrs6 : ((x.drop (hgt layout 5)).take 6).length = 6 := by
    rw [List.length_take, List.length_drop]; omega
  have b8 : σ (.n 39) = ptrAtV (cstBase chi.length c 8) := h.buf 8 (by norm_num)
  refine eqtreeAt_complete (by norm_num) (fun a ha => storesOf_isLoad ha) cst_eqReads
    (fun a ha hS => h.holdsNS (mem_atomsB_eqtree ha) hS) hrs6 (fun t ht => ?_) (fun t h1 h2 i hi => ?_)
  · rw [h.v254, loadHolds_mul_gen_pow, Nat.zero_add]
    have hv := hpt (hgt layout 5 + t) (by rw [List.length_append, List.length_replicate]; omega)
    convert hv using 1
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp only [List.getElem_take, List.getElem_drop]
    rw [List.getElem_append_left (by omega)]
  · rw [b8, Nat.zero_add]
    have hlen : 2 ^ t - 2 + i < 126 := by
      have : 2 ^ t ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h2
      have : 2 ^ t + i < 2 ^ (t + 1) := by rw [pow_succ]; omega
      have : 2 ^ (t + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at *; omega
    have hv := h.w8 (2 ^ t - 2 + i) (by rw [tqW, List.length_map, List.length_range]; exact hlen)
    convert hv using 1
    simp only [tqW, List.getElem_map, List.getElem_range]
    rw [tqEntry_level layout x h1 hi]

/-- **Every atom of `check_stack_terminal` before its assertion holds.** -/
theorem CstHyp.holds : ∀ a ∈ cstAtomsB, a.Holds rd σ := by
  intro a ha
  by_cases hS : a ∈ cstS
  · obtain ⟨d, p, off, rfl⟩ := storesOf_isLoad hS
    by_cases hE : Atom.load d p off ∈ eqStoresAt (.n 39) 0 255 6
    · exact h.eqHolds _ (eqStoresAt_mem hE)
    · exact (h.load ha).2 (Or.inr hE)
  · exact h.holdsNS ha hS

end

end
end LeanVM.Guest.B1.VsC
