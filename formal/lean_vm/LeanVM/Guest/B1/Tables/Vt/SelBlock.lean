/-
  LeanVM.Guest.B1.Tables.Vt.SelBlock

  What a table block's selector statements give: its eq weight is `eqAbove` at its placement.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SelBlocks
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# A table block's selector

`vt_selblock`: from a table block's statements (`vtSelT`), its table's shared tables (`vt_shared`)
and its certified offset (`vt_sort`), the block's eq weight is `eqAbove ⟨τ_t, offset⟩` at the bus
point, its copy is it, and the running `selector_sum` grows by it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The running sum after a block: the eq weight at the side's first block, else the sum. -/
def vtSelSum (w t : ℕ) (prev : Option ℕ) : ℕ := if prev.isNone then vtSelE w t else vtSelE w t + 2

/-- The block's copy of its eq weight. -/
def vtSelCopy (w t : ℕ) (prev : Option ℕ) : ℕ :=
  if prev.isNone then vtSelE w t + 2 else vtSelE w t + 3

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **A table block's selector.** -/
theorem vt_selblock {σ : Val} (h : VtH Lm.read σ) {w b t pos : ℕ} {prev : Option ℕ}
    (hcheck : stmtsEqb (vtSelT w b t prev)
      ((vtAt pos).take (vtSelT w b t prev).length) = true)
    {point : List E} {d τ : ℕ} (hpl : point.length = d + τ) (hd34 : d + τ ≤ 34)
    (hdv : σ (.n (vtShLen t)) = gen ^ d)
    (hrun : RunTables Lm.read (σ (.n (vtEqV t))) (σ (.n (vtGV t))) d
      (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take d))
    {off : ℕ} (hoff : σ (.n (vtBoffV b)) = gen ^ off) (hob : off < 2 ^ 62) :
    σ (.n (vtSelE w t)) = Placement.eqAbove ⟨τ, off⟩ point ∧
      σ (.n (vtSelCopy w t prev)) = σ (.n (vtSelE w t)) ∧
      σ (.n (vtSelSum w t prev)) = (match prev with | none => 0 | some p => σ (.n p)) +
        σ (.n (vtSelE w t)) := by
  obtain ⟨k, hs⟩ := h.sliceAt pos _ hcheck
  simp only [vtSelT, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, List.map_cons,
    List.map_nil] at hs
  obtain ⟨-, -, hd, qE, hrest⟩ := hs
  simp only [Atom.Holds] at qE
  have hq := e_add_eq_zero_iff.mp qE
  -- the arm
  obtain ⟨j, hj, hjv, hrel⟩ := hd
  have hj34 : j < 34 := by simpa [vtBstNames] using hj
  rw [hdv, ← gen_pow_eq_ofK] at hjv
  obtain rfl := gen_pow_inj (by omega) (by omega) hjv
  simp only [vtBstNames, List.getElem_map, List.getElem_range] at hrel
  have hb := block_selector_tab_holds _ hj34 _ hμ Lm _ _ hrel
  simp only [BlockSelTabOut] at hb
  obtain ⟨bs, hbl, -, hout⟩ := hb
  obtain ⟨he, hg⟩ := hout _ _ _ (by simp; omega) (by simp; omega)
    (by simp [gSquaresList]; omega) hrun
  rw [vt_bitsPow_sq hbl (by omega)] at hg
  have hoff' : gen ^ (2 ^ τ * vtBitsV bs d) = gen ^ off := by rw [← hoff, ← hq, hg]
  have e := vt_offset_bits (by omega) hob hoff'
  refine ⟨by rw [he, vt_eqAbove hbl (by omega), ← e], ?_, ?_⟩
  · cases prev with
    | none =>
      simp only [vtSelTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hrest
      simp only [vtSelCopy, Option.isNone_none, ↓reduceIte]; exact hrest
    | some p =>
      simp only [vtSelTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hrest
      simp only [vtSelCopy, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]; exact hrest.2
  · cases prev with
    | none => simp [vtSelSum]
    | some p =>
      simp only [vtSelTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hrest
      simp only [vtSelSum, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]; exact hrest.1

end

end
end LeanVM.Guest.B1.Tables
