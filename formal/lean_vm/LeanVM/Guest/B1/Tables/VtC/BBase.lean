/-
  LeanVM.Guest.B1.Tables.VtC.BBase

  Tools for `verify_tables`' completeness on its bus sides (statements `769 ..< 2589`): the
  equations of its pure atoms and its weight reads as a predicate the soundness's algebra can be
  replayed on (`VtP`), and the statements' relations from the honest valuation: reads, range
  checks, dispatches, equality checks.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Hon
public import LeanVM.Guest.B1.Tables.Vt.SelMath

/-!
# Tools for the bus sides

`VtP rd σ`: every atom of `vtPre` that `okP` selects (constants, sums, copies, products of
older values, reads of the bus weights `fp_w` below `16`) holds; `VtP.atom` reads one with the
selection decided. `vtP_honest`: the honest valuation satisfies it when the memory holds `16`
weights at `fp_w`. The soundness's algebraic lemmas, stated on `VtH`, replay on `VtP`.

`vtB_readM`: a read of a word the memory holds; `vtB_retsM`: a dispatch's returns, the oracle's;
`vtB_blockA`: a block holds when its statements beyond evaluation do.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- The atoms `VtP` keeps: constants, sums, copies, products of older values, reads through
`fp_w` (`.n 13`) below `16`. -/
def okP : Atom → Bool
  | .load _ p off => decide (p = .n 13) && decide (off < 16)
  | .const .. => true
  | .add .. => true
  | .copy .. => true
  | .mul d x y => decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | _ => false

/-- **The kept atoms of `vtPre` hold.** -/
def VtP (rd : Reader) (σ : Val) : Prop :=
  ∀ (n : ℕ) (a : Atom), tbStmtsEqb [.atom a] ((vtPre.drop n).take 1) = true → okP a = true →
    a.Holds rd σ

theorem VtP.atom {rd : Reader} {σ : Val} (h : VtP rd σ) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vtPre.drop n).take 1) = true) (hok : okP a = true := by decide) :
    a.Holds rd σ :=
  h n a heq hok

/-- `VtP.atom` at `vtAt`, what a kernel check evaluates fast. -/
theorem VtP.atomAt {rd : Reader} {σ : Val} (h : VtP rd σ) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vtAt n).take 1) = true) (hok : okP a = true := by decide) :
    a.Holds rd σ :=
  h n a (vtPre_drop n ▸ heq) hok

/-- No store goes through `fp_w`. -/
theorem vtSL_no13 : vtSL.all (fun a ↦ match a with
    | .load _ p _ => !decide (p = .n 13)
    | _ => true) = true := by decide +kernel

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **The honest valuation satisfies `VtP`.** -/
theorem vtP_honest (hl : args.length = 20) {W : List E} (hW16 : 16 ≤ W.length)
    (hW : TbReadsAt rd (vtσ rd w args (.n 13)) W) : VtP rd (vtσ rd w args) := by
  intro n a heq hok
  have hs : Stmt.atom a ∈ vtPre := vt_mem_slice (blk := [_]) heq List.mem_cons_self
  have hg := vt_goodS (rd := rd) (w := w) hl hs
  rw [fixNe_atom] at hg
  cases a with
  | load d p off =>
    simp only [okP, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, hoff⟩ := hok
    have hS : Atom.load d (.n 13) off ∉ vtSL := by
      intro hm
      have := List.all_eq_true.mp vtSL_no13 _ hm
      simp at this
    simp only [fixA, GoodS, Good] at hg
    have hm := hW off (by omega)
    show LoadHolds rd _ off _
    rw [hg.resolve_left hS, rdAt, hm.2]
    exact hm
  | const => exact hg
  | add => exact hg
  | copy => exact hg
  | mul d x y =>
    simp only [okP, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [fixA, GoodS, Good] at hg
    rw [ite_pos' hok] at hg
    exact hg
  | _ => simp [okP] at hok

/-! ## By membership -/

/-- A read of a word the memory holds, the statement in `vtPre`. -/
theorem vtB_readM (hl : args.length = 20) {d p : V} {off : ℕ}
    (hs : Stmt.atom (.load d p off) ∈ vtPre) (hS : Atom.load d p off ∉ vtSL) {v : E}
    (hm : LoadHolds rd (vtσ rd w args p) off v) :
    vtσ rd w args d = v ∧ VSH (coreProgram.Rel rd) rd (vtσ rd w args) (.atom (.load d p off)) := by
  have hg := vt_goodS (rd := rd) (w := w) hl hs
  simp only [fixNe, GoodS, Good] at hg
  have e : vtσ rd w args d = v := by rw [hg.resolve_left hS, rdAt, hm.2]; rfl
  refine ⟨e, ?_⟩
  show LoadHolds rd _ _ _
  rw [e]; exact hm

/-- The returns of a dispatch in `vtPre`: the oracle's. -/
theorem vtB_retsM (hl : args.length = 20) {x : V} {fs : List String} {args' rets : List V}
    (hs : Stmt.dispatch x fs args' rets ∈ vtPre) : ∀ v ∈ rets, vtσ rd w args v = w v.idx :=
  vt_goodS (rd := rd) (w := w) hl hs

/-- **A block's statements hold** when those evaluation alone does not settle do. -/
theorem vtB_blockA (hl : args.length = 20) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vtPre.drop n).take blk.length) = true)
    (h : ∀ s ∈ blk, autoB s = false → VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) :
    ∀ s ∈ blk, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  intro s hs
  cases ha : autoB s
  · exact h s hs ha
  · exact vsh_auto hl (vt_mem_slice heq hs) ha

end

end
end LeanVM.Guest.B1.Tables
