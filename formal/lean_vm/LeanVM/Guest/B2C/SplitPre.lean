/-
  LeanVM.Guest.B2C.SplitPre

  What every group of arms of a split window computes alike, computed once per window.
-/

module

public import LeanVM.Guest.B2C.CplSplit

/-!
# A split window's common part, once

A window of one `match` is checked by groups of its arms, each in its own kernel evaluation:
`Check.checkWinS` for the soundness check, `cplWinS` for the completeness walk. Every group of a
window starts alike: the window's executor run (`execWinCS`) and its index, the fixed cells, the
renumbered values, the window's statements, and the links of its segments. `winPre j i` is that
part. `kernel_lit` (`Guest/KernelLit.lean`) writes it once per window as a value the kernel checked
(`Checked/X{j}_{i}`), and each group's check starts from the value (`checkWinSP`, `cplWinSP`):
`checkWinS_of_pre` and `cplWinS_of_pre` give the group's `checkWinS` and `cplWinS` from it, so the
window's theorems (`checkWinC_of_split`, `cplWin_of_split`) are unchanged.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-- What every group of window `i` of function `j` computes alike. -/
structure WinPre where
  /-- The executor's segments on the window. -/
  segs : List Exec.Seg
  /-- Their index. -/
  idx : Trie Exec.Seg
  /-- The fixed cells (`cplWinS`). -/
  stat : Trie PC
  /-- The renumbered values the function's own atoms name (`cplWinS`). -/
  nv : ℕ
  /-- The statements of the window's first part (`cplWinS`). -/
  pst : List Core.Stmt
  /-- The window's statements (`checkWinS`). -/
  wst : List Core.Stmt
  /-- The links of the segments (`checkWinS`). -/
  lw : Bool

/-- The executor's segments on window `i` of function `j`, from its start and, entered, its other
arms. -/
noncomputable def winSegs (j i : ℕ) : List Exec.Seg :=
  (execWinCS (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
    (((certOf j).succAt i).drop 1) ((certOf j).endAt (fnOf j) i)).segs

/-- **What every group of window `i` of function `j` computes alike.** -/
noncomputable def winPre (j i : ℕ) : WinPre :=
  ⟨winSegs j i, index (winSegs j i), statT (fsN j) (plumbOf j).stat .nil, (plumbOf j).nv,
    partStmts j i 0, (certOf j).stmtsAt (coreOf j) i,
    linkedWeak (index (winSegs j i)) (winSegs j i)
      (bif Nat.blt i (certOf j).cuts.length then ((certOf j).cutAt (i + 1)).J else 0)
      (bif Nat.blt i (certOf j).cuts.length then envOf ((certOf j).cutAt (i + 1)).env else .nil)⟩

/-! ## The completeness walk's groups -/

/-- `cplWinS` from the window's common part `p`. -/
noncomputable def cplWinSP (p : WinPre) (j i lo hi gm gn am an : ℕ) : Bool :=
  Nat.beq (nParts j i) 1 && Nat.beq (partM j i 0) 0 && Nat.blt i (certOf j).cuts.length &&
  match p.pst with
  | [.match_ v (a0 :: as)] =>
    matchAtoms lo hi [.match_ v (a0 :: as)] &&
      (clocG (certOf j) i gm gn am an).seq fun loc ↦
      (partC j i 0).seq fun c ↦ natSeq (partU j i 0) fun u ↦ natSeq (partJ j i 0) fun J ↦
      (stmtsVals (selStmts lo hi [.match_ v (a0 :: as)])).all (fun x ↦ (loc.get? x.idx).isSome) &&
      nextSelOk (cxOf j p.idx loc p.stat p.nv (stopOf j i 0)) v &&
      match getF p.idx J with
      | some s => bif Nat.beq s.start J then
          partEnd j i 0 (cwSplit (cxOf j p.idx loc p.stat p.nv (stopOf j i 0)) lo hi (partEnt j i 0) v
            (a0 :: as) ⟨s, s.items, .nil, [], [], [], c, u, some J, 0⟩)
        else false
      | none => false
  | _ => false

theorem cplWinS_eq_pre (j i lo hi gm gn am an : ℕ) :
    cplWinS j i lo hi gm gn am an = cplWinSP (winPre j i) j i lo hi gm gn am an := by
  unfold cplWinS cplWinSP winPre winSegs
  generalize execWinCS (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
    (((certOf j).succAt i).drop 1) ((certOf j).endAt (fnOf j) i) = R
  cases R
  simp only [listSeq_eq, Exec.Trie.seq_eq, CLoc.seq_eq, Cnt.seq_eq, natSeq_eq]
  rfl

/-- **A completeness group from the window's common part**, which the kernel checked once. -/
theorem cplWinS_of_pre {j i lo hi gm gn am an : ℕ} {p : WinPre} (hp : winPre j i = p)
    (h : cplWinSP p j i lo hi gm gn am an = true) : cplWinS j i lo hi gm gn am an = true := by
  rw [cplWinS_eq_pre, hp]
  exact h

end
end LeanVM.Guest.B2C

namespace LeanVM.Guest.Check

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.B2C

@[expose] public section

/-! ## The soundness check's groups -/

/-- `checkWinS` of function `j`'s window `i` from the window's common part `p`. -/
noncomputable def checkWinSP (p : WinPre) (j : ℕ) (main : Bool) (i lo hi : ℕ) (rs : List (ℕ × ℕ)) :
    Bool :=
  matchAtoms lo hi p.wst &&
  ((certOf j).locAtR i rs).seq fun loc ↦
    !(i == 0) && (certOf j).rsFit i rs &&
    covOk loc (selStmts lo hi p.wst) && p.lw &&
    (match segAt ((certOf j).fxAt glob (fnOf j) (coreOf j) main i p.segs p.idx loc)
        ((certOf j).cutAt i).J (bookOf ((certOf j).cutAt i).facts .nil) ((certOf j).cutAt i).bnd with
      | some st => st.seg.env.sub Sym.beq (envOf ((certOf j).cutAt i).env) &&
          winEnd (certOf j) i p.idx
            (chkWinS ((certOf j).fxAt glob (fnOf j) (coreOf j) main i p.segs p.idx loc) lo hi
              ((certOf j).cutAt i).env ((certOf j).selAt i) ((certOf j).succAt i) p.wst st)
      | none => false)

theorem checkWinS_eq_pre (j : ℕ) (main : Bool) (i lo hi : ℕ) (rs : List (ℕ × ℕ)) :
    checkWinS glob j (coreOf j) (certOf j) main i lo hi rs = checkWinSP (winPre j i) j main i lo hi rs := by
  unfold checkWinS checkWinSP winPre winSegs
  generalize execWinCS (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
    (((certOf j).succAt i).drop 1) ((certOf j).endAt (fnOf j) i) = R
  cases R
  simp only [listSeq_eq, Exec.Trie.seq_eq]
  rfl

/-- **A soundness group from the window's common part**, which the kernel checked once. -/
theorem checkWinS_of_pre {j i lo hi : ℕ} {main : Bool} {rs : List (ℕ × ℕ)} {p : WinPre}
    (hp : winPre j i = p) (h : checkWinSP p j main i lo hi rs = true) :
    checkWinS glob j (coreOf j) (certOf j) main i lo hi rs = true := by
  rw [checkWinS_eq_pre, hp]
  exact h

end
end LeanVM.Guest.Check
