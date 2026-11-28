/-
  LeanVM.Guest.B2C.CplSplitPre

  The completeness walk's groups of a split window from the window's common part (`winPre`), which
  the soundness check computed once per window.
-/

module

public import LeanVM.Guest.B2C.CplSplit
public import LeanVM.Guest.B2C.SplitPre

/-!
# A split window's completeness groups, from its common part

A window of one `match` has its completeness walk checked by groups of its arms (`cplWinS`), each in
its own kernel evaluation. Every group starts from the window's executor run, its index and links,
which `SplitPre`'s `winPre j i` holds and `win_lit` wrote once as a value the kernel checked
(`Checked/X{j}_{i}`). `cplWinSP p j i …` is the group's check from that value, reading the
function's completeness data itself (its fixed cells, renumbered values and first part's
statements); `cplWinS_of_pre` gives the group's `cplWinS` from it, so the window's theorem
(`cplWin_of_split`) is unchanged.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-- `cplWinS` from the window's common part `p`. -/
noncomputable def cplWinSP (p : WinPre) (j i lo hi gm gn am an : ℕ) : Bool :=
  Nat.beq (nParts j i) 1 && Nat.beq (partM j i 0) 0 && Nat.blt i (certOf j).cuts.length &&
  match partStmts j i 0 with
  | [.match_ v (a0 :: as)] =>
    matchAtoms lo hi [.match_ v (a0 :: as)] &&
      (clocG (certOf j) i gm gn am an).seq fun loc ↦
      (statT (fsN j) (plumbOf j).stat .nil).seq fun stat ↦
      (partC j i 0).seq fun c ↦ natSeq (partU j i 0) fun u ↦ natSeq (partJ j i 0) fun J ↦
      natSeq (plumbOf j).nv fun nv ↦
      (stmtsVals (selStmts lo hi [.match_ v (a0 :: as)])).all (fun x ↦ (loc.get? x.idx).isSome) &&
      nextSelOk (cxOf j p.idx loc stat nv (stopOf j i 0)) v &&
      match getF p.idx J with
      | some s => bif Nat.beq s.start J then
          partEnd j i 0 (cwSplit (cxOf j p.idx loc stat nv (stopOf j i 0)) lo hi (partEnt j i 0) v
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
