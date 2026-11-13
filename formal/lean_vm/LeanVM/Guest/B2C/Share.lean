/-
  LeanVM.Guest.B2C.Share

  The sharing check of the guest's functions (`ShareCheck.lean`), on their data.
-/

module

public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.Data.Snaps
public import LeanVM.Guest.B2C.ShareCheck
public import LeanVM.Guest.CheckWinC

/-!
# Values sharing a cell, function by function

`shareStatic j` and `shareWin j` are the checks of `ShareCheck.lean` on function `j`'s data (`certOf j`,
`plumbOf j`, `fsN j`, its snapshots `snapsOf j`), by `rfl` (`shareStatic_eqD`, `shareWin_eqD`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-- The snapshots of function `j`'s windows after the first. -/
noncomputable def snapsOf (j : ℕ) : List Snap :=
  ((Data.snaps.find? fun p ↦ Nat.beq p.1 j).map Prod.snd).getD []

/-- **The cells apart**, in `C`'s order: the fixed cells from the temporaries', the call sites'
from the temporaries', the runs', the fixed cells and every value's, the table targets' from all
of those, the fixed cells, the sites' and the targets' each once, the entry environment's cells
fixed frame pointer cells; in `main`, all below the jump table. -/
noncomputable def apartOk (j : ℕ) : Bool :=
  natSeq (Nat.lor (tmpCells (plumbOf j)) (bitsOf ((plumbOf j).runs.map Prod.snd))) fun tr ↦
  natSeq (bitsOf ((plumbOf j).stat.map Prod.fst)) fun st ↦
  natSeq (Nat.lor (Nat.lor tr st) (bitsOf (certOf j).locs)) fun trsv ↦
  natSeq (bitsOf (siteCells (plumbOf j))) fun sc ↦
  natSeq (bitsOf ((plumbOf j).arms.map fun a ↦ a.2.1)) fun ac ↦
  apart st (tmpCells (plumbOf j)) && apart sc trsv && apart ac (Nat.lor trsv sc) &&
    bitsNodup ((plumbOf j).stat.map Prod.fst) 0 && bitsNodup (siteCells (plumbOf j)) 0 &&
    bitsNodup ((plumbOf j).arms.map fun a ↦ a.2.1) 0 &&
    (certOf j).facts.env.all (fun p ↦ (plumbOf j).stat.any fun q ↦ Nat.beq q.1 p.1 && q.2 == .fpg 0) &&
    (bif Nat.beq j 1 then Nat.blt (Nat.lor (Nat.lor trsv sc) ac) (2 ^ Data.mainCells) else true)

/-- **What the sharing check says once of function `j`**: the first window's cells' bound, the
lists, the windows' order, the cells apart, the parameters numbered in the first window's cells. -/
noncomputable def shareStatic (j : ℕ) : Bool :=
  (locW (certOf j) 0).seq fun loc ↦ natSeq (tmpCells (plumbOf j)) fun tc ↦
  natSeq (fpgCells (plumbOf j)) fun fc ↦ (byCell (plumbOf j).tmps).seq fun tt ↦
  (listElementOrDefault (certOf j).cells 0 []).all (fun c ↦ Nat.blt c 65536) &&
  listsOk (plumbOf j) (fsN j) && snapsOk (certOf j) (snapsOf j) &&
    apartOk j && (coreOf j).params.all (valOk loc tt tc fc (fsN j))

/-- **Window `k` of function `j`**, starting from the snapshots `snaps`: its values numbered, in
its soundness window's cells and in the frame; its walk from the parameters' naming (the first
window) or from its snapshot, ending in a state that refines the next one's. -/
noncomputable def shareWin (j : ℕ) (snaps : List Snap) (k : ℕ) : Bool :=
  (locW (certOf j) (winW snaps k)).seq fun loc ↦ natSeq (bitsOf (plumbOf j).sh) fun sh ↦
  natSeq (tmpCells (plumbOf j)) fun tc ↦ natSeq (fpgCells (plumbOf j)) fun fc ↦
  (byCell (plumbOf j).tmps).seq fun tt ↦
  (listElementOrDefault (certOf j).cells (winW snaps k) []).all (fun c ↦ Nat.blt c 65536) &&
  valsAll (valOk loc tt tc fc (fsN j)) (stmtsW (coreOf j).body snaps k) &&
  (match swL loc sh tt (plumbOf j)
      (bif k == 0 then nameStep loc sh (initSt (plumbOf j)) (coreOf j).params else (snapAt snaps k).st)
      (stmtsW (coreOf j).body snaps k) with
    | some m => bif Nat.blt k snaps.length then refines m (snapAt snaps (k + 1)) else true
    | none => false)

/-- **The sharing check of function `j`**: its static part and every window's. -/
def ShareOk (j : ℕ) : Prop :=
  shareStatic j = true ∧ ∀ k ≤ (snapsOf j).length, shareWin j (snapsOf j) k = true

theorem apartOk_eq (j : ℕ) : apartOk j = apartOkD (certOf j) (plumbOf j) (Nat.beq j 1) Data.mainCells := rfl

theorem shareStatic_eqD (j : ℕ) :
    shareStatic j = shareStaticD (coreOf j) (certOf j) (plumbOf j) (fsN j) (snapsOf j) (Nat.beq j 1) Data.mainCells :=
  rfl

theorem shareWin_eqD (j : ℕ) (snaps : List Snap) (k : ℕ) :
    shareWin j snaps k = shareWinD (coreOf j) (certOf j) (plumbOf j) (fsN j) snaps k := rfl

/-- **A function's sharing check from its pack's**, over its data (`Check.Link`). -/
theorem shareOk_of_link {j : ℕ} {G : Glob} {f : CompiledFunction} {cf : Core.Fn} {C : Cert} {P : Plumb}
    {fs : ℕ} {snaps : List Snap} {main : Bool} {mc : ℕ} (h : Link j G f cf C) (hP : plumbOf j = P)
    (hfs : fsN j = fs) (hs : snapsOf j = snaps) (hm : Nat.beq j 1 = main)
    (hmc : main = true → Data.mainCells = mc) (ok : ShareOkD cf C P fs snaps main mc) : ShareOk j := by
  have hst : shareStatic j = shareStaticD cf C P fs snaps main mc := by
    rw [shareStatic_eqD, h.core, h.cert, hP, hfs, hs, hm]
    cases main
    · rfl
    · rw [hmc rfl]
  refine ⟨by rw [hst]; exact ok.1, fun k hk ↦ ?_⟩
  rw [hs] at hk ⊢
  rw [shareWin_eqD, h.core, h.cert, hP, hfs]
  exact ok.2 k hk

end
end LeanVM.Guest.B2C
