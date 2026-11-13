/-
  LeanVM.Guest.B2C.Cpl

  B2's completeness check of one compiled function: its code runs from its entry to its return
  on a memory whose frame holds what the honest memory puts there, window by window of its
  soundness certificate.
-/

module

public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.Data.CplParts
public import LeanVM.Guest.Data.CplArms
public import LeanVM.Guest.CheckWinC
public import LeanVM.Guest.B2C.CplCheck

/-!
# The completeness check

`cplWin j i k`: the check of part `k` of window `i` of function `j`, the walk of its statements
against the compiled code (`cplRes`); `CplOk j`, every part of every window. They are the checks
of `CplCheck.lean` on function `j`'s data in the whole program's context (`cplWin_eq`, by `rfl`),
which the kernel evaluates on the function's own data and view (`Pack/*/Cplw*`). What the check means of a run, the frame it reads (`FrameHolds`), the
callees' runs (`KidsRun`) and what it gives (`CplRun`), is `CplSpec.lean`: apart, so that the
kernel-checked certificates import the check alone.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-- The parts of function `j`'s windows. -/
noncomputable def cplPartsOf (j : ℕ) : List (List (List ℕ)) := listElementOrDefault Data.cplParts j []

/-- The parts of window `i` of function `j`. -/
noncomputable def partsOf (j i : ℕ) : List (List ℕ) := partsOfD (cplPartsOf j) i

/-- The number of parts of a window. -/
noncomputable def nParts (j i : ℕ) : ℕ := nPartsD (cplPartsOf j) i

/-- The window statement part `k` starts at. -/
noncomputable def partS (j i k : ℕ) : ℕ := partSD (cplPartsOf j) i k

/-- The code offset part `k` starts at: the window's start for the first. -/
noncomputable def partJ (j i k : ℕ) : ℕ := partJD (certOf j) (cplPartsOf j) i k

/-- The counts at part `k`'s start. -/
noncomputable def partC (j i k : ℕ) : Cnt := partCD (cplPartsOf j) i k

/-- The set-up site cells at part `k`'s start. -/
noncomputable def partU (j i k : ℕ) : ℕ := partUD (cplPartsOf j) i k

/-- The items of its segment part `k` starts after (`0`: at the segment's start). -/
noncomputable def partM (j i k : ℕ) : ℕ := partMD (cplPartsOf j) i k

/-- Part `k` entered: it starts with a chained `match`, entered by a table jump into its arms. -/
noncomputable def partEnt (j i k : ℕ) : Option (ℕ × List ℕ) := partEntD (cplPartsOf j) i k

/-- Where part `k` stops: inside a segment, if the next part starts there. -/
noncomputable def stopOf (j i k : ℕ) : Option (ℕ × ℕ) :=
  bif Nat.blt (k + 1) (nParts j i) && !(Nat.beq (partM j i (k + 1)) 0) then
    some (partJ j i (k + 1), partM j i (k + 1))
  else none

/-- The statements of part `k`. -/
noncomputable def partStmts (j i k : ℕ) : List Core.Stmt :=
  bif Nat.blt (k + 1) (nParts j i) then
    (((certOf j).stmtsAt (coreOf j) i).drop (partS j i k)).take (partS j i (k + 1) - partS j i k)
  else ((certOf j).stmtsAt (coreOf j) i).drop (partS j i k)

/-- The context of window `i` of function `j`. -/
noncomputable def cxOf (j : ℕ) (idx : Trie Exec.Seg) (loc : CLoc) (stat : Trie PC) (nv : ℕ)
    (stop : Option (ℕ × ℕ)) : CX :=
  cxOfD glob (fnOf j) (coreOf j) (certOf j) (plumbOf j) (fsN j) (listElementOrDefault Data.cplArms j [])
    (j == 1) idx loc stat nv stop

/-- How part `k` of window `i` must end: at the next part's start, the next window's, within
what is handed on there (in its chained `match`'s table jump if it is entered), or by the
return. -/
noncomputable def partEnd (j i k : ℕ) : RC → Bool
  | .join J c u =>
    bif Nat.blt (k + 1) (nParts j i) then
      Nat.beq J (partJ j i (k + 1)) && Nat.beq (partM j i (k + 1)) 0 && (partEnt j i (k + 1)).isNone &&
        c.le (partC j i (k + 1)) && subK u (partU j i (k + 1))
    else Nat.blt i (certOf j).cuts.length && Nat.beq J ((certOf j).cutAt (i + 1)).J &&
      (partEnt j (i + 1) 0).isNone && c.le (partC j (i + 1) 0) && subK u (partU j (i + 1) 0)
  | .mid J m c u => Nat.blt (k + 1) (nParts j i) && Nat.beq J (partJ j i (k + 1)) &&
      Nat.beq m (partM j i (k + 1)) && !(Nat.beq m 0) && (partEnt j i (k + 1)).isNone &&
      c.le (partC j i (k + 1)) && subK u (partU j i (k + 1))
  | .chain o succ c u => !succ.isEmpty &&
    bif Nat.blt (k + 1) (nParts j i) then
      decide (partEnt j i (k + 1) = some (o, succ)) && Nat.beq (partJ j i (k + 1)) (succ.headD 0) &&
        c.le (partC j i (k + 1)) && subK u (partU j i (k + 1))
    else Nat.blt i (certOf j).cuts.length && decide (partEnt j (i + 1) 0 = some (o, succ)) &&
      Nat.beq (partJ j (i + 1) 0) (succ.headD 0) && c.le (partC j (i + 1) 0) && subK u (partU j (i + 1) 0)
  | .done => !(Nat.blt (k + 1) (nParts j i)) && !(Nat.blt i (certOf j).cuts.length)
  | .fail _ => false

/-- The walk's result of part `k` of window `i` of function `j`. -/
noncomputable def cplRes (j i k : ℕ) : RC :=
  match execWinCS (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
      (((certOf j).succAt i).drop 1) ((certOf j).endAt (fnOf j) i) with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ (clocW (certOf j) i).seq fun loc ↦
    (statT (fsN j) (plumbOf j).stat .nil).seq fun stat ↦
    (fileB loc (fsN j) (partStmts j i k) .nil).seq fun B ↦
    (partC j i k).seq fun c ↦ natSeq (partU j i k) fun u ↦ natSeq (partJ j i k) fun J ↦
    natSeq (plumbOf j).nv fun nv ↦ natSeq (partM j i k) fun m ↦
    match getF idx J with
    | some s => bif Nat.beq s.start J then
        match partEnt j i k with
        | some (o, succ) => cwE (cxOf j idx loc stat nv (stopOf j i k)) o succ
            ⟨s, s.items, B, [], [], [], c, u, some J, 0⟩ (partStmts j i k)
        | none => cw (cxOf j idx loc stat nv (stopOf j i k)) (partStmts j i k)
          ⟨s, s.items.drop m, B, [], [], [], c, u, bif Nat.beq m 0 then some J else none, 0⟩
      else .fail 91
    | none => .fail 90

/-- What a window's first part also checks: its cells pack, and the function's first window
starts with nothing handed on, its parameters `V.n 0, V.n 1, …`, its self frame pointer cells
fixed, and its values the top-level atoms name as `Plumb.nv` says, which every part reads. -/
noncomputable def winOkC (j i : ℕ) : Bool :=
  (listElementOrDefault (certOf j).cells i []).all (fun c ↦ Nat.blt c 65536) &&
  Nat.beq (partS j i 0) 0 && Nat.beq (partM j i 0) 0 &&
  (match partEnt j i 0 with
    | some (o, succ) => Nat.beq o ((certOf j).selAt i) && succ == (certOf j).succAt i && !succ.isEmpty
    | none => ((certOf j).succAt i).isEmpty) &&
  (coreOf j).params == (List.range (coreOf j).params.length).map V.n &&
  (bif Nat.beq i 0 then (partC j 0 0).le Cnt.zero && Nat.beq (partU j 0 0) 0 &&
      (certOf j).facts.env.all (fun p ↦ Sym.beq p.2 (.fpg 0) &&
        decide (getF (statT (fsN j) (plumbOf j).stat .nil) p.1 = some (.fpg 0))) &&
      Nat.beq (nvOf (coreOf j).body 0) (plumbOf j).nv
    else true)

/-- The last part of the function's last window. -/
noncomputable def lastPart (j i k : ℕ) : Bool :=
  !(Nat.blt (k + 1) (nParts j i)) && !(Nat.blt i (certOf j).cuts.length)

/-- **The completeness check of part `k` of window `i` of function `j`**: its statements return
only at the function's end, it starts within its window and after the part before it, and its
walk ends as `partEnd` says. -/
noncomputable def cplWin (j i k : ℕ) : Bool :=
  (bif Nat.beq k 0 then winOkC j i else Nat.ble (partS j i (k - 1)) (partS j i k)) &&
  Nat.ble (partS j i k) ((certOf j).stmtsAt (coreOf j) i).length &&
  (bif lastPart j i k then lastOkC (partStmts j i k)
    else Stmt.noRetList (partStmts j i k)) &&
  partEnd j i k (cplRes j i k)

/-- The check of function `j` is the check of `CplCheck.lean` on its data. -/
theorem cplWin_eq (j i k : ℕ) : cplWin j i k = cplWinD glob (fnOf j) (coreOf j) (certOf j) (plumbOf j)
    (fsN j) (cplPartsOf j) (listElementOrDefault Data.cplArms j []) (j == 1) i k := rfl

/-- **The completeness check of function `j`**: every part of every window. -/
noncomputable def CplOk (j : ℕ) : Prop :=
  ∀ i ≤ (certOf j).cuts.length, ∀ k < nParts j i, cplWin j i k = true

/-- **A function's completeness check from its pack's**, over its data and view (`Check.Link`). -/
theorem cplOk_of_link {j : ℕ} {G : Glob} {f : CompiledFunction} {cf : Core.Fn} {C : Cert} {P : Plumb}
    {fs : ℕ} {ps : List (List (List ℕ))} {acs : List (ℕ × List (List ℕ))} {main : Bool}
    (h : Link j G f cf C) (hP : plumbOf j = P) (hfs : fsN j = fs) (hps : cplPartsOf j = ps)
    (hacs : listElementOrDefault Data.cplArms j [] = acs) (hm : (j == 1) = main)
    (ok : CplOkD G f cf C P fs ps acs main) : CplOk j := by
  intro i hi k hk
  rw [h.cert] at hi
  have hk' : k < nPartsD ps i := by rw [← hps]; exact hk
  rw [cplWin_eq, h.code, h.core, h.cert, hP, hfs, hps, hacs, hm, cplWinD_congr h.view]
  exact ok i hi k hk'

end
end LeanVM.Guest.B2C
