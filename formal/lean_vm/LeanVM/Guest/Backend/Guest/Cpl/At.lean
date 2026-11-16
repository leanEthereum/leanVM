/-
  LeanVM.Guest.Backend.Guest.Cpl.At

  The guest's placed functions, entry by entry, and the per-function test the kernel evaluates on
  them for the completeness instance.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Static
public import LeanVM.Guest.Backend.Guest.Piece.Layout
public import LeanVM.Guest.Frames
public import LeanVM.Guest.Data.FrameSizes
public import LeanVM.Guest.B2C.Defs

/-!
# The guest's placed functions

`placedAt i` is entry `i` of the back end's input (`guestTraced`, function `i + 1`) placed from the
jump tables the entries before it leave, as the pieces place it (`placedLocsAt`'s placement);
`fsWant i` the frame size the completeness instance gives it: `Data.mainCells` for `main` (its
frame proper, without the jump tables), else `max 2 (fsAt (i + 1))`, `B2C.fs`'s.

`cplOkWith i pf` is the per-function test of entry `i` placed as `pf`: the static test
(`staticOk`) against `fsWant i`; the placement-side hypotheses (`Complete.scopedB`,
`Complete.noSelfCallB`, `Complete.tmpsApartB`, `Complete.alL`); and the counts: `Complete.pmaxP` is
the table's `pmax` (`B2C.plumbOf`) and `Complete.armsP` is `Data.cplArms`, keyed (counting arms
apart) when `Data.cplArms` lists the function, the arms' selectors distinct. `cplOkAt i` runs the
placement; `CplOkAll` says the test passes for every entry, which the kernel decides for runs of
entries (`Eval/`).
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Guest LeanVM.Guest.Core GuestPiece

@[expose] public section

/-- **Entry `i` placed** from the jump tables the entries before it leave; `none` if its
placement fails. -/
noncomputable def placedAt (i : ℕ) : Option Placed :=
  match placeFn loopsG sigsG (tablesAt outsG i) (guestTraced.getD i default) with
  | .ok r => some r.1
  | .error _ => none

/-- The frame size of entry `i` in the completeness instance. -/
def fsWant (i : ℕ) : ℕ := if i = 0 then Data.mainCells else max 2 (fsAt (i + 1))

/-- The separately counted arms of function `i + 1` (`Data.cplArms`). -/
def armsOf (i : ℕ) : List (ℕ × List (List ℕ)) := listElementOrDefault Data.cplArms (i + 1) []

/-- Whether function `i + 1`'s arms are counted separately. -/
def keyedOf (i : ℕ) : Bool := !(armsOf i).isEmpty

/-- **The per-function test** of entry `i` on its placed function `pf`. -/
noncomputable def cplOkWith (i : ℕ) (pf : Placed) : Bool :=
  staticOk loopsG (guestTraced.getD i default) pf (fsWant i) &&
    Complete.scopedB (guestTraced.getD i default) &&
    Complete.noSelfCallB (guestTraced.getD i default) &&
    Complete.tmpsApartB (guestTraced.getD i default) pf &&
    Complete.alL pf.fn.body (guestTraced.getD i default).core.body &&
    natsDistinct ((Complete.armsP (keyedOf i) (guestTraced.getD i default) pf).map (·.1)) &&
    decide (Complete.ofCnt (Complete.pmaxP (keyedOf i) pf) = (B2C.plumbOf (i + 1)).pmax) &&
    decide (Complete.armsP (keyedOf i) (guestTraced.getD i default) pf = armsOf i)

/-- **The per-function test of entry `i`**, its placement run. -/
noncomputable def cplOkAt (i : ℕ) : Bool :=
  match placedAt i with
  | some pf => cplOkWith i pf
  | none => false

theorem placedAt_of {i : ℕ} {pf : Placed} {t' : Tables}
    (h : placeFn loopsG sigsG (tablesAt outsG i) (guestTraced.getD i default) = .ok (pf, t')) :
    placedAt i = some pf := by
  unfold placedAt
  rw [h]

theorem cplOkAt_of {i : ℕ} {pf : Placed} (hp : placedAt i = some pf) (h : cplOkWith i pf = true) :
    cplOkAt i = true := by
  unfold cplOkAt
  rw [hp]
  exact h

theorem cplOkWith_of {i : ℕ} {pf : Placed} (hp : placedAt i = some pf) (h : cplOkAt i = true) :
    cplOkWith i pf = true := by
  unfold cplOkAt at h
  rw [hp] at h
  exact h

/-- **The per-function test passes for every entry** of the guest. -/
def CplOkAll : Prop := ∀ i < 1549, cplOkAt i = true

/-- **What the per-function test says.** -/
structure CplFacts (i : ℕ) (pf : Placed) : Prop where
  sfacts : StaticFacts loopsG (guestTraced.getD i default) pf (fsWant i)
  isScoped : Complete.Scoped (guestTraced.getD i default)
  noSelf : Complete.NoSelfCall (guestTraced.getD i default)
  apart : Complete.TmpsApart (guestTraced.getD i default) pf
  aligned : Complete.Aligned (guestTraced.getD i default) pf
  armsNodup : ((Complete.armsP (keyedOf i) (guestTraced.getD i default) pf).map (·.1)).Nodup
  pmax : Complete.ofCnt (Complete.pmaxP (keyedOf i) pf) = (B2C.plumbOf (i + 1)).pmax
  arms : Complete.armsP (keyedOf i) (guestTraced.getD i default) pf = armsOf i

theorem cplOkWith_spec {i : ℕ} {pf : Placed} (h : cplOkWith i pf = true) : CplFacts i pf := by
  unfold cplOkWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hsc⟩, hns⟩, hta⟩, hal⟩, hnd⟩, hpm⟩, har⟩ := h
  exact ⟨staticOk_spec hs, hsc, hns, hta, hal, natsDistinct_nodup hnd, hpm, har⟩

end
end LeanVM.Guest.Backend.Cpl
