/-
  LeanVM.Guest.Bridge.AllocDefs

  The allocation hints by offset: the bump pointer's static part at each offset of a function, the
  buffers reserved so far and whether a callee frame is reserved and not yet entered.
-/

module

public import LeanVM.Guest.Bridge.AlignDefs
public import Statement.Prover.Execute

/-!
# The allocation hints by offset

The bump pointer at an instruction of a frame (`EndExecA.lean`) is the instance's cursor past the
buffers its function has reserved so far (`nbAt`) and its calls made, moved by the reservation of
the next callee's block when its frame is reserved and not yet entered (`pendAt`). Both static
parts are read off the function's allocation hints by offset (`allocHints`), each by its role
(`isFrame`: its pointer a call site's callee frame cell; `isBuf`: the rest). The bus era's
definitions (tag `formal-bus-archive`), on Hotwire's hints, whose allocations carry the `aligned`
flag.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Guest.Check (getF)

@[expose] public section

/-- An allocation hint's pointer cell. -/
def allocPtr : Prover.Exec.Hint → Option ℕ
  | .alloc p _ _ | .allocDyn p _ | .allocArm p _ _ _ | .allocFrames p _ _ _ _ _ => some p
  | _ => none

/-- The function's hints with their offsets, by pc then in the list at a pc. -/
def hintsOff (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : List (ℕ × Prover.Exec.Hint) :=
  d.2.2.flatMap fun p ↦ p.2.map fun h ↦ (p.1 - d.1, h)

/-- The function's allocation hints with their offsets, in order. -/
def allocHints (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : List (ℕ × Prover.Exec.Hint) :=
  (hintsOff d).filter fun q ↦ (allocPtr q.2).isSome

/-- A callee frame's hint: its pointer a call site's callee frame cell. -/
noncomputable def isFrame (X : AlignCtx) (h : Prover.Exec.Hint) : Bool :=
  match allocPtr h with
  | some p => (getF X.sites p).isSome
  | none => false

/-- A buffer's hint. -/
noncomputable def isBuf (X : AlignCtx) (h : Prover.Exec.Hint) : Bool :=
  (allocPtr h).isSome && !isFrame X h

/-- The offset of the first jump at or after offset `a`. -/
def nextJump (code : List OffsetInstruction) (a : ℕ) : ℕ := a + (code.drop a).findIdx OffsetInstruction.isJump

/-- **The buffers reserved before offset `off`.** -/
noncomputable def nbAt (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (off : ℕ) : ℕ :=
  ((allocHints d).filter fun q ↦ decide (q.1 < off) && isBuf X q.2).length

/-- The function's buffer hints with their offsets. -/
noncomputable def bufsOf (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) :
    List (ℕ × Prover.Exec.Hint) :=
  (allocHints d).filter fun q ↦ isBuf X q.2

/-- The function's frame hints with their offsets. -/
noncomputable def frames (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) :
    List (ℕ × Prover.Exec.Hint) :=
  (allocHints d).filter fun q ↦ isFrame X q.2

/-- A frame hint of `fr` before offset `off`, its call site's jump at or after it. -/
def pendIn (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint)) (off : ℕ) : Bool :=
  fr.any fun q ↦ decide (q.1 < off) && decide (off ≤ nextJump code q.1)

/-- **A callee frame reserved and not yet entered at offset `off`**: a frame hint before it, its
call site's jump at or after it. -/
noncomputable def pendAt (X : AlignCtx) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (off : ℕ) : Bool :=
  pendIn code (frames X d) off

/-- A frame hint: an `alloc`, `allocArm` or `allocFrames` before the next jump, which goes through
the hint's pointer as its frame cell, its condition no constant `0`, its frame cell neither the own
frame nor a next frame, and no return. -/
noncomputable def frameOk (X : AlignCtx) (code : List OffsetInstruction) (a : ℕ) (h : Prover.Exec.Hint) : Bool :=
  (match h with
    | .alloc .. | .allocArm .. | .allocFrames .. => true
    | _ => false) &&
  match code[nextJump code a]?, allocPtr h with
  | some (.jump oc od q), some p => Nat.beq q p && !X.zeroAt oc && !X.selfAt q && !X.nextAt q &&
      !(Nat.beq od 0 && Nat.beq q 1)
  | _, _ => false

/-- A jump before a buffer hint of `bs`, at offset `i`: on a constant `0` through no call site or next
frame, or a forward jump in the frame to a constant pc, through no call site or table, no return, no
buffer hint strictly between. -/
noncomputable def bufJumpOk (X : AlignCtx) (bs : List (ℕ × Prover.Exec.Hint)) (i oc od of : ℕ) : Bool :=
  (X.zeroAt oc && (getF X.sites of).isNone && !X.nextAt of) || (X.selfAt of && (getF X.sites of).isNone &&
    !(Nat.beq od 0 && Nat.beq of 1) && (getF X.arms od).isNone && match X.pcAt od with
      | some t => bs.all fun q ↦ !(decide (i < q.1) && decide (X.entry + q.1 < t))
      | none => false)

end

public section

theorem nbAt_zero (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : nbAt X d 0 = 0 := by
  unfold nbAt; simp

theorem pendAt_zero (X : AlignCtx) (code : List OffsetInstruction) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) :
    pendAt X code d 0 = false := by
  unfold pendAt pendIn; simp

end

end LeanVM.Guest.Bridge
