/-
  LeanVM.Guest.Bridge.AllocDefs

  The allocation hints' check: a function's buffers reserved in its body's order before its first
  jump, each callee frame reserved once, straight before its call site's jump, and the bump
  pointer's static part at each offset.
-/

module

public import LeanVM.Guest.Bridge.AlignDefs

/-!
# The allocation hints' check

The bump pointer at an instruction of a frame (`EndExecA.lean`) is the instance's cursor past the
buffers its function has reserved so far (`nbAt`) and its calls made, plus the block of the next
callee when its frame is reserved and not yet entered (`pendAt`). Both static parts are read off
the function's allocation hints by offset (`allocHints`), each by its role (`isFrame`: its
pointer a call site's callee frame cell; `isLate`: an `allocLate`, a buffer an `allocAdvice` reserved
first, which finds its pointer written; `isBuf`: the rest).

`allocChk X fs P body code d`, by `decide +kernel` per function (`scripts/bridge-cert/alloc.py`):

* the body's allocation atoms are top-level statements (`Stmt.noAlloc` elsewhere), and no statement
  before the last of them returns (`allocShape`), so every path allocates them all, in order;
* the buffer hints compile those atoms one for one, their values in the frame (`pairsA`): an `alloc`
  or `allocDyn` its own, an `allocDyn` whose size cell holds a power `g^n` an `alloc` of `n` cells,
  an `allocDyn` an `allocAdvice` at its pointer; all at offsets up to the first jump, none after a
  frame hint;
* each late hint comes after its `allocAdvice`;
* each frame hint is an `alloc`, `allocArm` or `allocFrames` before the next jump, whose frame cell
  is the hint's pointer (`frameOk`), and every jump through a call site's frame cell is exactly one
  frame hint's (`sitesOk`);
* no jump target is pending: a constant target (`pcAt`), a call site's return pc.

The body's shape is its own conjunct (`allocShape`, `allocRest` the rest), so that a long function
checks it in a module of its own; the code is read only by a function with frame hints or call
sites.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

@[expose] public section

/-! ## The body's allocations -/

/-- An allocation atom. -/
def allocAtom : Atom → Bool
  | .hint h => !coreFlow h
  | _ => false

/-- The allocation hints of a block's top-level atoms, in order. -/
def topAllocs : List Stmt → List Core.Hint
  | [] => []
  | .atom (.hint h) :: ss => bif coreFlow h then topAllocs ss else h :: topAllocs ss
  | _ :: ss => topAllocs ss

mutual
/-- No allocation atom in a statement. -/
def Stmt.noAlloc : Stmt → Bool
  | .atom a => !allocAtom a
  | .ite _ z n => Stmt.noAllocList z && Stmt.noAllocList n
  | .match_ _ arms => Stmt.noAllocArms arms
  | _ => true

/-- No allocation atom in a block. -/
def Stmt.noAllocList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.noAlloc s && Stmt.noAllocList ss

/-- No allocation atom in arms. -/
def Stmt.noAllocArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.noAllocList a && Stmt.noAllocArms as
end

mutual
/-- No `ret` in a statement. -/
def Stmt.retFree : Stmt → Bool
  | .ret _ => false
  | .ite _ z n => Stmt.retFreeList z && Stmt.retFreeList n
  | .match_ _ arms => Stmt.retFreeArms arms
  | _ => true

/-- No `ret` in a block. -/
def Stmt.retFreeList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.retFree s && Stmt.retFreeList ss

/-- No `ret` in arms. -/
def Stmt.retFreeArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.retFreeList a && Stmt.retFreeArms as
end

/-- **Every path allocates the top-level allocation atoms, in order**: no allocation atom below
the top level, and no statement before the last of them returns. -/
def allocShape : List Stmt → Bool
  | [] => true
  | .atom _ :: ss => allocShape ss
  | s :: ss => Stmt.noAlloc s && ((topAllocs ss).isEmpty || Stmt.retFree s) && allocShape ss

/-! ## The advice's allocation hints -/

/-- An allocation hint's pointer cell. -/
def allocPtr : Prover.Exec.Hint → Option ℕ
  | .alloc p _ | .allocDyn p _ | .allocAdvice p _ | .allocArm p _ _ | .allocFrames p _ _ _ _
  | .allocLate p _ => some p
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

/-- An advised buffer's own hint, after its `allocAdvice`. -/
def isLate : Prover.Exec.Hint → Bool
  | .allocLate .. => true
  | _ => false

/-- A buffer's hint. -/
noncomputable def isBuf (X : AlignCtx) (h : Prover.Exec.Hint) : Bool :=
  (allocPtr h).isSome && !isFrame X h && !isLate h

/-- The offset of the first jump at or after offset `a`. -/
def nextJump (code : List OffsetInstruction) (a : ℕ) : ℕ := a + (code.drop a).findIdx OffsetInstruction.isJump

/-- **The buffers reserved before offset `off`.** -/
noncomputable def nbAt (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (off : ℕ) : ℕ :=
  ((allocHints d).filter fun q ↦ decide (q.1 < off) && isBuf X q.2).length

/-- The function's frame hints with their offsets. -/
noncomputable def frames (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : List (ℕ × Prover.Exec.Hint) :=
  (allocHints d).filter fun q ↦ isFrame X q.2

/-- A frame hint of `fr` before offset `off`, its call site's jump at or after it. -/
def pendIn (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint)) (off : ℕ) : Bool :=
  fr.any fun q ↦ decide (q.1 < off) && decide (off ≤ nextJump code q.1)

/-- **A callee frame reserved and not yet entered at offset `off`**: a frame hint before it, its
call site's jump at or after it. -/
noncomputable def pendAt (X : AlignCtx) (code : List OffsetInstruction) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint))
    (off : ℕ) : Bool :=
  pendIn code (frames X d) off

/-! ## The check -/

/-- A value's cell holds it in the frame: a hint-only cell, or (its index below `2^30`) a certificate
cell of the frame past its header. -/
noncomputable def allocCellOk (X : AlignCtx) (fs : ℕ) (v : V) : Bool :=
  (X.extra.lookup v.idx).isSome ||
    (decide (v.idx < 2 ^ 30) && decide (2 ≤ X.locAt v.idx) && decide (X.locAt v.idx < fs))

/-- A buffer hint compiles an allocation atom, its values in the frame: its own kind, an `allocDyn`
whose size cell holds `g^n` as an `alloc` of `n`, an `allocDyn` as the `allocAdvice` at its pointer. -/
noncomputable def compilesA (X : AlignCtx) (fs : ℕ) : Core.Hint → Prover.Exec.Hint → Bool
  | .alloc d n, .alloc p n' => allocCellOk X fs d && Nat.beq (X.locAt d.idx) p && Nat.beq n n'
  | .allocDyn d n, .allocDyn p c => allocCellOk X fs d && allocCellOk X fs n && Nat.beq (X.locAt d.idx) p &&
      Nat.beq (X.locAt n.idx) c
  | .allocDyn d n, .alloc p n' => allocCellOk X fs d && allocCellOk X fs n && Nat.beq (X.locAt d.idx) p &&
      X.pcAt (X.locAt n.idx) == some n'
  | .allocDyn d _, .allocAdvice p _ => allocCellOk X fs d && Nat.beq (X.locAt d.idx) p
  | _, _ => false

/-- The atoms and the buffer hints pair one for one, each compiling its own. -/
noncomputable def pairsA (X : AlignCtx) (fs : ℕ) : List Core.Hint → List Prover.Exec.Hint → Bool
  | [], [] => true
  | a :: as, h :: hs => compilesA X fs a h && pairsA X fs as hs
  | _, _ => false

/-- No buffer hint after a frame hint. -/
noncomputable def bufsFirst (X : AlignCtx) : Bool → List (ℕ × Prover.Exec.Hint) → Bool
  | _, [] => true
  | seen, q :: qs => (!seen || !isBuf X q.2) && bufsFirst X (seen || isFrame X q.2) qs

/-- Each late hint after an `allocAdvice` at its pointer. -/
def lateOk : List ℕ → List (ℕ × Prover.Exec.Hint) → Bool
  | _, [] => true
  | seen, q :: qs => (!isLate q.2 || seen.contains ((allocPtr q.2).getD 0)) &&
      lateOk (match q.2 with | .allocAdvice p _ => p :: seen | _ => seen) qs

/-- A frame hint: an `alloc`, `allocArm` or `allocFrames` before the next jump, which goes through
the hint's pointer as its frame cell. -/
def frameOk (code : List OffsetInstruction) (a : ℕ) (h : Prover.Exec.Hint) : Bool :=
  (match h with
    | .alloc .. | .allocArm .. | .allocFrames .. => true
    | _ => false) &&
  match code[nextJump code a]?, allocPtr h with
  | some (.jump _ _ q), some p => Nat.beq q p
  | _, _ => false

/-- Every jump through a call site's frame cell is the next jump of a frame hint at that cell, and
no jump is the next jump of two frame hints. -/
noncomputable def sitesOk (X : AlignCtx) (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint)) :
    ℕ → List OffsetInstruction → Bool
  | _, [] => true
  | i, ins :: rest => (match ins with
      | .jump _ _ q => (!(getF X.sites q).isSome ||
          fr.any (fun r ↦ allocPtr r.2 == some q && Nat.beq (nextJump code r.1) i)) &&
          decide ((fr.filter fun r ↦ Nat.beq (nextJump code r.1) i).length ≤ 1)
      | _ => true) && sitesOk X code fr (i + 1) rest

/-- No constant jump target pending, the frame hints `fr`. -/
noncomputable def targetsOk (X : AlignCtx) (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint)) :
    List OffsetInstruction → Bool
  | [] => true
  | ins :: rest => (match ins with
      | .jump _ od _ => match X.pcAt od with
        | some t => !pendIn code fr (t - X.entry)
        | none => true
      | _ => true) && targetsOk X code fr rest

/-- The allocation hints' check but the body's shape. -/
noncomputable def allocRest (X : AlignCtx) (fs : ℕ) (P : B2C.Plumb) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  Exec.listSeq (allocHints d) fun hs ↦
    Exec.listSeq (hs.filter fun q ↦ isFrame X q.2) fun fr ↦
    Exec.listSeq (hs.filter fun q ↦ isBuf X q.2) fun bs ↦
  pairsA X fs (topAllocs body) (bs.map (·.2)) &&
    (bs.isEmpty || Exec.natSeq (code.findIdx OffsetInstruction.isJump) fun fj ↦ bs.all fun q ↦ decide (q.1 ≤ fj)) &&
    bufsFirst X false hs && lateOk [] hs && fr.all (fun q ↦ frameOk code q.1 q.2) &&
    ((fr.isEmpty && P.sites.isEmpty) || (sitesOk X code fr 0 code && targetsOk X code fr code)) &&
    P.sites.all (fun s ↦ !pendIn code fr (s.r - X.entry))

/-- **The allocation hints' check** of a function: its context, frame size, plumbing, body, code and
advice; the body's shape apart, so that a long function checks it separately. -/
noncomputable def allocChk (X : AlignCtx) (fs : ℕ) (P : B2C.Plumb) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  allocShape body && allocRest X fs P body code d

end

end LeanVM.Guest.Bridge
