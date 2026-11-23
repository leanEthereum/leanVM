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
pointer a call site's callee frame cell; `isBuf`: the rest).

`allocChk X fs loop P body code d`, by `decide +kernel` per function (`scripts/bridge-cert/alloc.py`):

* the body's allocation atoms are top-level statements (`Stmt.noAlloc` elsewhere), and no statement
  before the last of them returns (`allocShape`), so every path allocates them all, in order;
* the buffer hints compile those atoms one for one, their values in the frame (`pairsA`): an `alloc`
  or `allocDyn` its own, an `allocDyn` whose size cell holds a power `g^n` an `alloc` of `n` cells;
* `curChk`, what the bump pointer's moves rest on: at most as many buffer hints as allocation atoms
  anywhere in the body (`cntL`); every jump before a buffer hint on a constant `0` or a forward jump
  in the frame to a constant pc, no buffer hint between (`bufsJumps`); no buffer hint after a frame
  hint; each frame hint an `alloc`, `allocArm` or
  `allocFrames` before the next jump, which goes through the hint's pointer, a call site's frame cell
  (`frameOk`), and every jump through a call site's frame cell exactly one frame hint's (`sitesOk`);
  no jump target pending: a constant target (`targetsOk`), a `match`'s arm (`blockM`, `armTgtsOk`), a
  call site's return pc; each address hint names a cell of the frame holding its address, or (in a
  loop helper) the next frame (`addrOk`).

The body's walks are their own conjuncts (`allocShape`, `curBody`; `allocRest` the rest), so that a
long function checks them in modules of their own.
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
  | .alloc p _ | .allocDyn p _ | .allocArm p _ _ | .allocFrames p _ _ _ _ => some p
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

/-- A buffer hint compiles an allocation atom, its values in the frame: its own kind, or an `allocDyn`
whose size cell holds `g^n`, `n < 2^28`, as an `alloc` of `n`. -/
noncomputable def compilesA (X : AlignCtx) (fs : ℕ) : Core.Hint → Prover.Exec.Hint → Bool
  | .alloc d n, .alloc p n' => allocCellOk X fs d && Nat.beq (X.locAt d.idx) p && Nat.beq n n'
  | .allocDyn d n, .allocDyn p c => allocCellOk X fs d && allocCellOk X fs n && Nat.beq (X.locAt d.idx) p &&
      Nat.beq (X.locAt n.idx) c
  | .allocDyn d n, .alloc p n' => allocCellOk X fs d && allocCellOk X fs n && Nat.beq (X.locAt d.idx) p &&
      X.pcAt (X.locAt n.idx) == some n' && Nat.blt n' (2 ^ 28)
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

/-- A jump before a buffer hint of `bs`, at offset `i`: on a constant `0` through no call site or next
frame, or a forward jump in the frame to a constant pc, through no call site or table, no return, no
buffer hint strictly between. -/
noncomputable def bufJumpOk (X : AlignCtx) (bs : List (ℕ × Prover.Exec.Hint)) (i oc od of : ℕ) : Bool :=
  (X.zeroAt oc && (getF X.sites of).isNone && !X.nextAt of) || (X.selfAt of && (getF X.sites of).isNone && !(Nat.beq od 0 && Nat.beq of 1) &&
    (getF X.arms od).isNone && match X.pcAt od with
      | some t => bs.all fun q ↦ !(decide (i < q.1) && decide (X.entry + q.1 < t))
      | none => false)

/-- Every jump before a buffer hint of `bs` passes `bufJumpOk`, the code from offset `i`. -/
noncomputable def bufsJumps (X : AlignCtx) (bs : List (ℕ × Prover.Exec.Hint)) : ℕ → List OffsetInstruction → Bool
  | _, [] => true
  | i, ins :: rest => (match ins with
      | .jump oc od of => !(bs.any fun q ↦ decide (i < q.1)) || bufJumpOk X bs i oc od of
      | _ => true) && bufsJumps X bs (i + 1) rest

/-- The allocation atoms of a block, nested ones included: by the recursor, for the kernel. -/
noncomputable def cntL : List Stmt → ℕ :=
  Stmt.rec_1 (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun a ↦ bif allocAtom a then 1 else 0) (fun _ _ _ hz hn ↦ hz + hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ 0)
    (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ 0) (fun _ ↦ 0) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

/-- Every `match` of a block, nested ones included, passes `ok` on its selector and arm count: by
the recursor, for the kernel. -/
noncomputable def blockM (ok : V → ℕ → Bool) : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun x arms ha ↦ ok x arms.length && ha) (fun _ _ _ ↦ true)
    (fun _ _ _ ↦ true) (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

/-- No arm target of a `match` of selector `x` and `n` arms pending, the frame hints `fr`: through
each table jump of the selector, each of its `n` slots. -/
noncomputable def armTgtsOk (X : AlignCtx) (P : B2C.Plumb) (code : List OffsetInstruction)
    (fr : List (ℕ × Prover.Exec.Hint)) (x : V) (n : ℕ) : Bool :=
  (armsOf P).all fun a ↦ !(Nat.beq a.2.1 x.idx) || (List.range n).all fun k ↦ match getF X.jt (a.2.2 + k) with
    | some t => !pendIn code fr (t - X.entry)
    | none => true

/-- An address hint of a function of frame size `fs`, a loop helper or not: a next frame's address
`fs` cells on, in a loop helper; a cell's address, below `fs`, at a cell holding it (`fpg`). -/
noncomputable def addrOk (X : AlignCtx) (fs : ℕ) (loop : Bool) : Prover.Exec.Hint → Bool
  | .frameAddress o => Nat.beq o fs && loop
  | .cellAddress q o => (match X.statOf q with
      | some (.fpg o') => Nat.beq o' o
      | _ => false) && Nat.blt o fs
  | _ => true

/-- **The allocation hints' check behind the bump pointer's moves, on the code**: every jump before
a buffer hint passing `bufJumpOk`, no buffer hint after a frame hint, each frame hint passing `frameOk`, every jump through a call site's frame cell one
frame hint's, no constant jump target or call site's return pc pending, every address hint passing
`addrOk`. -/
noncomputable def curCode (X : AlignCtx) (fs : ℕ) (loop : Bool) (P : B2C.Plumb) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  d.2.2.all (fun p ↦ p.2.all (addrOk X fs loop)) &&
  Exec.listSeq (allocHints d) fun hs ↦
    Exec.listSeq (hs.filter fun q ↦ isFrame X q.2) fun fr ↦
    Exec.listSeq (hs.filter fun q ↦ isBuf X q.2) fun bs ↦
  bufsJumps X bs 0 code && bufsFirst X false hs && fr.all (fun q ↦ frameOk X code q.1 q.2) &&
    ((fr.isEmpty && P.sites.isEmpty) || (sitesOk X code fr 0 code && targetsOk X code fr code)) &&
    P.sites.all (fun s ↦ !pendIn code fr (s.r - X.entry))

/-- **The allocation hints' check behind the bump pointer's moves, on the body**: at most as many
buffer hints as the body has allocation atoms, no `match` arm target pending. -/
noncomputable def curBody (X : AlignCtx) (P : B2C.Plumb) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  Exec.listSeq (allocHints d) fun hs ↦
    Exec.listSeq (hs.filter fun q ↦ isFrame X q.2) fun fr ↦
  decide (cntL body ≤ (hs.filter fun q ↦ isBuf X q.2).length) && (fr.isEmpty || blockM (armTgtsOk X P code fr) body)

/-- **The allocation hints' check behind the bump pointer's moves.** -/
noncomputable def curChk (X : AlignCtx) (fs : ℕ) (loop : Bool) (P : B2C.Plumb) (body : List Stmt)
    (code : List OffsetInstruction) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  curCode X fs loop P code d && curBody X P body code d

/-- The allocation hints' check on the code: the buffer hints compile the body's top-level allocation
atoms, and `curCode`. -/
noncomputable def allocRest (X : AlignCtx) (fs : ℕ) (loop : Bool) (P : B2C.Plumb) (body : List Stmt)
    (code : List OffsetInstruction) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  pairsA X fs (topAllocs body) (((allocHints d).filter fun q ↦ isBuf X q.2).map (·.2)) && curCode X fs loop P code d

/-- **The allocation hints' check** of a function: its context, frame size, plumbing, body, code and
advice; the body's walks apart, so that a long function checks them in modules of their own. -/
noncomputable def allocChk (X : AlignCtx) (fs : ℕ) (loop : Bool) (P : B2C.Plumb) (body : List Stmt)
    (code : List OffsetInstruction) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  allocShape body && curBody X P body code d && allocRest X fs loop P body code d

end

end LeanVM.Guest.Bridge
