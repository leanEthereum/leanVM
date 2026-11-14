/-
  LeanVM.Guest.Bridge.PairDefs

  The data check the computed hints' bridge reads of each function: every value a computed hint names at its certificate cell in the frame, and every buffer it writes or reads allocated on every path.
-/

module

public import LeanVM.Guest.Memory.HintsCheck

/-!
# The computed hints' cells

A computed hint (`compHint`: neither a witness nor an allocation) reads and writes frame values (`hintFrame`: its input, its start cell, its frame destination, a `log2Ceil`'s frame bits) and at most one buffer (`hintBuf`: its heap destination, or the bits a `log2Ceil` reads). `pairChk extra locs n body`, for a function's hint-only cells `extra` (its alignment's), certificate cells `locs` and frame size `n`, checks every computed hint atom of the body at any depth (`blockAll`, by the recursor, for the kernel):

- each frame value at its certificate cell, in `[2, n)`, no hint-only cell, its number below `2^30`, where the alignment's cell map is the certificate's (`cellOk`);
- each buffer read from offset `0`, of length in `(0, 2^30)`, its pointer at its certificate cell or a hint-only cell, allocated and written whole by a hint among the body's spine (`spine`: its top-level atoms before the first return or branch or `match` that may return, on every path that returns).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A computed core hint: neither a witness nor an allocation. -/
def compHint : Core.Hint → Bool
  | .witness .. | .alloc .. | .allocDyn .. => false
  | _ => true

/-- A destination's frame values. -/
def stackVals : Dest → List V
  | .stack vs => vs
  | .heap .. => []

/-- **The frame values a computed hint names**: its input, its start cell, its frame destination,
a `log2Ceil`'s frame bits and output. -/
def hintFrame : Core.Hint → List V
  | .bits v _ _ d => v :: stackVals d
  | .bitsExp v _ d => v :: stackVals d
  | .digitsExp v _ _ _ _ sc d => v :: (sc.toList ++ stackVals d)
  | .windowsExp v _ _ _ d => v :: stackVals d
  | .limbs v ds => v :: ds
  | .log2Ceil b _ _ dst => dst :: stackVals b
  | .inverse x d => [x, d]
  | _ => []

/-- **The buffer a computed hint writes**, or a `log2Ceil` reads: pointer, offset, length. -/
def hintBuf : Core.Hint → Option (V × ℕ × ℕ)
  | .log2Ceil b _ _ _ => destHeap? b
  | h => (hintDest? h).bind destHeap?

/-- No `ret` in a block, nested ones included: by the recursor, for the kernel. -/
noncomputable def noRet : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ false) true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- No `ret` in arms. -/
noncomputable def noRetArms : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ false) true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- **A body's spine**: its top-level atoms before the first return, a branch or `match` that may
return included. -/
noncomputable def spine : List Stmt → List Atom
  | .atom a :: ss => a :: spine ss
  | .call .. :: ss => spine ss
  | .callIf .. :: ss => spine ss
  | .dispatch .. :: ss => spine ss
  | .ite _ z n :: ss => bif noRet z && noRet n then spine ss else []
  | .match_ _ arms :: ss => bif noRetArms arms then spine ss else []
  | _ => []

/-- An allocation atom's pointer. -/
def allocOf : Atom → Option V
  | .hint (.alloc d _) => some d
  | .hint (.allocDyn d _) => some d
  | _ => none

/-- A frame value at its certificate cell, in `[2, n)`, no hint-only cell (of `extra`), its number below
`2^30`. -/
def cellOk (extra : List (ℕ × ℕ)) (locs : List ℕ) (n : ℕ) (v : V) : Bool :=
  (extra.lookup v.idx).isNone && Nat.blt v.idx (2 ^ 30) && Nat.ble 2 (locs.getD v.idx 0) && Nat.blt (locs.getD v.idx 0) n

/-- A buffer from offset `0`, of length in `(0, 2^30)`, its pointer at its certificate cell or a
hint-only one, allocated and written whole on the spine `sp`. -/
def bufOk (extra : List (ℕ × ℕ)) (locs : List ℕ) (n : ℕ) (sp : List Atom) (b : V × ℕ × ℕ) : Bool :=
  Nat.beq b.2.1 0 && Nat.blt 0 b.2.2 && Nat.blt b.2.2 (2 ^ 30) &&
    (cellOk extra locs n b.1 || (extra.lookup b.1.idx).isSome) &&
    sp.any (fun a ↦ allocOf a == some b.1) && sp.any (fun a ↦ atomHeapDest? a == some b)

/-- **A computed hint atom's cells and buffer.** -/
def pairAtomOk (extra : List (ℕ × ℕ)) (locs : List ℕ) (n : ℕ) (sp : List Atom) : Atom → Bool
  | .hint h => !compHint h || ((hintFrame h).all (cellOk extra locs n) && match hintBuf h with
    | none => true
    | some b => bufOk extra locs n sp b)
  | _ => true

/-- Every atom of a block, at any depth, passes `p`: by the recursor, for the kernel. -/
noncomputable def blockAll (p : Atom → Bool) : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun a ↦ p a) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- Every atom of arms, at any depth, passes `p`. -/
noncomputable def armsAll (p : Atom → Bool) : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun a ↦ p a) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- **The computed hints' check of a function**: its hint-only cells, certificate cells, frame size
and body. -/
noncomputable def pairChk (extra : List (ℕ × ℕ)) (locs : List ℕ) (n : ℕ) (body : List Stmt) : Bool :=
  blockAll (pairAtomOk extra locs n (spine body)) body

end

end LeanVM.Guest.Bridge
