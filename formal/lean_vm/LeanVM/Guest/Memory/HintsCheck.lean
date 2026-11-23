/-
  LeanVM.Guest.Memory.HintsCheck

  The heap hint check of a function's body, as data the kernel evaluates: every heap hint writes
  into a `HeapBuf` its path allocates or only words its path loads.
-/

module

public import LeanVM.Guest.Core
public import LeanVM.Guest.Pow

/-!
# The heap hint check

`hintsOkL Γ ss` checks a block: each heap hint (`atomHeapDest?`) rests (`coverOk`) on the kept
atoms (`atomKeep`: loads, `HeapBuf`s, constants) before it on the path (`Γ`) or in the run of atoms
and calls right after it (`runAtoms`): a `HeapBuf` before it of at least `off + len` words at its
pointer (`allocCovers`; a dynamic one's size a constant `g^e`), or loads after it of each of its
words, in order (`loadsSeq`). `quickR` (a block without heap hints whose callees pass a test) and `calleesR` (its
callees pass it) walk a block by the recursors, which the kernel reduces faster than structural
recursion.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The destination a hint writes, the computed ones' with destinations included. -/
def hintDest? : Hint → Option Dest
  | .witness _ d => some d
  | .bits _ _ _ d => some d
  | .bitsExp _ _ d => some d
  | .digitsExp _ _ _ _ _ _ d => some d
  | .windowsExp _ _ _ _ d => some d
  | _ => none

/-- A heap destination's pointer, offset and length. -/
def destHeap? : Dest → Option (V × ℕ × ℕ)
  | .heap p off len => some (p, off, len)
  | .stack _ => none

/-! ## The check -/

/-- An atom's heap hint destination: its pointer, offset and length. -/
def atomHeapDest? : Atom → Option (V × ℕ × ℕ)
  | .hint h => (hintDest? h).bind destHeap?
  | _ => none

/-- Values compared, their indices first. -/
def vEq (a b : V) : Bool := a.idx == b.idx && decide (a = b)

/-- An atom a hint's words may rest on: a load, a `HeapBuf`, a constant. -/
def atomKeep : Atom → Bool
  | .load .. => true
  | .hint (.alloc ..) => true
  | .hint (.allocDyn ..) => true
  | .const .. => true
  | _ => false

/-- A constant word is `g^e`: the word `2^e` below the first reduction, by digits above. -/
def powWord (w : E) (e : ℕ) : Bool :=
  decide (e < 2 ^ 20) && decide (w.limb 1 = 0) &&
    (if e < 64 then decide (w.limb 0 = K.ofBits (2 ^ e)) else decide (w.limb 0 = Pow.gpowW e))

/-- A constant of `Q` makes `s` a `g^e` with `n ≤ e < n + 64`. -/
def sizeAtLeast (Q : List Atom) (s : V) (n : ℕ) : Bool :=
  Q.any fun a => match a with
    | .const d w => vEq d s && (List.range 64).any fun i => powWord w (n + i)
    | _ => false

/-- A `HeapBuf` of `Q` at `p` has at least `n` words. -/
def allocCovers (Q : List Atom) (p : V) (n : ℕ) : Bool :=
  Q.any fun a => match a with
    | .hint (.alloc d m) => vEq d p && decide (n ≤ m)
    | .hint (.allocDyn d s) => vEq d p && sizeAtLeast Q s n
    | _ => false

/-- **The loads of `Q` read `p·g^(o + k)`, `k < n`**, in this order. -/
def loadsSeq (p : V) : ℕ → ℕ → List Atom → Bool
  | _, 0, _ => true
  | _, _ + 1, [] => false
  | o, n + 1, a :: Q => match a with
    | .load _ q o' => if vEq q p && o' == o then loadsSeq p (o + 1) n Q else loadsSeq p o (n + 1) Q
    | _ => loadsSeq p o (n + 1) Q

/-- **A hint's heap words rest on the kept atoms before it, `Γ`, and after it, `post`**: a
`HeapBuf` before it holding them, or loads after it of each, in order. -/
def coverOk (Γ post : List Atom) (a : Atom) : Bool :=
  match atomHeapDest? a with
  | some (p, off, len) => allocCovers Γ p (off + len) || loadsSeq p off len post
  | none => true

/-- The kept atoms of a block's leading run of atoms and calls. -/
def runAtoms : List Stmt → List Atom
  | .atom a :: ss => if atomKeep a then a :: runAtoms ss else runAtoms ss
  | .call .. :: ss => runAtoms ss
  | .callIf .. :: ss => runAtoms ss
  | _ => []

/-- The kept atoms before the rest of a block, after a statement. -/
def keepAfter (Γ : List Atom) : Stmt → List Atom
  | .atom a => if atomKeep a then a :: Γ else Γ
  | _ => Γ

mutual
/-- A statement's check, `post` the kept atoms of the run after it. -/
def hintsOkS (Γ post : List Atom) : Stmt → Bool
  | .atom a => coverOk Γ post a
  | .ite _ z n => hintsOkL Γ z && hintsOkL Γ n
  | .match_ _ arms => hintsOkA Γ arms
  | .call .. => true
  | .callIf .. => true
  | .dispatch .. => true
  | .ret _ => true

/-- **The check of a block**: each heap hint rests on the kept atoms before it on the path (`Γ`)
or in the run of atoms and calls after it. -/
def hintsOkL (Γ : List Atom) : List Stmt → Bool
  | [] => true
  | s :: ss => hintsOkS Γ (runAtoms ss) s && hintsOkL (keepAfter Γ s) ss

/-- The arms' check. -/
def hintsOkA (Γ : List Atom) : List (List Stmt) → Bool
  | [] => true
  | a :: as => hintsOkL Γ a && hintsOkA Γ as
end

/-- A destination other than the heap, by the recursor. -/
noncomputable def destNoHeap (d : Dest) : Bool := Dest.rec (fun _ => true) (fun _ _ _ => false) d

/-- A hint without a heap destination, by the recursor. -/
noncomputable def hintNoHeap (h : Hint) : Bool :=
  Hint.rec (fun _ d => destNoHeap d) (fun _ _ _ d => destNoHeap d) (fun _ _ d => destNoHeap d)
    (fun _ _ _ _ _ _ d => destNoHeap d) (fun _ _ _ _ d => destNoHeap d) (fun _ _ => true)
    (fun _ _ _ _ => true) (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h

/-- An atom without a heap hint, by the recursor. -/
noncomputable def atomNoHeap (a : Atom) : Bool :=
  Atom.rec (fun _ _ => true) (fun _ _ _ => true) (fun _ _ _ => true) (fun _ _ => true)
    (fun _ _ _ => true) (fun _ _ => true) (fun _ _ _ => true) (fun _ _ _ _ _ => true)
    (fun _ _ => true) (fun _ _ _ _ => true) (fun _ _ => true) (fun h => hintNoHeap h) (fun _ _ => true) a

/-- **A statement without heap hints whose callees pass `p`**, by the recursors. -/
noncomputable def quickS (p : String → Bool) (s : Stmt) : Bool :=
  Stmt.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun a => atomNoHeap a) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba)
    (fun f _ _ => p f) (fun _ f _ => p f) (fun _ fs _ _ => fs.all p) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) s

/-- **A block without heap hints whose callees pass `p`**, by the recursors. -/
noncomputable def quickR (p : String → Bool) (ss : List Stmt) : Bool :=
  Stmt.rec_1 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun a => atomNoHeap a) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba)
    (fun f _ _ => p f) (fun _ f _ => p f) (fun _ fs _ _ => fs.all p) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) ss

/-- Arms without heap hints whose callees pass `p`, by the recursors. -/
noncomputable def quickA (p : String → Bool) (as : List (List Stmt)) : Bool :=
  Stmt.rec_2 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun a => atomNoHeap a) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba)
    (fun f _ _ => p f) (fun _ f _ => p f) (fun _ fs _ _ => fs.all p) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) as

/-- **A statement's callees pass `p`**, by the recursors. -/
noncomputable def calleesS (p : String → Bool) (s : Stmt) : Bool :=
  Stmt.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba)
    (fun f _ _ => p f) (fun _ f _ => p f) (fun _ fs _ _ => fs.all p) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) s

/-- **A block's callees pass `p`**, by the recursors. -/
noncomputable def calleesR (p : String → Bool) (ss : List Stmt) : Bool :=
  Stmt.rec_1 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba)
    (fun f _ _ => p f) (fun _ f _ => p f) (fun _ fs _ _ => fs.all p) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) ss

/-- Arms' callees pass `p`, by the recursors. -/
noncomputable def calleesA (p : String → Bool) (as : List (List Stmt)) : Bool :=
  Stmt.rec_2 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba)
    (fun f _ _ => p f) (fun _ f _ => p f) (fun _ fs _ _ => fs.all p) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) as

end
end LeanVM.Guest.Memory
