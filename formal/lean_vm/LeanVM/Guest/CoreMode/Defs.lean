/-
  LeanVM.Guest.CoreMode.Defs

  The core route's heap data: cells over core names, witnesses, a function's heap signature and
  certificate; and the heap events of a path, read off `walk`, that the route's facts are about.
-/

module

public import LeanVM.Guest.Memory.Eval
public import LeanVM.Guest.Check
public import LeanVM.Guest.Renumber

/-!
# The core route's heap data

`formal/notes/core-mode.md`, section 3. Modedness splits in two: frame cells stay at the ISA (a data-free walk), heap cells move to the core IR, where each read of a function is proved written by an earlier event of its path or by a precondition. This file holds the data both halves and their composition share.

**Cells.** A heap cell over core names (`CCell`) is a monomial `∏ σ(.n b)^e` over value numbers (the guest's core values are `V.n b`, `Fn.renumber`), sorted by `b`, times `g^off`: `CCell.val σ c`, a word; its address `CCell.addr σ c` is the word's first limb, the cell a `DEREF` through a pointer of that word names at offset `0`. A `DEREF` through `p` at offset `off` names `cellAt σ p off`, as `LoadHolds` reads it.

**Events, in order.** The core semantics is relational over a final memory, so "written before" is read off the path: `walk σ body` (`Memory/Eval.lean`) is the sequence of events a valuation's path runs, in statement order, branches decided by `σ`; the tree track (`Bridge/Track.lean`) splits it at every frame's position into the events run (`pre`) and left. An atom of the path writes (`Writes`): a `load`, its cell (a store writes it, a read finds it written; `load`s the certificate does not name as reads are stores, which the frame walk confirms by the frame side being written), and a hint with a heap destination, each cell of it. An atom reads (`Reads`): a `load` the certificate names as a read (`HCert.readWit`, keyed by the atom's word, pointer and offset, so a store of a read word elsewhere is not a read), and a `log2Ceil` hint whose bits are on the heap, each bit. `Written H σ es x`: `x` is a precondition's address or written by an atom of `es`. What the route proves of a function (`CoreMode/HeapSound.lean`): on a path, every address an atom reads is `Written` by the events before it.

**Certificates.** `HSig` is the calling convention (milestone 1 uses `pre`, point cells over the parameter numbers, whose addresses the caller guarantees written; the rest is for calls and loops, later milestones, and empty for now). `HCert` adds the reads with their witnesses (`Wit`: a write event of the pass in scope, by its serial, or a precondition) and the residuals.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Cells -/

/-- **A heap cell over core names**: the word `∏ σ(.n b)^e · g^off`, the bases `(b, e)` sorted by
value number. -/
structure CCell where
  bases : List (ℕ × ℕ)
  off : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The product of the bases' powers. -/
def prodB (σ : Val) : List (ℕ × ℕ) → E
  | [] => 1
  | (b, e) :: l => σ (V.n b) ^ e * prodB σ l

/-- The word a cell's monomial names. -/
def CCell.val (σ : Val) (c : CCell) : E := prodB σ c.bases * ofK (addressOfIndex c.off)

/-- The address of a cell: its word's first limb. -/
def CCell.addr (σ : Val) (c : CCell) : K := (c.val σ).limb 0

/-- The address a `DEREF` through `p` at offset `off` names (`LoadHolds`). -/
def cellAt (σ : Val) (p : V) (off : ℕ) : K := (σ p).limb 0 * addressOfIndex off

/-! ## Witnesses and certificates -/

/-- An index of a run: a constant, or the exponent of the `g`-power a value holds. -/
inductive CIdx where
  | num (n : ℕ)
  | val (v : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- A run of cells `base · g^(stride · j)`, `lo ≤ j < hi` (loops, a later milestone). -/
structure CRun where
  base : CCell
  stride : ℕ
  lo : CIdx
  hi : CIdx
  deriving DecidableEq, Repr, Inhabited

/-- A closed statement on core names (the residual families, a later milestone). -/
inductive CRes where
  /-- The exponent of the first index is below the second's. -/
  | lt (a b : CIdx)
  /-- The value is nonzero. -/
  | nz (v : ℕ)
  /-- The cell is one of the run's. -/
  | sub (c : CCell) (r : CRun)
  deriving DecidableEq, Repr, Inhabited

/-- **Why a read's cell is written.** -/
inductive Wit where
  /-- The write event of this serial, in scope: the pass numbers write events in statement order,
  every arm of a branch, and keeps in scope those of the blocks enclosing the read. -/
  | ev (n : ℕ)
  /-- The function's precondition of this index. -/
  | pre (k : ℕ)
  /-- A run, with its residuals (loops, a later milestone). -/
  | run (r : ℕ) (res : List ℕ)
  /-- A residual alone (pointer tables, table indices, a later milestone). -/
  | res (k : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- **The heap calling convention**: cells over parameter numbers a caller guarantees written
(`pre`) and the callee guarantees on return (`post`), runs of them, termination facts. Milestone 1
uses `pre` only. -/
structure HSig where
  pre : List CCell
  post : List CCell
  preR : List CRun
  postR : List CRun
  term : List (CIdx × CIdx)
  deriving Repr, Inhabited

/-- The empty convention. -/
def HSig.empty : HSig := ⟨[], [], [], [], []⟩

/-- **A function's heap certificate**: its signature; its reads, by the word's value number `d`,
each read `load (.n d) (.n p) off` as `(p, off, w)` with its witness `w`; its residuals. -/
structure HCert where
  sig : HSig
  reads : List (ℕ × List (ℕ × ℕ × Wit))
  res : List CRes
  deriving Repr, Inhabited

/-- A value's number, `n` for `V.n n`. -/
def vnum (v : V) : Option ℕ := bif v.path.isEmpty && Nat.beq v.tag 0 then some v.idx else none

/-- The witness of the read `(p, off)` among a word's reads. -/
def findRead (p off : ℕ) : List (ℕ × ℕ × Wit) → Option Wit
  | [] => none
  | (p', off', w) :: l => bif Nat.beq p p' && Nat.beq off off' then some w else findRead p off l

/-- The reads by word, as a trie. -/
noncomputable def HCert.readT (H : HCert) : Exec.Trie (List (ℕ × ℕ × Wit)) :=
  H.reads.foldl (fun t r ↦ (Check.setF r.2 Exec.indexDepth t r.1).seq id) .nil

/-- **The witness of a read**, `none` for a `load` that is a store. -/
noncomputable def readWitT (T : Exec.Trie (List (ℕ × ℕ × Wit))) (d p : V) (off : ℕ) : Option Wit :=
  match vnum d, vnum p with
  | some d, some p => match Check.getF T d with
    | some l => findRead p off l
    | none => none
  | _, _ => none

/-- The witness of a read of the certificate. -/
noncomputable def HCert.readWit (H : HCert) (d p : V) (off : ℕ) : Option Wit := readWitT H.readT d p off

/-! ## Heap events of a path -/

/-- Where a hint writes heap words: the pointer, the offset of the first and their number. -/
def hintHeap : Hint → Option (V × ℕ × ℕ)
  | .witness _ (.heap p off len) => some (p, off, len)
  | .bits _ _ _ (.heap p off len) => some (p, off, len)
  | .bitsExp _ _ (.heap p off len) => some (p, off, len)
  | .digitsExp _ _ _ _ _ _ (.heap p off len) => some (p, off, len)
  | .windowsExp _ _ _ _ (.heap p off len) => some (p, off, len)
  | _ => none

/-- **The addresses an atom writes**: a `load`'s cell, a heap hint destination's cells. -/
def Writes (σ : Val) : Atom → K → Prop
  | .load _ p off, x => x = cellAt σ p off
  | .hint h, x => ∃ p off len, hintHeap h = some (p, off, len) ∧ ∃ k < len, x = cellAt σ p (off + k)
  | _, _ => False

/-- **The addresses an atom reads**: a `load` the certificate names as a read, the heap bits of a
`log2Ceil` hint. -/
def Reads (H : HCert) (σ : Val) : Atom → K → Prop
  | .load d p off, x => (H.readWit d p off).isSome ∧ x = cellAt σ p off
  | .hint (.log2Ceil (.heap p off len) nbits _ _), x => ∃ k < min nbits len, x = cellAt σ p (off + k)
  | _, _ => False

/-- **Written after the events `es`**: a precondition's address, or an address an atom of `es`
writes. -/
def Written (H : HCert) (σ : Val) (es : List Ev) (x : K) : Prop :=
  (∃ c ∈ H.sig.pre, c.addr σ = x) ∨ ∃ a, Ev.atom a ∈ es ∧ Writes σ a x

/-- **Every read of a path is written before it**: each address an atom of `es` reads is written
by the preconditions or the atoms before it. -/
def ReadsWritten (H : HCert) (σ : Val) (es : List Ev) : Prop :=
  ∀ es1 a es2 x, es = es1 ++ Ev.atom a :: es2 → Reads H σ a x → Written H σ es1 x

end

end LeanVM.Guest.CoreMode
