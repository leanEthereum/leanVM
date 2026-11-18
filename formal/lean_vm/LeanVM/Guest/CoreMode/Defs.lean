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

**Certificates.** `HSig` is the calling convention (milestone 1 uses `pre`, point cells over the parameter numbers, whose addresses the caller guarantees written; calls and loops, `CoreMode/HeapC.lean`, use all of it, over slots: the parameters, then the returned words). `HCert` adds the reads with their witnesses (`Wit`: a write event of the pass in scope, by its serial, a precondition, or a run), the residuals, and the witnesses of the calls' callee preconditions and of the returns' guarantees.
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

/-- An index of a run: a constant, the exponent of the `g`-power a value (a slot, in a signature)
holds, or that of a monomial's word. -/
inductive CIdx where
  | num (n : ℕ)
  | val (v : ℕ)
  | mono (c : CCell)
  deriving DecidableEq, Repr, Inhabited

/-- A run of cells `base · g^(stride · j)`, `lo ≤ j < hi` (loops, a later milestone). -/
structure CRun where
  base : CCell
  stride : ℕ
  lo : CIdx
  hi : CIdx
  deriving DecidableEq, Repr, Inhabited

/-- **A branch condition** on core names: arm `j` of a `match`/`dispatch` on the value `x` (its word
`g^j`), or the `0` / nonzero side of an `ite` / `callIf` guard `c`. -/
inductive CCond where
  | arm (x j : ℕ)
  | zero (c : ℕ)
  | nonzero (c : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- A closed statement on core names (the residual families, a later milestone). -/
inductive CRes where
  /-- The exponent of the first index is below the second's. -/
  | lt (a b : CIdx)
  /-- The value is nonzero. -/
  | nz (v : ℕ)
  /-- The cell is one of the run's. -/
  | sub (c : CCell) (r : CRun)
  /-- Every cell of the first run is one of the second's. -/
  | subR (q r : CRun)
  /-- The statement where the branch conditions hold (a residual asked on a branch path). -/
  | under (g : List CCond) (r : CRes)
  /-- The cell is one of the cells (its address among theirs). -/
  | subP (c : CCell) (cs : List CCell)
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
  /-- A pointer fact in scope, by its point serial: the cell read is past the word loaded from the
  fact's cell; or, for a pointer fact needed, that very fact. -/
  | pf (n : ℕ)
  /-- A pointer run in scope, by its run serial, with its residuals: the cell read is past the word
  loaded from a cell of the run; or, for a pointer fact or run needed, inside it. -/
  | pfr (r : ℕ) (res : List ℕ)
  /-- A pointer fact needed at a cell whose word a load event of this point serial named, the cells
  past it each witnessed by the witnesses that follow. -/
  | word (m : ℕ)
  /-- A pointer run needed with constant bounds, each of its cells' pointer facts witnessed by the
  witnesses that follow. -/
  | pts
  /-- A run needed with constant bounds, the upper at most the lower: no cell. -/
  | empty
  /-- A dispatch arm that cannot run: a fact (the own termination facts and these residuals) puts its
  selector's exponent below the arm's index. -/
  | skip (res : List ℕ)
  /-- A run needed, split at the constant index `k`: the witnesses of its part below `k`, then of its
  part from `k`, follow. -/
  | cat (k : ℕ)
  /-- A run needed, of stride `S'`, merged from its `S` residues: the witnesses of each residue run
  `base·g^(S'·r)`, `r < S`, of stride `S'·S` from the lower bound's `S`-th part to the upper bound's
  `S`-th root, follow; facts of these residuals give the root's exponent. -/
  | mrg (s : ℕ) (res : List ℕ)
  /-- A cell among cells: residual `k`, `subP c cs` at the site, and each cell of `cs` the write event of
  the point serial at its position in `ns`. -/
  | perm (k : ℕ) (ns : List ℕ)
  /-- A cell of a run in scope of lower bound `g^0` extended by the point before it (`base·g^-stride`,
  witnessed by `q`): the cell's index at most the upper bound's, which has an exponent by a fact. -/
  | prep (r : ℕ) (q : Wit) (res : List ℕ)
  /-- Leading a dispatch's witnesses: its returned word `j` is a pointer whose cells at the offsets
  every arm kept writes (each arm's witnesses of them follow its preconditions'). -/
  | vp (j : ℕ) (offs : List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- **The heap calling convention**: cells over parameter numbers a caller guarantees written
(`pre`) and the callee guarantees on return (`post`), runs of them, termination facts, the
returned words' monomials over the parameters (`retM`: `(k, c)`, returned word `k` is `c`'s word),
and pointer facts (`preP`, `postP`: `(c, offs)`, the word at `c` points to written cells at the
offsets `offs`), runs of them (`prePR`, `postPR`: every cell of the run holds such a pointer).
Milestone 1 uses `pre` only. Every field defaults to `[]`: write a signature as a structure
instance naming the fields it uses. -/
structure HSig where
  pre : List CCell := []
  post : List CCell := []
  preR : List CRun := []
  postR : List CRun := []
  term : List (CIdx × CIdx) := []
  retM : List (ℕ × CCell) := []
  preP : List (CCell × List ℕ) := []
  postP : List (CCell × List ℕ) := []
  prePR : List (CRun × List ℕ) := []
  postPR : List (CRun × List ℕ) := []
  /-- Words at return: `(i, m)`, the word at `post` cell `i` is `m`'s, both over slots. -/
  postV : List (ℕ × CCell) := []
  /-- Ghost slots: slot `m + j` (`m` the parameter count, `j < ghosts`) of `preR`, `preP`, `prePR` is a
  word the caller names at each call (`HCert.gargs`), no parameter; in the own pass, value `GB + j`. -/
  ghosts : ℕ := 0
  deriving Repr, Inhabited

/-- The empty convention. -/
def HSig.empty : HSig := {}

/-- **A function's heap certificate**: its signature; its reads, by the word's value number `d`,
each read `load (.n d) (.n p) off` as `(p, off, w)` with its witness `w`; its residuals; and, for the
check with calls and loops (`CoreMode/HeapC.lean`), the witnesses of each call statement's callee
preconditions (`calls`, by call serial: the callee's `pre` cells then its `preR` runs) and of the own
guarantees at each `ret` (`rets`, by ret serial: `post` then `postR`), and the value numbers of
the quotients the check divides out (`divs`: `q` of a `mul d q b`, `b` a constant). Milestone 1's
check reads none of them. -/
structure HCert where
  sig : HSig
  reads : List (ℕ × List (ℕ × ℕ × Wit))
  res : List CRes
  calls : List (List Wit) := []
  rets : List (List Wit) := []
  divs : List ℕ := []
  /-- Reads taking the word stored at their cell (`hvs`, by value number). -/
  hvs : List ℕ := []
  /-- Callees' ghost words, by call: `(g, args, ms)`, a call of `g` on the values `V.n a`, `a ∈ args`,
  names its callee's ghost `j` by the monomial `ms[j]` over this function's values. -/
  gargs : List (String × List ℕ × List CCell) := []
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
