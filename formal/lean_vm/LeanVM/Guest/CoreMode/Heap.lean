/-
  LeanVM.Guest.CoreMode.Heap

  The core route's heap check of a function with no call and no loop: one pass over its body,
  each read's cell recomputed from the defining atoms and matched with its witness.
-/

module

public import LeanVM.Guest.CoreMode.Defs

/-!
# The heap check

`heapOk pows sigOf f H`: the core route's heap check (`formal/notes/core-mode.md`) for a function with no call and no loop. One pass over the body in statement order (`chkL`), its state (`HSt`) three things:

* the **environment**, a value number's monomial (`CCell`): the first of its defining atoms on the way, a constant power of `g` (`powOf`, by the powers' table `pows`), a product (`CCell.mul`, bases merged), a copy or an `assert ==` either way; a value without one is its own base (`baseC`);
* the **scope**, the cells of the write events on the way by serial: every `load` (a store writes its cell, a read finds it written) and each cell of a heap hint's destination;
* the next serial.

A `load` the certificate names as a read (`HCert.readWit`) must have the cell of its witness: the write event of that serial in scope, or the precondition of that index; the cells are compared as data, so the monomials must agree exactly. An `ite` or a `match` checks each block from the state before it, the serials running on through them, and goes on with the state before it and the last serial: what a block learns stays in it. A `ret` ends its block's pass (nothing after it runs). A call, a conditional call, a dispatch or a `log2Ceil` hint reading heap bits fails the check.

`heapOk` also asks the parameters to be `V.n 0, V.n 1, …`, the preconditions over them, and the rest of the signature empty: the facts a caller translates.

It is kept beside `heapOkC` (`HeapC.lean`, `HeapK.c`) for the functions with no call and no loop: their guarantees are cells their own loads witness (`postOk`, `CFun.post`), which `heapOkC`'s route does not take, and its pass keeps three tries where `heapOkC`'s keeps fifteen.

Written for the kernel: tries keyed by `ℕ` (`Check.getF`, `setF`), every state and cell handed on evaluated (`HSt.seq`, `CCell.seq`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Exec (Trie PowTree natSeq)
open LeanVM.Guest.Check (getF setF limbNat)

@[expose] public section

/-! ## Monomials -/

/-- A value number as its own monomial. -/
def baseC (k : ℕ) : CCell := ⟨[(k, 1)], 0⟩

/-- A base's power multiplied into sorted bases. -/
def insB (k e : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(k, e)]
  | (k', e') :: l =>
      bif Nat.beq k k' then (k, e + e') :: l
      else bif Nat.blt k k' then (k, e) :: (k', e') :: l
      else (k', e') :: insB k e l

/-- The product of two sorted bases. -/
def mergeB : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], l => l
  | (k, e) :: a, l => insB k e (mergeB a l)

/-- The product of two monomials. -/
def CCell.mul (a b : CCell) : CCell := ⟨mergeB a.bases b.bases, a.off + b.off⟩

/-- A monomial times `g^o`. -/
def CCell.shift (c : CCell) (o : ℕ) : CCell := ⟨c.bases, c.off + o⟩

/-- Two cells are equal. -/
def basesBeq : List (ℕ × ℕ) → List (ℕ × ℕ) → Bool
  | [], [] => true
  | (a, e) :: l, (a', e') :: l' => Nat.beq a a' && Nat.beq e e' && basesBeq l l'
  | _, _ => false

/-- Two cells are equal. -/
def CCell.beq (a b : CCell) : Bool := Nat.beq a.off b.off && basesBeq a.bases b.bases

section Seq

variable {β : Type}

/-- `k l`, `l` evaluated to its last number first. -/
def basesSeq : List (ℕ × ℕ) → (List (ℕ × ℕ) → β) → β
  | [], k => k []
  | (a, e) :: l, k => natSeq a fun a ↦ natSeq e fun e ↦ basesSeq l fun l ↦ k ((a, e) :: l)

/-- `k c`, `c` evaluated first. -/
def CCell.seq (c : CCell) (k : CCell → β) : β :=
  basesSeq c.bases fun bs ↦ natSeq c.off fun o ↦ k ⟨bs, o⟩

theorem basesSeq_eq : ∀ (l : List (ℕ × ℕ)) (k : List (ℕ × ℕ) → β), basesSeq l k = k l
  | [], _ => rfl
  | (a, e) :: l, k => by
    rw [basesSeq, Exec.natSeq_eq, Exec.natSeq_eq, basesSeq_eq l]

theorem CCell.seq_eq (c : CCell) (k : CCell → β) : c.seq k = k c := by
  rw [CCell.seq, basesSeq_eq, Exec.natSeq_eq]

end Seq

/-- The exponent of a constant power of `g`: `g^0 = 1`, the others by the table. -/
noncomputable def powOf (pows : PowTree) (c : E) : Option ℕ :=
  bif Nat.beq (limbNat c 1) 0 then
    (bif Nat.beq (limbNat c 0) 1 then some 0 else pows.find (limbNat c 0))
  else none

/-! ## The pass -/

/-- The pass's state: the environment, the scope, the next serial. -/
structure HSt where
  env : Trie CCell
  sc : Trie CCell
  n : ℕ

/-- `k st`, `st` evaluated first. -/
def HSt.seq {β : Type} (st : HSt) (k : HSt → β) : β :=
  st.env.seq fun e ↦ st.sc.seq fun s ↦ natSeq st.n fun n ↦ k ⟨e, s, n⟩

theorem HSt.seq_eq {β : Type} (st : HSt) (k : HSt → β) : st.seq k = k st := by
  rw [HSt.seq, Trie.seq_eq, Trie.seq_eq, Exec.natSeq_eq]

/-- The state with another next serial. -/
def HSt.withN (st : HSt) (n : ℕ) : HSt := ⟨st.env, st.sc, n⟩

/-- What the pass reads: the powers' table, the reads by word, the preconditions by index. -/
structure HX where
  pows : PowTree
  R : Trie (List (ℕ × ℕ × Wit))
  pre : Trie CCell

/-- A list's entries stored into the trie `t` from key `i` on, each evaluated. -/
noncomputable def trieFrom {α : Type} : List α → ℕ → Trie α → Trie α
  | [], _, t => t
  | a :: l, i, t => (setF a Exec.indexDepth t i).seq fun t ↦ natSeq (i + 1) fun i ↦ trieFrom l i t

/-- A value's monomial, if it is `V.n k`. -/
noncomputable def monoOf (env : Trie CCell) (v : V) : Option CCell :=
  match vnum v with
  | some k => some ((getF env k).getD (baseC k))
  | none => none

/-- A value's first monomial: kept if it has one. -/
noncomputable def envPut (env : Trie CCell) (k : ℕ) (c : CCell) : Trie CCell :=
  match getF env k with
  | some _ => env
  | none => c.seq fun c ↦ (setF c Exec.indexDepth env k).seq id

/-- The state with a value's first monomial. -/
noncomputable def HSt.def (st : HSt) (k : ℕ) (c : CCell) : HSt := ⟨envPut st.env k c, st.sc, st.n⟩

/-- A write event of the cell `c`, at the next serial. -/
noncomputable def HSt.push (st : HSt) (c : CCell) : HSt :=
  (setF c Exec.indexDepth st.sc st.n).seq fun s ↦ ⟨st.env, s, st.n + 1⟩

/-- The write events of the cells `m · g^(off + j)`, `j < len`, in order. -/
noncomputable def HSt.pushN (st : HSt) (m : CCell) (off : ℕ) : ℕ → HSt
  | 0 => st
  | len + 1 => (st.pushN m off len).seq fun st ↦ (m.shift (off + len)).seq fun c ↦ st.push c

/-- `x = y`, by a copy or an `assert ==`: the first of the two without a monomial gets the
other's. -/
noncomputable def copyH (st : HSt) (x y : V) : HSt :=
  match vnum x, vnum y with
  | some kx, some ky => match getF st.env kx, getF st.env ky with
    | none, _ => st.def kx ((getF st.env ky).getD (baseC ky))
    | some cx, none => st.def ky cx
    | some _, some _ => st
  | _, _ => st

/-- **A witness of the cell `c`**: the write event of its serial in scope, or the precondition of
its index, of that very cell. -/
noncomputable def witOk (pre : Trie CCell) (sc : Trie CCell) (c : CCell) : Wit → Bool
  | .ev n => match getF sc n with
    | some c' => c'.beq c
    | none => false
  | .pre k => match getF pre k with
    | some c' => c'.beq c
    | none => false
  | _ => false

/-- A `load` of the cell `c`: a store, or a read with a witness of `c`. -/
noncomputable def loadOk (X : HX) (sc : Trie CCell) (d p : V) (off : ℕ) (c : CCell) : Bool :=
  match readWitT X.R d p off with
  | some w => witOk X.pre sc c w
  | none => true

/-- A hint reading heap bits. -/
def heapRead : Hint → Bool
  | .log2Ceil (.heap ..) .. => true
  | _ => false

/-- **An atom**: its defining equation in the environment, its write events in the scope, its read
witnessed. -/
noncomputable def atomH (X : HX) (st : HSt) : Atom → Option HSt
  | .const d c => match vnum d, powOf X.pows c with
    | some k, some e => some (st.def k ⟨[], e⟩)
    | _, _ => some st
  | .mul d a b => match vnum d, monoOf st.env a, monoOf st.env b with
    | some k, some ma, some mb => some (st.def k (ma.mul mb))
    | _, _, _ => some st
  | .copy d s => some (copyH st d s)
  | .assertEq a b => some (copyH st a b)
  | .load d p off => match monoOf st.env p with
    | some m => (m.shift off).seq fun c ↦ bif loadOk X st.sc d p off c then some (st.push c) else none
    | none => none
  | .hint h => match hintHeap h with
    | some (p, off, len) => match monoOf st.env p with
      | some m => some (st.pushN m off len)
      | none => none
    | none => bif heapRead h then none else some st
  | _ => some st

mutual
/-- **The pass over a block**: the state at its end, or at its `ret`. -/
noncomputable def chkL (X : HX) : List Stmt → HSt → Option HSt
  | [], st => some st
  | .atom a :: ss, st => match atomH X st a with
    | some st' => st'.seq fun st' ↦ chkL X ss st'
    | none => none
  | .ite _ z n :: ss, st => match chkL X z st with
    | some s1 => match chkL X n (st.withN s1.n) with
      | some s2 => (st.withN s2.n).seq fun st' ↦ chkL X ss st'
      | none => none
    | none => none
  | .match_ _ arms :: ss, st => match chkArms X arms st with
    | some n => (st.withN n).seq fun st' ↦ chkL X ss st'
    | none => none
  | .ret _ :: _, st => some st
  | _ :: _, _ => none

/-- The pass over each arm, from the state before the `match`: the last serial. -/
noncomputable def chkArms (X : HX) : List (List Stmt) → HSt → Option ℕ
  | [], st => some st.n
  | a :: as, st => match chkL X a st with
    | some s1 => chkArms X as (st.withN s1.n)
    | none => none
end

/-! ## The check -/

/-- The parameters are `V.n i`, `i` from `i0`. -/
def paramsN : List V → ℕ → Bool
  | [], _ => true
  | v :: vs, i => (match vnum v with
    | some k => Nat.beq k i
    | none => false) && paramsN vs (i + 1)

/-- The cells are over the first `m` value numbers. -/
def preOver (m : ℕ) (cs : List CCell) : Bool :=
  cs.all fun c ↦ c.bases.all fun b ↦ Nat.blt b.1 m

/-- `heapOk`'s signature: preconditions only. -/
def HSig.pointsOnly (G : HSig) : Bool :=
  G.post.isEmpty && G.preR.isEmpty && G.postR.isEmpty && G.term.isEmpty

/-- **The heap check** of a function with no call and no loop: its parameters `V.n i`, its
preconditions over them and nothing else in its signature, and the pass over its body. Callees'
signatures (`sigOf`) are for the check with calls (`heapOkC`). -/
noncomputable def heapOk (pows : PowTree) (_sigOf : String → HSig) (f : Fn) (H : HCert) : Bool :=
  paramsN f.params 0 && preOver f.params.length H.sig.pre && H.sig.pointsOnly &&
    H.readT.seq fun R ↦ (trieFrom H.sig.pre 0 .nil).seq fun P ↦
      (chkL ⟨pows, R, P⟩ f.body ⟨.nil, .nil, 0⟩).isSome

end

end LeanVM.Guest.CoreMode
