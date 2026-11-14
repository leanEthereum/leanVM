module

public import LeanVM.Guest.ExecCore
public import Statement.Prover.Execute

/-!
# The mode walk: its domain and its rules

What a function's walk knows at an instruction, relative to its frame (`Abs`): the frame offsets
written (`w`), the words known of frame cells (`v`: a product `Mono` of powers of the frame pointer,
of `g` and of *bases*, or a constant), the frame cells known nonzero (`nz`), the heap cells known
written (`h`, each named by a product), runs of them (`r`, a `Rng`: the cells named by
`q·g^(S·j + d)` for `j` between two exponents), the words known of heap cells (`hv`), inequalities
between exponents (`lt`, over `Idx`: a constant, or a base's exponent plus a constant), the last
products (`pr`, for the range-check and `!=` gadgets), sums by their cell (`xs`), and runs of
pointers (`p`: each cell of a run holds a word naming a cell whose given cells past it are written,
which a load from the run teaches of the loaded cell). A base is a
frame cell (`fr o`) or cell `d` past the cell a frame cell names (`hp q d`). A heap cell of the frame
itself (`fp^1·g^d`) is frame cell `d`, kept in `w` and `v`.

`stepOp` is one instruction, `stepHint` one hint: the cells either reads must be known written (else
`none`), and what it surely writes, and what that teaches, joins. A `DEREF` of mode `cell` stores when
its frame side is known written, loads when its heap side is, and otherwise links, learning nothing.
`Abs.inter` is what two paths into a join both know. Calls, tail calls and returns (`entryOk`,
`afterCall`, `tailOk`, `retOk`) read the callee's `Sig`: the cells its walk needs written at entry,
the heap facts it needs over its own bases (`pre`, `preR`, `preP`), and those it guarantees at return
(`ret`, its returned words `retV`, `post`, `postR`, `postP`, a loop's `postL`, `postLP`), translated
through the caller's knowledge of the callee frame (`trBase`). `walk` runs a function's code once,
forward (`runCode`), keeping at most two paths apart at each offset and meeting more into one; the
pending edges of a jump go in groups by their targets (`Grp`), a group of three or more paths met at
once, so a table jump's arms share one state; the fall-through of a `JUMP` on a sum learns its two
terms equal (`Abs.learn0`). At a cut (`Fun.cuts`) the walk goes on from given weaker paths and
pending edges (`cutAt`), so a long function is checked in windows (`Mode/Win.lean`). The states are
evaluated as they are built (`Abs.force`, `foldlA`), for the kernel. Their meaning is
`Mode/Sem.lean`, their soundness `Mode/Sound*.lean`.

Everything here is structural recursion over `ℕ`, lists and tries, for the kernel.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec
open LeanVM.Prover.Exec (Op Hint BitsDest maxCells)

@[expose] public section

/-! ## Products -/

/-- A base of a product: frame cell `o`, or cell `d` past the cell frame cell `q` names. -/
inductive Base where
  | fr (o : ℕ)
  | hp (q d : ℕ)
  deriving DecidableEq, Repr

/-- Equality of bases, as a `Bool`. -/
def Base.beq : Base → Base → Bool
  | .fr a, .fr b => a == b
  | .hp a b, .hp c d => a == c && b == d
  | _, _ => false

/-- The order bases are kept sorted in. -/
def Base.blt : Base → Base → Bool
  | .fr a, .fr b => a < b
  | .fr _, .hp _ _ => true
  | .hp _ _, .fr _ => false
  | .hp a b, .hp c d => a < c || (a == c && b < d)

/-- `fp^fp · g^k · ∏ b^e` over the bases `bs`. -/
structure Mono where
  fp : ℕ
  k : ℕ
  bs : List (Base × ℕ)
  deriving DecidableEq, Repr

/-- Equality of base lists, as a `Bool`. -/
def bsBeq : List (Base × ℕ) → List (Base × ℕ) → Bool
  | [], [] => true
  | (a, e) :: as, (b, f) :: bs => a.beq b && e == f && bsBeq as bs
  | _, _ => false

/-- Equality of products, as a `Bool`. -/
def Mono.beq (a b : Mono) : Bool := a.fp == b.fp && a.k == b.k && bsBeq a.bs b.bs

/-- `1`. -/
def Mono.one : Mono := ⟨0, 0, []⟩

/-- `g^e`. -/
def Mono.gp (e : ℕ) : Mono := ⟨0, e, []⟩

/-- Frame cell `o`'s word. -/
def Mono.root (o : ℕ) : Mono := ⟨0, 0, [(.fr o, 1)]⟩

/-- `fp · g^d`, the address of frame cell `d`. -/
def Mono.own (d : ℕ) : Mono := ⟨1, d, []⟩

/-- The product times `g^o`. -/
def Mono.shift (m : Mono) (o : ℕ) : Mono := ⟨m.fp, m.k + o, m.bs⟩

/-- Multiply a sorted base list by `b^e`. -/
def insertBs (a : Base × ℕ) : List (Base × ℕ) → List (Base × ℕ)
  | [] => [a]
  | b :: bs =>
    if a.1.beq b.1 then (b.1, a.2 + b.2) :: bs
    else if a.1.blt b.1 then a :: b :: bs
    else b :: insertBs a bs

/-- The product of two base lists. -/
def mulBs : List (Base × ℕ) → List (Base × ℕ) → List (Base × ℕ)
  | [], l => l
  | a :: as, l => insertBs a (mulBs as l)

/-- The product of two products. -/
def Mono.mul (a b : Mono) : Mono := ⟨a.fp + b.fp, a.k + b.k, mulBs a.bs b.bs⟩

/-- The base list `bs` divided by `b^e`, if it holds `b^e` exactly. -/
def removeBs (a : Base × ℕ) : List (Base × ℕ) → Option (List (Base × ℕ))
  | [] => none
  | b :: bs =>
    if a.1.beq b.1 then (if a.2 == b.2 then some bs else none)
    else (removeBs a bs).map (b :: ·)

/-- The frame cell `d` a product names, when it is `fp · g^d`. -/
def Mono.ownCell (m : Mono) : Option ℕ :=
  if m.fp == 1 && m.bs.isEmpty && m.k < 2 ^ 62 then some m.k else none

/-- The frame cell a product is the word of, when it is `[q]`. -/
def Mono.rootCell (m : Mono) : Option ℕ :=
  match m with
  | ⟨0, 0, [(.fr q, 1)]⟩ => some q
  | _ => none

/-! ## Words, exponents, runs -/

/-- A frame cell's known word: a product, or the constant `k0 + k1·y` (`immediateWord`). -/
inductive Val where
  | m (x : Mono)
  | imm (k0 k1 : ℕ)
  /-- The word of the heap cell `x · g^d` names (a jump table's entry). -/
  | tab (x : Base) (d : ℕ)
  deriving DecidableEq, Repr

/-- Equality of words, as a `Bool`. -/
def Val.beq : Val → Val → Bool
  | .m a, .m b => a.beq b
  | .imm a b, .imm c d => a == c && b == d
  | .tab x a, .tab y b => x.beq y && a == b
  | _, _ => false

/-- An exponent: the constant `n`, or the exponent of base `x`'s word plus `c`. -/
inductive Idx where
  | num (n : ℕ)
  | ex (x : Base) (c : ℕ)
  deriving DecidableEq, Repr

/-- Equality of exponents, as a `Bool`. -/
def Idx.beq : Idx → Idx → Bool
  | .num a, .num b => a == b
  | .ex x a, .ex y b => x.beq y && a == b
  | _, _ => false

/-- The exponent plus one. -/
def Idx.succ : Idx → Idx
  | .num n => .num (n + 1)
  | .ex x c => .ex x (c + 1)

/-- The exponent plus `t`. -/
def Idx.shift (i : Idx) (t : ℕ) : Idx :=
  match i with
  | .num n => .num (n + t)
  | .ex x c => .ex x (c + t)

/-- The `t` with `b = a + t`, when `a` and `b` are the same base's (or constants) and `a`'s constant
is at most `b`'s. -/
def Idx.off : Idx → Idx → Option ℕ
  | .num a, .num b => if a ≤ b then some (b - a) else none
  | .ex x a, .ex y b => if x.beq y && a ≤ b then some (b - a) else none
  | _, _ => none

/-- `a ≤ b` whatever the bases' words: equal bases, or a constant below the other's constant. -/
def Idx.sle : Idx → Idx → Bool
  | .num a, .num b => a ≤ b
  | .num a, .ex _ c => a ≤ c
  | .ex x a, .ex y b => x.beq y && a ≤ b
  | .ex _ _, .num _ => false

/-- The cells named by `q · g^(S·j + d)` for `j` from exponent `lo` to below exponent `hi`. -/
structure Rng where
  q : Mono
  lo : Idx
  hi : Idx
  S : ℕ
  d : ℕ
  deriving DecidableEq, Repr

/-- Equality of runs, as a `Bool`. -/
def Rng.beq (a b : Rng) : Bool :=
  a.q.beq b.q && a.lo.beq b.lo && a.hi.beq b.hi && a.S == b.S && a.d == b.d

/-- Facts that hold when base `x`'s exponent is `j`: heap cells written, runs, runs of pointers,
exponents in order, heap words. -/
structure Cnd where
  x : Base
  j : ℕ
  h : List Mono
  r : List Rng
  p : List (Rng × List ℕ)
  lt : List (Idx × Idx)
  hv : List (Mono × Val)

/-! ## The state -/

/-- What the walk knows at an instruction. -/
structure Abs where
  /-- Frame offsets written. -/
  w : Trie Unit
  /-- Words of frame cells. -/
  v : Trie Val
  /-- Frame cells nonzero. -/
  nz : Trie Unit
  /-- Words of heap cells. -/
  hv : List (Mono × Val)
  /-- Heap cells written. -/
  h : List Mono
  /-- Runs of heap cells written. -/
  r : List Rng
  /-- Exponents in order: `a < b`. -/
  lt : List (Idx × Idx)
  /-- The last products `(a, b, c)`: `[c] = [a]·[b]`. -/
  pr : List (ℕ × ℕ × ℕ)
  /-- Sums, by their cell: `c ↦ (a, b)`, `[c] = [a] + [b]`. -/
  xs : Trie (ℕ × ℕ)
  /-- Runs of pointers: each cell of the run holds a word naming a cell whose cells `os` past it are
  written. -/
  p : List (Rng × List ℕ)
  /-- Facts under a condition on a base's exponent (a table call's arms). -/
  c : List Cnd

/-- `k A`, `A` and its tries evaluated first. -/
def Abs.force {β : Type} (A : Abs) (k : Abs → β) : β :=
  match A with
  | ⟨w, v, nz, hv, h, r, lt, pr, xs, p, c⟩ =>
    w.seq fun w ↦ v.seq fun v ↦ nz.seq fun nz ↦ xs.seq fun xs ↦ k ⟨w, v, nz, hv, h, r, lt, pr, xs, p, c⟩

/-- `l.foldl f A`, each state evaluated before the next step. -/
noncomputable def foldlA {α : Type} (f : Abs → α → Abs) (A : Abs) (l : List α) : Abs :=
  List.rec (motive := fun _ ↦ Abs → Abs) (fun A ↦ A) (fun x _ ih A ↦ (f A x).force ih) l A

/-- `l.foldl (·.set () envDepth ·) t`, each trie evaluated before the next step. -/
noncomputable def foldlT (t : Trie Unit) (l : List ℕ) : Trie Unit :=
  List.rec (motive := fun _ ↦ Trie Unit → Trie Unit) (fun t ↦ t)
    (fun o _ ih t ↦ (t.set () envDepth o).seq ih) l t

/-- `l.mapM f`, its elements evaluated in order. -/
noncomputable def mapOpt {α β : Type} (f : α → Option β) (l : List α) : Option (List β) :=
  List.rec (motive := fun _ ↦ List β → Option (List β)) (fun acc ↦ some acc.reverse)
    (fun x _ ih acc ↦ match f x with
      | some y => ih (y :: acc)
      | none => none) l []

/-- Frame offset `o` is known written. -/
def Abs.hasW (A : Abs) (o : ℕ) : Bool := (A.w.get o).isSome

/-- Frame offset `o` is known nonzero. -/
def Abs.hasNz (A : Abs) (o : ℕ) : Bool := (A.nz.get o).isSome

/-- Frame offset `o` written. -/
noncomputable def Abs.addW (A : Abs) (o : ℕ) : Abs := { A with w := A.w.set () envDepth o }

/-- Frame offset `o` nonzero. -/
noncomputable def Abs.addNz (A : Abs) (o : ℕ) : Abs := { A with nz := A.nz.set () envDepth o }

/-- Frame offset `o` holds `x`, unless its word is known. -/
noncomputable def Abs.addV (A : Abs) (o : ℕ) (x : Val) : Abs :=
  match A.v.get o with
  | some _ => A
  | none => { A with v := A.v.set x envDepth o }

/-- The word frame cell `o` is known to hold, as a product (its own base unless known). -/
def Abs.mono (A : Abs) (o : ℕ) : Option Mono :=
  match A.v.get o with
  | some (.m x) => some x
  | some _ => none
  | none => some (.root o)

/-- The word of the heap cell a product names, if known: a frame cell's, or a recorded one. -/
def Abs.hvGet (A : Abs) (k : Mono) : Option Val :=
  match k.ownCell with
  | some d => if A.hasW d then some ((A.v.get d).getD (.m (.root d))) else none
  | none => (A.hv.find? fun p ↦ p.1.beq k).map (·.2)

/-- The heap cell `k` holds `x` (recorded unless known). -/
noncomputable def Abs.addHv (A : Abs) (k : Mono) (x : Val) : Abs :=
  match k.ownCell with
  | some d => A.addV d x
  | none => if A.hv.any (fun p ↦ p.1.beq k) then A else { A with hv := (k, x) :: A.hv }

/-- The heap cell `k` written. -/
noncomputable def Abs.addH (A : Abs) (k : Mono) : Abs :=
  match k.ownCell with
  | some d => A.addW d
  | none => if A.h.any (·.beq k) then A else { A with h := k :: A.h }

/-- Exponents in order. -/
def Abs.addLt (A : Abs) (a b : Idx) : Abs := { A with lt := (a, b) :: A.lt }

/-- `a ≤ b`, directly, or through a known `p < q` with `b = q + t` and `a ≤ p + 1 + t`. -/
def Abs.le (A : Abs) (a b : Idx) : Bool :=
  a.sle b || A.lt.any fun p ↦ match p.2.off b with
    | some t => a.sle (p.1.succ.shift t)
    | none => false

/-- `a < b`, directly, or through a known `p < q` with `a = p + t` and `q + t ≤ b`. -/
def Abs.ltI (A : Abs) (a b : Idx) : Bool :=
  a.succ.sle b || A.lt.any fun p ↦ match p.1.off a with
    | some t => (p.2.shift t).sle b
    | none => false

/-- The exponent `k` names in run `r`, when `k = r.q · x^S · g^(S·c + d)` (`x + c`) or
`k = r.q · g^(S·c + d)` (`c`). -/
def Rng.idxOf (r : Rng) (k : Mono) : Option Idx :=
  if k.fp == r.q.fp && r.q.k + r.d ≤ k.k && (k.k - r.q.k - r.d) % r.S == 0 && 0 < r.S then
    if bsBeq k.bs r.q.bs then some (.num ((k.k - r.q.k - r.d) / r.S))
    else match k.bs.find? (fun p ↦ p.2 == r.S && !(r.q.bs.any fun q ↦ q.1.beq p.1)) with
      | some (x, _) =>
        match removeBs (x, r.S) k.bs with
        | some rest => if bsBeq rest r.q.bs then some (.ex x ((k.k - r.q.k - r.d) / r.S)) else none
        | none => none
      | none => none
  else none

/-- The same run, its offset `d` moved into its exponents as far as it goes. -/
def Rng.down (r : Rng) : Rng :=
  let t := r.d / r.S
  ⟨r.q, r.lo.shift t, r.hi.shift t, r.S, r.d - r.S * t⟩

/-- Run `r` holds the heap cell `k`, as it is or moved down. -/
def Abs.inRng (A : Abs) (k : Mono) (r : Rng) : Bool :=
  let at1 := fun (r : Rng) ↦ match r.idxOf k with
    | some i => A.le r.lo i && A.ltI i r.hi
    | none => false
  at1 r || (0 < r.S && r.S ≤ r.d && at1 r.down)

/-- The heap cell `k` is a known one or in a known run. -/
def Abs.coveredHR (A : Abs) (k : Mono) : Bool := A.h.any (·.beq k) || A.r.any (A.inRng k)

/-- Every base of `m` has a word, by the written frame cells and `coveredHR` alone. -/
def Abs.knownH (A : Abs) (m : Mono) : Bool :=
  m.bs.all fun p ↦ match p.1 with
    | .fr o => A.hasW o
    | .hp q d => A.hasW q && A.coveredHR ⟨0, d, [(.fr q, 1)]⟩

/-- The least of two bounds. -/
def minO : Option ℕ → ℕ → Option ℕ
  | none, b => some b
  | some a, b => some (min a b)

/-- A constant the exponent `hi` is at most: its own, or the least a known `p < q` gives, `hi = p + t`
and `q` a constant. -/
def Abs.bound (A : Abs) (hi : Idx) : Option ℕ :=
  match hi with
  | .num n => some n
  | .ex _ _ => A.lt.foldl (fun acc p ↦ match p.2, p.1.off hi with
      | .num q, some t => minO acc (q + t - 1)
      | _, _ => acc) none

/-- Every cell of run `r`, from a constant to a known bound at most 64 further, is known by
`coveredHR`: a run another state entails at a join. -/
def Abs.entR (A : Abs) (r : Rng) : Bool :=
  match r.lo, A.bound r.hi with
  | .num a, some b => decide (b - a ≤ 64) && A.knownH r.q &&
      (List.range (b - a)).all fun j ↦ A.coveredHR (r.q.shift (r.S * (a + j) + r.d))
  | _, _ => false

/-- The exponent of base `b`, when known exactly (the least such, if several). -/
def Abs.pin (A : Abs) (b : Base) : Option ℕ :=
  A.lt.foldl (fun acc p ↦ match p with
    | (.ex b' 0, .num q) =>
      if b'.beq b && 0 < q && A.lt.any (fun p' ↦ p'.1.beq (.num (q - 1)) && p'.2.beq (.ex b 1)) then
        minO acc (q - 1)
      else acc
    | _ => acc) none

/-- A base's power moved into a product: a power of `g` when its exponent is known. -/
def Abs.pinStep (A : Abs) (m : Mono) (p : Base × ℕ) : Mono :=
  match A.pin p.1 with
  | some c => m.shift (c * p.2)
  | none => ⟨m.fp, m.k, m.bs ++ [p]⟩

/-- The product, each base of known exponent made a power of `g`. -/
def Abs.pinned (A : Abs) (k : Mono) : Mono := k.bs.foldl A.pinStep ⟨k.fp, k.k, []⟩

/-- `k = q·x^e·g^c` with `x`'s exponent below a known bound, every cell `q·g^(e·j + c)` below it
known (`entR`): a table read at a bounded index. -/
def Abs.tabCovered (A : Abs) (k : Mono) : Bool :=
  k.fp == 0 && k.bs.any fun p ↦ match removeBs p k.bs with
    | some rest => A.entR ⟨⟨0, 0, rest⟩, .num 0, .ex p.1 1, p.2, k.k⟩
    | none => false

/-- The heap cell `k` is known written: a frame cell, a known cell or one in a known run, as it is or
with its bases of known exponent made powers of `g`, a cell of a run of pointers, a cell past a
pointer such a run holds, or a table read at a bounded index. -/
def Abs.covered (A : Abs) (k : Mono) : Bool :=
  match k.ownCell with
  | some d => A.hasW d
  | none => A.coveredHR k || A.coveredHR (A.pinned k) || A.p.any (fun q ↦ A.inRng k q.1) ||
      (match k with
        | ⟨0, o, [(.hp q d, 1)]⟩ => A.p.any fun p ↦ p.2.contains o && A.inRng ⟨0, d, [(.fr q, 1)]⟩ p.1
        | _ => false) ||
      A.tabCovered k

/-- The base an exponent reads has a known exponent: some inequality mentions it. -/
def Idx.base? : Idx → Option Base
  | .num _ => none
  | .ex b _ => some b

/-- An exponent known to have a value: a constant, or a base some known inequality reads. -/
def Abs.hasIdx (A : Abs) (i : Idx) : Bool :=
  match i with
  | .num _ => true
  | .ex b _ => A.lt.any fun p ↦ (match p.1.base? with | some x => x.beq b | none => false) ||
      (match p.2.base? with | some x => x.beq b | none => false)

/-- A base whose word is known to exist: a written frame cell, or a cell past a written pointer
cell that the walk knows written. -/
def Abs.knownB (A : Abs) : Base → Bool
  | .fr o => A.hasW o
  | .hp q d => A.hasW q && A.covered ⟨0, d, [(.fr q, 1)]⟩

/-- A product whose word is known to exist. -/
def Abs.known (A : Abs) (m : Mono) : Bool := m.bs.all fun p ↦ A.knownB p.1

/-- Every cell of run `r` is known written: it is a known run, a known run holds it, or each of its
(at most `2^12`) points, from a constant to a known bound, is known written. -/
def Abs.coveredR (A : Abs) (r : Rng) : Bool :=
  A.r.any (·.beq r) || A.r.any (fun r' ↦ r'.q.beq r.q && r'.S == r.S && r'.d == r.d && A.le r'.lo r.lo &&
    A.le r.hi r'.hi && A.hasIdx r.lo && A.hasIdx r.hi) ||
  match r.lo, A.bound r.hi with
  | .num a, some b => decide (b - a ≤ 4096) && A.known r.q &&
      (List.range (b - a)).all fun j ↦ A.covered (r.q.shift (r.S * (a + j) + r.d))
  | _, _ => false

/-- A loop's run's point at its counter's start: the product `q·x^S·g^(S·c + d)` for `lo = x + c`. -/
def Rng.first (r : Rng) : Mono :=
  match r.lo with
  | .num c => r.q.shift (r.S * c + r.d)
  | .ex x c => (r.q.mul ⟨0, 0, [(x, r.S)]⟩).shift (r.S * c + r.d)

/-- The heap cell `k` holds a known word whose cells `os` past it are known written. -/
def Abs.ptrAt (A : Abs) (k : Mono) (os : List ℕ) : Bool :=
  match A.hvGet k with
  | some (.m m) => os.all fun o ↦ A.covered (m.shift o)
  | _ => false

/-- The heap cell `k` holds a pointer with the cells `os` past it written: a known word, or a cell of
a run of pointers naming them. -/
def Abs.ptrIn (A : Abs) (k : Mono) (os : List ℕ) : Bool :=
  A.ptrAt k os || A.p.any fun q ↦ os.all (q.2.contains ·) && A.inRng k q.1

/-- Every cell of run `r` is known to hold a pointer with the cells `os` past it written: a known run
of pointers holds it, or it is one point, or each of its (at most `2^12`) points, from a constant to a
known bound, is known. -/
def Abs.coveredP (A : Abs) (r : Rng) (os : List ℕ) : Bool :=
  A.p.any (fun q ↦ q.1.q.beq r.q && q.1.S == r.S && q.1.d == r.d && A.le q.1.lo r.lo &&
    A.le r.hi q.1.hi && A.hasIdx r.lo && A.hasIdx r.hi && os.all (q.2.contains ·)) ||
  (r.hi.beq r.lo.succ && A.hasIdx r.lo && A.ptrIn r.first os) ||
  match r.lo, A.bound r.hi with
  | .num a, some b => decide (b - a ≤ 4096) && A.known r.q &&
      (List.range (b - a)).all fun j ↦ A.ptrIn (r.q.shift (r.S * (a + j) + r.d)) os
  | _, _ => false

/-! ## Intersection -/

/-- Pairs both lists hold. -/
def interL {α : Type} (eq : α → α → Bool) (a b : List α) : List α := a.filter fun x ↦ b.any (eq x)

/-- How many leading elements two lists agree on. -/
def agree {α : Type} (eq : α → α → Bool) : List α → List α → ℕ
  | x :: xs, y :: ys => if eq x y then agree eq xs ys + 1 else 0
  | _, _ => 0

/-- Pairs both lists hold, their longest common tail kept whole: two states from one path share most
of their facts, as a tail. -/
def interT {α : Type} (eq : α → α → Bool) (a b : List α) : List α :=
  let t := agree eq a.reverse b.reverse
  interL eq (a.take (a.length - t)) b ++ a.drop (a.length - t)

/-- Runs both states know: those both hold, their common tail kept whole, and those one holds and the
other entails (`entR`). -/
def interR (A B : Abs) : List Rng :=
  let t := agree Rng.beq A.r.reverse B.r.reverse
  (A.r.take (A.r.length - t)).filter (fun r ↦ B.r.any (Rng.beq r) || B.entR r) ++
    A.r.drop (A.r.length - t) ++
    (B.r.take (B.r.length - t)).filter (fun r ↦ !(A.r.any (Rng.beq r)) && A.entR r)

/-- Equality of pairs of exponents, as a `Bool`. -/
def ltBeq (p q : Idx × Idx) : Bool := p.1.beq q.1 && p.2.beq q.2

/-- Equality of heap words, as a `Bool`. -/
def hvBeq (p q : Mono × Val) : Bool := p.1.beq q.1 && p.2.beq q.2

/-- Equality of runs of pointers, as a `Bool`. -/
def ptrBeq (p q : Rng × List ℕ) : Bool := p.1.beq q.1 && p.2 == q.2

/-- The conditional facts both lists hold, under the same condition. -/
def interC (a b : List Cnd) : List Cnd :=
  a.filterMap fun c ↦ match b.find? (fun c' ↦ c'.x.beq c.x && c'.j == c.j) with
    | some c' =>
      let d : Cnd := ⟨c.x, c.j, interL Mono.beq c.h c'.h, interL Rng.beq c.r c'.r, interL ptrBeq c.p c'.p,
        interL ltBeq c.lt c'.lt, interL hvBeq c.hv c'.hv⟩
      if d.h.isEmpty && d.r.isEmpty && d.p.isEmpty && d.lt.isEmpty && d.hv.isEmpty then none else some d
    | none => none

/-- What two states both know. -/
noncomputable def Abs.inter (A B : Abs) : Abs :=
  ⟨Trie.inter (fun _ _ ↦ true) A.w B.w, Trie.inter Val.beq A.v B.v,
    Trie.inter (fun _ _ ↦ true) A.nz B.nz,
    interT hvBeq A.hv B.hv, interT Mono.beq A.h B.h,
    interR A B, interT ltBeq A.lt B.lt, [],
    Trie.inter (fun p q ↦ p.1 == q.1 && p.2 == q.2) A.xs B.xs,
    interT ptrBeq A.p B.p, interC A.c B.c⟩

/-- `A.inter B`, its lists' spines evaluated. -/
noncomputable def Abs.interS (A B : Abs) : Abs :=
  match A.inter B with
  | ⟨w, v, nz, hv, h, r, lt, pr, xs, p, c⟩ =>
    listSeq hv fun hv ↦ listSeq h fun h ↦ listSeq r fun r ↦ listSeq lt fun lt ↦ listSeq p fun p ↦
      ⟨w, v, nz, hv, h, r, lt, pr, xs, p, c⟩

/-- Every fact of `S` is one of `A`'s, under the same condition. -/
def Cnd.sub (S A : Cnd) : Bool :=
  S.x.beq A.x && S.j == A.j && S.h.all (fun k ↦ A.h.any (·.beq k)) && S.r.all (fun r ↦ A.r.any (·.beq r)) &&
    S.p.all (fun p ↦ A.p.any (ptrBeq p)) && S.lt.all (fun p ↦ A.lt.any (ltBeq p)) &&
    S.hv.all (fun p ↦ A.hv.any (hvBeq p))

/-- Every fact of `S` is one of `A`'s. -/
noncomputable def Abs.sub (S A : Abs) : Bool :=
  Trie.sub (fun _ _ ↦ true) S.w A.w && Trie.sub Val.beq S.v A.v && Trie.sub (fun _ _ ↦ true) S.nz A.nz &&
  S.hv.all (fun p ↦ A.hv.any fun q ↦ p.1.beq q.1 && p.2.beq q.2) && S.h.all (fun k ↦ A.h.any (·.beq k)) &&
  S.r.all (fun r ↦ A.r.any (·.beq r)) && S.lt.all (fun p ↦ A.lt.any fun q ↦ p.1.beq q.1 && p.2.beq q.2) &&
  S.pr.all (fun p ↦ A.pr.any fun q ↦ p.1 == q.1 && p.2.1 == q.2.1 && p.2.2 == q.2.2) &&
  Trie.sub (fun p q ↦ p.1 == q.1 && p.2 == q.2) S.xs A.xs &&
  S.p.all (fun p ↦ A.p.any fun q ↦ p.1.beq q.1 && p.2 == q.2) &&
  S.c.all (fun c ↦ A.c.any c.sub)

/-- Pending edges into later offsets: each target of `ts` (increasing) is entered by every state of
`Bs`; `m`: `Bs` is one state, the meet of at least three. -/
structure Grp where
  ts : List ℕ
  Bs : List Abs
  m : Bool

/-- The pending edges, in groups. -/
abbrev Pend := List Grp

/-- Each state of `S` is weaker than the one in its place in `As`. -/
noncomputable def subAll : List Abs → List Abs → Bool
  | [], [] => true
  | S :: Ss, A :: As => S.sub A && subAll Ss As
  | _, _ => false

/-- Each group of `S` has the targets and states of the one in its place in `P`, each state weaker. -/
noncomputable def pendSub : Pend → Pend → Bool
  | [], [] => true
  | S :: Ss, G :: Gs => S.ts == G.ts && S.m == G.m && subAll S.Bs G.Bs && pendSub Ss Gs
  | _, _ => false

/-! ## What the walk is told -/

/-- What a caller knows of a function. -/
structure Sig where
  /-- Its entry pc. -/
  pc : ℕ
  /-- Frame offsets written at entry: the header, the arguments. -/
  entry : List ℕ
  /-- The cell holding its own frame's address at entry (a loop). -/
  self : Option ℕ
  /-- Heap cells written at entry, over its bases. -/
  pre : List Mono
  /-- Runs written at entry. -/
  preR : List Rng
  /-- Exponents in order at entry, by the run's termination (a loop's counter below its bound). -/
  term : List (Idx × Idx)
  /-- Frame offsets written at return. -/
  ret : List ℕ
  /-- Heap cells written at return. -/
  post : List Mono
  /-- Runs written at return. -/
  postR : List Rng
  /-- Runs a loop writes over its counter's range: each iteration's point written on every path
  to a return or a tail call, the whole run at the outermost return. -/
  postL : List Rng
  /-- Runs of pointers at entry, each with the cells past it it names written. -/
  preP : List (Rng × List ℕ)
  /-- Runs of pointers at return. -/
  postP : List (Rng × List ℕ)
  /-- Runs of pointers a loop writes over its counter's range, as `postL`. -/
  postLP : List (Rng × List ℕ)
  /-- Frame offsets holding at return the word of a product over its bases. -/
  retV : List (ℕ × Mono)

/-- A residual: a value fact the walk assumes at an instruction, proved apart. -/
inductive Res where
  /-- Two exponents in order. -/
  | lt (a b : Idx)
  /-- A frame cell nonzero. -/
  | nz (o : ℕ)
  /-- Every cell of run `a` is a cell of one of the runs `bs`. -/
  | sub (a : Rng) (bs : List Rng)
  deriving DecidableEq, Repr

/-- The program the walks share. -/
structure Env where
  /-- The powers of `g` the constants name. -/
  pows : PowTree
  /-- The jump table: slot to target pc (absolute cells `jtLo` up). -/
  jt : Trie ℕ
  jtLo : ℕ
  jtHi : ℕ
  /-- The signatures by entry pc. -/
  sigs : Trie Sig
  /-- The halting pc. -/
  halt : ℕ

/-- What one function's walk is told. -/
structure Fun where
  /-- Its entry pc and length. -/
  entry : ℕ
  len : ℕ
  /-- Its signature. -/
  sig : Sig
  /-- The hints by offset. -/
  hints : Trie (List Hint)
  /-- The residuals by offset. -/
  res : Trie (List Res)
  /-- The table jumps by offset: the table's size. -/
  tabs : Trie ℕ
  /-- It is `main` (its frame is `0`; it halts). -/
  main : Bool
  /-- The cuts by offset: weaker paths and pending edges the walk goes on from. -/
  cuts : Trie (List Abs × Pend)

/-! ## One instruction -/

/-- An offset-form instruction as the executor's. -/
def opOfOff : OffsetInstruction → Op
  | .xor a b c => .xor a b c
  | .mul a b c => .mul a b c
  | .set o k0 k1 => .set o (OffsetInstruction.immediateWord k0 k1)
  | .deref a o c mode => .deref a o c mode
  | .jump c d f => .jump c d f
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    .keccak (keccakIns m0 m1 m2 m3 tail b8 cap).toArray out inOdd outOdd outCells.cellCount

/-- The jump table's cells, written before `main` starts. -/
def jtRng (E : Env) : Rng := ⟨.one, .num E.jtLo, .num E.jtHi, 1, 0⟩

/-- `g⁻¹`'s bits, `x^63 + x^3 + x^2 + 1`: the word `g^(2^64 - 2)`. -/
def ginvBits : ℕ := 2 ^ 63 + 13

/-- The word a `SET` immediate is known as. -/
def valOfImm (E : Env) (k0 k1 : ℕ) : Val :=
  if k1 == 0 then
    if k0 == 1 then .m .one
    else if k0 == ginvBits then .m (.gp (2 ^ 64 - 2))
    else match E.pows.find k0 with
      | some e => .m (.gp e)
      | none => .imm k0 k1
  else .imm k0 k1

/-- The word a load from the heap cell `k` gives: known, or the jump table's, or the base
`hp q d` for a cell `d` past frame cell `q`'s. -/
def loadVal (E : Env) (A : Abs) (k : Mono) : Option Val :=
  match A.hvGet k with
  | some x => some x
  | none =>
    match k with
    | ⟨0, d, []⟩ => if E.jtLo ≤ d && d < E.jtHi then (E.jt.get d).map fun e ↦ .m (.gp e) else none
    | ⟨0, d, [(x, 1)]⟩ =>
      if A.inRng k (jtRng E) then some (.tab x d)
      else match x with
        | .fr q => some (.m ⟨0, 0, [(.hp q d, 1)]⟩)
        | _ => none
    | _ => none

/-- A load into frame cell `c` from the heap cell `k`: for each run of pointers holding `k`, the cells
past `c`'s word it names written. -/
noncomputable def ptrLoad (A : Abs) (k : Mono) (c : ℕ) (B : Abs) : Abs :=
  foldlA (fun B q ↦
    if A.inRng k q.1 then
      match B.mono c with
      | some m => foldlA (fun B o ↦ B.addH (m.shift o)) B q.2
      | none => B
    else B) B A.p

/-- Frame cell `x`'s exponent below `b`, and so its word's base's, when its word is one base. -/
def Abs.addLtC (A : Abs) (x : ℕ) (b : Idx) : Abs :=
  let A' := A.addLt (.ex (.fr x) 0) b
  match A.mono x with
  | some ⟨0, 0, [(y, 1)]⟩ => A'.addLt (.ex y 0) b
  | _ => A'

/-- The range check `DEREF *(x); MUL [z] = [x]·[y]; DEREF *(y)` with `[z] = g^k`, a base's word
times `g^k`, or a base's word over `g`, ending at the `DEREF` through `y`: `x`'s exponent is at most
`z`'s. -/
def rangeFact (A : Abs) (y : ℕ) : Abs :=
  match A.pr with
  | (x, y', z) :: _ =>
    if y' == y && A.ltI (.ex (.fr x) 0) (.num maxCells) then
      match A.mono z with
      | some ⟨0, k, []⟩ => if k < 2 ^ 62 then A.addLtC x (.num (k + 1)) else A
      | some ⟨0, k, [(b, 1)]⟩ =>
        if k == 0 || (k < 2 ^ 62 && A.ltI (.ex b 0) (.num maxCells)) then
          A.addLtC x (.ex b (k + 1))
        else if k == 2 ^ 64 - 2 then A.addLtC x (.ex b 0)
        else A
      | _ => A
    else A
  | [] => A

/-- The sum `[c] = [a] + [b]` recorded, unless one is for `c`. -/
noncomputable def addSum (t : Trie (ℕ × ℕ)) (c a b : ℕ) : Trie (ℕ × ℕ) :=
  match t.get c with
  | some _ => t
  | none => t.set (a, b) envDepth c

/-- **One instruction** at pc `pc`, its operands as offsets. -/
noncomputable def stepOp (E : Env) (pc : ℕ) (A : Abs) : OffsetInstruction → Option Abs
  | .xor a b c =>
    if A.hasW a && A.hasW b then
      let A' := A.addW c
      -- two distinct powers of `g` differ
      let A' := match A.mono a, A.mono b with
        | some ⟨0, x, []⟩, some ⟨0, y, []⟩ => if x != y && x < 2 ^ 62 && y < 2 ^ 62 then A'.addNz c else A'
        | _, _ => A'
      some { A' with pr := [], xs := addSum A.xs c a b }
    else none
  | .mul a b c =>
    if A.hasW a && A.hasW b then
      let A' := A.addW c
      let A' := match A.mono a, A.mono b with
        | some x, some y => A'.addV c (.m (x.mul y))
        | _, _ => A'
      let A' := if A.hasNz a && A.hasNz b then A'.addNz c else A'
      some { A' with pr := [(a, b, c)] }
    else if A.hasW c && A.hasW a && A.hasNz a then
      let A' := A.addW b
      some { (if A.hasNz c then A'.addNz b else A') with pr := [(a, b, c)] }
    else if A.hasW c && A.hasW b && A.hasNz b then
      let A' := A.addW a
      some { (if A.hasNz c then A'.addNz a else A') with pr := [(a, b, c)] }
    else none
  | .set o k0 k1 =>
    let A' := (A.addW o).addV o (valOfImm E k0 k1)
    let A' := match valOfImm E k0 k1 with
      | .m _ => A'.addNz o
      | _ => A'
    -- the `!=` gadget: `MUL [p] = [x]·[inv]; SET [p] = 1`
    let A' := match A.pr with
      | (x, i, p) :: _ => if p == o && k0 == 1 && k1 == 0 then (A'.addNz x).addNz i else A'
      | [] => A'
    some { A' with pr := [] }
  | .deref a o c mode =>
    if A.hasW a then
      match A.mono a with
      | none => none
      | some m =>
        let k := m.shift o
        let A0 := (A.addNz a).addLt (.ex (.fr a) 0) (.num maxCells)
        let A0 := if o == 0 then rangeFact A0 a else A0
        let A0 := { A0 with pr := A.pr }
        match mode with
        | .pc => some { (A0.addH k).addHv k (.m (.gp (pc + 2))) with pr := [] }
        | .fp => some { (A0.addH k).addHv k (.m (.own 0)) with pr := [] }
        | .cell =>
          if A.hasW c then
            some { (A0.addH k).addHv k ((A.v.get c).getD (.m (.root c))) with pr := A.pr }
          else if A.covered k then
            let A1 := A0.addW c
            some { ptrLoad A k c (match loadVal E A k with
              | some x => A1.addV c x
              | none => A1) with pr := A.pr }
          else some A0
    else none
  | .jump c d f => if A.hasW c && A.hasW d && A.hasW f then some A else none
  | .keccak m0 m1 m2 m3 tail b8 cap out _ _ outCells =>
    if (keccakIns m0 m1 m2 m3 tail b8 cap).all A.hasW then
      some { foldlA (fun A j ↦ A.addW (out + j)) A (List.range outCells.cellCount) with pr := [] }
    else none

/-! ## One hint -/

/-- A run's start: frame offset `base` (stack), or the product a pointer cell holds. -/
def destOf (A : Abs) : BitsDest → Option (Option ℕ × Option Mono)
  | .stack base => some (some base, none)
  | .heap ptr => if A.hasW ptr then (A.mono ptr).map fun m ↦ (none, some m) else none

/-- Write `n` cells from `pos` at a run's start, each nonzero and below `2^bits` in exponent when
`bits` is given (a stack run); on the heap, one run. -/
noncomputable def writeRun (A : Abs) (dst : Option ℕ × Option Mono) (pos n : ℕ) (bits : Option ℕ) :
    Abs :=
  match dst with
  | (some base, _) =>
    foldlA (fun A j ↦
      let A := A.addW (base + pos + j)
      match bits with
      | some b =>
        if b ≤ 61 then (A.addNz (base + pos + j)).addLt (.ex (.fr (base + pos + j)) 0) (.num (2 ^ b))
        else A.addNz (base + pos + j)
      | none => A) A (List.range n)
  | (none, some m) => { A with r := ⟨m, .num pos, .num (pos + n), 1, 0⟩ :: A.r }
  | (none, none) => A

/-- **One hint**: the cells it reads must be known written. -/
noncomputable def stepHint (A : Abs) : Hint → Option Abs
  | .frameAddress _ => some A
  | .alloc ptr _ => some (A.addW ptr)
  | .allocDyn ptr size => if A.hasW size then some (A.addW ptr) else none
  -- its entry may be empty: the pointer is written by the allocation that follows it
  | .allocAdvice _ _ => some A
  | .allocArm ptr sel _ => if A.hasW sel then some (A.addW ptr) else none
  | .allocFrames ptr _ stop _ _ => if A.hasW stop then some (A.addW ptr) else none
  | .cellAddress ptr cell => some (((A.addW ptr).addV ptr (.m (.own cell))).addNz ptr)
  | .witnessStack _ base len => some (writeRun A (some base, none) 0 len none)
  | .witnessHeap _ ptr lo len => (destOf A (.heap ptr)).map fun d ↦ writeRun A d lo len none
  | .log2Ceil bits dst nbits _ =>
    match destOf A bits with
    | some (some base, _) =>
      if (List.range nbits).all (fun j ↦ A.hasW (base + j)) then some ((A.addW dst).addNz dst)
      else none
    | some (none, some m) =>
      if (List.range nbits).all (fun j ↦ A.covered (m.shift j)) then some ((A.addW dst).addNz dst)
      else none
    | _ => none
  | .bitDecompose value bits nbits =>
    if A.hasW value then (destOf A bits).map fun d ↦ writeRun A d 0 nbits none else none
  | .bitDecomposeExp value bits nbits =>
    if A.hasW value then (destOf A bits).map fun d ↦ writeRun A d 0 nbits none else none
  | .windowsExp value dest pos _ width count =>
    if A.hasW value then (destOf A dest).map fun d ↦ writeRun A d pos count (some width) else none
  | .digitDecomposeExp value dst _ ndigits digitBits _ startCell =>
    if A.hasW value && (match startCell with | some c => A.hasW c | none => true) then
      (destOf A dst).map fun d ↦ writeRun A d 0 ndigits (some digitBits)
    else none
  | .fieldLimbs value base len =>
    if A.hasW value then some (writeRun A (some base, none) 0 len none) else none
  | .inverse value dst =>
    if A.hasW value then
      some (if A.hasNz value then (A.addW dst).addNz dst else A.addW dst)
    else none

/-- The hints, in order. -/
noncomputable def stepHints (A : Abs) : List Hint → Option Abs
  | [] => some A
  | h :: hs => (stepHint A h).bind (stepHints · hs)

/-- An exponent's base has a word: a frame cell known written, or the cell past one it names. -/
def Abs.idxOk (A : Abs) : Idx → Bool
  | .ex (.fr o) _ => A.hasW o
  | .ex (.hp q d) _ => A.covered ⟨0, d, [(.fr q, 1)]⟩
  | .num _ => true

/-- The residuals: each one's cells known written, the fact added; a run inside known runs is known. -/
def addRes (A : Abs) : List Res → Option Abs
  | [] => some A
  | .lt a b :: rs => if A.idxOk a && A.idxOk b then addRes (A.addLt a b) rs else none
  | .nz o :: rs =>
    if A.hasW o then addRes { A with nz := A.nz.set () envDepth o } rs else none
  | .sub a bs :: rs =>
    if A.known a.q && A.idxOk a.lo && A.idxOk a.hi && bs.all A.coveredR then
      addRes { A with r := a :: A.r } rs
    else none

/-! ## Calls -/

/-- A callee's base, in the caller's terms, the callee's frame named by the product `mq` (its
address word, held by frame cell `q` when `mq = [q]`, or `fp·g^e` for a tail call). -/
def trFr (A : Abs) (mq : Mono) (o : ℕ) : Option Mono :=
  if 2 ^ 30 ≤ o then none else
  match A.hvGet (mq.shift o) with
  | some (.m x) => some x
  | some _ => none
  | none =>
    match mq.rootCell with
    | some q => some ⟨0, 0, [(.hp q o, 1)]⟩
    | none => none

/-- A callee's base `b`, in the caller's terms. -/
def trBase (A : Abs) (mq : Mono) : Base → Option Mono
  | .fr o => trFr A mq o
  | .hp p d =>
    match trFr A mq p with
    | none => none
    | some mp =>
      if 2 ^ 30 ≤ d then none else
      match A.hvGet (mp.shift d) with
      | some (.m x) => some x
      | some _ => none
      | none =>
        match mp with
        | ⟨0, k, [(.fr q, 1)]⟩ => some ⟨0, 0, [(.hp q (k + d), 1)]⟩
        | _ => none

/-- `x^e`. -/
def Mono.npow (x : Mono) : ℕ → Mono
  | 0 => .one
  | e + 1 => (x.npow e).mul x

/-- A callee's product, in the caller's terms (its frame pointer is `mq`'s word). -/
def trMono (A : Abs) (mq : Mono) (m : Mono) : Option Mono :=
  m.bs.foldl (fun acc p ↦ acc.bind fun acc ↦
      if p.2 == 0 then none else (trBase A mq p.1).map fun x ↦ acc.mul (x.npow p.2))
    (some ((mq.npow m.fp).mul (.gp m.k)))

/-- A callee's exponent, in the caller's terms, with the power of `g` its base is a caller's base
times (`0` unless it is a caller's base shifted). -/
def trIdxK (A : Abs) (mq : Mono) : Idx → Option (Idx × ℕ)
  | .num n => some (.num n, 0)
  | .ex x c =>
    match trBase A mq x with
    | some ⟨0, k, []⟩ => if k < 2 ^ 62 then some (.num (c + k), 0) else none
    | some ⟨0, k, [(y, 1)]⟩ => if k < 2 ^ 62 then some (.ex y (c + k), k) else none
    | _ => none

/-- An exponent below `2^62`: a constant below it, a base's exponent, or one at most such. -/
def Idx.small : Idx → Bool
  | .num n => n < 2 ^ 62
  | .ex _ c => c == 0

/-- An exponent known below `2^62`. -/
def Abs.small (A : Abs) (j : Idx) : Bool := j.small || A.lt.any fun p ↦ p.2.small && A.le j p.2

/-- A callee's exponent, in the caller's terms, for a fact moving out to the caller: a shifted base's
exponent must be known to exist there. -/
def idxUp (A : Abs) (mq : Mono) (i : Idx) : Option Idx :=
  match trIdxK A mq i with
  | some (j, k) => if k == 0 || A.hasIdx j then some j else none
  | none => none

/-- A callee's exponent, in the caller's terms, for a fact moving in to the callee: a shifted base's
exponent must be known below `2^62`. -/
def idxDown (A : Abs) (mq : Mono) (i : Idx) : Option Idx :=
  match trIdxK A mq i with
  | some (j, k) => if k == 0 || A.small j then some j else none
  | none => none

/-- A callee's run, in the caller's terms, its exponents translated by `tr`. -/
def trRngBy (A : Abs) (mq : Mono) (tr : Idx → Option Idx) (r : Rng) : Option Rng :=
  match trMono A mq r.q, tr r.lo, tr r.hi with
  | some q, some lo, some hi => some ⟨q, lo, hi, r.S, r.d⟩
  | _, _, _ => none

/-- A callee's run, moving out. -/
def trRngUp (A : Abs) (mq : Mono) (r : Rng) : Option Rng := trRngBy A mq (idxUp A mq) r

/-- A callee's run, moving in. -/
def trRngDown (A : Abs) (mq : Mono) (r : Rng) : Option Rng := trRngBy A mq (idxDown A mq) r

/-- The caller holds what callee `G` needs at entry, its frame named by `mq`. -/
def entryOk (A : Abs) (mq : Mono) (G : Sig) : Bool :=
  G.entry.all (fun o ↦ decide (o < 2 ^ 30) && A.covered (mq.shift o)) &&
  (match G.self with
    | some o => decide (o < 2 ^ 30) && match A.hvGet (mq.shift o) with
      | some x => x.beq (.m mq)
      | none => false
    | none => true) &&
  G.pre.all (fun m ↦ match trMono A mq m with
    | some k => A.known k && A.covered k
    | none => false) &&
  G.preR.all (fun r ↦ match trRngDown A mq r with
    | some r => A.coveredR r
    | none => false) &&
  G.preP.all (fun q ↦ match trRngDown A mq q.1 with
    | some r => A.coveredP r q.2
    | none => false)

/-- The termination facts of callee `G` hold at the call. -/
noncomputable def atCall (A : Abs) (mq : Mono) (G : Sig) : Abs :=
  foldlA (fun A p ↦ match idxUp A mq p.1, idxUp A mq p.2 with
    | some a, some b => A.addLt a b
    | _, _ => A) A G.term

/-- A run at offset `d ≥ S` and its point one stride below its start give the run from that point:
a loop's run, met with what precedes it, covering the loop that ran no iteration. -/
def Abs.extR (A : Abs) (r : Rng) : Abs :=
  if 0 < r.S && r.S ≤ r.d then
    let r' : Rng := ⟨r.q, r.lo, r.hi.succ, r.S, r.d - r.S⟩
    if A.covered r'.first then { A with r := r' :: A.r } else A
  else A

/-- What the caller knows after callee `G` returns. -/
noncomputable def afterCall (A : Abs) (mq : Mono) (G : Sig) : Abs :=
  let A := foldlA (fun A o ↦ A.addH (mq.shift o)) A G.ret
  let A := foldlA (fun A p ↦ match trMono A mq p.2 with
    | some x => if p.1 < 2 ^ 30 then A.addHv (mq.shift p.1) (.m x) else A
    | none => A) A G.retV
  let A := foldlA (fun A m ↦ match trMono A mq m with
    | some k => A.addH k
    | none => A) A G.post
  let A := foldlA (fun A r ↦ match trRngUp A mq r with
    | some r => ({ A with r := r :: A.r } : Abs).extR r
    | none => A) A (G.postR ++ G.postL)
  let A := foldlA (fun A q ↦ match trRngUp A mq q.1 with
    | some r => { A with p := (r, q.2) :: A.p }
    | none => A) A (G.postP ++ G.postLP)
  atCall A mq G

/-- The walk's state at a function's entry. -/
noncomputable def entryAbs (E : Env) (G : Sig) : Abs :=
  let A : Abs := ⟨foldlT .nil G.entry, .nil, .nil, [], G.pre,
    jtRng E :: G.preR, G.term, [], .nil, G.preP, []⟩
  match G.self with
  | some o => ((A.addW o).addV o (.m (.own 0))).addNz o
  | none => A

/-- A loop writes each run's point at its counter's start before a return or a tail call. -/
def loopOk (A : Abs) (G : Sig) : Bool :=
  (G.postL.all fun r ↦ match trMono A (.own 0) r.first with
    | some k => A.covered k
    | none => false) &&
  G.postLP.all fun q ↦ match trMono A (.own 0) q.1.first with
    | some k => A.ptrIn k q.2
    | none => false

/-- At a loop's return, its bound is its counter's next exponent: a constant the counter's exponent
plus one is known equal to, or a frame cell known to hold the counter's word times `g`. -/
def exitOk (A : Abs) : Idx → Idx → Bool
  | .ex x 0, .num n => decide (1 ≤ n) && A.le (.num n) (.ex x 1) && A.le (.ex x 1) (.num n)
  | .ex x 0, .ex (.fr q) 0 =>
    match A.v.get q with
    | some (.m ⟨0, 1, [(y, 1)]⟩) => y.beq x
    | _ => false
  | _, _ => false

/-- What the function guarantees holds at a return. -/
def retOk (A : Abs) (G : Sig) : Bool :=
  loopOk A G && G.term.all (fun p ↦ exitOk A p.1 p.2) &&
  G.ret.all A.hasW &&
  G.retV.all (fun p ↦ A.hasW p.1 && match A.mono p.1, trMono A (.own 0) p.2 with
    | some x, some y => x.beq y
    | _, _ => false) &&
  G.post.all (fun m ↦ match trMono A (.own 0) m with
    | some k => A.covered k
    | none => false) &&
  (G.postR.all fun r ↦ match trRngDown A (.own 0) r with
    | some r => A.coveredR r
    | none => false) &&
  G.postP.all fun q ↦ match trRngDown A (.own 0) q.1 with
    | some r => A.coveredP r q.2
    | none => false

/-! ## Table calls -/

/-- The base a table call through target cell `t` dispatches on. -/
def selOf (A : Abs) (t : ℕ) : Option Base :=
  match A.v.get t with
  | some (.tab x _) => some x
  | _ => none

/-- What holds when base `x`'s exponent is `j`: the facts under that condition, and the exponent. -/
def Abs.assume (A : Abs) : Option Base → ℕ → Abs
  | none, _ => A
  | some x, j =>
    let A := (A.addLt (.ex x 0) (.num (j + 1))).addLt (.num j) (.ex x 1)
    match A.c.find? (fun c ↦ c.x.beq x && c.j == j) with
    | some c =>
      { A with
        h := c.h ++ A.h
        r := c.r ++ A.r
        p := c.p ++ A.p
        lt := c.lt ++ A.lt
        hv := A.hv ++ c.hv.filter (fun p ↦ !(A.hv.any fun q ↦ q.1.beq p.1)) }
    | none => A

/-- The facts of `X` not in `B`, under base `x`'s exponent `j`, if any. -/
def condDiff (B X : Abs) (x : Base) (j : ℕ) : Option Cnd :=
  let d : Cnd := ⟨x, j, X.h.filter (fun k ↦ !(B.h.any (Mono.beq k))), X.r.filter (fun r ↦ !(B.r.any (Rng.beq r))),
    X.p.filter (fun p ↦ !(B.p.any (ptrBeq p))), X.lt.filter (fun p ↦ !(B.lt.any (ltBeq p))),
    X.hv.filter (fun p ↦ !(B.hv.any (hvBeq p)))⟩
  if d.h.isEmpty && d.r.isEmpty && d.p.isEmpty && d.lt.isEmpty && d.hv.isEmpty then none else some d

/-- What the caller knows after one of a call's arms returns, each arm's state given: what all know,
and, for a table call on base `x`, what each knows beyond it, under `x`'s exponent its index. -/
noncomputable def armsMeet (sel : Option Base) : List Abs → Abs
  | [] => ⟨.nil, .nil, .nil, [], [], [], [], [], .nil, [], []⟩
  | B :: Bs =>
    let M := foldlA Abs.interS B Bs
    match sel with
    | none => M
    | some x =>
      { M with
        c := ((B :: Bs).zipIdx.filterMap fun p ↦ condDiff M p.1 x p.2) ++
          M.c.filter (fun c ↦ !(c.x.beq x && decide (c.j < Bs.length + 1))) }

/-! ## Jumps -/

/-- Where a `JUMP` goes. -/
inductive Go where
  /-- Offsets of the function (a forward jump, a table jump's arms, a call's return point). -/
  | to (ts : List ℕ)
  /-- Nowhere in the function (a return, a tail call, halting). -/
  | out
  deriving Repr

/-- The callees a target cell names: a power of `g` at a signature's pc, or a jump table entry
`hp x d` with `x` below `n`, each arm's signature. -/
noncomputable def calleesOf (E : Env) (F : Fun) (A : Abs) (i t : ℕ) : Option (List Sig) :=
  match A.v.get t with
  | some (.m ⟨0, e, []⟩) => (E.sigs.get e).map ([·])
  | some (.tab x d) =>
    match F.tabs.get i with
    | some n =>
      if A.ltI (.ex x 0) (.num n) && E.jtLo ≤ d && d + n ≤ E.jtHi then
        mapOpt (fun j ↦ (E.jt.get (d + j)).bind E.sigs.get) (List.range n)
      else none
    | none => none
  | _ => none

/-- The arms of a table jump at offset `i` through target cell `t`, as offsets. -/
noncomputable def armsOf (E : Env) (F : Fun) (A : Abs) (i t : ℕ) : Option (List ℕ) :=
  match A.v.get t, F.tabs.get i with
  | some (.tab x d), some n =>
    if A.ltI (.ex x 0) (.num n) && E.jtLo ≤ d && d + n ≤ E.jtHi then
      mapOpt (fun j ↦ (E.jt.get (d + j)).bind fun pc ↦
        if F.entry + i < pc && pc < F.entry + F.len then some (pc - F.entry) else none) (List.range n)
    else none
  | _, _ => none

/-- A loop's tail call into frame `fp·g^e` moves each termination fact's counter up by a positive
power of `g` and keeps its bound. -/
def termStep (A : Abs) (e : ℕ) (G : Sig) : Bool :=
  G.term.all fun p ↦ match p with
    | (.ex _ 0, .ex _ 0) | (.ex _ 0, .num _) =>
      (match idxUp A (.own e) p.1 with
        | some a => match p.1.off a with
          | some t => decide (0 < t)
          | none => false
        | none => false) &&
      (match idxUp A (.own e) p.2 with
        | some b => b.beq p.2
        | none => false)
    | _ => false

/-- The frame `fp·g^e`'s header is this frame's: its cells `0` and `1` hold this frame's words. -/
def headerOk (A : Abs) (e : ℕ) : Bool :=
  [0, 1].all fun o ↦ A.hasW o && match A.hvGet ((Mono.own e).shift o), A.mono o with
    | some (.m x), some y => x.beq y
    | _, _ => false

/-- A loop's tail call into frame `fp·g^e` of callee `G`: its entry from this state, its header this
frame's, its counters moved up, and each run it accumulates the next iteration's from one further. -/
def tailOk (A : Abs) (e : ℕ) (G : Sig) : Bool :=
  entryOk A (.own e) G && headerOk A e && termStep A e G && (G.postL ++ G.postLP.map (·.1)).all fun r ↦
    match trRngUp A (.own e) r with
    | some r' => r'.beq ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩
    | none => false

/-- **A `JUMP` at offset `i`** (`[c]`, `[d]`, `[f]`): what it needs, and where it goes. The state
after it is the state at its successors (a call's return point gets `afterCall`'s). -/
noncomputable def jumpI (E : Env) (F : Fun) (i : ℕ) (A : Abs) (d f : ℕ) :
    Option (Go × Abs) :=
  if d == 0 && f == 1 then
    if retOk A F.sig then some (.out, A) else none
  else
    let self := match A.mono f with
      | some ⟨1, 0, []⟩ => true
      | some ⟨0, 0, []⟩ => F.main
      | _ => false
    if self then
      match A.mono d with
      | some ⟨0, e, []⟩ =>
        if F.entry + i < e && e < F.entry + F.len then some (.to [e - F.entry], A)
        else if F.main && e == E.halt then some (.out, A)
        else none
      | _ => (armsOf E F A i d).map fun ts ↦ (.to ts, A)
    else
    match A.mono f with
    | some ⟨1, e, []⟩ =>
      match A.mono d with
      | some ⟨0, t, []⟩ =>
        match E.sigs.get t with
        | some G => if t == F.entry && tailOk A e G && loopOk A F.sig then some (.out, A) else none
        | none => none
      | _ => none
    | some mq =>
      match A.hvGet (mq.shift 1), A.hvGet (mq.shift 0) with
      | some (.m ⟨1, 0, []⟩), some (.m ⟨0, r, []⟩) =>
        match calleesOf E F A i d with
        | some (G :: Gs) =>
          let As := (G :: Gs).zipIdx.map fun p ↦ (p.1, atCall (A.assume (selOf A d) p.2) mq p.1)
          if As.all (fun p ↦ entryOk p.2 mq p.1) && F.entry + i < r && r < F.entry + F.len then
            some (.to [r - F.entry], armsMeet (selOf A d) (As.map fun p ↦ afterCall p.2 mq p.1))
          else none
        | _ => none
      | _, _ => none
    | none => none

/-- A `JUMP` on a condition known `0` falls through; one known nonzero does not. -/
def condOf (A : Abs) (c : ℕ) : Option Bool :=
  if A.hasNz c then some true else
  match A.v.get c with
  | some (.imm a b) => if a == 0 && b == 0 then some false
    else if a < 2 ^ 64 && b < 2 ^ 64 then some true else none
  | some (.m ⟨_, _, []⟩) => some true
  | _ => none

/-! ## The pass -/

/-- Two frame cells holding one word, known as the constant `g^k` and as a base's word times `g^c`:
the base's exponent is `k - c`. -/
def Abs.pinEq (A : Abs) : Val → Val → Abs
  | .m ⟨0, k, []⟩, .m ⟨0, c, [(b, 1)]⟩ =>
    if k < 2 ^ 62 && c ≤ k then (A.addLt (.ex b 0) (.num (k - c + 1))).addLt (.num (k - c)) (.ex b 1)
    else A
  | _, _ => A

/-- The fall-through of a `JUMP` on `[c]`: `[c] = 0`, so a sum `[c] = [a] + [b]` gives `[a] = [b]`: the
word of one known for the other, or, both known, the exponent of a base equal to a constant; `b`
equal to a constant `g^k`, its exponent, its word left its own base (a product over it then names
the same cells on either side of the branch). -/
noncomputable def Abs.learn0 (A : Abs) (c : ℕ) : Abs :=
  match A.xs.get c with
  | some (a, b) =>
    match A.v.get b, A.v.get a with
    | none, some (.m ⟨0, k, []⟩) => A.pinEq (.m ⟨0, k, []⟩) (.m (.root b))
    | none, _ => A.addV b ((A.v.get a).getD (.m (.root a)))
    | some _, none => A.addV a ((A.v.get b).getD (.m (.root b)))
    | some y, some x => (A.pinEq x y).pinEq y x
  | none => A

/-- At most two paths apart: more are met into one. -/
noncomputable def cap : List Abs → List Abs
  | A :: B :: C :: Ds => [(B :: C :: Ds).foldl Abs.inter A]
  | As => As

/-- The meet of the states, in order, evaluated as it goes. -/
noncomputable def meetAll : List Abs → List Abs
  | A :: Bs => [foldlA Abs.interS A Bs]
  | [] => []

/-- `k As`, each state evaluated first. -/
noncomputable def forceAll {β : Type} : List Abs → (List Abs → β) → β
  | [], k => k []
  | A :: As, k => A.force fun A ↦ forceAll As fun As ↦ k (A :: As)

/-- Strictly increasing. -/
def incr : List ℕ → Bool
  | a :: b :: l => a < b && incr (b :: l)
  | _ => true

/-- A jump's edges from `A` into the targets `ts`: joined to the first group of the same targets,
else a new group last. A group of at least three states is met at once, as it would be at each of its
targets. -/
noncomputable def addGrp (ts : List ℕ) (A : Abs) : Pend → Pend
  | [] => [⟨ts, [A], false⟩]
  | g :: gs =>
    if g.ts == ts then
      listSeq (g.Bs ++ [A]) fun Bs ↦
        if g.m || 3 ≤ Bs.length then forceAll (meetAll Bs) fun Ms ↦ ⟨g.ts, Ms, true⟩ :: gs
        else ⟨g.ts, Bs, false⟩ :: gs
    else g :: addGrp ts A gs

/-- The states the groups give offset `i`, in order, the paths they count (a met group three), and
the groups past `i`. -/
noncomputable def popAt (i : ℕ) : Pend → List Abs × ℕ × Pend
  | [] => ([], 0, [])
  | g :: gs =>
    match popAt i gs with
    | (As, n, ps) =>
      match g.ts with
      | t :: ts =>
        if t == i then
          (g.Bs ++ As, n + (if g.m then 3 else g.Bs.length), if ts.isEmpty then ps else ⟨ts, g.Bs, g.m⟩ :: ps)
        else (As, n, g :: ps)
      | [] => (As, n, ps)

/-- The paths at offset `i`: what falls through and what the groups give, met into one when more
than two. -/
noncomputable def joinAt (i : ℕ) (cur : List Abs) (pend : Pend) : List Abs × Pend :=
  match popAt i pend with
  | (As, n, ps) => (if 2 < cur.length + n then meetAll (cur ++ As) else cur ++ As, ps)

/-- One path at one offset: the hints, the residuals, the instruction. `none` if anything fails;
else what falls through, and the pending edges. -/
noncomputable def offStep (E : Env) (F : Fun) (i : ℕ) (A : Abs) (ins : OffsetInstruction)
    (pend : Pend) : Option (List Abs × Pend) := do
  let A ← stepHints A ((F.hints.get i).getD [])
  let A ← addRes A ((F.res.get i).getD [])
  match ins with
  | .jump c d f =>
    let A ← stepOp E (F.entry + i) A ins
    match condOf A c with
    | some false => some ([A.learn0 c], pend)
    | k =>
      let (go, A') ← jumpI E F i A d f
      let fall := if k == some true then [] else [A.learn0 c]
      match go with
      | .to ts =>
        if ts.all (i < ·) && incr ts then
          some (fall, if ts.isEmpty then pend else A'.force fun A' ↦ addGrp ts A' pend)
        else none
      | .out => some (fall, pend)
  | ins => (stepOp E (F.entry + i) A ins).map fun A ↦ ([A], pend)

/-- Every path at one offset. -/
noncomputable def stepAll (E : Env) (F : Fun) (i : ℕ) (ins : OffsetInstruction) :
    List Abs → Pend → Option (List Abs × Pend)
  | [], pend => some ([], pend)
  | A :: As, pend =>
    match offStep E F i A ins pend with
    | some (cs, pend) => (stepAll E F i ins As pend).map fun p ↦ (cs ++ p.1, p.2)
    | none => none

/-- At a cut, the paths and pending edges must be at least its own, which the walk goes on from. -/
noncomputable def cutAt (F : Fun) (i : ℕ) (cur : List Abs) (pend : Pend) : Option (List Abs × Pend) :=
  match F.cuts.get i with
  | some S => if subAll S.1 cur && pendSub S.2 pend then some S else none
  | none => some (cur, pend)

/-- The walk over the code from offset `i`: the paths and pending edges after it. -/
noncomputable def runCode (E : Env) (F : Fun) :
    List OffsetInstruction → ℕ → List Abs → Pend → Option (List Abs × Pend)
  | [], _, cur, pend => some (cur, pend)
  | ins :: code, i, cur, pend =>
    match joinAt i cur pend with
    | (sts, pend) =>
      match stepAll E F i ins sts pend with
      | some (cur, pend) => forceAll cur fun cur ↦
        match cutAt F (i + 1) cur pend with
        | some (cur, pend) => runCode E F code (i + 1) cur pend
        | none => none
      | none => none

/-- **The walk accepts a function's code**: it goes through, no edge left pending. -/
noncomputable def walk (E : Env) (F : Fun) (code : List OffsetInstruction) : Bool :=
  match runCode E F code 0 [entryAbs E F.sig] [] with
  | some (_, pend) => pend.isEmpty
  | none => false

end

end LeanVM.Guest.Mode
