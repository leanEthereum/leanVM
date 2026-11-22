module

public import LeanVM.Guest.ExecCore
public import LeanVM.Guest.Mode.Bucket
public import Statement.Prover.Execute

/-!
# The frame walk's domain

What a function's frame walk knows at an instruction, relative to its frame (`Abs`): the frame offsets
written (`w`), the words known of frame cells (`v`: a product `Mono` of powers of the frame pointer,
of `g` and of *bases*, or a constant), the frame cells known nonzero (`nz`), the heap cells known
written (`h`, each named by a product), runs of them (`r`, a `Rng`: the cells named by
`q·g^(S·j + d)` for `j` between two exponents), the words known of heap cells (`hv`), inequalities
between exponents (`lt`, over `Idx`: a constant, or a base's exponent plus a constant), the last
products (`pr`, for the range-check and `!=` gadgets), sums by their cell (`xs`), and runs of
pointers (`p`). A base is a frame cell (`fr o`) or cell `d` past the cell a frame cell names
(`hp q d`). A heap cell of the frame itself (`fp^1·g^d`) is frame cell `d`, kept in `w` and `v`.

A function's view: its signature (`Sig`: the cells it needs written at entry, the heap facts it needs
and guarantees), its residuals (`Res`), the program's (`Env`) and its own (`Fun`); `entryAbs`, what
holds at its entry; `stepHint`, one hint, the cells it reads known written and what it writes. The
states are evaluated as they are built (`Abs.force`, `foldlA`), for the kernel, and a list is searched
for a fact by key (`buckets`, `Mode/Bucket.lean`). Their meaning is `Mode/Sem.lean`.

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

/-- The base list `bs` divided by `b^e`, if it holds `b^e` exactly. -/
def removeBs (a : Base × ℕ) : List (Base × ℕ) → Option (List (Base × ℕ))
  | [] => none
  | b :: bs =>
    if a.1.beq b.1 then (if a.2 == b.2 then some bs else none)
    else (removeBs a bs).map (b :: ·)

/-- The frame cell `d` a product names, when it is `fp · g^d`. -/
def Mono.ownCell (m : Mono) : Option ℕ :=
  if m.fp == 1 && m.bs.isEmpty && m.k < 2 ^ 62 then some m.k else none

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

/-- A product's key, for lists of facts by key (`buckets`): equal products have equal keys. -/
def monoKey (m : Mono) : ℕ := (m.k + m.fp) % 4096

/-- A run's key: runs of one product, stride and offset have equal keys. -/
def rngKey (r : Rng) : ℕ := (r.d + r.q.k) % 4096

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

/-- `k A`, `A`, its tries and its lists evaluated first. -/
def Abs.force {β : Type} (A : Abs) (k : Abs → β) : β :=
  match A with
  | ⟨w, v, nz, hv, h, r, lt, pr, xs, p, c⟩ =>
    w.seq fun w ↦ v.seq fun v ↦ nz.seq fun nz ↦ xs.seq fun xs ↦ lseq hv fun hv ↦ lseq h fun h ↦
      lseq r fun r ↦ lseq lt fun lt ↦ lseq pr fun pr ↦ lseq p fun p ↦ lseq c fun c ↦
        k ⟨w, v, nz, hv, h, r, lt, pr, xs, p, c⟩

/-- `l.foldl f A`, each state evaluated before the next step. -/
noncomputable def foldlA {α : Type} (f : Abs → α → Abs) (A : Abs) (l : List α) : Abs :=
  List.rec (motive := fun _ ↦ Abs → Abs) (fun A ↦ A) (fun x _ ih A ↦ (f A x).force ih) l A

/-- `l.foldl (·.set () envDepth ·) t`, each trie evaluated before the next step. -/
noncomputable def foldlT (t : Trie Unit) (l : List ℕ) : Trie Unit :=
  List.rec (motive := fun _ ↦ Trie Unit → Trie Unit) (fun t ↦ t)
    (fun o _ ih t ↦ (t.set () envDepth o).seq ih) l t

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

/-- Exponents in order. -/
def Abs.addLt (A : Abs) (a b : Idx) : Abs := { A with lt := (a, b) :: A.lt }

/-- A base's key. -/
def baseKey : Base → ℕ
  | .fr o => 2 * o + 1
  | .hp q d => 2 * (64 * q + d) + 2

/-- An exponent's key, its base's: inequalities are filed by the exponents a comparison reads them
through (`Idx.off`, `Idx.sle`), which share their base. -/
def idxKey : Idx → ℕ
  | .num _ => 0
  | .ex x _ => 1 + baseKey x % 4095

/-- An exponent's kind: a constant, a base's exponent, or one plus a positive constant. -/
def idxKind : Idx → ℕ
  | .num _ => 0
  | .ex _ 0 => 1
  | .ex _ _ => 2

/-- An inequality's key by its exponents' bases. -/
def leKey (p : Idx × Idx) : ℕ := (idxKey p.1 + 67 * idxKey p.2) % 4096

/-- `1` for an inequality `p < q` with `q` a constant at most `p`'s: the only kind through which
`Abs.le` can find `a ≤ b` for constants `a > b`. -/
def bigKey (p : Idx × Idx) : ℕ :=
  match p with
  | (.num c, .num m) | (.ex _ c, .num m) => if m ≤ c then 1 else 0
  | _ => 0

/-- `a ≤ b`, directly, or through a known `p < q` with `b = q + t` and `a ≤ p + 1 + t` (only a `p` of
`a`'s base serves when `a` is a base's exponent, only a `q` of `b`'s base). -/
def Abs.le (A : Abs) (a b : Idx) : Bool :=
  a.sle b ||
    let f := fun (p : Idx × Idx) ↦ match p.2.off b with
      | some t => a.sle (p.1.succ.shift t)
      | none => false
    match a, b with
    | .ex _ _, _ => anyB (buckets leKey A.lt) f (leKey (a, b))
    | .num _, .ex _ _ => anyB (buckets (idxKey ·.2) A.lt) f (idxKey b)
    | .num _, .num _ => anyB (buckets bigKey A.lt) f 1

/-- An inequality's key by its lower exponent's kind and its upper exponent's base. -/
def ltKey (p : Idx × Idx) : ℕ := idxKind p.1 + 3 * idxKey p.2

/-- `a < b`, directly, or through a known `p < q` with `a = p + t` and `q + t ≤ b`, or with
`a + 1 ≤ p` and `q ≤ b + 1` (only a `q` that is a constant or of `b`'s base serves). -/
def Abs.ltI (A : Abs) (a b : Idx) : Bool :=
  a.succ.sle b ||
    let f := fun (p : Idx × Idx) ↦ (match p.1.off a with
      | some t => (p.2.shift t).sle b
      | none => false) || (a.succ.sle p.1 && p.2.sle b.succ)
    match a, b with
    | .ex _ _, .ex _ _ => anyB (buckets leKey A.lt) f (leKey (a, .num 0)) || anyB (buckets leKey A.lt) f (leKey (a, b))
    | .ex _ _, .num _ => anyB (buckets leKey A.lt) f (leKey (a, .num 0))
    | .num _, .ex _ _ => anyB (buckets ltKey A.lt) f 0 || anyB (buckets ltKey A.lt) f 2 ||
        anyB (buckets ltKey A.lt) f (3 * idxKey b) || anyB (buckets ltKey A.lt) f (3 * idxKey b + 2)
    | .num _, .num _ => anyB (buckets ltKey A.lt) f 0 || anyB (buckets ltKey A.lt) f 2

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

/-- A product's bases' key, with its power of the frame pointer. -/
def bsKey (fp : ℕ) (bs : List (Base × ℕ)) : ℕ := bs.foldl (fun a p ↦ (33 * a + baseKey p.1 + 5 * p.2) % 4096) fp % 4096

/-- A run's key, its product's bases'. -/
def rngQKey (r : Rng) : ℕ := bsKey r.q.fp r.q.bs

/-- A run's key for its cell, if it is one point between constants (`monoKey` of the cell), else
`4096`, no cell's. -/
def ptKey (r : Rng) : ℕ :=
  match r.lo, r.hi with
  | .num a, .num b => if b == a + 1 then monoKey (r.q.shift (r.S * a + r.d)) else 4096
  | _, _ => 4096

/-- A run of one point between constants. -/
def Rng.isPt (r : Rng) : Bool :=
  match r.lo, r.hi with
  | .num a, .num b => b == a + 1
  | _, _ => false

/-- A known run holds the heap cell `k`: a run of one point that is `k`'s cell is tried first (by
`ptKey`); otherwise only a run whose product has `k`'s bases, or all but one of them, can
(`Rng.idxOf`), so only those are tried. -/
def Abs.inRuns (A : Abs) (k : Mono) : Bool :=
  anyB (buckets ptKey (A.r.filter Rng.isPt)) (A.inRng k) (monoKey k) ||
  anyB (buckets rngQKey A.r) (A.inRng k) (bsKey k.fp k.bs) ||
  k.bs.any fun e ↦ anyB (buckets rngQKey A.r) (A.inRng k) (bsKey k.fp (k.bs.filter fun p ↦ !p.1.beq e.1))

/-- The heap cell `k` is a known one or in a known run. -/
def Abs.coveredHR (A : Abs) (k : Mono) : Bool :=
  anyB (buckets monoKey A.h) (·.beq k) (monoKey k) || A.inRuns k

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
  | .ex _ _ => (((buckets (idxKey ·.1) A.lt).get (idxKey hi)).getD []).foldl (fun acc p ↦ match p.2, p.1.off hi with
      | .num q, some t => minO acc (q + t - 1)
      | _, _ => acc) none

/-- Every cell of run `r`, from a constant to a known bound at most 64 further, is known: a known run
of constant bounds holds them all, or each is known by `coveredHR` (its last tried first): a run
another state entails at a join. -/
def Abs.entR (A : Abs) (r : Rng) : Bool :=
  match r.lo, A.bound r.hi with
  | .num a, some b => decide (b - a ≤ 64) && A.knownH r.q &&
      (anyB (buckets rngKey A.r) (fun r' ↦ r'.q.beq r.q && r'.S == r.S && r'.d == r.d && match r'.lo, r'.hi with
          | .num a', .num b' => decide (a' ≤ a) && decide (b ≤ b')
          | _, _ => false) (rngKey r) ||
        (decide (b ≤ a) || A.coveredHR (r.q.shift (r.S * (b - 1) + r.d))) &&
        (List.range (b - a)).all fun j ↦ A.coveredHR (r.q.shift (r.S * (a + j) + r.d)))
  | _, _ => false

/-- The exponent of base `b`, when known exactly (the least such, if several). -/
def Abs.pin (A : Abs) (b : Base) : Option ℕ :=
  (((buckets (idxKey ·.1) A.lt).get (idxKey (.ex b 0))).getD []).foldl (fun acc p ↦ match p with
    | (.ex b' 0, .num q) =>
      if b'.beq b && 0 < q &&
          anyB (buckets (idxKey ·.2) A.lt) (fun p' ↦ p'.1.beq (.num (q - 1)) && p'.2.beq (.ex b 1))
            (idxKey (.ex b 1)) then
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

/-! ## Intersection -/

/-- Pending edges into later offsets: each target of `ts` (increasing) is entered by every state of
`Bs`; `m`: `Bs` is one state, the meet of at least three. -/
structure Grp where
  ts : List ℕ
  Bs : List Abs
  m : Bool

/-- The pending edges, in groups. -/
abbrev Pend := List Grp

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
  /-- Exponents in order at return. -/
  postT : List (Idx × Idx)
  /-- Exponents in order at return when a base's exponent is a value: `(x, j, lts)`. -/
  postC : List (Base × ℕ × List (Idx × Idx))

/-- A residual: a value fact the walk assumes at an instruction, proved apart. -/
inductive Res where
  /-- Two exponents in order. -/
  | lt (a b : Idx)
  /-- A frame cell nonzero. -/
  | nz (o : ℕ)
  /-- Every cell of run `a` is a cell of one of the runs `bs`. -/
  | sub (a : Rng) (bs : List Rng)
  /-- No fact: frame cell `o`'s word named by its cell, its product forgotten (a product of
  several bases used as an exponent). -/
  | name (o : ℕ)
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

/-- A `SET` immediate with a nonzero limb below `2^64`: a nonzero word. -/
def immNz (k0 k1 : ℕ) : Bool := (k0 != 0 && decide (k0 < 2 ^ 64)) || (k1 != 0 && decide (k1 < 2 ^ 64))

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
  | .allocArm ptr sel _ => if A.hasW sel then some (A.addW ptr) else none
  | .allocFrames ptr _ stop _ => if A.hasW stop then some (A.addW ptr) else none
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

/-! ## Cases on an exponent -/

/-! ## Calls -/

/-- An exponent read off the entry cells `es`: a constant, or an entry cell's. -/
def idxFr (es : List ℕ) : Idx → Bool
  | .num _ => true
  | .ex (.fr o) _ => decide (o ∈ es)
  | .ex (.hp _ _) _ => false

/-- Each termination fact read off the signature's entry cells. -/
def termFr (G : Sig) : Bool := G.term.all fun p ↦ idxFr G.entry p.1 && idxFr G.entry p.2

/-- The walk's state at a function's entry. -/
noncomputable def entryAbs (E : Env) (G : Sig) : Abs :=
  let A : Abs := ⟨foldlT .nil G.entry, .nil, .nil, [], G.pre,
    jtRng E :: G.preR, G.term, [], .nil, G.preP, []⟩
  match G.self with
  | some o => ((A.addW o).addV o (.m (.own 0))).addNz o
  | none => A

end

end LeanVM.Guest.Mode
