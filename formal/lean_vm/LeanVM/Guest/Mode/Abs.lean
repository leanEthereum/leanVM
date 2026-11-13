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
products (`pr`, for the range-check and `!=` gadgets), and sums by their cell (`xs`). A base is a
frame cell (`fr o`) or cell `d` past the cell a frame cell names (`hp q d`). A heap cell of the frame
itself (`fp^1·g^d`) is frame cell `d`, kept in `w` and `v`.

`stepOp` is one instruction, `stepHint` one hint: the cells either reads must be known written (else
`none`), and what it surely writes, and what that teaches, joins. A `DEREF` of mode `cell` stores when
its frame side is known written, loads when its heap side is, and otherwise links, learning nothing.
`Abs.inter` is what two paths into a join both know. Calls, tail calls and returns (`entryOk`,
`afterCall`, `tailOk`, `retOk`) read the callee's `Sig`: the cells its walk needs written at entry,
the heap facts it needs over its own bases (`pre`, `preR`), and those it guarantees at return
(`ret`, `post`, `postR`, a loop's `postL`), translated through the caller's knowledge of the callee
frame (`trBase`). `walk` runs a function's code once, forward, keeping at most two paths apart at
each offset and meeting more into one; the fall-through of a `JUMP` on a sum learns its two terms
equal (`Abs.learn0`). Their meaning is `Mode/Sem.lean`,
their soundness `Mode/Sound*.lean`.

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

/-- The heap cell `k` is known written. -/
def Abs.covered (A : Abs) (k : Mono) : Bool :=
  match k.ownCell with
  | some d => A.hasW d
  | none => A.h.any (·.beq k) || A.r.any (A.inRng k)

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

/-- Every cell of run `r` is known written: a known run holds it, or each of its (at most `2^12`)
points is known written. -/
def Abs.coveredR (A : Abs) (r : Rng) : Bool :=
  A.r.any (fun r' ↦ r'.q.beq r.q && r'.S == r.S && r'.d == r.d && A.le r'.lo r.lo &&
    A.le r.hi r'.hi && A.hasIdx r.lo && A.hasIdx r.hi) ||
  match r.lo, r.hi with
  | .num a, .num b => b - a ≤ 4096 && r.q.bs.all (fun p ↦ match p.1 with
      | .fr o => A.hasW o
      | .hp _ _ => false) &&
      (List.range (b - a)).all fun j ↦ A.covered (r.q.shift (r.S * (a + j) + r.d))
  | _, _ => false

/-! ## Intersection -/

/-- Pairs both lists hold. -/
def interL {α : Type} (eq : α → α → Bool) (a b : List α) : List α := a.filter fun x ↦ b.any (eq x)

/-- What two states both know. -/
noncomputable def Abs.inter (A B : Abs) : Abs :=
  ⟨Trie.inter (fun _ _ ↦ true) A.w B.w, Trie.inter Val.beq A.v B.v,
    Trie.inter (fun _ _ ↦ true) A.nz B.nz,
    interL (fun p q ↦ p.1.beq q.1 && p.2.beq q.2) A.hv B.hv, interL Mono.beq A.h B.h,
    interL Rng.beq A.r B.r, interL (fun p q ↦ p.1.beq q.1 && p.2.beq q.2) A.lt B.lt, [],
    Trie.inter (fun p q ↦ p.1 == q.1 && p.2 == q.2) A.xs B.xs⟩

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

/-- A residual: a value fact the walk assumes at an instruction, proved apart. -/
inductive Res where
  /-- Two exponents in order. -/
  | lt (a b : Idx)
  /-- A frame cell nonzero. -/
  | nz (o : ℕ)
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

/-- The range check `DEREF *(x); MUL [z] = [x]·[y]; DEREF *(y)` with `[z] = g^k`, a base's word
times `g^k`, or a base's word over `g`, ending at the `DEREF` through `y`: `x`'s exponent is at most
`z`'s. -/
def rangeFact (A : Abs) (y : ℕ) : Abs :=
  match A.pr with
  | (x, y', z) :: _ =>
    if y' == y && A.ltI (.ex (.fr x) 0) (.num maxCells) then
      match A.mono z with
      | some ⟨0, k, []⟩ => if k < 2 ^ 62 then A.addLt (.ex (.fr x) 0) (.num (k + 1)) else A
      | some ⟨0, k, [(b, 1)]⟩ =>
        if k == 0 || (k < 2 ^ 62 && A.ltI (.ex b 0) (.num maxCells)) then
          A.addLt (.ex (.fr x) 0) (.ex b (k + 1))
        else if k == 2 ^ 64 - 2 then A.addLt (.ex (.fr x) 0) (.ex b 0)
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
            some { (match loadVal E A k with
              | some x => A1.addV c x
              | none => A1) with pr := A.pr }
          else some A0
    else none
  | .jump c d f => if A.hasW c && A.hasW d && A.hasW f then some A else none
  | .keccak m0 m1 m2 m3 tail b8 cap out _ _ outCells =>
    if (keccakIns m0 m1 m2 m3 tail b8 cap).all A.hasW then
      some { (List.range outCells.cellCount).foldl (fun A j ↦ A.addW (out + j)) A with pr := [] }
    else none

/-! ## One hint -/

/-- A run's start: frame offset `base` (stack), or the product a pointer cell holds. -/
def destOf (A : Abs) : BitsDest → Option (Option ℕ × Option Mono)
  | .stack base => some (some base, none)
  | .heap ptr => if A.hasW ptr then (A.mono ptr).map fun m ↦ (none, some m) else none

/-- Write `n` cells from `pos` at a run's start, each nonzero and below `2^bits` in exponent when
`bits` is given (a stack run). -/
noncomputable def writeRun (A : Abs) (dst : Option ℕ × Option Mono) (pos n : ℕ) (bits : Option ℕ) :
    Abs :=
  match dst with
  | (some base, _) =>
    (List.range n).foldl (fun A j ↦
      let A := A.addW (base + pos + j)
      match bits with
      | some b =>
        if b ≤ 61 then (A.addNz (base + pos + j)).addLt (.ex (.fr (base + pos + j)) 0) (.num (2 ^ b))
        else A.addNz (base + pos + j)
      | none => A) A
  | (none, some m) => (List.range n).foldl (fun A j ↦ A.addH (m.shift (pos + j))) A
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

/-- The residuals: each one's cells known written, the fact added. -/
def addRes (A : Abs) : List Res → Option Abs
  | [] => some A
  | .lt a b :: rs =>
    let ok := fun (i : Idx) ↦ match i with
      | .ex (.fr o) _ => A.hasW o
      | .ex (.hp q d) _ => A.covered ⟨0, d, [(.fr q, 1)]⟩
      | .num _ => true
    if ok a && ok b then addRes (A.addLt a b) rs else none
  | .nz o :: rs =>
    if A.hasW o then addRes { A with nz := A.nz.set () envDepth o } rs else none

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

/-- A base whose word is known to exist: a written frame cell, or a cell past a written pointer
cell that the walk knows written. -/
def Abs.knownB (A : Abs) : Base → Bool
  | .fr o => A.hasW o
  | .hp q d => A.hasW q && A.covered ⟨0, d, [(.fr q, 1)]⟩

/-- A product whose word is known to exist. -/
def Abs.known (A : Abs) (m : Mono) : Bool := m.bs.all fun p ↦ A.knownB p.1

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
    | none => false)

/-- The termination facts of callee `G` hold at the call. -/
def atCall (A : Abs) (mq : Mono) (G : Sig) : Abs :=
  G.term.foldl (fun A p ↦ match idxUp A mq p.1, idxUp A mq p.2 with
    | some a, some b => A.addLt a b
    | _, _ => A) A

/-- What the caller knows after callee `G` returns. -/
noncomputable def afterCall (A : Abs) (mq : Mono) (G : Sig) : Abs :=
  let A := G.ret.foldl (fun A o ↦ A.addH (mq.shift o)) A
  let A := G.post.foldl (fun A m ↦ match trMono A mq m with
    | some k => A.addH k
    | none => A) A
  let A := (G.postR ++ G.postL).foldl (fun A r ↦ match trRngUp A mq r with
    | some r => { A with r := r :: A.r }
    | none => A) A
  atCall A mq G

/-- The walk's state at a function's entry. -/
noncomputable def entryAbs (E : Env) (G : Sig) : Abs :=
  let A : Abs := ⟨G.entry.foldl (fun t o ↦ t.set () envDepth o) .nil, .nil, .nil, [], G.pre,
    jtRng E :: G.preR, G.term, [], .nil⟩
  match G.self with
  | some o => ((A.addW o).addV o (.m (.own 0))).addNz o
  | none => A

/-- A loop's run's point at its counter's start: the product `q·x^S·g^(S·c + d)` for `lo = x + c`. -/
def Rng.first (r : Rng) : Mono :=
  match r.lo with
  | .num c => r.q.shift (r.S * c + r.d)
  | .ex x c => (r.q.mul ⟨0, 0, [(x, r.S)]⟩).shift (r.S * c + r.d)

/-- A loop writes each run's point at its counter's start before a return or a tail call. -/
def loopOk (A : Abs) (G : Sig) : Bool :=
  G.postL.all fun r ↦ match trMono A (.own 0) r.first with
    | some k => A.covered k
    | none => false

/-- What the function guarantees holds at a return. -/
def retOk (A : Abs) (G : Sig) : Bool :=
  loopOk A G &&
  G.ret.all A.hasW && G.post.all (fun m ↦ match trMono A (.own 0) m with
    | some k => A.covered k
    | none => false) &&
  G.postR.all fun r ↦ match trRngDown A (.own 0) r with
    | some r => A.coveredR r
    | none => false

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
def calleesOf (E : Env) (F : Fun) (A : Abs) (i t : ℕ) : Option (List Sig) :=
  match A.v.get t with
  | some (.m ⟨0, e, []⟩) => (E.sigs.get e).map ([·])
  | some (.tab x d) =>
    match F.tabs.get i with
    | some n =>
      if A.ltI (.ex x 0) (.num n) && E.jtLo ≤ d && d + n ≤ E.jtHi then
        (List.range n).mapM fun j ↦ (E.jt.get (d + j)).bind E.sigs.get
      else none
    | none => none
  | _ => none

/-- The arms of a table jump at offset `i` through target cell `t`, as offsets. -/
def armsOf (E : Env) (F : Fun) (A : Abs) (i t : ℕ) : Option (List ℕ) :=
  match A.v.get t, F.tabs.get i with
  | some (.tab x d), some n =>
    if A.ltI (.ex x 0) (.num n) && E.jtLo ≤ d && d + n ≤ E.jtHi then
      (List.range n).mapM fun j ↦ (E.jt.get (d + j)).bind fun pc ↦
        if F.entry + i < pc && pc < F.entry + F.len then some (pc - F.entry) else none
    else none
  | _, _ => none

/-- A loop's tail call into frame `fp·g^e` moves each termination fact's counter up by a positive
power of `g` and keeps its bound. -/
def termStep (A : Abs) (e : ℕ) (G : Sig) : Bool :=
  G.term.all fun p ↦ match p with
    | (.ex _ 0, .ex _ 0) =>
      (match idxUp A (.own e) p.1 with
        | some a => match p.1.off a with
          | some t => decide (0 < t)
          | none => false
        | none => false) &&
      (match idxUp A (.own e) p.2 with
        | some b => b.beq p.2
        | none => false)
    | _ => false

/-- A loop's tail call into frame `fp·g^e` of callee `G`: its entry from this state, its counters
moved up, and each run it accumulates the next iteration's from one further. -/
def tailOk (A : Abs) (e : ℕ) (G : Sig) : Bool :=
  entryOk A (.own e) G && termStep A e G && G.postL.all fun r ↦ match trRngUp A (.own e) r with
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
          let A := (G :: Gs).foldl (fun A G ↦ atCall A mq G) A
          if (G :: Gs).all (entryOk A mq) && F.entry + i < r && r < F.entry + F.len then
            some (.to [r - F.entry], Gs.foldl (fun B G ↦ B.inter (afterCall A mq G))
              (afterCall A mq G))
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

/-- The fall-through of a `JUMP` on `[c]`: `[c] = 0`, so a sum `[c] = [a] + [b]` gives `[a] = [b]`. -/
noncomputable def Abs.learn0 (A : Abs) (c : ℕ) : Abs :=
  match A.xs.get c with
  | some (a, b) =>
    if (A.v.get b).isNone then A.addV b ((A.v.get a).getD (.m (.root a)))
    else A.addV a ((A.v.get b).getD (.m (.root b)))
  | none => A

/-- Pending edges into later offsets, by increasing target, with what each path into it knows. -/
abbrev Pend := List (ℕ × List Abs)

/-- Add an edge into `t` knowing `A`. -/
def addEdge (t : ℕ) (A : Abs) : Pend → Pend
  | [] => [(t, [A])]
  | (u, Bs) :: ps =>
    if t < u then (t, [A]) :: (u, Bs) :: ps
    else if t = u then (u, Bs ++ [A]) :: ps
    else (u, Bs) :: addEdge t A ps

/-- At most two paths apart: more are met into one. -/
noncomputable def cap : List Abs → List Abs
  | A :: B :: C :: Ds => [(B :: C :: Ds).foldl Abs.inter A]
  | As => As

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
      let pend := match go with
        | .to ts => ts.foldl (fun p t ↦ if i < t then addEdge t A' p else p) pend
        | .out => pend
      if (match go with | .to ts => ts.all (i < ·) | .out => true) then
        some (if k == some true then [] else [A.learn0 c], pend)
      else none
  | ins => (stepOp E (F.entry + i) A ins).map fun A ↦ ([A], pend)

/-- Every path at one offset. -/
noncomputable def stepAll (E : Env) (F : Fun) (i : ℕ) (ins : OffsetInstruction) :
    List Abs → Pend → Option (List Abs × Pend)
  | [], pend => some ([], pend)
  | A :: As, pend =>
    match offStep E F i A ins pend with
    | some (cs, pend) => (stepAll E F i ins As pend).map fun p ↦ (cs ++ p.1, p.2)
    | none => none

/-- The paths at offset `i`: what falls through and the pending edges into `i`, capped. -/
noncomputable def atJoin (i : ℕ) (cur : List Abs) (pend : Pend) : List Abs × Pend :=
  match pend with
  | (t, Bs) :: ps => if t = i then (cap (cur ++ Bs), ps) else (cap cur, pend)
  | [] => (cap cur, pend)

/-- The walk over the code from offset `i`. -/
noncomputable def walkFrom (E : Env) (F : Fun) : List OffsetInstruction → ℕ → List Abs → Pend → Bool
  | [], _, _, pend => pend.isEmpty
  | ins :: code, i, cur, pend =>
    match atJoin i cur pend with
    | (sts, pend) =>
      match stepAll E F i ins sts pend with
      | some (cur, pend) => walkFrom E F code (i + 1) cur pend
      | none => false

/-- **The walk accepts a function's code.** -/
noncomputable def walk (E : Env) (F : Fun) (code : List OffsetInstruction) : Bool :=
  walkFrom E F code 0 [entryAbs E F.sig] []

end

end LeanVM.Guest.Mode
