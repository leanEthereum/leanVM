/-
  LeanVM.Guest.Core

  The core IR of the aggregation guest: straight-line statements over named field values, forward
  branches, `match`, calls and loop functions, as the zkDSL compiler emits them per compiled
  function; and its relational semantics.
-/

module

public import LeanVM.Guest.Word

/-!
# The core IR

One core function (`Fn`) per function the compiler lowers: an original function, a `Const`
specialization (`f__L3_L5`) or a `mul_range` helper (`__loopN`), with the names the compiler
gives them. Its values (`V`) are named by their position in the expansion (`Seg`), never by a
frame offset: a certificate from the compiler maps each to the frame cell holding it, several
names possibly to one cell (the compiler shares pure results, pooled constants and repeated
loads, which changes no relation).

**Statements.** An `Atom` is one or a few instructions on values: constants (`SET`), `+`
(`XOR`), `*` (`MUL`), copies (`MUL` by the frame's one cell), memory words through a pointer
(`DEREF`, a heap read and a heap store being the same relation), the three assertions,
`assert_in_k` (an untaken `JUMP`), `BLAKE2S`, the address of a frame run (`addr`) and hints. A
`Stmt` adds the control flow: a forward branch on a `K` word, a `match` whose arms run inline in
the frame, a call, the conditional call that ends a loop helper, and a fused `match` of calls.

**Semantics** (`Fn.Sem`, `Program.Rel`). A function relates the memory reader `rd`, its
argument words and its return words: some valuation `σ` of all its values satisfies every atom
on the path the branches take. Every atom's relation is the conjunction of its instructions'
relations (`LeanVM.Semantics.executeWith`), so nothing is assumed of the allocator: a hint, a
`HeapBuf` pointer and a fresh frame cell are unconstrained values, and distinct names may hold
the same word. Frame plumbing (frame pointers, return addresses, jump targets) is not in the IR.
Calls are interpreted by a relation `C`; `Program.relN P rd n` is the call relation of depth `n`
and `Program.Rel` its union, the least fixed point.

Two meanings are the compiler's and not an instruction's. A `match` (and a fused `dispatch`)
holds of one arm `j < arms.length` at `x = g^j`: the selector being in range is a conjunct of its
semantics (`Stmt.holdsArms_iff`), which the bytecode's table jump gives only once the selector is
known to be in range, and which the surrounding proof discharges however it knows it, from a
range check in the function, a precondition of the function or a postcondition of a callee.
And `frameAddr p run` says that `p` is in `K` and that every readable word at `p·g^k`,
`k < run.length`, is the run's cell `k`, which is what the frame being memory gives.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## Names -/

/-- One step of a value's position in the expansion of its function. -/
inductive Seg where
  /-- Statement `i` of a block. -/
  | s (i : Nat)
  /-- The `unroll` iteration whose counter is `j`. -/
  | u (j : Nat)
  /-- The `then` block of an `if`, folded or not. -/
  | t
  /-- The `else` block of an `if`, folded or not. -/
  | e
  /-- Arm `j` of a `match`. -/
  | a (j : Nat)
  /-- The body of an `@inline` call to `f`, the `site`-th value position of its caller. -/
  | i (f : String) (site : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- A value: its position (innermost step first), the order in which its statement made it,
and its index in a run of consecutive cells (`StackBuf`, the targets of a `match`, a
function's parameters), zero for a single value. -/
structure V where
  path : List Seg
  tag : Nat
  idx : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Parameter cell `k` of a function: its arguments, flattened. -/
def V.param (k : Nat) : V := ⟨[], 0, k⟩

/-- Two values the compiler certainly places in consecutive frame cells. -/
def V.adjacent (a b : V) : Bool := a.path == b.path && a.tag == b.tag && b.idx == a.idx + 1

/-! ## Statements -/

/-- Where a hint writes: frame cells, or `len` memory words from `ptr·g^off`. -/
inductive Dest where
  | stack (cells : List V)
  | heap (ptr : V) (off len : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A hint: values the prover writes, constrained by nothing here (`RHint`). -/
inductive Hint where
  /-- The next entry of a witness stream. -/
  | witness (stream : String) (dest : Dest)
  /-- Bits `start ..< start + nbits` of a word, as `0`/`1` words. -/
  | bits (value : V) (start nbits : Nat) (dest : Dest)
  /-- The `nbits` low bits of `n`, where `value = g^n`. -/
  | bitsExp (value : V) (nbits : Nat) (dest : Dest)
  /-- The first limbs of a word. -/
  | limbs (value : V) (dest : List V)
  /-- `g^max(⌈log₂ v⌉, floor)` for the value `v` of `nbits` bits. -/
  | log2Ceil (bits : Dest) (nbits floor : Nat) (dst : V)
  /-- `x⁻¹`, or `0`. -/
  | inverse (x dst : V)
  /-- A fresh `HeapBuf(size)` pointer. -/
  | alloc (dst : V) (size : Nat)
  /-- A fresh `HeapBuf` pointer, the size in the exponent of `size`. -/
  | allocDyn (dst size : V)
  deriving DecidableEq, Repr, Inhabited

/-- An atom: one or a few instructions of the compiled function, on values. -/
inductive Atom where
  /-- `SET`: `d = c`. -/
  | const (d : V) (c : E)
  /-- `XOR`: `d = a + b`. -/
  | add (d a b : V)
  /-- `MUL`: `d = a · b`; a division `q = a / b` is `mul a q b`. -/
  | mul (d a b : V)
  /-- A copy, `MUL` by the frame's one cell: `d = s`. -/
  | copy (d s : V)
  /-- `DEREF`: `p` is in `K` and the word at `p·g^off` is `d`. -/
  | load (d p : V) (off : Nat)
  /-- `assert a == b`: `XOR` into the frame's zero cell. -/
  | assertEq (a b : V)
  /-- `assert a != b` on `x = a + b`: `p = x · inv` (`MUL`) and `p = 1` (`SET`). -/
  | assertNe (x inv p : V)
  /-- `assert log x < log (g·k)`: `DEREF` through `x` into `t1`, `k = x · y` (`MUL`), `DEREF`
  through `y` into `t2`. -/
  | rangeCheck (x y t1 t2 k : V)
  /-- `assert_in_k(a, b)`: a `JUMP` on the zero cell, to `a`, with frame `b`. -/
  | assertInK (a b : V)
  /-- `BLAKE2S`: `(out0, out1)` is the compression of `m0..m3` under `(cv0, cv1)` with the
  metadata word `md`. -/
  | blake2s (m0 m1 m2 m3 cv0 cv1 out0 out1 md : V)
  /-- `addr(run)`: `p` is the address of the frame run. -/
  | frameAddr (p : V) (run : List V)
  /-- A hint. -/
  | hint (h : Hint)
  deriving DecidableEq, Inhabited

/-- A statement. -/
inductive Stmt where
  | atom (a : Atom)
  /-- A forward branch on `c`, which must be in `K`: `zero` runs at `c = 0`. -/
  | ite (c : V) (zero nonzero : List Stmt)
  /-- `match`: arm `j` runs, inline, at `x = g^j`; the semantics requires `j < arms.length`. -/
  | match_ (x : V) (arms : List (List Stmt))
  /-- A call: the callee's relation on the argument and return words. -/
  | call (f : String) (args rets : List V)
  /-- The conditional call ending a loop helper (`CallIfNe`): `f` runs at `c ≠ 0`. -/
  | callIf (c : V) (f : String) (args : List V)
  /-- A fused `match` of calls: `fs[j]` runs at `x = g^j`, `j < fs.length`, on one shared
  frame. -/
  | dispatch (x : V) (fs : List String) (args rets : List V)
  /-- Return these words. -/
  | ret (vs : List V)
  deriving Inhabited, BEq

/-- A core function. -/
structure Fn where
  name : String
  /-- The argument cells, flattened (`V.param k`). -/
  params : List V
  body : List Stmt
  deriving Inhabited, BEq

/-- A core program: its functions, `main` first. -/
abbrev Program := List Fn

/-- The function of a name. -/
def Program.find? (P : Program) (f : String) : Option Fn := List.find? (fun g => g.name == f) P

/-! ## Semantics -/

/-- A valuation of every value. -/
abbrev Val := V → E

/-- The memory, as the ISA reads it: the word at an address, if any (`MemImage.read`). -/
abbrev Reader := K → Option E

/-- A call relation: callee, argument words, return words. -/
abbrev CallRel := String → List E → List E → Prop

/-- A `DEREF` through the pointer word `p`: `p` is in `K` and the word at `p·g^off` is `d`. -/
def LoadHolds (rd : Reader) (p : E) (off : Nat) (d : E) : Prop :=
  IsInK p ∧ rd (p.limb 0 * gpow off) = some d

/-- The relation of an atom. -/
def Atom.Holds (rd : Reader) (σ : Val) : Atom → Prop
  | .const d c => σ d = c
  | .add d a b => σ d = σ a + σ b
  | .mul d a b => σ d = σ a * σ b
  | .copy d s => σ d = σ s
  | .load d p off => LoadHolds rd (σ p) off (σ d)
  | .assertEq a b => σ a + σ b = 0
  | .assertNe x inv p => σ p = σ x * σ inv ∧ σ p = 1
  | .rangeCheck x y t1 t2 k =>
      LoadHolds rd (σ x) 0 (σ t1) ∧ σ k = σ x * σ y ∧ LoadHolds rd (σ y) 0 (σ t2)
  | .assertInK a b => IsInK (σ a) ∧ IsInK (σ b)
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
      CompressCells ![σ m0, σ m1, σ m2, σ m3] (σ cv0) (σ cv1) (σ o0) (σ o1) (σ md)
  | .frameAddr p run =>
      IsInK (σ p) ∧ ∀ (k : Nat) (hk : k < run.length) (w : E),
        rd ((σ p).limb 0 * gpow k) = some w → w = σ run[k]
  | .hint _ => True

mutual
/-- A statement holds, then `next` (the rest of its block) holds; a `ret` hands its words to
`kret` instead. -/
def Stmt.Holds (C : CallRel) (rd : Reader) (σ : Val) :
    Stmt → Prop → (List E → Prop) → Prop
  | .atom a, next, _ => a.Holds rd σ ∧ next
  | .ite c z n, next, kret =>
      IsInK (σ c) ∧ (σ c = 0 → Stmt.HoldsList C rd σ z next kret) ∧
        (σ c ≠ 0 → Stmt.HoldsList C rd σ n next kret)
  | .match_ x arms, next, kret => Stmt.HoldsArms C rd σ x 0 arms next kret
  | .call f args rets, next, _ => C f (args.map σ) (rets.map σ) ∧ next
  | .callIf c f args, next, _ => IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) []) ∧ next
  | .dispatch x fs args rets, next, _ =>
      (∃ (j : Nat) (h : j < fs.length), σ x = ofK (gpow j) ∧ C fs[j] (args.map σ) (rets.map σ)) ∧
        next
  | .ret vs, _, kret => kret (vs.map σ)

/-- A block holds, then `next`. -/
def Stmt.HoldsList (C : CallRel) (rd : Reader) (σ : Val) :
    List Stmt → Prop → (List E → Prop) → Prop
  | [], next, _ => next
  | s :: ss, next, kret => Stmt.Holds C rd σ s (Stmt.HoldsList C rd σ ss next kret) kret

/-- Arm `j + i` holds at `x = g^(j + i)`, for some arm `i` of the list. -/
def Stmt.HoldsArms (C : CallRel) (rd : Reader) (σ : Val) (x : V) :
    Nat → List (List Stmt) → Prop → (List E → Prop) → Prop
  | _, [], _, _ => False
  | j, a :: as, next, kret =>
      (σ x = ofK (gpow j) ∧ Stmt.HoldsList C rd σ a next kret) ∨
        Stmt.HoldsArms C rd σ x (j + 1) as next kret
end

/-- A function's relation: some valuation takes the parameters to the arguments and its body to
a `ret` of the return words. -/
def Fn.Sem (C : CallRel) (rd : Reader) (f : Fn) (args rets : List E) : Prop :=
  ∃ σ : Val, f.params.map σ = args ∧ Stmt.HoldsList C rd σ f.body False (fun rs => rs = rets)

/-- The call relation of depth `n`: calls nested at most `n` deep. -/
def Program.relN (P : Program) (rd : Reader) : Nat → CallRel
  | 0 => fun _ _ _ => False
  | n + 1 => fun f args rets => ∃ fn, P.find? f = some fn ∧ fn.Sem (P.relN rd n) rd args rets

/-- A program's call relation: every finite depth. -/
def Program.Rel (P : Program) (rd : Reader) : CallRel :=
  fun f args rets => ∃ n, P.relN rd n f args rets

end
end LeanVM.Guest.Core
