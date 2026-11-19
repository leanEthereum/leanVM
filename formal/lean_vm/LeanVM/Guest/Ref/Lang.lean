/-
  LeanVM.Guest.Ref.Lang

  The runtime stage of the zkDSL: constraints on named words and branches on a word, and the
  relation a function of them denotes.
-/

module

public import LeanVM.Guest.Core
public import LeanVM.Guest.B1.Common.HashPair

/-!
# Reference functions

The zkDSL (`crates/zkdsl_compiler/zkDSL.md`) has two stages. Its compile-time stage (`Const`
parameters, `unroll`, `if const`, a folded `if`, integer arithmetic, the rebinding of names) is
evaluated by the compiler; its runtime stage is what is left: reads and stores of memory words,
write-once frame cells, the Keccak builtins and branches on a word.

A source function's *reference function* is the source read stage by stage: a Lean function of
its `Const` arguments (the compile-time stage is Lean's own evaluation: `unroll` is `unroll`
below, `if const` an `if`) that returns its runtime stage as a `Func`, a list of commands on
words named as in the source (`X`: a parameter, a `StackBuf` cell, the word a read binds).

**Semantics** (`Func.Sem`). A function relates the memory reader, its argument words and its
return words: some valuation of its names satisfies every command. A name is a logic variable:
nothing is assumed of a frame cell before the command that writes it, so a store into a cell and
a `keccak` whose output lands on it are assertions about one word.

* `x[GEN ** k]` read into `d`, and `x[GEN ** k] = d`: `Cmd.load d x k`, one relation.
* `keccak(l, r, out)` on two-cell runs: `Cmd.hash2`, the output cells are the digest of the 64
  bytes of the input cells (`HashesPair`).
* `if c != 0: N else: Z` on a word: `Cmd.ifNz c Z N`; `c` is in `K`, as the branch instruction
  asks.

`LeanVM.Guest.Ref.Link` ties a compiled specialization to its reference function.
-/

namespace LeanVM.Guest.Ref

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

variable {X : Type}

/-- A word: a named one, a constant, a sum or a product. -/
inductive Tm (X : Type) where
  | v (x : X)
  | const (w : E)
  | add (a b : Tm X)
  | mul (a b : Tm X)

/-- The word a term denotes under a valuation of the names. -/
def Tm.eval (ρ : X → E) : Tm X → E
  | .v x => ρ x
  | .const w => w
  | .add a b => a.eval ρ + b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ

/-- A runtime command. -/
inductive Cmd (X : Type) where
  /-- The memory word at `p·g^off` is `d`: a read into `d`, or a store of `d`. -/
  | load (d p : Tm X) (off : Nat)
  /-- `keccak(l, r, out)` on two-cell runs. -/
  | hash2 (l0 l1 r0 r1 o0 o1 : Tm X)
  /-- A branch on the word `c`: `zero` at `c = 0`, else `nonzero`. -/
  | ifNz (c : Tm X) (zero nonzero : List (Cmd X))

mutual
/-- The relation of a command. -/
def Cmd.Sat (rd : Reader) (ρ : X → E) : Cmd X → Prop
  | .load d p off => LoadHolds rd (p.eval ρ) off (d.eval ρ)
  | .hash2 l0 l1 r0 r1 o0 o1 =>
      HashesPair (l0.eval ρ) (l1.eval ρ) (r0.eval ρ) (r1.eval ρ) (o0.eval ρ) (o1.eval ρ)
  | .ifNz c z n =>
      IsInK (c.eval ρ) ∧ (c.eval ρ = 0 → Cmd.SatList rd ρ z) ∧ (c.eval ρ ≠ 0 → Cmd.SatList rd ρ n)

/-- Every command of a block holds. -/
def Cmd.SatList (rd : Reader) (ρ : X → E) : List (Cmd X) → Prop
  | [] => True
  | c :: cs => Cmd.Sat rd ρ c ∧ Cmd.SatList rd ρ cs
end

/-- A reference function's runtime stage: its parameters' names, its commands, the words it
returns. -/
structure Func (X : Type) where
  params : List X
  body : List (Cmd X)
  rets : List (Tm X)

/-- A reference function's relation: some valuation of the names takes the parameters to the
arguments, satisfies every command and takes the returned terms to the return words. -/
def Func.Sem (rd : Reader) (r : Func X) (args rets : List E) : Prop :=
  ∃ ρ : X → E, r.params.map ρ = args ∧ Cmd.SatList rd ρ r.body ∧ r.rets.map (Tm.eval ρ) = rets

/-- `for i in unroll(lo, hi)`: the commands of each iteration, in order. -/
def unroll (lo hi : Nat) (body : Nat → List (Cmd X)) : List (Cmd X) :=
  (List.range' lo (hi - lo)).flatMap body

/-! ## Blocks -/

variable {rd : Reader} {ρ : X → E}

theorem Cmd.satList_nil : Cmd.SatList rd ρ [] := by rw [Cmd.SatList]; trivial

theorem Cmd.satList_cons {c : Cmd X} {cs : List (Cmd X)} :
    Cmd.SatList rd ρ (c :: cs) ↔ c.Sat rd ρ ∧ Cmd.SatList rd ρ cs := by rw [Cmd.SatList]

theorem Cmd.satList_append (as bs : List (Cmd X)) :
    Cmd.SatList rd ρ (as ++ bs) ↔ Cmd.SatList rd ρ as ∧ Cmd.SatList rd ρ bs := by
  induction as with
  | nil => simp [Cmd.SatList]
  | cons a as ih => simp [Cmd.SatList, ih, and_assoc]

theorem Cmd.satList_unroll (lo hi : Nat) (body : Nat → List (Cmd X)) :
    Cmd.SatList rd ρ (unroll lo hi body) ↔ ∀ i, lo ≤ i → i < hi → Cmd.SatList rd ρ (body i) := by
  have h : ∀ l : List Nat, Cmd.SatList rd ρ (l.flatMap body) ↔
      ∀ i ∈ l, Cmd.SatList rd ρ (body i) := fun l ↦ by
    induction l with
    | nil => simp [Cmd.SatList]
    | cons a l ih => simp [Cmd.satList_append, ih]
  rw [unroll, h]
  exact ⟨fun H i h1 h2 ↦ H i (List.mem_range'_1.mpr ⟨h1, by omega⟩),
    fun H i hm ↦ by have := List.mem_range'_1.mp hm; exact H i this.1 (by omega)⟩

end
end LeanVM.Guest.Ref
