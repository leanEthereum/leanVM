import LeanVM.Protocol.ToClean.ComponentPolynomial
import LeanVM.Arithmetization.Statement

/-!
# Tests: Clean components as polynomials

A classic test for kernel evaluation. An expression with a degree-two constraint is translated
and evaluated on a satisfying and a failing row, and is Clean's polynomial of it; a variable at
the width reads `0`, as Clean reads a missing cell; the syntactic degree bounds but need not
equal the degree.

The six opcode tables and the two blocks of leanISA are translated with leanISA's separators,
directions and counted channels (the memory and bytecode pulls), and the result is checked
against the pinned Rust (`crates/leanvm_core/src/tables.rs` at
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`): the widths are the committed column counts `N` of
`:460`, `:542`, `:613`, `:716`, `:867` (`XOR` and `MUL` share `arith`), the count columns are
`count_columns()` of `:486`, `:551`, `:636`, `:725`, `:876`, and only `JUMP` has constraints,
its two of degree two (`n_constraints`, `:727-729`; the default is none, `:323-325`). Every
constraint and message coordinate has syntactic degree at most two, the bound `d = 2` of the M3
instance; the kernel decides it. Every read count is a column (`CountsAreVariables`, which a
constant count fails) and every message has at most fifteen coordinates, so a tuple determines
its message.
-/

namespace LeanVMTests.Protocol.ComponentPolynomial

open LeanVM.Parameters LeanVM.Arithmetization LeanVM.Protocol Air.Flat CPoly

/-! ## One expression -/

/-- The constraint `x · y` on a row of two cells. -/
def xy : Expression K := .mul (.var ⟨0⟩) (.var ⟨1⟩)

example : xy.degreeBound = 2 := rfl

-- The polynomial vanishes where Clean's evaluation does, and not elsewhere.
#guard (xy.toCMvPolynomial 2).eval ![0, 5] = 0
#guard (xy.toCMvPolynomial 2).eval ![3, 5] ≠ 0

/-- The translation evaluates as Clean does, on every row and data. -/
example (row : Fin 2 → K) (data : ProverData K) :
    (xy.toCMvPolynomial 2).eval row = xy.eval (Environment.fromArray (Array.ofFn row) data) :=
  Expression.eval_toCMvPolynomial row data xy

/-- Within the width, the translation is Clean's polynomial of the expression. -/
example : fromCMvPolynomial (xy.toCMvPolynomial 2) = xy.toBoundedPolynomial 2 (by decide) :=
  Expression.fromCMvPolynomial_toCMvPolynomial xy _

/-- A variable at the width is `0`, as Clean reads a missing cell. -/
example : (Expression.var ⟨2⟩ : Expression K).toCMvPolynomial 2 = 0 := rfl

-- The degree bound is an upper bound: `x·y + x·y` is `2·x·y = 0` in characteristic two.
example : (Expression.add xy xy).degreeBound = 2 := rfl
#guard (Expression.add xy xy).toCMvPolynomial 2 = 0

/-! ## leanISA's tables -/

/-- The channels whose coordinate `1` is a read count: the memory and bytecode pulls. -/
def counted (c : RawChannel K) : Bool := c.name = MemPull.name || c.name = BytecodePull.name

/-- The ensemble's eight components, in its order. -/
def components : List (Component K) :=
  [⟨xorTable⟩, ⟨mulTable⟩, ⟨setTable⟩, ⟨derefTable⟩, ⟨jumpTable⟩, ⟨blake2sTable⟩, ⟨memTable⟩,
    ⟨bytecodeTable⟩]

-- The widths are the Rust's committed column counts, and the blocks' row widths.
example : components.map Component.width = [15, 15, 8, 15, 14, 37, 5, 10] := by decide +kernel

-- The count columns are `count_columns()`, in its order; each block's finalize count is its
-- column `1`.
example : components.map (fun c ↦ (c.toM3 channelSep channelDir counted).count.map (·.val)) =
    [[11, 12, 13, 14], [11, 12, 13, 14], [6, 7], [11, 12, 13, 14], [8, 9, 10, 11],
      [27, 28, 29, 30, 31, 32, 33, 34, 35, 36], [1], [1]] := by
  decide +kernel

-- Only `JUMP` has constraints: two, of degree two. No component has a lookup.
example : components.map (fun c ↦ c.rowOperations.constraints.map Expression.degreeBound) =
    [[], [], [], [], [2, 2], [], [], []] := by
  decide +kernel
example : components.map (fun c ↦ c.rowOperations.lookups.length) = [0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

-- Every message coordinate has syntactic degree at most two.
example : components.all fun c ↦ c.rowOperations.interactions.all fun i ↦
    i.msg.toList.all fun e ↦ e.degreeBound ≤ 2 := by
  decide +kernel

-- The `JUMP` table's flushes: ten interactions, the state pull and push first; the push is
-- on the push side of the bus.
#guard ((⟨jumpTable⟩ : Component K).toM3 channelSep channelDir counted).flushes.map (·.1) =
  [.pull, .push, .pull, .push, .pull, .push, .pull, .push, .pull, .push]

-- Every read count of the eight components is a column: no count column is lost.
example : components.all fun c ↦ decide (CountsAreVariables c counted) := by
  decide +kernel

-- Every multiplicity is `1` or `-1`, so the tables drop none. A pull's is the product
-- `-1 · 1`, which has a value; a variable has none.
example : components.all fun c ↦ decide (UnitMultiplicities c) := by
  decide +kernel
example : (Expression.mul (.const (-1)) (.const 1) : Expression K).constValue = some (-1) := by
  decide +kernel
example : (Expression.var ⟨0⟩ : Expression K).constValue = none := rfl

-- Every message has at most fifteen coordinates, so its tuple determines it.
example : components.all fun c ↦ c.rowOperations.interactions.all fun i ↦
    decide (i.channel.arity ≤ 15) := by
  decide +kernel

-- A constant count is no count column: the predicate rejects it.
example : ¬ CountsAreVariables (⟨memTable⟩ : Component K) fun c ↦
    c.name = MemPush.name := by
  decide +kernel

-- Every expression of the eight components is within its width.
example : components.all fun c ↦ (c.rowOperations.constraints.all fun e ↦
    decide (e.WithinWidth c.width)) && c.rowOperations.interactions.all fun i ↦
      i.msg.toList.all fun e ↦ decide (e.WithinWidth c.width) := by
  decide +kernel

end LeanVMTests.Protocol.ComponentPolynomial
