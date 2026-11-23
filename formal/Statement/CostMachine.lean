module

public import Mathlib.Data.Nat.Notation

/-!
# The cost machine

**The machine.** A first-order functional language with prices. A program is an array of function
bodies; a body reads its arguments and the values it binds by position, calls functions by index,
applies closures, builds and inspects constructors, and runs priced primitive operations on natural
numbers and arrays. Values are immutable. A program carries its literals, and its size counts them
in full (`MachineProgram.size`); its only runtime data is its input.

`runMachineProgram program fuel input` runs function `0` of `program` on `input`: its value and its
price, the sum of its steps' prices, or `none` when the run misuses a value (a primitive on the
wrong kind of value, a missing variable, field, alternative or function) or nests more than `fuel`
calls. A misuse is a failure, never undefined behavior. `outputWithin program sizeBound budget
input` is the value if `program`'s size is at most `sizeBound` and the price at most `budget`: a
program's two resources, in one place. Each call costs at least `1`, so the fuel never fails a run
of price at most `budget`.

**Why the prices are honest** (trusted, not a hypothesis: they give the budgets of
`KnowledgeSoundness (extractorComputedBy P)` and `GuestKnowledgeSoundness` their meaning). Each step
is priced by the algorithm that computes it on a 64-bit machine, at least `1`. The environment is a
stack frame, read in place: a position costs `1`; a `let` pushes one value, a `case` the fields it
binds and a closure's application the captured values it puts in front of the arguments, each at `1`
per value; a call's frame is written by its argument terms, each of price at least `1`. A
constructor, a closure and a new array cost `1` and their entries; a field and an array's entry cost
`1`, read in place: values are immutable, so they are shared, not copied (an array's update copies
it). A natural number is held in limbs of 64 bits (`limbCount`) and knows their count: an operation
on natural numbers costs the limbs it reads or writes, the larger count (`linearlyPricedResult`),
and a product, quotient, remainder or carry-less product the product of its operands' limb counts,
at least the limbs it writes (`quadraticallyPricedResult`, schoolbook). An array's entry is read at
`1` whatever its index: an array of `2^64` entries or more costs at least `2^64` to build, so a
two-limb index is a constant factor off at most. The unit is a word operation: on one-limb operands
each operation is a few instructions of a 64-bit CPU (one, and a comparison for a shift by `64` or
more, a truncated subtraction or a division by `0`), the carry-less product x86-64's PCLMULQDQ or
ARMv8's PMULL; on more limbs, a constant number per limb or pair of limbs.

**Carry-less product.** `carryless a b`, the product of `a` and `b` read as polynomials over
`GF(2)` (bit `i` the coefficient of `x^i`), is the primitive `carrylessMultiply`; its loop is
bounded by the fuel `b` (each step halves `b`).
-/

namespace LeanVM.Cost

@[expose] public section

/-- The loop of `carryless`: while `b ≠ 0`, add `a` if `b`'s low bit is set, then shift. -/
def carrylessAux : (fuel a b out : ℕ) → ℕ
  | 0, _, _, out => out
  | fuel + 1, a, b, out =>
    if b = 0 then out
    else carrylessAux fuel (a <<< 1) (b >>> 1) (if b % 2 = 1 then out ^^^ a else out)

/-- `carryless a b`: the product of two binary polynomials. -/
def carryless (a b : ℕ) : ℕ := carrylessAux b a b 0

/-- The machine's values. -/
inductive MachineValue where
  /-- A natural number, of any size. -/
  | nat (n : ℕ)
  /-- A constructor: its tag and its fields. -/
  | constructor (tag : ℕ) (fields : List MachineValue)
  /-- An array. -/
  | array (entries : Array MachineValue)
  /-- A closure: function `functionIndex` with its first arguments. -/
  | closure (functionIndex : ℕ) (capturedArguments : List MachineValue)
  deriving Inhabited, BEq, Repr

/-- `false` and `true`: the constructors of tags `0` and `1`. -/
def MachineValue.ofBool (b : Bool) : MachineValue := .constructor (if b then 1 else 0) []

/-- A list: `nil` the constructor of tag `0`, `cons` of tag `1`. -/
def MachineValue.ofList : List MachineValue → MachineValue
  | [] => .constructor 0 []
  | x :: xs => .constructor 1 [x, MachineValue.ofList xs]

/-- The elements of a list value. -/
def MachineValue.toList? : MachineValue → Option (List MachineValue)
  | .constructor 0 [] => some []
  | .constructor 1 [x, xs] => (MachineValue.toList? xs).map (x :: ·)
  | _ => none

/-- The limbs of 64 bits of a natural number, at least one. -/
def limbCount (n : ℕ) : ℕ := n.log2 / 64 + 1

/-- The primitive operations, on natural numbers and arrays. None reads a constructor's tag or a
closure's function index as a number (see the section *Size* below). -/
inductive PrimitiveOperation where
  /-- `and`, `or`, `xor`, the shifts, `+`, truncated `−`, `=`, `<`. -/
  | bitwiseAnd | bitwiseOr | bitwiseXor | shiftLeft | shiftRight | add | truncatedSubtract
  | equal | lessThan
  /-- `·`, `/`, `%` (by `0`: `0` and `a`, as Lean's), the carry-less product (the product of
  `a` and `b` read as polynomials over `GF(2)`: `carryless`, whose loop runs once per bit of `b`,
  its fuel). -/
  | multiply | divide | modulo | carrylessMultiply
  /-- An array's size; its entry `i` or a default. -/
  | arraySize | arrayGet
  /-- A copy with entry `i` set (unchanged out of bounds), with one entry appended. -/
  | arraySet | arrayPush
  /-- An array from a list; a list from an array; two arrays appended; entries `[i, j)`; `n`
  copies of a value. -/
  | arrayOfList | arrayToList | arrayAppend | arrayExtract | arrayReplicate
  deriving DecidableEq, Repr

/-- The result `r` of an operation reading `a` and `b` once: the limbs it reads or writes, the
larger count. -/
def linearlyPricedResult (r a b : ℕ) : Option (MachineValue × ℕ) :=
  some (.nat r, max (limbCount r) (max (limbCount a) (limbCount b)))

/-- The result `r` of an operation pairing each limb of `a` with each limb of `b`: the product of
their counts, at least the limbs it writes. -/
def quadraticallyPricedResult (r a b : ℕ) : Option (MachineValue × ℕ) :=
  some (.nat r, max (limbCount r) (limbCount a * limbCount b))

/-- A primitive's value and price on its arguments, or `none` on a misuse. -/
def PrimitiveOperation.apply : PrimitiveOperation → List MachineValue → Option (MachineValue × ℕ)
  | .bitwiseAnd, [.nat a, .nat b] => linearlyPricedResult (a &&& b) a b
  | .bitwiseOr, [.nat a, .nat b] => linearlyPricedResult (a ||| b) a b
  | .bitwiseXor, [.nat a, .nat b] => linearlyPricedResult (a ^^^ b) a b
  | .shiftLeft, [.nat a, .nat k] => linearlyPricedResult (a <<< k) a k
  | .shiftRight, [.nat a, .nat k] => linearlyPricedResult (a >>> k) a k
  | .add, [.nat a, .nat b] => linearlyPricedResult (a + b) a b
  | .truncatedSubtract, [.nat a, .nat b] => linearlyPricedResult (a - b) a b
  | .equal, [.nat a, .nat b] => some (.ofBool (decide (a = b)), max (limbCount a) (limbCount b))
  | .lessThan, [.nat a, .nat b] => some (.ofBool (decide (a < b)), max (limbCount a) (limbCount b))
  | .multiply, [.nat a, .nat b] => quadraticallyPricedResult (a * b) a b
  | .divide, [.nat a, .nat b] => quadraticallyPricedResult (a / b) a b
  | .modulo, [.nat a, .nat b] => quadraticallyPricedResult (a % b) a b
  | .carrylessMultiply, [.nat a, .nat b] =>
    quadraticallyPricedResult (carryless a b) a b
  | .arraySize, [.array xs] => some (.nat xs.size, 1)
  | .arrayGet, [.array xs, .nat i, d] => some (xs.getD i d, 1)
  | .arraySet, [.array xs, .nat i, v] => some (.array (xs.setIfInBounds i v), xs.size + 1)
  | .arrayPush, [.array xs, v] => some (.array (xs.push v), xs.size + 2)
  | .arrayOfList, [l] => (MachineValue.toList? l).map fun xs ↦ (.array xs.toArray, xs.length + 1)
  | .arrayToList, [.array xs] => some (.ofList xs.toList, 3 * xs.size + 1)
  | .arrayAppend, [.array xs, .array ys] => some (.array (xs ++ ys), xs.size + ys.size + 1)
  | .arrayExtract, [.array xs, .nat i, .nat j] =>
    some (.array (xs.extract i j), (xs.extract i j).size + 1)
  | .arrayReplicate, [.nat n, v] => some (.array (Array.replicate n v), n + 1)
  | _, _ => none

/-- The language's terms. -/
inductive Term where
  /-- The value at position `position` of the environment. -/
  | position (position : ℕ)
  /-- A literal value (part of the program). -/
  | literal (value : MachineValue)
  /-- A primitive operation on the values of the terms. -/
  | primitive (operation : PrimitiveOperation) (args : List Term)
  /-- A constructor of the values of the terms. -/
  | constructor (tag : ℕ) (args : List Term)
  /-- Field `fieldIndex` of a constructor. -/
  | field (fieldIndex : ℕ) (term : Term)
  /-- On a constructor of tag `k`, alternative `k` with the fields in front of the
  environment. -/
  | case (term : Term) (alternatives : List Term)
  /-- The body with the value of `term` in front of the environment. -/
  | letIn (term body : Term)
  /-- A call of function `functionIndex` on the values of the terms. -/
  | call (functionIndex : ℕ) (args : List Term)
  /-- A closure of function `functionIndex` with the values of the terms as its first arguments. -/
  | closure (functionIndex : ℕ) (args : List Term)
  /-- A closure applied to the values of the terms. -/
  | applyClosure (term : Term) (args : List Term)
  deriving Inhabited

/-- A program: the function bodies; function `0` is the entry. -/
abbrev MachineProgram := Array Term

mutual

/-- A term's value and price in an environment, with `fuel` nested calls at most. -/
def evaluateTerm (program : MachineProgram) :
    ℕ → List MachineValue → Term → Option (MachineValue × ℕ)
  | _, env, .position i => env[i]?.map (·, 1)
  | _, _, .literal v => some (v, 1)
  | n, env, .primitive o ts => do
    let (vs, c) ← evaluateTerms program n env ts
    let (v, d) ← o.apply vs
    pure (v, c + d)
  | n, env, .constructor k ts => do
    let (vs, c) ← evaluateTerms program n env ts
    pure (.constructor k vs, c + vs.length + 1)
  | n, env, .field i t => do
    let (v, c) ← evaluateTerm program n env t
    match v with
    | .constructor _ fs => fs[i]?.map (·, c + 1)
    | _ => none
  | n, env, .case t alts => do
    let (v, c) ← evaluateTerm program n env t
    match v with
    | .constructor k fs =>
      match _h : alts[k]? with
      | some a => do
        let (w, d) ← evaluateTerm program n (fs ++ env) a
        pure (w, c + d + fs.length + 1)
      | none => none
    | _ => none
  | n, env, .letIn t b => do
    let (v, c) ← evaluateTerm program n env t
    let (w, d) ← evaluateTerm program n (v :: env) b
    pure (w, c + d + 1)
  | n, env, .call f ts => do
    let (vs, c) ← evaluateTerms program n env ts
    let (w, d) ← evaluateFunctionBody program n f vs
    pure (w, c + d + 1)
  | n, env, .closure f ts => do
    let (vs, c) ← evaluateTerms program n env ts
    pure (.closure f vs, c + vs.length + 1)
  | n, env, .applyClosure t ts => do
    let (g, c) ← evaluateTerm program n env t
    let (vs, d) ← evaluateTerms program n env ts
    match g with
    | .closure f us => do
      let (w, e) ← evaluateFunctionBody program n f (us ++ vs)
      pure (w, c + d + e + us.length + 1)
    | _ => none
termination_by n _ t => (n, sizeOf t)
decreasing_by
  all_goals
    (try have := List.sizeOf_lt_of_mem (List.mem_of_getElem? ‹_[_]? = some _›))
    decreasing_tactic

/-- The terms' values, in order, and their total price. -/
def evaluateTerms (program : MachineProgram) :
    ℕ → List MachineValue → List Term → Option (List MachineValue × ℕ)
  | _, _, [] => some ([], 0)
  | n, env, t :: ts => do
    let (v, c) ← evaluateTerm program n env t
    let (vs, d) ← evaluateTerms program n env ts
    pure (v :: vs, c + d)
termination_by n _ ts => (n, sizeOf ts)

/-- Function `f`'s body on the arguments `vs`, one call deeper. -/
def evaluateFunctionBody (program : MachineProgram) :
    ℕ → ℕ → List MachineValue → Option (MachineValue × ℕ)
  | 0, _, _ => none
  | n + 1, f, vs => match program[f]? with
    | some b => evaluateTerm program n vs b
    | none => none
termination_by n _ _ => (n, 0)

end

/-- **A run**: function `0` on the input `input`, with `fuel` nested calls at most below it. -/
def runMachineProgram (program : MachineProgram) (fuel : ℕ) (input : MachineValue) : Option
    (MachineValue × ℕ) :=
  evaluateFunctionBody program (fuel + 1) 0 [input]

/-! ## Size

A constructor's tag and a closure's function index count one with their node, whatever their
number, and so do a term's positions and function indices (`position`, `field`, `call`, `closure`).
That is sound because the machine reads them only by bounded lookups, never as data: a tag selects
one of a `case`'s alternatives, which the program lists, or is compared with a constant (a list's
`nil` and `cons` in `arrayOfList`, `MachineValue.toList?`); a function index is looked up in the
program (`P[f]?`); no primitive operation (`PrimitiveOperation.apply`) takes a tag or an index as
a number. -/

mutual

/-- A value's size: one per constructor, array and closure, and a natural number's limbs (a
literal counts in full; a tag or a function index counts with its node). -/
def MachineValue.size : MachineValue → ℕ
  | .nat n => limbCount n
  | .constructor _ fs => MachineValue.sizeList fs + 1
  | .array xs => MachineValue.sizeList xs.toList + 1
  | .closure _ us => MachineValue.sizeList us + 1

/-- The sizes of the values. -/
def MachineValue.sizeList : List MachineValue → ℕ
  | [] => 0
  | v :: vs => v.size + MachineValue.sizeList vs

end

mutual

/-- A term's size: one per node, literals by their size (a position, a tag or a function index
counts with its node). -/
def Term.size : Term → ℕ
  | .position _ => 1
  | .literal v => v.size + 1
  | .primitive _ ts | .constructor _ ts | .call _ ts | .closure _ ts => Term.sizeList ts + 1
  | .field _ t => t.size + 1
  | .case t alts => t.size + Term.sizeList alts + 1
  | .letIn t b => t.size + b.size + 1
  | .applyClosure t ts => t.size + Term.sizeList ts + 1

/-- The sizes of the terms. -/
def Term.sizeList : List Term → ℕ
  | [] => 0
  | t :: ts => t.size + Term.sizeList ts

end

/-- A program's size: the sizes of its bodies. -/
def MachineProgram.size (program : MachineProgram) : ℕ := (program.toList.map Term.size).sum

/-- **The output within a size bound and a budget**: `program`'s value on `input` if `program`'s
size is at most `sizeBound` (`MachineProgram.size`) and its run costs at most `budget`; `none`
otherwise. -/
def outputWithin (program : MachineProgram) (sizeBound budget : ℕ) (input : MachineValue) :
    Option MachineValue :=
  if MachineProgram.size program ≤ sizeBound then
    match runMachineProgram program budget input with
    | some (v, c) => if c ≤ budget then some v else none
    | none => none
  else none

/-! ## The encoding -/

/-- A machine encoding of `α`. -/
class MachineEncoding (α : Type) where
  /-- The value of `a`. -/
  encodeValue : α → MachineValue

export MachineEncoding (encodeValue)

instance : MachineEncoding UInt64 := ⟨fun x ↦ .nat x.toNat⟩
instance : MachineEncoding ℕ := ⟨.nat⟩
instance {n : ℕ} : MachineEncoding (Fin n) := ⟨fun i ↦ .nat i.val⟩
instance : MachineEncoding Bool := ⟨MachineValue.ofBool⟩
/-- A bit vector: its number. -/
instance {w : ℕ} : MachineEncoding (BitVec w) := ⟨fun v ↦ .nat v.toNat⟩
instance {α : Type} [MachineEncoding α] : MachineEncoding (List α) :=
  ⟨fun l ↦ .ofList (l.map encodeValue)⟩

instance {α β : Type} [MachineEncoding α] [MachineEncoding β] : MachineEncoding (α × β) :=
  ⟨fun p ↦ .constructor 0 [encodeValue p.1, encodeValue p.2]⟩

/-- An option: `none` the constructor of tag `0`, `some a` of tag `1`. -/
instance {α : Type} [MachineEncoding α] : MachineEncoding (Option α) where
  encodeValue | none => .constructor 0 [] | some a => .constructor 1 [encodeValue a]

instance {α : Type} [MachineEncoding α] {n : ℕ} : MachineEncoding (Vector α n) :=
  ⟨fun v ↦ .array (v.toArray.map encodeValue)⟩

/-- A function of a finite domain, as the array of its values. -/
def encodeFiniteFunction {α : Type} [MachineEncoding α] {n : ℕ} (f : Fin n → α) : MachineValue :=
  .array (Array.ofFn fun i ↦ encodeValue (f i))

/-- A function of a finite domain: the array of its values. -/
instance {α : Type} [MachineEncoding α] {n : ℕ} : MachineEncoding (Fin n → α) :=
  ⟨encodeFiniteFunction⟩

end

end LeanVM.Cost
