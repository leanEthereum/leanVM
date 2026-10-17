module

public import Clean.Circuit
public import Clean.Circuit.Subcircuit

/-!
Shared helpers for circuits over GF(2), Clean's field `F 2`: linear forms as sets of signals,
32-bit words of linear forms, rows emitted as Clean assertions, chunking of operation lists and
array-backed witness generation.

Signal `0` is the constant one and Clean variable `v` is signal `v + 1`.
-/

@[expose] public section

namespace Gf2

abbrev F := _root_.F 2
abbrev E := Expression F

/-- A linear form over GF(2): strictly increasing signals, signal `0` the constant one. -/
abbrev Lin := Array ℕ

/-- Sum of two forms: the symmetric difference of their signal sets. -/
def Lin.add (a b : Lin) : Lin := Id.run do
  let mut out : Lin := Array.emptyWithCapacity (a.size + b.size)
  let mut i := 0
  let mut j := 0
  while i < a.size && j < b.size do
    let x := a[i]!
    let y := b[j]!
    if x < y then
      out := out.push x
      i := i + 1
    else if y < x then
      out := out.push y
      j := j + 1
    else
      i := i + 1
      j := j + 1
  return out ++ a.extract i a.size ++ b.extract j b.size

def signalE (s : ℕ) : E := if s = 0 then .const 1 else .var ⟨s - 1⟩

/-- The form as a flat Clean sum of variables. -/
def Lin.toE (l : Lin) : E :=
  if l.isEmpty then .const 0 else (l.extract 1 l.size).foldl (fun e s => e + signalE s) (signalE l[0]!)

/-- A row `A · B = C`, each side a linear form. -/
structure Row where
  a : Lin
  b : Lin
  c : Lin

/-- The row as the Clean assertion `A · B + C = 0` (or `C = 0` when `A` or `B` is empty). -/
def Row.toE (r : Row) : E :=
  if r.a.isEmpty || r.b.isEmpty then r.c.toE else r.a.toE * r.b.toE + r.c.toE

/-- A 32-bit word, bit `i` (LSB first) a linear form. -/
abbrev Word := Array Lin

def Word.xor (x y : Word) : Word := x.zipWith Lin.add y

/-- Rotation right by `r`: bit `i` of the result is bit `i + r mod 32` of `x`. -/
def Word.rotr (x : Word) (r : ℕ) : Word := Array.ofFn (n := 32) fun i => x[(i.val + r) % 32]!

def Word.const (c : UInt32) : Word :=
  Array.ofFn (n := 32) fun i => if (c >>> i.val.toUInt32) &&& 1 = 1 then #[0] else #[]

/-- The word whose bit `i` is signal `base + i`. -/
def Word.signals (base : ℕ) : Word := Array.ofFn (n := 32) fun i => #[base + i.val]

def bitF (x : UInt32) (i : ℕ) : F := if (x >>> i.toUInt32) &&& 1 = 1 then 1 else 0

/-- The 32 bits of `x`, LSB first. -/
def pushWord (acc : Array F) (x : UInt32) : Array F :=
  (List.range 32).foldl (fun acc i => acc.push (bitF x i)) acc

/-- Word `w` of the 32-bit words stored LSB first from variable `base`. -/
def readWord (get : ℕ → F) (base w : ℕ) : UInt32 :=
  (List.range 32).foldl (fun x i => if get (base + 32 * w + i) = 1 then x ||| (1 <<< i.toUInt32) else x) 0

def asserts (es : List E) : Circuit F Unit := fun _ => ((), es.map .assert)

/--
Wraps a circuit's operations into a single subcircuit with vacuous specs. Clean's list
functions on operations recurse over list length, so this keeps every list short.
-/
def chunk {α : Type} (c : Circuit F α) : Circuit F α := fun offset =>
  let (a, ops) := c offset
  (a, [.subcircuit (n := offset) {
    ops := .nested ("chunk", Operations.toNested ops)
    Assumptions := fun _ => False
    Spec := fun _ => True
    ProverAssumptions := fun _ => False
    ProverSpec := fun _ => True
    localLength := Operations.localLength ops
    soundness := fun _ h => h.elim
    completeness := fun _ _ => ⟨fun h => h.elim, trivial⟩
    localLength_eq := by rw [Operations.toNested_toFlat, FlatOperation.localLength_toFlat]
  }])

partial def foldNested {σ : Type} [Inhabited σ] (f : σ → FlatOperation F → σ) (s : σ) :
    NestedOperations F → σ
  | .single op => f s op
  | .nested (_, l) => l.foldl (foldNested f) s

/-- Left fold over the flattened operations, without materializing them. -/
def foldOps {σ : Type} [Inhabited σ] (f : σ → FlatOperation F → σ) (s : σ)
    (ops : List (Operation F)) : σ :=
  ops.foldl (fun s op =>
    match op with
    | .witness m c => f s (.witness m c)
    | .assert e => f s (.assert e)
    | .lookup l => f s (.lookup l)
    | .interact i => f s (.interact i)
    | .subcircuit sc => foldNested f s sc.ops) s

def arrayEnv (hint : ProverHint F) (w : Array F) : ProverEnvironment F where
  get i := w[i]?.getD 0
  data _ _ := #[]
  hint

/--
Array-backed witness generation, the same fold as Clean's `FlatOperation.dynamicWitnesses`
(each witness operation evaluates its `WitgenIR` against all witnesses so far).
-/
def witgen (hint : ProverHint F) (ops : List (Operation F)) : Array F :=
  foldOps (fun acc op =>
    match op with
    | .witness _ code => acc ++ (code.eval (arrayEnv hint acc)).toArray
    | .assert _ | .lookup _ | .interact _ => acc) #[] ops

/-- Number of asserts that do not evaluate to zero (lookups and interactions count as failures). -/
def countViolations (ops : List (Operation F)) (w : Array F) : ℕ :=
  let env := (arrayEnv default w).toEnvironment
  foldOps (fun n op =>
    match op with
    | .assert e => if env e = 0 then n else n + 1
    | .lookup _ | .interact _ => n + 1
    | .witness _ _ => n) 0 ops

end Gf2
