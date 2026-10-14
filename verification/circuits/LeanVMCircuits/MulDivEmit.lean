module

public import LeanVMCircuits.MulDivExport
public import Std.Data.HashMap

@[expose] public section

/-!
Rust for the multiplication classes, one Builder call per checked step.

`multiply64` and `multiply128` replay the multiplier's steps on input ports `a` and `b` from a generated table, one
entry per XOR or product. Each class function is its artifact's steps, the multiplier's replaced by a call of the
multiplier function on the lowered operands, its outputs bound to the call's result. Every product step is one
`c.and`, in step order, and the emitter refuses a product with a structurally zero operand, so the products and their
slots are exactly the artifact's.
-/

namespace LeanVMCircuits.MulDivEmit

open LeanVMCircuits Gates Flock Netlist

structure State where
  bindings : Std.HashMap ℕ String
  cache : Std.HashMap (String × String) String := {}
  /-- Each wire's name and Builder call, in order. -/
  lines : Array (String × String) := #[]
  /-- The names a later call or the result reads. -/
  used : Std.HashSet String := {}
  next : ℕ := 0
  products : ℕ := 0

abbrev M := StateT State (Except String)

def fresh (operation : String) : M String := do
  let s ← get
  let name := s!"w{s.next}"
  set { s with next := s.next + 1, lines := s.lines.push (name, operation) }
  return name

def use (name : String) : M String := do
  modify fun s => { s with used := s.used.insert name }
  return name

/-- The calls as lines: a product nothing reads is still made, for its slot. -/
def render (s : State) : List String :=
  s.lines.toList.map fun (name, operation) =>
    if s.used.contains name then s!"    let {name} = {operation};" else s!"    {operation};"

def bind (index : ℕ) (name : String) : M Unit := do
  let s ← get
  if s.bindings.contains index then throw s!"variable {index} bound twice"
  set { s with bindings := s.bindings.insert index name }

/-- An affine combination as wires: XOR with the zero is the other operand, and equal XORs are shared. -/
def emitAffine : Affine → M String
  | .zero => return "Wire::ZERO"
  | .one => return "Wire::ONE"
  | .var index => do
    match (← get).bindings[index]? with
    | some name => use name
    | none => throw s!"unbound or forward variable {index}"
  | .xor left right => do
    let l ← emitAffine left
    let r ← emitAffine right
    if l == "Wire::ZERO" then return r
    if r == "Wire::ZERO" then return l
    match (← get).cache[(l, r)]? with
    | some name => use name
    | none =>
      let name ← fresh s!"c.xor({l}, {r})"
      modify fun s => { s with cache := s.cache.insert (l, r) name }
      use name

def emitStep : Step → M Unit
  | .define output value => do bind output (← emitAffine value)
  | .product output left right => do
    let l ← emitAffine left
    let r ← emitAffine right
    if l == "Wire::ZERO" || r == "Wire::ZERO" then throw s!"product {output} has a structurally zero operand"
    let name ← fresh s!"c.and({l}, {r})"
    modify fun s => { s with products := s.products + 1 }
    bind output name

def emitSteps (steps : List Step) : M Unit := steps.forM emitStep

/-- The output wires, four per line. -/
def wireLines (names : List String) : List String :=
  (List.range ((names.length + 3) / 4)).map fun line =>
    "        " ++ String.intercalate ", " ((names.drop (4 * line)).take 4) ++ ","

/-- The multiplier's steps on ports `a` and `b`, from variable 128. `MulDivExport.multiplier_call` shows a class's
multiplier steps are these, renamed by the call. -/
def multiplierSteps (n : ℕ) : List Step := stepsFrom MulDivExport.canon 128 0 (Multiply.layout n).gates

/-- The multiplier's output variables from its first local variable `base`. -/
def multiplierOutputs (n base : ℕ) : List ℕ := (List.range n).map fun p => base + Multiply.rippleBase n 64 + 5 * p + 4

/-! A step table: operand 0 is the zero, 1 the one, `2 + j` input `j`, `130 + k` the wire of entry `k`. -/

structure Table where
  operands : Std.HashMap ℕ ℕ
  cache : Std.HashMap (ℕ × ℕ) ℕ := {}
  entries : Array (ℕ × ℕ × ℕ) := #[]
  products : ℕ := 0

abbrev T := StateT Table (Except String)

def push (kind x y : ℕ) : T ℕ := do
  let t ← get
  set { t with entries := t.entries.push (kind, x, y) }
  return 130 + t.entries.size

def tableAffine : Affine → T ℕ
  | .zero => return 0
  | .one => return 1
  | .var index => do
    match (← get).operands[index]? with
    | some operand => return operand
    | none => throw s!"unbound or forward variable {index}"
  | .xor left right => do
    let l ← tableAffine left
    let r ← tableAffine right
    if l == 0 then return r
    if r == 0 then return l
    match (← get).cache[(l, r)]? with
    | some operand => return operand
    | none =>
      let operand ← push 0 l r
      modify fun t => { t with cache := t.cache.insert (l, r) operand }
      return operand

def tableStep : Step → T Unit
  | .define output value => do
    let v ← tableAffine value
    modify fun t => { t with operands := t.operands.insert output v }
  | .product output left right => do
    let l ← tableAffine left
    let r ← tableAffine right
    if l == 0 || r == 0 then throw s!"product {output} has a structurally zero operand"
    let operand ← push 1 l r
    modify fun t => { t with operands := t.operands.insert output operand, products := t.products + 1 }

/-- The multiplier as a step table `MULTIPLY{n}`, its outputs `MULTIPLY{n}_OUT`, and the function replaying them. -/
def emitMultiplier (n : ℕ) (products : ℕ) : Except String String := do
  let operands : Std.HashMap ℕ ℕ := (List.range 128).foldl (fun m j => m.insert j (2 + j)) {}
  let (outs, t) ← (do
      (multiplierSteps n).forM tableStep
      (multiplierOutputs n 128).mapM fun v => tableAffine (.var v)).run { operands }
  unless t.products == products do throw s!"multiply{n}: {t.products} products, expected {products}"
  let entries := t.entries.toList.map fun (k, x, y) => s!"[{k}, {x}, {y}]"
  let rows := (List.range ((entries.length + 7) / 8)).map fun r =>
    "    " ++ String.intercalate ", " ((entries.drop (8 * r)).take 8) ++ ","
  let outRows := (List.range ((outs.length + 15) / 16)).map fun r =>
    "    " ++ String.intercalate ", " (((outs.drop (16 * r)).take 16).map toString) ++ ","
  let lines := [
    s!"/// The checked {n}-bit CSA multiplier's steps (`LeanVMCircuits.Multiply`), products in plan order.",
    "#[rustfmt::skip]",
    s!"static MULTIPLY{n}: [[u32; 3]; {entries.length}] = [",
    ] ++ rows ++ ["];", "",
    s!"/// The operands of the low {n} bits of the product.",
    "#[rustfmt::skip]",
    s!"static MULTIPLY{n}_OUT: [u32; {n}] = ["] ++ outRows ++ ["];", "",
    s!"/// The low {n} bits of `a b`: the checked multiplier's steps replayed on `a` and `b`.",
    s!"pub fn multiply{n}(c: &mut Builder, a: &[Wire; 64], b: &[Wire; 64]) -> [Wire; {n}] \{",
    s!"    let wires = replay(c, a, b, &MULTIPLY{n});",
    s!"    MULTIPLY{n}_OUT.map(|operand| wires[operand as usize])",
    "}"]
  return String.intercalate "\n" lines ++ "\n"

/-- The replay of a step table, the same for both multipliers. -/
def replayFn : String := "
/// The wires of a generated step table on inputs `a` and `b`, by operand: the zero, the one, `a`, `b`, then one per
/// step. A step `[0, x, y]` is the free XOR of its operands, `[1, x, y]` their product at the next slot.
fn replay(c: &mut Builder, a: &[Wire; 64], b: &[Wire; 64], steps: &[[u32; 3]]) -> Vec<Wire> {
    let mut wires = Vec::with_capacity(130 + steps.len());
    wires.extend([Wire::ZERO, Wire::ONE]);
    wires.extend_from_slice(a);
    wires.extend_from_slice(b);
    for &[kind, x, y] in steps {
        let (x, y) = (wires[x as usize], wires[y as usize]);
        let wire = if kind == 0 { c.xor(x, y) } else { c.and(x, y) };
        wires.push(wire);
    }
    wires
}
"

/-- A class: its steps before the multiplier, the call on the lowered operands `ainp`, then the steps after. -/
structure Class where
  name : String
  doc : List String
  parameters : String
  result : String
  bindings : List (ℕ × String)
  pre : List Step
  n : ℕ
  mid : ℕ
  ainp : ℕ → Affine
  post : List Step
  outputs : List Affine
  /-- Formats the output wires as the function's result. -/
  ret : List String → List String
  products : ℕ

def emitClass (k : Class) : Except String String := do
  let body : M (List String) := do
    emitSteps k.pre
    let a ← (List.range 64).mapM fun j => emitAffine (k.ainp j)
    let b ← (List.range 64).mapM fun j => emitAffine (k.ainp (64 + j))
    let m ← fresh s!"multiply{k.n}(c, &[{String.intercalate ", " a}], &[{String.intercalate ", " b}])"
    let m ← use m
    for (v, p) in (multiplierOutputs k.n k.mid).zipIdx do bind v s!"{m}[{p}]"
    emitSteps k.post
    k.outputs.mapM emitAffine
  let (outs, s) ← body.run { bindings := Std.HashMap.ofList k.bindings }
  unless s.products == k.products do throw s!"{k.name}: {s.products} glue products, expected {k.products}"
  let header := k.doc.map (fun l => "/// " ++ l) ++
    [s!"pub fn {k.name}(c: &mut Builder{k.parameters}) -> {k.result} \{"]
  return String.intercalate "\n" (header ++ render s ++ k.ret outs ++ ["}"]) ++ "\n"

def portBindings (ports : List (String × ℕ)) : List (ℕ × String) :=
  (ports.foldl (fun (acc, base) (name, width) =>
    (acc ++ (List.range width).map (fun i => (base + i, s!"{name}[{i}]")), base + width)) ([], 0)).1

def word64 (outs : List String) : List String := ["    ["] ++ wireLines outs ++ ["    ]"]

def mul : Class where
  name := "mul64"
  doc := ["The checked low multiplication (`LeanVMCircuits.Mul`): `v1 v2` modulo `2^64`, its low 32 bits",
    "sign-extended when `flags[0]` is set."]
  parameters := ", v1: &[Wire; 64], v2: &[Wire; 64], flags: &[Wire; 1]"
  result := "[Wire; 64]"
  bindings := portBindings [("v1", 64), ("v2", 64), ("flags", 1)]
  pre := []
  n := 64
  mid := MulDivExport.Mul.start
  ainp := MulDivExport.Mul.ainp
  post := MulDivExport.Mul.postSteps
  outputs := MulDivExport.Mul.outputs
  ret := word64
  products := 32

def mulh : Class where
  name := "mulh64"
  doc := ["The checked high multiplication (`LeanVMCircuits.Mulh`): the high word of `v1 v2`, `v1` signed when",
    "`flags[0]` is set and `v2` when `flags[1]` is."]
  parameters := ", v1: &[Wire; 64], v2: &[Wire; 64], flags: &[Wire; 2]"
  result := "[Wire; 64]"
  bindings := portBindings [("v1", 64), ("v2", 64), ("flags", 2)]
  pre := []
  n := 128
  mid := MulDivExport.Mulh.start
  ainp := MulDivExport.Mulh.ainp
  post := MulDivExport.Mulh.postSteps
  outputs := MulDivExport.Mulh.outputs
  ret := word64
  products := 2 * (1 + 64 + 64)

def div : Class where
  name := "div64"
  doc := ["The checked division (`LeanVMCircuits.Div`): the quotient or the remainder as `flags` select (signed,",
    "remainder, word), and `bad`, set exactly when the divisor is nonzero and the hints `q`, `r` are not the",
    "magnitudes' quotient and remainder."]
  parameters := ", v1: &[Wire; 64], v2: &[Wire; 64], flags: &[Wire; 3], q: &[Wire; 64], r: &[Wire; 64]"
  result := "([Wire; 64], Wire)"
  bindings := portBindings [("v1", 64), ("v2", 64), ("flags", 3), ("q", 64), ("r", 64)]
  pre := MulDivExport.Div.preSteps
  n := 128
  mid := MulDivExport.Div.mid
  ainp := MulDivExport.Div.ainp
  post := MulDivExport.Div.postSteps
  outputs := MulDivExport.Div.outputs
  ret := fun outs => ["    ("] ++ word64 (outs.take 64) ++ ["    ,", s!"    {outs.getD 64 "Wire::ZERO"},", "    )"]
  products := 196 + (63 + 64 + 63 + 64) + 67 + 352

/-- The multipliers, then the classes. -/
def emit : Except String String := do
  let m64 ← emitMultiplier 64 2143
  let m128 ← emitMultiplier 128 4287
  let mul ← emitClass mul
  let mulh ← emitClass mulh
  let div ← emitClass div
  return m64 ++ "\n" ++ m128 ++ replayFn ++ "\n" ++ mul ++ "\n" ++ mulh ++ "\n" ++ div

end LeanVMCircuits.MulDivEmit
