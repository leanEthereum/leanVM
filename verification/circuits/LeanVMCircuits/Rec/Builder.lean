module

public import LeanVMCircuits.Rec.Merkle
public import Std.Data.HashMap

@[expose] public section

/-!
The recursion circuit's builder, `rec::circuit::Builder`, as a Lean program over wire numbers.

Every method allocates wires, appends rows, holds wires equal and adds public rows exactly as the Rust method does,
in the same order, so its wire numbers are the Rust builder's. The rows never depend on values, so the model
carries none: a circuit is its rows, the pairs of wires held equal, and the public rows' sources. `CheckRec`
replays a Rust builder's calls through these methods and checks the circuit it builds is the Rust one;
`LeanVMCircuits.Rec.Contracts` proves what each method's rows make its output in every satisfying assignment.
-/

namespace LeanVMCircuits.Rec.Model

/-- A wire's kind: the key of constant deduplication besides the value. -/
inductive Kind where
  | k
  | e
  | d
  deriving DecidableEq, Repr, Hashable

/-- A wire's value as four 64-bit words. -/
abbrev Limbs := List ℕ

/-- Where a public row's value comes from. -/
inductive PubSource where
  | const (v : Limbs)
  | statement (i : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- The tables, in `Table::ALL` order. -/
inductive Table where
  | emul
  | exk
  | hash
  | split
  | cast
  | pub
  deriving DecidableEq, Repr

def Table.all : List Table := [.emul, .exk, .hash, .split, .cast, .pub]

def Table.nSlots : Table → ℕ
  | .emul => 4
  | .exk => 4
  | .hash => 16
  | .split => 65
  | .cast => 8
  | .pub => 1

/-- `row_key`'s table tag. -/
def Table.tag : Table → ℕ
  | .emul => 0
  | .exk => 1
  | .hash => 2
  | .split => 3
  | .cast => 4
  | .pub => 5

/-- `Units`: the wires of the constants zero and one, once made. -/
structure Units where
  eZero : Option ℕ := none
  eOne : Option ℕ := none
  kZero : Option ℕ := none
  kOne : Option ℕ := none

/-- The builder's state. -/
structure State where
  /-- The next wire's number. -/
  next : ℕ := 0
  /-- Every pair of wires held equal, in order. -/
  unions : Array (ℕ × ℕ) := #[]
  /-- Each table's rows, a wire per slot. -/
  emul : Array (List ℕ) := #[]
  exk : Array (List ℕ) := #[]
  hash : Array (List ℕ) := #[]
  split : Array (List ℕ) := #[]
  cast : Array (List ℕ) := #[]
  /-- The public rows: each one's wire and where its value comes from. -/
  pub : Array (ℕ × PubSource) := #[]
  consts : Std.HashMap (Kind × Limbs) ℕ := {}
  units : Units := {}
  arith : Std.HashMap (ℕ × ℕ × ℕ × ℕ) ℕ := {}
  statement : ℕ := 0

abbrev M := StateM State

/-- `fn wire`: a fresh wire. -/
def wire : M ℕ := modifyGet fun s => (s.next, { s with next := s.next + 1 })

/-- `fn union`. -/
def union (a b : ℕ) : M Unit := modify fun s => { s with unions := s.unions.push (a, b) }

/-- `fn row` for an owned table. -/
def row (t : Table) (slots : List ℕ) : M Unit := modify fun s =>
  match t with
  | .emul => { s with emul := s.emul.push slots }
  | .exk => { s with exk := s.exk.push slots }
  | .hash => { s with hash := s.hash.push slots }
  | .split => { s with split := s.split.push slots }
  | .cast => { s with cast := s.cast.push slots }
  | .pub => s

/-- `fn row` for the public table, with the row's source. -/
def pubRow (w : ℕ) (src : PubSource) : M Unit := modify fun s => { s with pub := s.pub.push (w, src) }

/-- `constant`'s units after making the constant `v` of kind `k` as wire `w`. -/
def unitAfter (u : Units) (kind : Kind) (v : Limbs) (w : ℕ) : Units :=
  match kind, v with
  | .e, [0, 0, 0, 0] => { u with eZero := some w }
  | .e, [1, 0, 0, 0] => { u with eOne := some w }
  | .k, [0, 0, 0, 0] => { u with kZero := some w }
  | .k, [1, 0, 0, 0] => { u with kOne := some w }
  | _, _ => u

/-- `fn constant`: the wire of a constant, made with its public row the first time. -/
def constant (kind : Kind) (v : Limbs) : M ℕ := do
  match (← get).consts[(kind, v)]? with
  | some w => pure w
  | none =>
    let w ← wire
    pubRow w (.const v)
    modify fun s => { s with consts := s.consts.insert (kind, v) w, units := unitAfter s.units kind v w }
    pure w

def eConst (c0 c1 c2 : ℕ) : M ℕ := constant .e [c0, c1, c2, 0]
def kConst (v : ℕ) : M ℕ := constant .k [v, 0, 0, 0]
def dConst (v : Limbs) : M ℕ := constant .d v

def zero : M ℕ := do
  match (← get).units.eZero with
  | some w => pure w
  | none => eConst 0 0 0

def one : M ℕ := do
  match (← get).units.eOne with
  | some w => pure w
  | none => eConst 1 0 0

def kZero : M ℕ := do
  match (← get).units.kZero with
  | some w => pure w
  | none => kConst 0

/-- `fn expose`: a statement word's public row. -/
def expose (w : ℕ) : M ℕ := do
  let i := (← get).statement
  modify fun s => { s with statement := s.statement + 1 }
  pubRow w (.statement i)
  pure i

def eqConstE (a c0 c1 c2 : ℕ) : M Unit := do
  let c ← eConst c0 c1 c2
  union a c

def eqConstK (a v : ℕ) : M Unit := do
  let c ← kConst v
  union a c

/-! Arithmetic. -/

/-- `emul_key`: the factors in order, or for `1·x + d` the terms. -/
def emulKey (u : Units) (a b d : ℕ) : ℕ × ℕ × ℕ :=
  if u.eOne = some a ∨ u.eOne = some b then
    let x := if u.eOne = some a then b else a
    ((u.eOne.getD 0), min x d, max x d)
  else (min a b, max a b, d)

/-- `fn emul`: `a·b + d`, an earlier row's output for the same inputs. -/
def emul (a b d : ℕ) : M ℕ := do
  let (k0, k1, k2) := emulKey (← get).units a b d
  let key := (Table.emul.tag, k0, k1, k2)
  match (← get).arith[key]? with
  | some c => pure c
  | none =>
    let c ← wire
    row .emul [a, b, d, c]
    modify fun s => { s with arith := s.arith.insert key c }
    pure c

def add (a d : ℕ) : M ℕ := do
  let z := (← get).units.eZero
  if z = some d then pure a
  else if z = some a then pure d
  else
    let o ← one
    emul a o d

def mulAdd (a b d : ℕ) : M ℕ := do
  let u := (← get).units
  if u.eZero = some a ∨ u.eZero = some b then pure d
  else if u.eOne = some b then add a d
  else if u.eOne = some a then add b d
  else emul a b d

def mul (a b : ℕ) : M ℕ := do
  let z ← zero
  mulAdd a b z

def square (a : ℕ) : M ℕ := mul a a

def mulKAdd (a k d : ℕ) : M ℕ := do
  let u := (← get).units
  if u.eZero = some a ∨ u.kZero = some k then pure d
  else if u.kOne = some k then add a d
  else
    let key := (Table.exk.tag, a, k, d)
    match (← get).arith[key]? with
    | some c => pure c
    | none =>
      let c ← wire
      row .exk [a, k, d, c]
      modify fun s => { s with arith := s.arith.insert key c }
      pure c

def mulConstAdd (a c0 c1 c2 d : ℕ) : M ℕ := do
  if c1 = 0 ∧ c2 = 0 then
    let k ← kConst c0
    mulKAdd a k d
  else
    let c ← eConst c0 c1 c2
    mulAdd a c d

def inv (a : ℕ) : M ℕ := do
  let i ← wire
  let p ← mul a i
  eqConstE p 1 0 0
  pure i

def sum (terms : List ℕ) : M ℕ := do
  let z ← zero
  terms.foldlM add z

/-! Bits and views. -/

def splitRow (w : ℕ) (bits : List ℕ) : M Unit := row .split (w :: bits)

def split (w : ℕ) : M (List ℕ) := do
  let bits ← (List.range 64).mapM fun _ => wire
  splitRow w bits
  pure bits

def pack (bits : List ℕ) : M ℕ := do
  let z ← kZero
  let all := bits ++ List.replicate (64 - bits.length) z
  let w ← wire
  splitRow w all
  pure w

/-- `fn cast_row`: the given slots' wires, fresh wires in the others, in slot order. -/
def castRow (given : List (ℕ × ℕ)) : M (List ℕ) := do
  let wires ← (List.range 8).mapM fun s =>
    match given.find? (·.1 = s) with
    | some (_, w) => pure w
    | none => wire
  row .cast wires
  pure wires

def eToK (e : ℕ) : M (List ℕ) := do
  let w ← castRow [(1, e)]
  pure (w.drop 4 |>.take 3)

def kToE (k0 k1 k2 : ℕ) : M ℕ := do
  let w ← castRow [(4, k0), (5, k1), (6, k2)]
  pure (w.getD 1 0)

def kToE1 (k : ℕ) : M ℕ := do
  let z ← kZero
  kToE k z z

def dToK (d : ℕ) : M (List ℕ) := do
  let w ← castRow [(0, d)]
  pure (w.drop 4)

def dToEAndK (d : ℕ) : M (ℕ × ℕ) := do
  let w ← castRow [(0, d)]
  pure (w.getD 1 0, w.getD 7 0)

def halvesToD (lo hi : ℕ) : M ℕ := do
  let w ← castRow [(2, lo), (3, hi)]
  pure (w.getD 0 0)

/-! Hashing. -/

/-- `rv::Hash::FINAL`. -/
def final : ℕ := 0xFFFFFFFF

/-- `PARAM_IV` as four words, from RFC 7693's parameter block. -/
def paramIVLimbs : Limbs := List.ofFn fun k : Fin 4 => (digest paramIV k).toNat

/-- `fn hash_row`: the head's slots, the output and challenge, the message words. -/
def hashRow (h tf mux bit x ds : ℕ) (words : List ℕ) : M ℕ := do
  let o ← wire
  let ch ← wire
  row .hash ([h, tf, mux, bit, x, ds, o, ch] ++ words)
  pure o

def singleBlock (mux bit x ds : ℕ) : M ℕ := do
  let h ← dConst paramIVLimbs
  let tf ← dConst [64, final, 0, 0]
  let words ← (List.range 8).mapM fun _ => wire
  hashRow h tf mux bit x ds words

def compress (acc x ds : ℕ) : M ℕ := do
  let bit ← kZero
  singleBlock acc bit x ds

def node (acc bit : ℕ) : M ℕ := do
  let x ← wire
  let ds ← wire
  singleBlock acc bit x ds

def parent (left right : ℕ) : M ℕ := do
  let (x, ds) ← dToEAndK right
  let bit ← kZero
  singleBlock left bit x ds

def leafBlock (h : ℕ) (m : List ℕ) (t : ℕ) (last : Bool) : M ℕ := do
  let tf ← dConst [t, if last then final else 0, 0, 0]
  let mux ← wire
  let bit ← wire
  let x ← wire
  let ds ← wire
  hashRow h tf mux bit x ds m

/-- `chain`'s blocks from `j` on, of `n`, the message `words` padded with `z`, `bytes` long. -/
def chainBlocks (words : List ℕ) (z n bytes : ℕ) : List ℕ → ℕ → M ℕ
  | [], h => pure h
  | j :: js, h => do
    let m := (List.range 8).map fun i => words.getD (8 * j + i) z
    let h ← leafBlock h m (min (64 * (j + 1)) bytes) (j + 1 = n)
    chainBlocks words z n bytes js h

def chain (words : List ℕ) : M ℕ := do
  let nBlocks := max 1 ((words.length + 7) / 8)
  let z ← kZero
  let h ← dConst paramIVLimbs
  chainBlocks words z nBlocks (8 * words.length) (List.range nBlocks) h

/-! A call of the builder from outside it, as `CheckRec` reads it. -/

inductive Call where
  | freeE | freeK | freeD
  | eqE (a b : ℕ) | eqK (a b : ℕ) | eqD (a b : ℕ)
  | eqConstE (a c0 c1 c2 : ℕ) | eqConstK (a v : ℕ)
  | eConst (c0 c1 c2 : ℕ) | kConst (v : ℕ) | dConst (v : Limbs)
  | zero | one | exposeE (w : ℕ)
  | mulAdd (a b d : ℕ) | mul (a b : ℕ) | add (a d : ℕ) | square (a : ℕ) | mulKAdd (a k d : ℕ)
  | mulConstAdd (a c0 c1 c2 d : ℕ) | inv (a : ℕ) | sum (terms : List ℕ)
  | split (w : ℕ) | pack (bits : List ℕ) | eToK (e : ℕ) | kToE (k0 k1 k2 : ℕ) | kToE1 (k : ℕ) | dToK (d : ℕ)
  | dToEAndK (d : ℕ) | halvesToD (lo hi : ℕ)
  | compress (acc x ds : ℕ) | node (acc bit : ℕ) | parent (l r : ℕ) | leafBlock (h : ℕ) (m : List ℕ) (t : ℕ) (last : Bool)
  | chain (words : List ℕ)
  deriving Repr

/-- Run one call, returning its output wires (`expose_e`'s statement index). -/
def Call.exec : Call → M (List ℕ)
  | .freeE | .freeK | .freeD => do return [← wire]
  | .eqE a b | .eqK a b | .eqD a b => do Model.union a b; return []
  | .eqConstE a c0 c1 c2 => do Model.eqConstE a c0 c1 c2; return []
  | .eqConstK a v => do Model.eqConstK a v; return []
  | .eConst c0 c1 c2 => do return [← Model.eConst c0 c1 c2]
  | .kConst v => do return [← Model.kConst v]
  | .dConst v => do return [← Model.dConst v]
  | .zero => do return [← Model.zero]
  | .one => do return [← Model.one]
  | .exposeE w => do return [← Model.expose w]
  | .mulAdd a b d => do return [← Model.mulAdd a b d]
  | .mul a b => do return [← Model.mul a b]
  | .add a d => do return [← Model.add a d]
  | .square a => do return [← Model.square a]
  | .mulKAdd a k d => do return [← Model.mulKAdd a k d]
  | .mulConstAdd a c0 c1 c2 d => do return [← Model.mulConstAdd a c0 c1 c2 d]
  | .inv a => do return [← Model.inv a]
  | .sum terms => do return [← Model.sum terms]
  | .split w => Model.split w
  | .pack bits => do return [← Model.pack bits]
  | .eToK e => Model.eToK e
  | .kToE k0 k1 k2 => do return [← Model.kToE k0 k1 k2]
  | .kToE1 k => do return [← Model.kToE1 k]
  | .dToK d => Model.dToK d
  | .dToEAndK d => do let (e, k) ← Model.dToEAndK d; return [e, k]
  | .halvesToD lo hi => do return [← Model.halvesToD lo hi]
  | .compress acc x ds => do return [← Model.compress acc x ds]
  | .node acc bit => do return [← Model.node acc bit]
  | .parent l r => do return [← Model.parent l r]
  | .leafBlock h m t last => do return [← Model.leafBlock h m t last]
  | .chain words => do return [← Model.chain words]

/-- Run one call. -/
def Call.run (c : Call) : M Unit := discard c.exec

/-- The wires a call names. -/
def Call.args : Call → List ℕ
  | .freeE | .freeK | .freeD | .eConst .. | .kConst _ | .dConst _ | .zero | .one => []
  | .eqE a b | .eqK a b | .eqD a b => [a, b]
  | .eqConstE a .. | .eqConstK a _ => [a]
  | .exposeE w => [w]
  | .mulAdd a b d => [a, b, d]
  | .mul a b => [a, b]
  | .add a d => [a, d]
  | .square a => [a]
  | .mulKAdd a k d => [a, k, d]
  | .mulConstAdd a _ _ _ d => [a, d]
  | .inv a => [a]
  | .sum terms => terms
  | .split w => [w]
  | .pack bits => bits
  | .eToK e => [e]
  | .kToE k0 k1 k2 => [k0, k1, k2]
  | .kToE1 k => [k]
  | .dToK d => [d]
  | .dToEAndK d => [d]
  | .halvesToD lo hi => [lo, hi]
  | .compress acc x ds => [acc, x, ds]
  | .node acc bit => [acc, bit]
  | .parent l r => [l, r]
  | .leafBlock h m _ _ => h :: m
  | .chain words => words

/-- The sizes a call's Rust method asserts or its types bound: a block of eight words, counters and lengths in 64
bits, at most 64 bits packed. -/
def Call.ok : Call → Bool
  | .leafBlock _ m t _ => m.length = 8 ∧ t < 2 ^ 64
  | .chain words => 8 * words.length < 2 ^ 64
  | .pack bits => bits.length ≤ 64
  | _ => true

end LeanVMCircuits.Rec.Model
