module

public import Gf2.Basic

/-!
Native exporter for the GF(2) block R1CS `CLB1` and the batch witness `CLW2` (little-endian).

Every Clean assertion becomes exactly one row `(L1) · (L2) = L3` over GF(2): the expression is
normalized to `L1 * L2 + L3` or to `L3` (exported with empty `L1`, `L2`), coefficients reduced
mod 2 so duplicate signals cancel, each side a strictly increasing signal list. Anything of
higher degree, lookups and interactions are errors. Signal 0 is the constant one and Clean
variable `v` is signal `v + 1`.
-/

@[expose] public section

namespace Gf2.R1CS

/-- Sorts and cancels signals in pairs (coefficients mod 2). -/
def finalize (l : Array ℕ) : Lin := Id.run do
  let mut out : Lin := #[]
  for s in l.qsort (· < ·) do
    out := if out.back? == some s then out.pop else out.push s
  return out

/-- Normal form of an expression of degree at most two: `lin l` is `l`, `quad a b c` is `a * b + c`. -/
inductive NF where
  | lin (l : Array ℕ)
  | quad (a b c : Lin)

/-- The constant a finalized form stands for, if any. -/
def constOf? (l : Lin) : Option Bool :=
  if l.isEmpty then some false else if l == #[0] then some true else none

def normalize : E → Except String NF
  | .var v => pure (.lin #[v.index + 1])
  | .const c => pure (.lin (if c = 0 then #[] else #[0]))
  | .add x y => do
    match ← normalize x, ← normalize y with
    | .lin a, .lin b => pure (.lin (a ++ b))
    | .quad a b c, .lin d | .lin d, .quad a b c => pure (.quad a b (finalize (c ++ d)))
    | .quad .., .quad .. => throw "sum of two products"
  | .mul x y => do
    match ← normalize x, ← normalize y with
    | .lin a, .lin b =>
      let (a, b) := (finalize a, finalize b)
      match constOf? a, constOf? b with
      | some false, _ | _, some false => pure (.lin #[])
      | some true, _ => pure (.lin b)
      | none, some true => pure (.lin a)
      | none, none => pure (.quad a b #[])
    | .lin a, .quad p q r | .quad p q r, .lin a =>
      match constOf? (finalize a) with
      | some false => pure (.lin #[])
      | some true => pure (.quad p q r)
      | none => throw "product of degree above 2"
    | .quad .., .quad .. => throw "product of degree above 2"

def toRow (e : E) : Except String Row := do
  match ← normalize e with
  | .lin l => pure { a := #[], b := #[], c := finalize l }
  | .quad a b c =>
    if a.isEmpty || b.isEmpty then pure { a := #[], b := #[], c } else pure { a, b, c }

def pushU32 (b : ByteArray) (x : ℕ) : ByteArray :=
  let x := x.toUInt32
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

def pushLin (b : ByteArray) (l : Lin) : ByteArray := l.foldl pushU32 (pushU32 b l.size)

structure Stats where
  signals : ℕ
  constraints : ℕ
  nnzA : ℕ
  nnzB : ℕ
  nnzC : ℕ
  deriving Repr, DecidableEq

structure Export where
  body : ByteArray
  stats : Stats

/-- The `CLB1` bytes of `ops` (built at offset 0, no inputs) with `nPublic` public signals. -/
def toCLB1 (nPublic : ℕ) (ops : List (Operation F)) : Except String Export := do
  let signals := 1 + Operations.localLength ops
  unless signals < 2 ^ 32 do throw s!"{signals} signals do not fit in u32"
  unless nPublic < signals do throw s!"{nPublic} public signals but {signals} signals"
  let init : Except String Export :=
    pure { body := .empty, stats := { signals, constraints := 0, nnzA := 0, nnzB := 0, nnzC := 0 } }
  let st ← foldOps (fun (st : Except String Export) op => do
    let st ← st
    match op with
    | .witness _ _ => pure st
    | .assert e =>
      let r ← (toRow e).mapError fun msg => s!"constraint {st.stats.constraints}: {msg}"
      let s := st.stats
      pure {
        body := pushLin (pushLin (pushLin st.body r.a) r.b) r.c
        stats := { s with constraints := s.constraints + 1, nnzA := s.nnzA + r.a.size,
                          nnzB := s.nnzB + r.b.size, nnzC := s.nnzC + r.c.size } }
    | .lookup _ => throw "lookups cannot be exported to R1CS"
    | .interact _ => throw "interactions cannot be exported to R1CS") init ops
  let header := [1, st.stats.signals, nPublic, st.stats.constraints].foldl pushU32 "CLB1".toUTF8
  return { st with body := header ++ st.body }

/-- One instance's witness `w` (variables in order) packed LSB first after the constant one. -/
def packWitness (w : Array F) : ByteArray := Id.run do
  let n := w.size + 1
  let mut out := ByteArray.emptyWithCapacity ((n + 7) / 8)
  for byte in [0:(n + 7) / 8] do
    let mut x : UInt8 := 0
    for bit in [0:8] do
      let j := 8 * byte + bit
      if j == 0 || (j < n && w[j - 1]! = 1) then x := x ||| (1 <<< bit.toUInt8)
    out := out.push x
  return out

def witnessHeader (signals instances : ℕ) : ByteArray :=
  [1, signals, instances].foldl pushU32 "CLW2".toUTF8

end Gf2.R1CS
