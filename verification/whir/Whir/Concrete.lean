import Std

/-! Executable bit model. No `Field` instance is asserted for these operations.
The moduli are exactly the production K and E moduli. -/
namespace Whir.Concrete

abbrev K := UInt64

def kadd (a b : K) : K := a ^^^ b

def kmul (a b : K) : K := Id.run do
  let mut x := a
  let mut y := b
  let mut z : K := 0
  for _ in [:64] do
    if y &&& 1 == 1 then z := z ^^^ x
    let carry := x >>> 63
    x := x <<< 1
    if carry == 1 then x := x ^^^ 27
    y := y >>> 1
  return z

def kpow (a : K) (n : Nat) : K := Id.run do
  let mut x := a
  let mut out : K := 1
  for i in [:64] do
    if n.testBit i then out := kmul out x
    x := kmul x x
  return out

def kinv (a : K) : K := kpow a (2^64 - 2)

structure E where
  c0 : K := 0
  c1 : K := 0
  c2 : K := 0
  deriving BEq, DecidableEq, Repr, Inhabited

namespace E

def zero : E := ⟨0, 0, 0⟩
def one : E := ⟨1, 0, 0⟩
def ofK (a : K) : E := ⟨a, 0, 0⟩
def add (a b : E) : E := ⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1, a.c2 ^^^ b.c2⟩
def scale (a : E) (b : K) : E := ⟨kmul a.c0 b, kmul a.c1 b, kmul a.c2 b⟩
def mul (a b : E) : E :=
  let d0 := kmul a.c0 b.c0
  let d1 := kmul a.c0 b.c1 ^^^ kmul a.c1 b.c0
  let d2 := kmul a.c0 b.c2 ^^^ kmul a.c1 b.c1 ^^^ kmul a.c2 b.c0
  let d3 := kmul a.c1 b.c2 ^^^ kmul a.c2 b.c1
  let d4 := kmul a.c2 b.c2
  ⟨d0 ^^^ d3, d1 ^^^ d3 ^^^ d4, d2 ^^^ d4⟩
def toNat (a : E) : Nat := a.c0.toNat + 2^64 * a.c1.toNat + 2^128 * a.c2.toNat
end E

instance : Add E := ⟨E.add⟩
instance : Mul E := ⟨E.mul⟩
instance : Zero E := ⟨E.zero⟩
instance : One E := ⟨E.one⟩

def tab (n : Nat) (f : Nat → α) : Array α := (List.range n).toArray.map f

def dot {R : Type u} [Zero R] [Add R] [Mul R] [Inhabited R] (a b : Array R) : R :=
  (tab (min a.size b.size) fun i => a[i]! * b[i]!).foldl (· + ·) 0

def powers (a : E) (n : Nat) : Array E := Id.run do
  let mut out := #[]
  let mut x := E.one
  for _ in [:n] do
    out := out.push x
    x := x * a
  return out

/-- Coordinates and table indices are least-significant-bit first. -/
def eqTable {R : Type u} [One R] [Add R] [Mul R] (point : Array R) : Array R := Id.run do
  let mut out := #[(1 : R)]
  for r in point do
    out := (out.map fun x => x * (1 + r)) ++ (out.map fun x => x * r)
  return out

def foldPair {R : Type u} [Add R] [Mul R] (a b r : R) : R := a + r * (a + b)

def foldLow {R : Type u} [Add R] [Mul R] [Inhabited R] (a : Array R) (r : R) : Array R :=
  tab (a.size / 2) fun i => foldPair a[2*i]! a[2*i+1]! r

/-- One of the top-lane rounds: adjacent lane blocks, not adjacent words. -/
def foldLane {R : Type u} [Add R] [Mul R] [Inhabited R]
    (a : Array R) (block : Nat) (r : R) : Array R :=
  tab (a.size / 2) fun i =>
    let offset := (i / block) * (2*block) + i % block
    foldPair a[offset]! a[offset+block]! r

def mle {R : Type u} [Zero R] [One R] [Add R] [Mul R] [Inhabited R]
    (a : Array R) (point : Array R) : R := dot a (eqTable point)

def rotatePoint {R : Type u} (initialK : Nat) (point : Array R) : Array R :=
  point.extract initialK point.size ++ point.extract 0 initialK

/-- s_i(v_i), including i=n, using the standard polynomial basis v_i=x^i. -/
def subspaceRoots (n : Nat) : Array K := Id.run do
  let mut roots : Array K := #[1]
  let mut layer := tab n fun i => (1 : K) <<< UInt64.ofNat (i+1)
  for i in [:n] do
    layer := layer.map fun x => kmul x (x ^^^ roots[i]!)
    roots := roots.push layer[0]!
    layer := layer.extract 1 layer.size
  return roots

def normalizedSubspaces (n : Nat) (x : K) : Array K := Id.run do
  let roots := subspaceRoots n
  let mut out := #[]
  let mut s := x
  for i in [:n] do
    out := out.push (kmul s (kinv roots[i]!))
    s := kmul s (s ^^^ roots[i]!)
  return out

def column (n : Nat) (q : Nat) : Array E := Id.run do
  let mut out := #[E.one]
  for s in normalizedSubspaces n (UInt64.ofNat q) do
    out := out ++ out.map (fun x => x.scale s)
  return out

def encode (n rate : Nat) (coeffs : Array E) : Array E :=
  tab (2^(n+rate)) fun q => dot coeffs (column n q)

/-- L0 returns only the occupied tail of each leaf, in descending lane order. -/
def encodeBase (message : Array K) (logN initialK rate : Nat) : Array (Array E) :=
  let n := logN - initialK
  let block := 2^n
  let lanes := message.size / block
  let codes := tab lanes fun lane => encode n rate
    (tab block fun j => E.ofK message[lane*block+j]!)
  tab (2^(n+rate)) fun q => tab lanes fun t => codes[lanes-1-t]![q]!

/-- Later-level inputs are row major, with the low variables selecting the lane. -/
def encodeExt (message : Array E) (logN foldK rate : Nat) : Array (Array E) :=
  let n := logN-foldK
  let lanes := 2^foldK
  let codes := tab lanes fun lane => encode n rate
    (tab (2^n) fun j => message[j*lanes+lane]!)
  tab (2^(n+rate)) fun q => tab lanes fun lane => codes[lane]![q]!

/-- Executable weighted column combination, retaining default indexing on malformed inputs. -/
def inducedColumns {R : Type u} [Zero R] [Add R] [Mul R] [Inhabited R]
    (width : Nat) (cols : Array (Array R)) (weights : Array R) : Array R :=
  tab width fun j => (tab cols.size fun i => weights[i]! * cols[i]![j]!).foldl (· + ·) 0

def induced (n : Nat) (queries : Array Nat) (weights : Array E) : Array E :=
  inducedColumns (2^n) (queries.map (column n)) weights

def inducedAt (n : Nat) (queries : Array Nat) (weights point : Array E) : E := Id.run do
  let mut out := E.zero
  for i in [:queries.size] do
    let ws := normalizedSubspaces n (UInt64.ofNat queries[i]!)
    let mut product := weights[i]!
    for k in [:n] do
      product := product * (E.one + point[k]! * (E.one + E.ofK ws[k]!))
    out := out + product
  return out

def strata (count depth : Nat) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  for g in (List.range (count.log2+1)).reverse do
    if count.testBit g then
      let bits := min g depth
      for j in [:2^g] do out := out.push (bits, j % 2^bits)
  return out

/-- Independent supplied E squeezes, not a Fiat-Shamir implementation. -/
def deriveQueries (depth count : Nat) (squeezes : Array E) : Option (Array Nat) := do
  if depth == 0 || depth > 64 then none else do
    let per := 192 / depth
    if squeezes.size != (count + per - 1) / per then none else do
      let ss := strata count depth
      return tab count fun i =>
        let raw := (squeezes[i/per]!.toNat / 2^((i%per)*depth)) % 2^depth
        let (bits, index) := ss[i]!
        raw % 2^(depth-bits) + index * 2^(depth-bits)

end Whir.Concrete
