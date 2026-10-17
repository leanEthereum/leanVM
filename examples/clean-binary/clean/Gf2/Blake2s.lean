module

public import Gf2.Basic

/-!
One BLAKE2s compression over GF(2), as `flock::hash::blake2s_compress(h, m, 64, 0xFFFFFFFF, 0)`.

Variables: `h` (256 bits) and `m` (512 bits), then the output (256 bits), all public, then the
private bits. XOR and rotation are free: every bit is a linear form (a set of signals). Only the
adders cost rows. A two-operand add `s = x + y` witnesses its sum bits `s_1 .. s_31` (`s_0` is the
form `x_0 + y_0`); its carries `c_i = x_i + y_i + s_i` stay linear, and the carry recurrence
`c_{i+1} = (x_i + c_i) · (y_i + c_i) + c_i` becomes one row per bit,
`(y_i + s_i) · (x_i + s_i) = c_{i+1} + c_i`, for `i = 0 .. 30`. A three-operand add is
`(x + y) + z`. The `b` words left by the diagonal G of rounds 2, 4 and 6 are witnessed (one linear
row per bit), which keeps the linear forms of later rows small. The output bits are pinned to
`h ^ v[i] ^ v[i + 8]` by one linear row each.

The schedule is written once and run twice: symbolically for the rows and natively for the
private witness, so both see the same signal order. No formal soundness or completeness proofs:
`Gf2.Check` tests the circuit against reference vectors.
-/

@[expose] public section

namespace Gf2.Blake2s

def IV : Array UInt32 :=
  #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

def SIGMA : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- Lanes `[a, b, c, d]` of the eight G applications of a round. -/
def LANES : Array (Array ℕ) := #[
  #[0, 4, 8, 12], #[1, 5, 9, 13], #[2, 6, 10, 14], #[3, 7, 11, 15],
  #[0, 5, 10, 15], #[1, 6, 11, 12], #[2, 7, 8, 13], #[3, 4, 9, 14]]

/-- The byte counter and finalization flags the circuit fixes. -/
def T : UInt64 := 64
def F0 : UInt32 := 0xFFFFFFFF
def F1 : UInt32 := 0

def rotr32 (x : UInt32) (r : ℕ) : UInt32 := (x >>> r.toUInt32) ||| (x <<< (32 - r).toUInt32)

/-- The last eight words of the initial working state. -/
def stateRow (t : UInt64) (f0 f1 : UInt32) : Array UInt32 :=
  #[IV[0]!, IV[1]!, IV[2]!, IV[3]!, IV[4]! ^^^ t.toUInt32, IV[5]! ^^^ (t >>> 32).toUInt32,
    IV[6]! ^^^ f0, IV[7]! ^^^ f1]

/-- Reference compression, written as RFC 7693 does, independently of the circuit. -/
def compress (h m : Array UInt32) (t : UInt64) (f0 f1 : UInt32) : Array UInt32 := Id.run do
  let mut v := h ++ stateRow t f0 f1
  for s in SIGMA do
    for g in [0:8] do
      let l := LANES[g]!
      let (a, b, c, d) := (l[0]!, l[1]!, l[2]!, l[3]!)
      v := v.set! a (v[a]! + v[b]! + m[s[2 * g]!]!)
      v := v.set! d (rotr32 (v[d]! ^^^ v[a]!) 16)
      v := v.set! c (v[c]! + v[d]!)
      v := v.set! b (rotr32 (v[b]! ^^^ v[c]!) 12)
      v := v.set! a (v[a]! + v[b]! + m[s[2 * g + 1]!]!)
      v := v.set! d (rotr32 (v[d]! ^^^ v[a]!) 8)
      v := v.set! c (v[c]! + v[d]!)
      v := v.set! b (rotr32 (v[b]! ^^^ v[c]!) 7)
  return Array.ofFn (n := 8) fun i => h[i]! ^^^ v[i]! ^^^ v[i.val + 8]!

/-- Word operations the schedule runs over, with effects for the ones that create bits. -/
structure Arith (m : Type → Type) (W : Type) where
  const : UInt32 → W
  xor : W → W → W
  rotr : W → ℕ → W
  /-- `x + y mod 2^32`: witnesses the sum bits `1 .. 31`. -/
  add : W → W → m W
  /-- Witnesses a copy of the word. -/
  copy : W → m W

/-- Rounds whose diagonal G witnesses the `b` word it leaves. -/
def copyRounds : List ℕ := [2, 4, 6]

/-- The G function on lanes `l` of `v`; `copyB` witnesses the `b` word it leaves. -/
def g {m : Type → Type} [Monad m] {W : Type} [Inhabited W] (ar : Arith m W) (v : Array W)
    (l : Array ℕ) (mx my : W) (copyB : Bool) : m (Array W) := do
  let (a, b, c, d) := (l[0]!, l[1]!, l[2]!, l[3]!)
  let a1 ← ar.add (← ar.add v[a]! v[b]!) mx
  let d1 := ar.rotr (ar.xor v[d]! a1) 16
  let c1 ← ar.add v[c]! d1
  let b1 := ar.rotr (ar.xor v[b]! c1) 12
  let a2 ← ar.add (← ar.add a1 b1) my
  let d2 := ar.rotr (ar.xor d1 a2) 8
  let c2 ← ar.add c1 d2
  let b2 := ar.rotr (ar.xor b1 c2) 7
  let b2 ← if copyB then ar.copy b2 else pure b2
  return (((v.set! a a2).set! b b2).set! c c2).set! d d2

/-- The pinned compression's output words `h ^ v[i] ^ v[i + 8]`. -/
def schedule {m : Type → Type} [Monad m] {W : Type} [Inhabited W] (ar : Arith m W)
    (h msg : Array W) : m (Array W) := do
  let mut v := h ++ (stateRow T F0 F1).map ar.const
  for r in [0:SIGMA.size] do
    let s := SIGMA[r]!
    for i in [0:8] do
      v ← g ar v LANES[i]! msg[s[2 * i]!]! msg[s[2 * i + 1]!]! (i ≥ 4 && copyRounds.contains r)
  return Array.ofFn (n := 8) fun i => ar.xor (ar.xor h[i]! v[i]!) v[i.val + 8]!

/-- Native run: the words, logging every witnessed bit in circuit order. -/
def native : Arith (StateM (Array F)) UInt32 where
  const := id
  xor := (· ^^^ ·)
  rotr := rotr32
  add x y := do
    let s := x + y
    modify fun acc => (List.range 31).foldl (fun acc i => acc.push (bitF s (i + 1))) acc
    return s
  copy x := do
    modify (pushWord · x)
    return x

/-- Symbolic state: the next fresh signal and the rows so far. -/
structure Sym where
  next : ℕ
  rows : Array Row

def fresh : StateM Sym ℕ := modifyGet fun st => (st.next, { st with next := st.next + 1 })

def emit (r : Row) : StateM Sym Unit := modify fun st => { st with rows := st.rows.push r }

/-- Sum bits of `x + y`: `s_0 = x_0 + y_0` linear, `s_1 .. s_31` fresh, one carry row per bit. -/
def symAdd (x y : Word) : StateM Sym Word := do
  let mut s : Word := #[x[0]!.add y[0]!]
  for _ in [1:32] do
    s := s.push #[← fresh]
  -- The carry into bit `i` is `x_i + y_i + s_i`.
  let carry (i : ℕ) : Lin := (x[i]!.add y[i]!).add s[i]!
  for i in [0:31] do
    emit { a := y[i]!.add s[i]!, b := x[i]!.add s[i]!, c := (carry (i + 1)).add (carry i) }
  return s

/-- Fresh signals equal to the bits of `x`, with one linear row each. -/
def symCopy (x : Word) : StateM Sym Word :=
  x.mapM fun l => do
    let s ← fresh
    emit { a := #[], b := #[], c := l.add #[s] }
    return #[s]

def symbolic : Arith (StateM Sym) Word where
  const := Word.const
  xor := Word.xor
  rotr := Word.rotr
  add := symAdd
  copy := symCopy

def nPublic : ℕ := 1024

/-- Rows of the circuit at `offset` and its last signal plus one. -/
def rowsAt (offset : ℕ) : Array Row × ℕ :=
  let sig := offset + 1
  let h := Array.ofFn (n := 8) fun w => Word.signals (sig + 32 * w.val)
  let msg := Array.ofFn (n := 16) fun w => Word.signals (sig + 256 + 32 * w.val)
  let (out, st) := (schedule symbolic h msg).run { next := sig + nPublic, rows := #[] }
  let pins := Array.ofFn (n := 256) fun i =>
    { a := #[], b := #[], c := (out[i.val / 32]!)[i.val % 32]!.add #[sig + 768 + i.val] : Row }
  (st.rows ++ pins, st.next)

/-- Number of private variables. -/
def nPrivate : ℕ := (rowsAt 0).2 - 1 - nPublic

/-- Prover hint key of an instance's 768 input bits (`h` then `m`). -/
def inputKey : String := "blake2s.input"

def inputBits (h m : Array UInt32) : Vector F 768 :=
  let bits := (h ++ m).foldl pushWord #[]
  Vector.ofFn fun i => bits[i.val]!

def inputHint (bits : Vector F 768) : ProverHint F := fun key n =>
  if h : key = inputKey ∧ n = 768 then #[h.2 ▸ bits] else #[]

def toVector {n : ℕ} (xs : Array F) : Vector F n := Vector.ofFn fun i => xs[i.val]?.getD 0

def inputWords (env : ProverEnvironment F) (offset : ℕ) : Array UInt32 × Array UInt32 :=
  (Array.ofFn (n := 8) fun w => readWord env.get offset w.val,
   Array.ofFn (n := 16) fun w => readWord env.get (offset + 256) w.val)

/-- The output bits then the private bits, from one native run of the schedule. -/
def witnessBits (h m : Array UInt32) : Array F :=
  let (out, priv) := (schedule native h m).run #[]
  out.foldl pushWord (Array.emptyWithCapacity (256 + priv.size)) ++ priv

def circuit : Circuit F Unit := fun offset => (do
  let _ ← witnessVectorNative 768 fun env =>
    (env.hint inputKey 768)[0]?.getD (Vector.replicate 768 0)
  let _ ← witnessVectorNative (256 + nPrivate) fun env =>
    let (h, m) := inputWords env offset
    toVector (witnessBits h m)
  for rows in ((rowsAt offset).1.toList.toChunks 256) do
    chunk (asserts (rows.map Row.toE))) offset

/-- The circuit's operations at offset 0, built once. -/
def ops : List (Operation F) := (circuit 0).2

end Gf2.Blake2s
