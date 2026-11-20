import Rv64mc.Model.RingSwitch
import Rv64mc.Model.KeccakGkr
import Rv64mc.Model.Whir

/-!
# The PCS mirrors on the Rust's test inputs

The tests of `ring_switch.rs`, `whir.rs` and `keccak.rs`, run on the mirrors: each draws its
inputs from the same xorshift or LCG stream as the Rust test and checks the same identities.
-/

namespace Rv64mc.Model.TestsPcs

open Rv64mc.Model LeanVM.Parameters LeanVM.Protocol.Verifier

/-- The tests' xorshift stream: `count` values `E::new(state, state.rotate_left(rot))`. -/
def xorshift (seed : BitVec 64) (rot count : ℕ) : List E :=
  ((List.range count).foldl (fun (acc : List E × BitVec 64) _ ↦
    let s := acc.2 ^^^ (acc.2 <<< 13)
    let s := s ^^^ (s >>> 7)
    let s := s ^^^ (s <<< 17)
    (acc.1 ++ [ofLimbsW (s, s.rotateLeft rot)], s)) ([], seed)).1

/-! ## `ring_switch.rs`: `target_and_coefficients_expand_the_map` -/

section RingSwitch

def ringStream : List E := xorshift 0x9E3779B97F4A7C15#64 29 (16 + 64)

def ringF : List E := (ringStream.take 16).take 8

def ringG : List E := (ringStream.take 16).drop 8

def ringS : List E := ringStream.drop 16

def ringCoeffs : List E := ringCoefficientsRust ringF ringG

/-- `phi(value)`: the two stages written out. -/
def ringPhi (value : E) : E :=
  let psi := ringPsiRust value ringG
  sumRust ((List.range 8).map fun p ↦ ringF.getD p 0 * frobenius8Rust psi p)

/-- `sum_k c_k value^(2^k)`. -/
def ringImage (value : E) : E :=
  (ringCoeffs.foldl (fun (acc : E × E) c ↦ (acc.1 + c * acc.2, squareE acc.2)) (0, value)).1

#guard ringCoeffs.length == 64

#guard ringS.all fun value ↦ limbs (ringPhi value) == limbs (ringImage value)

#guard limbs (ringTargetRust ringS ringF ringG) ==
  limbs (polyEvalRust (ringS.map ringImage) gen)

end RingSwitch

/-! ## `keccak.rs`: `the_embedding_projects_products_to_and` -/

section Keccak

/-- The embedding of the sixteen bits of `a`. -/
def embed (a : ℕ) : BitVec 64 :=
  (List.range 16).foldl (fun acc i ↦
    if a.testBit i then acc ^^^ (rmfeEmbedRust.getD i 0).setWidth 64 else acc) 0

/-- The carry-less product of two `u64`s, truncated. -/
def carryless (a b : BitVec 64) : BitVec 64 :=
  (List.range 64).foldl (fun acc i ↦ if bit64 b i then acc ^^^ (a <<< i) else acc) 0

/-- The projection: per bit, the parity of the product's coefficients under its mask. -/
def project (p : BitVec 64) : ℕ :=
  (List.range 16).foldl (fun acc i ↦
    let masked := p &&& rmfeProjectRust.getD i 0
    if ((List.range 64).countP fun j ↦ masked.getLsbD j) % 2 = 1 then acc ||| (1 <<< i)
    else acc) 0

/-- The test's LCG stream of `(a, b)` pairs of `u16`s. -/
def lcgPairs (count : ℕ) : List (ℕ × ℕ) :=
  ((List.range count).foldl (fun (acc : List (ℕ × ℕ) × BitVec 64) _ ↦
    let x := acc.2 * 6364136223846793005#64 + 1442695040888963407#64
    (acc.1 ++ [((x >>> 16).toNat % 2 ^ 16, (x >>> 40).toNat % 2 ^ 16)], x))
    ([], 0x9E3779B97F4A7C15#64)).1

#guard (lcgPairs 1000).all fun (a, b) ↦ project (carryless (embed a) (embed b)) == (a &&& b)

-- `linear_transpose` on the xorshift stream: entries and the limbs' XOR, as the Rust prints them
-- (`verifier::keccak::linear_transpose` of `E::new(s, s.rotate_left(23))`, 1600 draws).
def ltOut : List Limbs :=
  ((linearTransposeRust (xorshift 0x2545F4914F6CDD1D#64 23 1600)).getD []).map limbs

#guard [0, 1, 63, 64, 319, 320, 777, 1599].map (ltOut.getD · (0#64, 0#64)) ==
  [(0x603b83380813b9ea#64, 0x9c0409dcf5301dc1#64), (0x66002c9f43e2a419#64, 0x4fa1f1520cb30016#64),
   (0xb4f5031d8811a63a#64, 0x8ec408d31d5a7a81#64), (0xc01c7341f3c7c42a#64, 0xa0f9e3e215600e39#64),
   (0x13df1a2272af1627#64, 0x1139578b1389ef8d#64), (0xece657d9d159351d#64, 0xece8ac9a8ef6732b#64),
   (0xf84da0a775b2c8fa#64, 0x53bad9647d7c26d0#64), (0xcadaedd1b9c3087b#64, 0xe8dce1843de56d76#64)]

#guard ltOut.foldl (fun acc l ↦ (acc.1 ^^^ l.1, acc.2 ^^^ l.2)) (0#64, 0#64) ==
  (0xe13834b0ddf16e3a#64, 0x586ef8b71d709c1a#64)

end Keccak

/-! ## `whir.rs`: the novel basis, `times_x`, the affine row fold -/

section Whir

/-- `W_i(x) = prod_(u in span(1, x, ..., x^(i-1))) (x + u)`. -/
def vanishing (i : ℕ) (x : K) : K :=
  (List.range (2 ^ i)).foldl (fun acc u ↦ acc * (x + BF64.ofBitVec (BitVec.ofNat 64 u))) 1

def referenceWhat (i : ℕ) (x : K) : K := vanishing i x * kInvK (vanishing i (kShl i))

def eqE (a b : E) : Bool := limbs a == limbs b

def eqOptE (a : Option E) (b : E) : Bool := a.map limbs == some (limbs b)

/-- The test's `times_x`: the product by `X` in the novel basis. -/
def timesX (coefficients : List E) (roots : List K) : List E :=
  let a := (List.range (roots.length - 1)).map fun i ↦
    roots.getD (i + 1) 0 * kInvK (kSquareK (roots.getD i 0))
  (List.range coefficients.length).foldl (fun out c ↦
    let h := coefficients.getD c 0
    let t := ((List.range 64).takeWhile fun i ↦ c.testBit i).length
    let st := ((a.take t).zipIdx).foldl (fun (st : List E × K) (aj : K × ℕ) ↦
      let i := (c >>> aj.2) <<< aj.2
      (st.1.set i (st.1.getD i 0 + mulKE h st.2), st.2 * aj.1)) (out, 1)
    st.1.set (c + 1) (st.1.getD (c + 1) 0 + mulKE h st.2))
    (List.replicate (coefficients.length + 1) 0)

def paddedSum (left right : List E) : List E :=
  (List.range (max left.length right.length)).map fun i ↦ left.getD i 0 + right.getD i 0

def sub4 : SubspaceRust := (SubspaceRust.new 4).getD ⟨[], []⟩

def sub5 : SubspaceRust := (SubspaceRust.new 5).getD ⟨[], []⟩

-- `novel_basis_matches_the_vanishing_products`
def nbStream : List E := xorshift 0x2545F4914F6CDD1D#64 23 20

def nbCoeffs : List E := nbStream.take 19

def nbPoints : List K :=
  [0, BF64.ofBitVec 5#64, kShl 4, BF64.ofBitVec (limbs (nbStream.getD 19 0)).1]

#guard nbPoints.all fun x ↦
  (List.range 5).all fun i ↦ ((sub4.at x).getD i 0).toBitVec == (referenceWhat i x).toBitVec

#guard nbPoints.all fun x ↦ eqOptE (novelEvalRust nbCoeffs (sub4.at x))
  (sumRust ((List.range 19).map fun c ↦ (List.range 5).foldl (fun acc i ↦
    if c.testBit i then mulKE acc (referenceWhat i x) else acc) (nbCoeffs.getD c 0)))

-- `times_x_is_multiplication_by_x`
def txStream : List E := xorshift 0x2545F4914F6CDD1D#64 23 19

#guard ((List.range 3).foldl (fun (st : Bool × List E) r ↦
    let product := timesX st.2 sub5.roots
    let x := BF64.ofBitVec (limbs (txStream.getD (16 + r) 0)).1
    let what := sub5.at x
    let ok := match novelEvalRust product what, novelEvalRust st.2 what with
      | some a, some b => eqE a (mulKE b x)
      | _, _ => false
    (st.1 && ok, product)) (true, txStream.take 16)).1

-- `affine_row_fold_and_high_correction`
def afStream : List E := xorshift 0x2545F4914F6CDD1D#64 23 (8 * 16 + 6 + 4)

def afLanes : List (List E) := (List.range 8).map fun l ↦ (afStream.drop (16 * l)).take 16

def afRounds : List FoldRound :=
  (List.range 3).map fun r ↦ ⟨afStream.getD (128 + 2 * r) 0, afStream.getD (128 + 2 * r + 1) 0⟩

def afPoints : List K :=
  (List.range 4).map fun i ↦ BF64.ofBitVec (limbs (afStream.getD (134 + i) 0)).1

def afRows : List (List E) := afPoints.map fun x ↦
  afLanes.map fun lane ↦ (novelEvalRust lane (sub5.at x)).getD 0

def afFolded : List E := (afRounds.foldl (fun lanes round ↦
    (List.range (lanes.length / 2)).map fun i ↦
      let f := lanes.getD (2 * i) []
      let g := lanes.getD (2 * i + 1) []
      let xf := timesX f sub5.roots
      paddedSum (paddedSum g (f.map (round.alpha * ·))) (xf.map (round.beta * ·)))
    afLanes).getD 0 []

#guard afFolded.length == 16 + 3

#guard (afPoints.zip afRows).all fun (x, row) ↦
  let what := sub5.at x
  match foldRowRust row x afRounds, novelEvalRust afFolded what,
      novelEvalRust (afFolded.drop 16) what, novelEvalRust (afFolded.take 16) what with
  | some value, some full, some high, some low =>
    eqE value full && eqE (value + mulKE high (what.getD 4 0)) low
  | _, _, _, _ => false

end Whir

end Rv64mc.Model.TestsPcs

/-! The axiom footprint of the PCS mirrors' simulations: Lean's three. -/

/--
info: 'Rv64mc.Model.SimR.ringSwitch' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Model.SimR.ringSwitch

/--
info: 'Rv64mc.Model.SimR.verifyKeccak' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Model.SimR.verifyKeccak

/--
info: 'Rv64mc.Model.SimRoots.verifyStackedOpening' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Rv64mc.Model.SimRoots.verifyStackedOpening
