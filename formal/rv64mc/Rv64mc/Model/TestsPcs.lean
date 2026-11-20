import Rv64mc.Model.RingSwitch
import Rv64mc.Model.KeccakGkr

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

-- The mirror of `linear_transpose` on the xorshift stream, against the statement's.
#guard (linearTransposeRust (xorshift 0x2545F4914F6CDD1D#64 23 1600)).map (·.map limbs) ==
  some ((keccakLinearTranspose (xorshift 0x2545F4914F6CDD1D#64 23 1600)).map limbs)

end Keccak

end Rv64mc.Model.TestsPcs
