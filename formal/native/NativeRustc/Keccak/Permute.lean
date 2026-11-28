module

public import NativeRustc.Keccak.Sponge

/-!
# `lanes::permute`'s round

`crates/keccak256/src/lanes.rs`, `permute`: the state's 25 lanes `a` and θ's five column parities
`c`, carried from round to round. A round computes θ's mixes `d[x] = c[x + 4] ^ c[x + 1] <<< 1`
(`thetaD`), the lanes `t(i) = a[i] ^ d[i % 5]` (`tC`), each row `y` of the lanes ρ and π send there
(`bC`), χ on each row (`chi`), ι on row 0, and the new parities as the XOR of the new rows.

`roundCL a c rc j`: lane `j` after the round from lanes `a` and parities `c`. When `c` is the
column parities `par A` of the lanes, it is lane `j` of `Keccak.round A rc` (`lane_round`), and the
new parities, the XOR of the new rows (`newPar`), are `par` of the round's lanes
(`par_round`). The lanes of
the state after the first `i` rounds (`roundsTo`), one round further (`roundsTo_succ`), are
`keccakF1600`'s after the 24 (`roundsTo_24`). As 64-bit vectors: `Keccak.rot` is a right rotation
(`toBitVec_rot`) and a left one (`toBitVec_rot_left`).
-/

@[expose] public section

namespace NativeRustc.Keccak

open LeanVM.Semantics LeanVM.Parameters LeanVM.Fast.Keccak

/-- θ's parity of column `x`. -/
def par (A : KeccakState) (x : Nat) : UInt64 :=
  Keccak.lane A x ^^^ Keccak.lane A (x + 5) ^^^ Keccak.lane A (x + 10) ^^^
    Keccak.lane A (x + 15) ^^^ Keccak.lane A (x + 20)

/-- θ's mix of column `x` from the parities `c` (`theta_d`). -/
def thetaD (c : Nat → UInt64) (x : Nat) : UInt64 :=
  c ((x + 4) % 5) ^^^ Keccak.rot (c ((x + 1) % 5)) 1

/-- `t(i)`: lane `i` with θ's mix of its column. -/
def tC (a c : Nat → UInt64) (i : Nat) : UInt64 := a i ^^^ thetaD c (i % 5)

/-- Lane `j` of the rows `permute` builds: the lane ρ and π send to row `j / 5`, column
`j % 5`, rotated by its ρ. -/
def bC (a c : Nat → UInt64) : Nat → UInt64
  | 0 => Keccak.rot (tC a c 0) 0
  | 1 => Keccak.rot (tC a c 6) 44
  | 2 => Keccak.rot (tC a c 12) 43
  | 3 => Keccak.rot (tC a c 18) 21
  | 4 => Keccak.rot (tC a c 24) 14
  | 5 => Keccak.rot (tC a c 3) 28
  | 6 => Keccak.rot (tC a c 9) 20
  | 7 => Keccak.rot (tC a c 10) 3
  | 8 => Keccak.rot (tC a c 16) 45
  | 9 => Keccak.rot (tC a c 22) 61
  | 10 => Keccak.rot (tC a c 1) 1
  | 11 => Keccak.rot (tC a c 7) 6
  | 12 => Keccak.rot (tC a c 13) 25
  | 13 => Keccak.rot (tC a c 19) 8
  | 14 => Keccak.rot (tC a c 20) 18
  | 15 => Keccak.rot (tC a c 4) 27
  | 16 => Keccak.rot (tC a c 5) 36
  | 17 => Keccak.rot (tC a c 11) 10
  | 18 => Keccak.rot (tC a c 17) 15
  | 19 => Keccak.rot (tC a c 23) 56
  | 20 => Keccak.rot (tC a c 2) 62
  | 21 => Keccak.rot (tC a c 8) 55
  | 22 => Keccak.rot (tC a c 14) 39
  | 23 => Keccak.rot (tC a c 15) 41
  | 24 => Keccak.rot (tC a c 21) 2
  | _ => 0

/-- χ (`Lane::chi`): `x ^ (!y & z)`. -/
def chi (x y z : UInt64) : UInt64 := x ^^^ (~~~ y &&& z)

/-- **Lane `j` after `permute`'s round** from the lanes `a` and the parities `c`, with the round
constant `rc`: χ on its row, ι on lane 0. -/
def roundCL (a c : Nat → UInt64) (rc : UInt64) (j : Nat) : UInt64 :=
  if j = 0 then chi (bC a c 0) (bC a c 1) (bC a c 2) ^^^ rc
  else chi (bC a c j) (bC a c (j - j % 5 + (j + 1) % 5)) (bC a c (j - j % 5 + (j + 2) % 5))

/-- **`permute`'s round is `Keccak.round`** where the parities are the lanes'. -/
theorem lane_round (A : KeccakState) (rc : UInt64) {j : Nat} (hj : j < 25) :
    Keccak.lane (Keccak.round A rc) j = roundCL (Keccak.lane A) (par A) rc j := by
  rw [round_eq_roundLanes]
  interval_cases j <;> rfl

/-- `permute`'s new parity of column `x`: the XOR of the new rows' lanes in that column. -/
def newPar (a c : Nat → UInt64) (rc : UInt64) (x : Nat) : UInt64 :=
  roundCL a c rc x ^^^ roundCL a c rc (x + 5) ^^^ roundCL a c rc (x + 10) ^^^
    roundCL a c rc (x + 15) ^^^ roundCL a c rc (x + 20)

/-- **The new parities are the round's.** -/
theorem par_round (A : KeccakState) (rc : UInt64) {x : Nat} (hx : x < 5) :
    par (Keccak.round A rc) x = newPar (Keccak.lane A) (par A) rc x := by
  rw [par, newPar, lane_round _ _ (by omega), lane_round _ _ (by omega),
    lane_round _ _ (by omega), lane_round _ _ (by omega), lane_round _ _ (by omega)]

/-! ## The rounds -/

/-- The state after the first `i` rounds. -/
def roundsTo (A : KeccakState) (i : Nat) : KeccakState := (keccakRC.take i).foldl Keccak.round A

theorem roundsTo_zero (A : KeccakState) : roundsTo A 0 = A := rfl

/-- One round more. -/
theorem roundsTo_succ (A : KeccakState) {i : Nat} (hi : i < 24) :
    roundsTo A (i + 1) = Keccak.round (roundsTo A i) (keccakRC.getD i 0) := by
  have hl : i < keccakRC.length := by simpa [keccakRC] using hi
  rw [roundsTo, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hl]
  simp [roundsTo, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

/-- **The 24 rounds are Keccak-f[1600].** -/
theorem roundsTo_24 (A : KeccakState) : roundsTo A 24 = keccakF1600 A := by
  rw [roundsTo, keccakF1600, List.take_of_length_le (by simp [keccakRC])]

/-! ## As 64-bit vectors -/

theorem rot_zero (x : UInt64) : Keccak.rot x 0 = x := rfl

/-- `Keccak.rot` by `0 < n < 64` is a right rotation by `64 - n`. -/
theorem toBitVec_rot (x : UInt64) {n : Nat} (h0 : 0 < n) (h : n < 64) :
    (Keccak.rot x n).toBitVec = x.toBitVec.rotateRight (64 - n) := by
  unfold Keccak.rot
  split
  · omega
  rw [BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt (by omega),
    Nat.sub_sub_self (by omega), BitVec.or_comm]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  congr 2 <;> simp [BitVec.toNat_umod, Nat.toUInt64_eq] <;> omega

/-- `Keccak.rot` by `n < 64` is a left rotation. -/
theorem toBitVec_rot_left (x : UInt64) {n : Nat} (h : n < 64) :
    (Keccak.rot x n).toBitVec = x.toBitVec.rotateLeft n := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt h]
  unfold Keccak.rot
  split
  · subst n
    rw [BitVec.ushiftRight_eq_zero (by simp), BitVec.or_zero, BitVec.shiftLeft_zero]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  congr 2 <;> simp [BitVec.toNat_umod, Nat.toUInt64_eq] <;> omega

end NativeRustc.Keccak
