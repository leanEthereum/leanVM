import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fin.VecNotation

/-!
# Keccak-f[1600] as the protocol sees it

A state is a bit per position, a position `(ℓ, z)` being slice `z` of lane `ℓ`, lane `ℓ` in
column `ℓ mod 5` and row `ℓ / 5`. A round is a linear map (theta, rho and pi), then chi and iota:
`a'[j] = b[j] + (1 + b[j →1]) b[j →2] + [ℓ = 0] RC[z]` with `b` the linear map's output and
`j →k` the position `k` columns along (`along`).

The protocol is sound for any linear map and round constants (`Perm`); `keccak` instantiates them
with the crate's `theta, rho, pi` (`crates/keccak_gkr/src/keccak.rs`) and the round constants of
`primitives::hash`.
-/

namespace KeccakGkr

abbrev Lane := Fin 25
abbrev Slice := Fin 64
abbrev Pos := Lane × Slice
/-- A state: a bit per position. -/
abbrev State := Pos → ZMod 2

/-- The lane `k` columns along from lane `ℓ`, in the same row. -/
def alongLane (ℓ : Lane) (k : ℕ) : Lane :=
  ⟨5 * (ℓ.val / 5) + (ℓ.val % 5 + k) % 5, by omega⟩

/-- The position `k` columns along from `j`, in the same row and slice. -/
def along (j : Pos) (k : ℕ) : Pos := (alongLane j.1 k, j.2)

theorem alongLane_alongLane (ℓ : Lane) (a b : ℕ) :
    alongLane (alongLane ℓ a) b = alongLane ℓ (a + b) := by
  ext
  simp only [alongLane]
  omega

theorem alongLane_five (ℓ : Lane) : alongLane ℓ 5 = ℓ := by
  ext
  simp only [alongLane]
  omega

theorem along_along (j : Pos) (a b : ℕ) : along (along j a) b = along j (a + b) := by
  simp [along, alongLane_alongLane]

theorem along_five (j : Pos) : along j 5 = j := by
  simp [along, alongLane_five]

/-- Moving `k` columns along, then `5 - k`, comes back. -/
def alongEquiv (k : ℕ) (hk : k ≤ 5) : Pos ≃ Pos where
  toFun j := along j k
  invFun j := along j (5 - k)
  left_inv j := by simp [along_along, Nat.add_sub_cancel' hk, along_five]
  right_inv j := by simp [along_along, Nat.sub_add_cancel hk, along_five]

/-- A permutation as the protocol sees it: its rounds' linear map and round constants. -/
structure Perm where
  /-- Theta, rho and pi. -/
  lin : Matrix Pos Pos (ZMod 2)
  /-- The constant iota adds to lane `0` in round `r`, counted from `0`. -/
  rc : ℕ → Slice → ZMod 2

/-- Chi and iota of round `r` on the linear map's output `b`. -/
def chi (rc : Slice → ZMod 2) (b : State) : State := fun j =>
  b j + (1 + b (along j 1)) * b (along j 2) + if j.1 = 0 then rc j.2 else 0

/-- Round `r`, counted from `0`. -/
def Perm.round (P : Perm) (r : ℕ) (a : State) : State := chi (P.rc r) (P.lin.mulVec a)

/-- The first `e` rounds from round `r₀`. -/
def Perm.rounds (P : Perm) (r₀ : ℕ) : ℕ → State → State
  | 0, a => a
  | e + 1, a => P.round (r₀ + e) (P.rounds r₀ e a)

/-! ## Keccak -/

/-- Where pi sends lane `x + 5y`: to lane `y + 5 ((2x + 3y) mod 5)`. -/
def pi : Lane → Lane := ![0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13,
  14, 24, 9, 19, 4]

/-- The lane pi sends to lane `ℓ`. -/
def piInv : Lane → Lane := ![0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17,
  23, 2, 8, 14, 15, 21]

theorem pi_piInv (ℓ : Lane) : pi (piInv ℓ) = ℓ := by revert ℓ; decide

/-- Rho's rotation of each lane. -/
def rho : Lane → ℕ := ![0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

/-- Iota's round constants. -/
def roundConstants : Fin 24 → ℕ := ![0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
  0x8000000080008000, 0x000000000000808B, 0x0000000080000001, 0x8000000080008081,
  0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009,
  0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
  0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A,
  0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001,
  0x8000000080008008]

/-- The parity of column `x` in slice `z`. -/
def column (a : State) (x : Fin 5) (z : Slice) : ZMod 2 :=
  ∑ y : Fin 5, a (⟨x.val + 5 * y.val, by omega⟩, z)

/-- `pi (rho (theta a))`, as `keccak.rs`'s `linear` computes it. -/
def keccakLinear (a : State) : State := fun j =>
  let ℓ := piInv j.1
  let z := j.2 - Fin.ofNat 64 (rho ℓ)
  let x : Fin 5 := ⟨ℓ.val % 5, by omega⟩
  a (ℓ, z) + column a (x + 4) z + column a (x + 1) (z - 1)

/-- `keccakLinear` as a linear map. -/
def keccakLin : State →ₗ[ZMod 2] State where
  toFun := keccakLinear
  map_add' a b := by
    funext j
    simp only [keccakLinear, column, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c a := by
    funext j
    simp only [keccakLinear, column, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      ← Finset.mul_sum]
    ring

/-- Keccak-f[1600]: `24` rounds of `theta, rho, pi, chi, iota`. -/
def keccak : Perm where
  lin := LinearMap.toMatrix' keccakLin
  rc r z := if r < 24 ∧ (roundConstants ⟨r % 24, by omega⟩).testBit z.val then 1 else 0

theorem keccak_lin_mulVec (a : State) : keccak.lin.mulVec a = keccakLinear a :=
  LinearMap.toMatrix'_mulVec keccakLin a

/-- The permutation Keccak-f[1600]. -/
def keccakF (a : State) : State := keccak.rounds 0 24 a

end KeccakGkr
