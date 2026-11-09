/-
  LeanVM.Prover.Keccak.States

  The executable prover's masks are the bits entering χ of the specification's states.
-/

module

public import LeanVM.Prover.Keccak.Tables

/-!
# The bits entering χ

`packMasks col' P (11 - d) z` lists, per position `j`, the sixteen instances' bits of `L` of the
states `11 - d` rounds into the segment: bit `i` of entry `j` is `Lb (stAt T P z i) j` for
`T = statesAt (P + 4) col (d + 1)`, the states layer `d` of the specification reads
(`testBit_layerMasks`), when the column `col'` agrees with `col` on the words the states read.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

/-- `col'` agrees with `col` on `q_keccak`'s `2^(P + 10)` words. -/
def ColAgree (P : ℕ) (col' col : ℕ → K) : Prop := ∀ n < 2 ^ (P + 10), col' n = col n

theorem pow_P10 (P : ℕ) : 2 ^ (P + 10) = 2 ^ (P + 4) * 64 := by
  rw [show P + 10 = (P + 4) + 6 by ring, pow_add]; norm_num

theorem slot_lt {P x o : ℕ} (hx : x < 2 ^ (P + 4)) (ho : o < 64) :
    x + 2 ^ (P + 4) * o < 2 ^ (P + 10) := by
  rw [pow_P10]
  have := Nat.mul_le_mul_left (2 ^ (P + 4)) (show o ≤ 63 by omega)
  have : 2 ^ (P + 4) * 64 = 2 ^ (P + 4) * 63 + 2 ^ (P + 4) := by ring
  omega

theorem inStateOf_eq {P : ℕ} {col' col : ℕ → K} (hcol : ColAgree P col' col) {m x : ℕ}
    (hm : m < 2) (hx : x < 2 ^ (P + 4)) : inStateOf col' (P + 4) m x = LeanVM.Protocol.KeccakGkr.inState (P + 4) col m x := by
  unfold inStateOf LeanVM.Protocol.KeccakGkr.inState
  congr 1
  funext l
  rw [hcol _ (slot_lt hx (by omega))]

theorem bitOf_linearOf (a : KeccakState) {j : ℕ} (hj : j < 1600) :
    bitOf (linearOf a) j = Lb (sbit a) j := by
  show sbit (Stage.rhoPi (Stage.theta a)) j = _
  rw [Stage.sbit_rhoPi _ hj, Stage.sbit_theta _ rhoPiSrc_lt]
  rfl

/-- **The masks are the bits entering χ.** -/
theorem testBit_packMasks {P : ℕ} {col' col : ℕ → K} (hcol : ColAgree P col' col) {d z i j : ℕ}
    (hd : d < 12) (hz : z < 2 ^ (P + 1)) (hi : i < 16) (hj : j < 1600) :
    ((packMasks col' P (11 - d) z).getD j 0).testBit i =
      Lb (stAt (statesAt (P + 4) col (d + 1)) P z i) j := by
  have hm : z / 2 ^ P < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [pow_succ] at hz
    linarith
  have hy : z % 2 ^ P < 2 ^ P := Nat.mod_lt _ (by positivity)
  have hx : i + 16 * (z % 2 ^ P) < 2 ^ (P + 4) := by
    rw [pow_add]
    omega
  rw [packMasks, array_getD_ofFn_lt _ hj, testBit_packBits, decide_eq_true hi, Bool.true_and,
    array_getD_ofFn_lt _ hi, bitOf_linearOf _ hj, inStateOf_eq hcol hm hx, stAt]
  unfold statesAt
  rw [show 12 - (d + 1) = 11 - d by omega]
  rfl

theorem testBit_layerMasks {P : ℕ} {col' col : ℕ → K} (hcol : ColAgree P col' col) {d z i j : ℕ}
    (hd : d < 12) (hz : z < 2 ^ (P + 1)) (hi : i < 16) (hj : j < 1600) :
    (((layerMasks col' P (11 - d)).getD z #[]).getD j 0).testBit i =
      Lb (stAt (statesAt (P + 4) col (d + 1)) P z i) j := by
  rw [layerMasks, array_getD_ofFn_lt _ hz]
  exact testBit_packMasks hcol hd hz hi hj

end
end LeanVM.Prover.KeccakGkr
