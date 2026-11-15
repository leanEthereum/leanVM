/-
  LeanVM.Guest.B1.KeccakGkr.Algebra

  The identities behind the guest's factored Keccak weights: the equality weights of the local
  point split into slice and lane, the first claim's weight as a product, and a layer's batched
  weights as a lane table times a slice table.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.InterfaceP
public import LeanVM.Protocol.Keccak.LayerSum

/-!
# The weights' algebra

With the bit position `j = 64·lane + z` and the local point `loc = a ++ b` (`a` the six slice
coordinates, `b` the five lane coordinates):

* `eqAt_lz`: `eq(loc, 64l + z) = eq(a, z) · eq(b, l)`;
* `sum_eqAt_pow`: `Σ_z eq(a, z)·x^z = Π_t (1 + a_t (1 + x^(2^t)))`;
* `firstWeight_eq`: the first claim's weight at `loc` (`dot (eq.take 1600) (firstWeights lanes)`) is `(Σ_l eq(b, l)·lanes_l) · Π_t (1 + a_t (1 + g^(2^t)))`;
* `batch_factor`: a layer's batched weights are `lanesOut ⊗ eqKernel a`, so the next
  claim's weights are `laterWeights (lanesOut loc β) (eqKernel a)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

/-- `eq(a ++ b, 64l + z) = eq(a, z)·eq(b, l)` for six slice coordinates. -/
theorem eqAt_lz (a b : List E) (ha : a.length = 6) {z : ℕ} (hz : z < 64) (l : ℕ) :
    eqAt (a ++ b) (64 * l + z) = eqAt a z * eqAt b l := by
  have h1 : eqAt a (64 * l + z) = eqAt a z := by
    rw [eqAt_mod a (64 * l + z), eqAt_mod a z, ha]
    congr 1
    norm_num
  have h2 : (64 * l + z) / 2 ^ 6 = l := by norm_num; omega
  rw [eqAt_append, ha, h1, h2]

/-- **The power sum of the equality weights**: `Σ_{z < 2^n} eq(a, z)·x^z = Π_t (1 + a_t(1 + x^(2^t)))`. -/
theorem sum_eqAt_pow : ∀ (a : List E) (x : E),
    ∑ z ∈ range (2 ^ a.length), eqAt a z * x ^ z =
      ((List.range a.length).map fun t ↦ 1 + a.getD t 0 * (1 + x ^ 2 ^ t)).prod
  | [], x => by simp [eqAt]
  | r :: a, x => by
    rw [List.length_cons, sum_cube_succ]
    have h : ∀ w ∈ range (2 ^ a.length), eqAt (r :: a) (2 * w) * x ^ (2 * w) +
        eqAt (r :: a) (2 * w + 1) * x ^ (2 * w + 1) = (1 + r * (1 + x)) * (eqAt a w * (x ^ 2) ^ w) := by
      intro w _
      rw [eqAt_cons, eqAt_cons]
      have e1 : 2 * w % 2 = 0 := by omega
      have e2 : (2 * w + 1) % 2 = 1 := by omega
      have e3 : 2 * w / 2 = w := by omega
      have e4 : (2 * w + 1) / 2 = w := by omega
      simp only [e1, e2, e3, e4, zero_ne_one, ite_false, ite_true]
      rw [← pow_mul, pow_succ]
      ring
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, sum_eqAt_pow a (x ^ 2)]
    simp only [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map,
      Function.comp_def, List.getD_cons_zero, List.getD_cons_succ, pow_zero, pow_one]
    have hf : (fun t ↦ 1 + a.getD t 0 * (1 + (x ^ 2) ^ 2 ^ t)) =
        (fun t ↦ 1 + a.getD t 0 * (1 + x ^ 2 ^ t.succ)) := by
      funext t; rw [← pow_mul, pow_succ, mul_comm (2 ^ t) 2]
    rw [hf]

theorem firstWeights_length (lanes : List E) : (firstWeights lanes).length = keccakBits := by
  simp [firstWeights]

theorem firstWeights_getD (lanes : List E) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    (firstWeights lanes).getD (64 * l + z) 0 = lanes.getD l 0 * gen ^ z := by
  rw [firstWeights, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simp [keccakBits]; omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega,
    gen_pow_eq_eOfNat hz]

/-- The equality weights of eleven coordinates, entry `j < 1600`. -/
theorem eqKernel11_getD (loc : List E) (hl : loc.length = 11) {j : ℕ} (hj : j < 1600) :
    (eqKernel loc).getD j 0 = eqAt (loc.take 6) (j % 64) * eqAt (loc.drop 6) (j / 64) := by
  rw [eqKernel_getD, hl, ite_eq_left (by omega)]
  conv_lhs => rw [← List.take_append_drop 6 loc, show j = 64 * (j / 64) + j % 64 by omega]
  exact eqAt_lz _ _ (by simp [hl]) (by omega) _

/-- **The first claim's weight** at the local point. -/
theorem firstWeight_eq (loc lanes : List E) (hl : loc.length = 11) :
    dot ((eqKernel loc).take keccakBits) (firstWeights lanes) =
      (∑ l ∈ range 25, eqAt (loc.drop 6) l * lanes.getD l 0) *
        ((List.range 6).map fun t ↦ 1 + (loc.take 6).getD t 0 * (1 + gen ^ 2 ^ t)).prod := by
  have hw : (firstWeights lanes).length = keccakBits := firstWeights_length lanes
  rw [show keccakBits = (firstWeights lanes).length from hw.symm,
    dot_eqKernel loc _ (by rw [hw, hl]; decide), hw, show keccakBits = 25 * 64 from rfl,
    sum_range_mul]
  have h6 : (loc.take 6).length = 6 := by simp [hl]
  have := sum_eqAt_pow (loc.take 6) gen
  rw [h6] at this
  rw [← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl' => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hl25 := Finset.mem_range.1 hl'
  have hz64 := Finset.mem_range.1 hz
  rw [firstWeights_getD lanes hl25 hz64]
  conv_lhs => rw [← List.take_append_drop 6 loc]
  rw [eqAt_lz _ _ h6 hz64]
  ring

/-- The lane table a layer writes: `eq(b, l) + β(eq(b, l + 4) + β eq(b, l + 3))`, the
column moved within the row. -/
def lanesOut (loc : List E) (beta : E) : List E :=
  (List.range 25).map fun l ↦ eqAt (loc.drop 6) l + beta * (eqAt (loc.drop 6)
    ((l % 5 + 4) % 5 + 5 * (l / 5)) + beta * eqAt (loc.drop 6) ((l % 5 + 3) % 5 + 5 * (l / 5)))

/-- **A layer's batched weights factor**: lane table times slice table. -/
theorem batch_factor (loc : List E) (hl : loc.length = 11) (beta : E) :
    ((List.range keccakBits).map fun j ↦ (eqKernel loc).getD j 0 + beta *
      ((eqKernel loc).getD (keccakAlong j 4) 0 + beta * (eqKernel loc).getD (keccakAlong j 3) 0)) =
      (List.range keccakBits).map fun j ↦
        (lanesOut loc beta).getD (j / 64) 0 * (eqKernel (loc.take 6)).getD (j % 64) 0 := by
  apply List.map_congr_left
  intro j hj
  have hj' : j < 1600 := List.mem_range.1 hj
  rw [eqKernel11_getD loc hl hj', eqKernel11_getD loc hl (keccakAlong_lt 4 hj'),
    eqKernel11_getD loc hl (keccakAlong_lt 3 hj'), keccakAlong_def, keccakAlong_def,
    eqKernel_getD, ite_eq_left (by simp [hl]; omega)]
  rw [lanesOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  have e1 : (64 * ((j / 64 % 5 + 4) % 5 + 5 * (j / 64 / 5)) + j % 64) % 64 = j % 64 := by omega
  have e2 : (64 * ((j / 64 % 5 + 4) % 5 + 5 * (j / 64 / 5)) + j % 64) / 64 =
      (j / 64 % 5 + 4) % 5 + 5 * (j / 64 / 5) := by omega
  have e3 : (64 * ((j / 64 % 5 + 3) % 5 + 5 * (j / 64 / 5)) + j % 64) % 64 = j % 64 := by omega
  have e4 : (64 * ((j / 64 % 5 + 3) % 5 + 5 * (j / 64 / 5)) + j % 64) / 64 =
      (j / 64 % 5 + 3) % 5 + 5 * (j / 64 / 5) := by omega
  rw [e1, e2, e3, e4]
  ring

end
end LeanVM.Guest.B1.VerifySub
