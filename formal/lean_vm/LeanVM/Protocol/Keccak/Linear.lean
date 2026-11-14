/-
  LeanVM.Protocol.Keccak.Linear

  The round's linear map over `E` and its transpose: bits as `0/1` field elements, `L` on
  vectors, and `⟨w, L v⟩ = ⟨keccakLinearTranspose w, v⟩`.
-/

module

public import LeanVM.Protocol.Keccak.Bits
public import LeanVM.Parameters.Field
public import Mathlib.Algebra.CharP.Two
import Mathlib.Data.List.GetD
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

/-!
# The linear map over `E` and its transpose

A layer of the reduction (`verify_layer`, `crates/verifier/src/keccak.rs`) moves a claim's
position weights across the round's linear map with `linear_transpose`
(`keccak.rs`, `keccakLinearTranspose`), whose defining property is
`⟨w, L(a)⟩ = ⟨Lᵀ(w), a⟩` (`doc/leanvm`, §`keccak:layer`, step 6). This module proves it:

* `bitE`: a bit as `0` or `1` of `E`; in characteristic two XOR is `+`, AND is `·` and NOT is
  `1 + ·` (`bitE_xor`, `bitE_and`, `bitE_not`);
* `Llin`: `L` on vectors `ℕ → E` (θ is the identity plus two column sums, ρπ a permutation of
  the positions), and `bitE (Lb f j) = Llin (bitE ∘ f) j` (`bitE_Lb`);
* `keccakLinearTranspose_getD`: the verifier's array program in closed form;
* `transpose`: `Σ_j w_j (L v)_j = Σ_j (Lᵀ w)_j v_j` over the `1600` positions, for every `v`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier Finset

@[expose] public section

/-! ## Bits in `E` -/

/-- A bit as a field element. -/
def bitE (b : Bool) : E := if b then 1 else 0

@[simp] theorem bitE_true : bitE true = 1 := rfl
@[simp] theorem bitE_false : bitE false = 0 := rfl

theorem bitE_xor (a b : Bool) : bitE (a ^^ b) = bitE a + bitE b := by
  cases a <;> cases b <;> simp [bitE, CharTwo.add_self_eq_zero]

theorem bitE_and (a b : Bool) : bitE (a && b) = bitE a * bitE b := by
  cases a <;> cases b <;> simp [bitE]

theorem bitE_not (a : Bool) : bitE (!a) = 1 + bitE a := by
  cases a <;> simp [bitE, CharTwo.add_self_eq_zero]

/-! ## The linear map on vectors -/

/-- A θ column sum: `Σ_y v(x + 5y, z)`. -/
def colL (v : ℕ → E) (x z : ℕ) : E := ∑ y ∈ range 5, v (64 * (x + 5 * y) + z)

/-- θ on vectors. -/
def thetaL (v : ℕ → E) (p : ℕ) : E :=
  v p + colL v ((p / 64 % 5 + 4) % 5) (p % 64) + colL v ((p / 64 % 5 + 1) % 5) ((p % 64 + 63) % 64)

/-- `L = π ∘ ρ ∘ θ` on vectors. -/
def Llin (v : ℕ → E) (j : ℕ) : E := thetaL v (rhoPiSrc j)

/-- The transpose of θ: `g` plus the columns `x + 1` at `z` and `x - 1` at `z + 1`. -/
def thetaT (g : ℕ → E) (p : ℕ) : E :=
  g p + colL g ((p / 64 % 5 + 1) % 5) (p % 64) + colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64)

theorem bitE_colB (f : ℕ → Bool) (x z : ℕ) : bitE (colB f x z) = colL (fun p ↦ bitE (f p)) x z := by
  simp only [colB, bitE_xor, colL, Finset.sum_range_succ, Finset.sum_range_zero]
  ring_nf

/-- On bits, `L` is `Llin`. -/
theorem bitE_Lb (f : ℕ → Bool) (j : ℕ) : bitE (Lb f j) = Llin (fun p ↦ bitE (f p)) j := by
  simp only [Lb, thetaB, bitE_xor, bitE_colB, Llin, thetaL]

/-! ## Reindexing sums -/

theorem sum_range_mul (a b : ℕ) (F : ℕ → E) :
    ∑ p ∈ range (a * b), F p = ∑ i ∈ range a, ∑ k ∈ range b, F (b * i + k) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.mul_comm a b]

/-- The positions by column, slice and row. -/
theorem sum_regroup (F : ℕ → E) :
    ∑ p ∈ range 1600, F p = ∑ x ∈ range 5, ∑ z ∈ range 64, ∑ y ∈ range 5, F (64 * (x + 5 * y) + z) := by
  rw [show 1600 = 25 * 64 from rfl, sum_range_mul, show 25 = 5 * 5 from rfl, sum_range_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  congr 1
  ring

/-- A sum weighted by a function of the column and the slice collects the columns. -/
theorem sum_col (g : ℕ → E) (H : ℕ → ℕ → E) :
    ∑ p ∈ range 1600, g p * H (p / 64 % 5) (p % 64) =
      ∑ x ∈ range 5, ∑ z ∈ range 64, H x z * colL g x z := by
  rw [sum_regroup]
  refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  rw [colL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  simp only [Finset.mem_range] at hx hz hy
  have h1 : (64 * (x + 5 * y) + z) / 64 % 5 = x := by omega
  have h2 : (64 * (x + 5 * y) + z) % 64 = z := by omega
  rw [h1, h2, mul_comm]

/-- A permutation of `range n` does not change a sum over it. -/
theorem sum_perm (n : ℕ) (σ τ : ℕ → ℕ) (hσ : ∀ x < n, σ x < n) (hτ : ∀ x < n, τ x < n)
    (hστ : ∀ x < n, σ (τ x) = x) (hτσ : ∀ x < n, τ (σ x) = x) (F : ℕ → E) :
    ∑ x ∈ range n, F (σ x) = ∑ x ∈ range n, F x :=
  Finset.sum_nbij' σ τ (fun x hx ↦ by simpa using hσ x (by simpa using hx))
    (fun x hx ↦ by simpa using hτ x (by simpa using hx))
    (fun x hx ↦ hτσ x (by simpa using hx)) (fun x hx ↦ hστ x (by simpa using hx))
    fun _ _ ↦ rfl

/-! ## The transpose of θ -/

theorem theta_transpose (g v : ℕ → E) :
    ∑ p ∈ range 1600, g p * thetaL v p = ∑ p ∈ range 1600, thetaT g p * v p := by
  simp only [thetaL, thetaT, mul_add, add_mul, Finset.sum_add_distrib]
  have t1 : ∑ p ∈ range 1600, g p * v p = ∑ p ∈ range 1600, v p * g p :=
    Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  have t2 : ∑ p ∈ range 1600, g p * colL v ((p / 64 % 5 + 4) % 5) (p % 64) =
      ∑ p ∈ range 1600, colL g ((p / 64 % 5 + 1) % 5) (p % 64) * v p := by
    rw [sum_col g (fun x z ↦ colL v ((x + 4) % 5) z)]
    rw [show (∑ p ∈ range 1600, colL g ((p / 64 % 5 + 1) % 5) (p % 64) * v p) =
      ∑ p ∈ range 1600, v p * colL g ((p / 64 % 5 + 1) % 5) (p % 64) from
        Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    rw [sum_col v (fun x z ↦ colL g ((x + 1) % 5) z)]
    rw [← sum_perm 5 (fun x ↦ (x + 1) % 5) (fun x ↦ (x + 4) % 5) (by omega) (by omega)
      (by omega) (by omega)]
    refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun z _ ↦ ?_
    simp only [Finset.mem_range] at hx
    have : ((x + 1) % 5 + 4) % 5 = x := by omega
    rw [this, mul_comm]
  have t3 : ∑ p ∈ range 1600, g p * colL v ((p / 64 % 5 + 1) % 5) ((p % 64 + 63) % 64) =
      ∑ p ∈ range 1600, colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) * v p := by
    rw [sum_col g (fun x z ↦ colL v ((x + 1) % 5) ((z + 63) % 64))]
    rw [show (∑ p ∈ range 1600, colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) * v p) =
      ∑ p ∈ range 1600, v p * colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) from
        Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    rw [sum_col v (fun x z ↦ colL g ((x + 4) % 5) ((z + 1) % 64))]
    rw [← sum_perm 5 (fun x ↦ (x + 4) % 5) (fun x ↦ (x + 1) % 5) (by omega) (by omega)
      (by omega) (by omega)]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [← sum_perm 64 (fun z ↦ (z + 1) % 64) (fun z ↦ (z + 63) % 64) (by omega) (by omega)
      (by omega) (by omega)]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    simp only [Finset.mem_range] at hx hz
    have e1 : ((x + 4) % 5 + 1) % 5 = x := by omega
    have e2 : ((z + 1) % 64 + 63) % 64 = z := by omega
    rw [e1, e2, mul_comm]
  rw [t2, t3]

/-! ## The verifier's transpose in closed form -/

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  unfold sumE
  suffices h : ∀ a : E, l.foldl (· + ·) a = a + l.sum by simpa using h 0
  induction l with
  | nil => simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem list_sum_range (f : ℕ → E) (n : ℕ) :
    ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem array_getD_toArray (l : List E) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem setIfInBounds_getD (a : Array E) (i p : ℕ) (x : E) :
    (a.setIfInBounds i x).getD p 0 = if i = p ∧ i < a.size then x else a.getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all
  omega

/-- A row of a grid flattened by rows. -/
theorem flatMap_getD (F : ℕ → ℕ → E) (m : ℕ) :
    ∀ (n x z : ℕ), x < n → z < m →
      ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).getD (m * x + z) 0 = F x z
  | 0, _, _, hx, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, x, z, hx, hz => by
    have hlen : ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
      simp [List.length_flatMap, List.sum_replicate]
    rw [List.range_succ, List.flatMap_append]
    by_cases hxn : x < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact flatMap_getD F m n x z hxn hz
    · have : x = n := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen]
      simp [Nat.mul_comm, hz, List.getD_eq_getElem?_getD]

theorem flatMap_length (F : ℕ → ℕ → E) (m n : ℕ) :
    ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
  simp [List.length_flatMap, List.sum_replicate]

/-- θ's input weights after ρπ: position `p` of θ's output carries `w` at `rhoPiDst p`. -/
def gOf (w : List E) (p : ℕ) : E := w.getD (rhoPiDst p) 0

/-- The inner loop of `keccak_linear_transpose`'s first array, writing one lane. -/
theorem inner_loop (W : ℕ → E) (lane : ℕ) (g : Array E) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).size =
        g.size ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.size then W (p - 64 * lane)
        else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := inner_loop W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], fun p ↦ ?_⟩
    rw [setIfInBounds_getD, hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-- `keccak_linear_transpose`'s first array, lane by lane. -/
theorem outer_loop (w : List E) :
    ∀ L, L ≤ 25 →
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).size = 1600 ∧
      ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).getD p 0 = if p < 64 * L then gOf w p else 0
  | 0, _ => ⟨by simp [keccakBits], fun p ↦ by
      simp [Array.getD_eq_getD_getElem?, keccakBits, Array.getElem?_replicate]
      split_ifs <;> rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := outer_loop w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_loop
      (fun z ↦ w.toArray.getD (64 * keccakPi L + (z + keccakRho.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArray, gOf, rhoPiDst]
      have e1 : p / 64 = L := by omega
      have e2 : p % 64 = p - 64 * L := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- `keccak_linear_transpose`'s column sums. -/
theorem columns_getD (A : Array E) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
        sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
      (64 * x + z) 0 = colL (fun p ↦ A.getD p 0) x z := by
  rw [array_getD_toArray, flatMap_getD (fun x z ↦
    sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)) 64 5 x z hx hz]
  rw [sumE_eq_sum, list_sum_range]
  rfl

/-- The list `keccak_linear_transpose` returns, from its first array `A`, in closed form. -/
theorem transposeList_getD (A : Array E) (g : ℕ → E) (hA : ∀ p < 1600, A.getD p 0 = g p)
    {p : ℕ} (hp : p < 1600) :
    ((List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
      A.getD (64 * lane + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 1) % 5) + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0).getD p 0 = thetaT g p := by
  have hp' : p = 64 * (p / 64) + p % 64 := by omega
  conv_lhs => rw [hp']
  rw [flatMap_getD _ 64 25 (p / 64) (p % 64) (by omega) (Nat.mod_lt _ (by omega))]
  rw [columns_getD _ (by omega) (Nat.mod_lt _ (by omega)),
    columns_getD _ (by omega) (Nat.mod_lt _ (by omega)), ← hp', hA p hp]
  have hcol : ∀ x z, x < 5 → z < 64 → colL (fun p ↦ A.getD p 0) x z = colL g x z := by
    intro x z hx hz
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    simp only [Finset.mem_range] at hy
    exact hA _ (by omega)
  rw [hcol _ _ (by omega) (Nat.mod_lt _ (by omega)), hcol _ _ (by omega) (Nat.mod_lt _ (by omega))]
  rfl

/-- **`keccak_linear_transpose` in closed form**: θ's transpose of the weights moved back
through ρπ. -/
theorem keccakLinearTranspose_getD (w : List E) {p : ℕ} (hp : p < 1600) :
    (keccakLinearTranspose w).getD p 0 = thetaT (gOf w) p := by
  obtain ⟨-, hg⟩ := outer_loop w 25 le_rfl
  exact transposeList_getD _ (gOf w) (fun q hq ↦ by rw [hg, ite_eq_left (by omega)]) hp

theorem keccakLinearTranspose_length (w : List E) : (keccakLinearTranspose w).length = 1600 := by
  unfold keccakLinearTranspose
  simp only []
  rw [flatMap_length]

/-- **The transpose.** For every vector `v` on the positions,
`Σ_j w_j (L v)_j = Σ_j (keccakLinearTranspose w)_j v_j` (`keccak.rs`). -/
theorem transpose (w : List E) (v : ℕ → E) :
    ∑ j ∈ range 1600, w.getD j 0 * Llin v j =
      ∑ j ∈ range 1600, (keccakLinearTranspose w).getD j 0 * v j := by
  have h1 : ∑ j ∈ range 1600, w.getD j 0 * Llin v j =
      ∑ p ∈ range 1600, gOf w p * thetaL v p :=
    Finset.sum_nbij' rhoPiSrc rhoPiDst (fun _ _ ↦ Finset.mem_range.2 rhoPiSrc_lt)
      (fun p hp ↦ Finset.mem_range.2 (rhoPiDst_lt (Finset.mem_range.1 hp)))
      (fun j hj ↦ rhoPiDst_src (Finset.mem_range.1 hj))
      (fun p hp ↦ rhoPiSrc_dst (Finset.mem_range.1 hp))
      fun j hj ↦ by rw [Llin, gOf, rhoPiDst_src (Finset.mem_range.1 hj)]
  rw [h1, theta_transpose]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [keccakLinearTranspose_getD w (Finset.mem_range.1 hp)]

/-- The transpose on bits: `Σ_j w_j (L a)_j = Σ_j (Lᵀ w)_j a_j`, bits as `0/1` of `E`. -/
theorem transpose_bits (w : List E) (f : ℕ → Bool) :
    ∑ j ∈ range 1600, w.getD j 0 * bitE (Lb f j) =
      ∑ j ∈ range 1600, (keccakLinearTranspose w).getD j 0 * bitE (f j) := by
  simp only [bitE_Lb]
  exact transpose w _

end
end LeanVM.Protocol.KeccakGkr
