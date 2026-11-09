/-
  LeanVM.Guest.B1.KeccakGkr.KFormMath

  `keccak_form`'s identity (G:2655-2681): a later claim's weights at the local point, through the
  transpose of θ, ρ, π, factor as lane weights times shift sums of the slice weights.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Algebra

/-!
# `keccak_form` as math

`later_dot`: `⟨eq(l), Lᵀ(lanes ⊗ eq(a₆))⟩`, the dot the verifier takes (V:2016-2019, `laterWeights`),
is `formVal` of the local point's lane weights `eq(l₆..₁₀, ·)`, the lanes at `π`, and the shift
sums `S(r) = Σ_z eq(a₆, z + r)·eq(l₀..₅, z)`: `Σ_lane f·lane·S(ρ) + Σ_x f_col(x)·(col(x + 1) +
col'(x - 1))`, `col` the column of `lane·S(ρ)` and `col'` of `lane·S(ρ + 1)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

/-- `ρ` of a lane. -/
def kRho (l : ℕ) : ℕ := keccakRho.getD l 0

/-- The lane weight a lane moves to (`lanes[π(lane)]`). -/
def kLane (lanes : List E) (l : ℕ) : E := lanes.getD (keccakPi l) 0

/-- The shift sum `S(r)`. -/
def kS (a6 b6 : List E) (r : ℕ) : E := ∑ z ∈ range 64, eqAt a6 ((z + r) % 64) * eqAt b6 z

/-- A column of `lane·S(ρ)`. -/
def colS (L S : ℕ → E) (x : ℕ) : E := ∑ y ∈ range 5, L (x + 5 * y) * S (kRho (x + 5 * y))

/-- A column of `lane·S(ρ + 1)`. -/
def colN (L S : ℕ → E) (x : ℕ) : E := ∑ y ∈ range 5, L (x + 5 * y) * S ((kRho (x + 5 * y) + 1) % 64)

/-- `keccak_form`'s value from the lane weights `fL`, the lanes `L` (at `π`) and the shifts `S`. -/
def formVal (fL L S : ℕ → E) : E :=
  ∑ l ∈ range 25, fL l * (L l * S (kRho l)) +
    ∑ x ∈ range 5, (∑ y ∈ range 5, fL (x + 5 * y)) * (colS L S ((x + 1) % 5) + colN L S ((x + 4) % 5))

/-- The weight θ's output position `64l + z` carries. -/
theorem gOf_later (lanes a6 : List E) (ha : a6.length = 6) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    gOf ((List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * (eqKernel a6).getD (j % 64) 0)
      (64 * l + z) = kLane lanes l * eqAt a6 ((z + kRho l) % 64) := by
  have hq : 64 * l + z < 1600 := by omega
  have hd := rhoPiDst_lt hq
  rw [gOf, List.getD_eq_getElem _ _ (by simp [keccakBits]; exact hd), List.getElem_map,
    List.getElem_range]
  have hd1 : (64 * l + z) / 64 = l := by omega
  have hm1 : (64 * l + z) % 64 = z := by omega
  have h1 : rhoPiDst (64 * l + z) / 64 = keccakPi l := by
    unfold rhoPiDst; rw [hd1, hm1]; omega
  have h2 : rhoPiDst (64 * l + z) % 64 = (z + kRho l) % 64 := by
    unfold rhoPiDst kRho; rw [hd1, hm1]; omega
  rw [h1, h2, eqKernel_getD, ha, kLane]
  simp [show (z + kRho l) % 64 < 64 from Nat.mod_lt _ (by norm_num)]

theorem sum25_mod (G H : ℕ → E) :
    ∑ l ∈ range 25, G l * H (l % 5) = ∑ x ∈ range 5, (∑ y ∈ range 5, G (x + 5 * y)) * H x := by
  rw [show (25 : ℕ) = 5 * 5 from rfl, sum_range_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have := Finset.mem_range.1 hx
  rw [show (5 * y + x) % 5 = x by omega, add_comm (5 * y)]

/-- A column of `θ`'s transpose at slice `z'`. -/
theorem colL_later (lanes a6 : List E) (ha : a6.length = 6) {x z' : ℕ} (hx : x < 5) (hz : z' < 64) :
    colL (gOf ((List.range keccakBits).map fun j ↦
      lanes.getD (j / 64) 0 * (eqKernel a6).getD (j % 64) 0)) x z' =
      ∑ y ∈ range 5, kLane lanes (x + 5 * y) * eqAt a6 ((z' + kRho (x + 5 * y)) % 64) := by
  unfold colL
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have := Finset.mem_range.1 hy
  exact gOf_later lanes a6 ha (by omega) hz

/-- **`keccak_form`'s identity** (G:2655-2681 against V:2016-2019). -/
theorem later_dot (locPt a6 lanes : List E) (hl : locPt.length = 11) (ha : a6.length = 6) :
    dot ((eqKernel locPt).take keccakBits) (laterWeights lanes (eqKernel a6)) =
      formVal (eqAt (locPt.drop 6)) (kLane lanes) (kS a6 (locPt.take 6)) := by
  have hlen : (laterWeights lanes (eqKernel a6)).length = keccakBits :=
    keccakLinearTranspose_length _
  have h6 : (locPt.take 6).length = 6 := by simp [hl]
  rw [show keccakBits = (laterWeights lanes (eqKernel a6)).length from hlen.symm,
    dot_eqKernel locPt _ (by rw [hlen, hl]; decide), hlen, show keccakBits = 25 * 64 from rfl,
    sum_range_mul]
  set fZ := eqAt (locPt.take 6) with hfZ
  set fL := eqAt (locPt.drop 6) with hfL
  set L := kLane lanes with hL
  set S := kS a6 (locPt.take 6) with hS
  have lane : ∀ l < 25, (∑ z ∈ range 64, eqAt locPt (64 * l + z) *
      (laterWeights lanes (eqKernel a6)).getD (64 * l + z) 0) =
      fL l * (L l * S (kRho l) + colS L S ((l % 5 + 1) % 5) + colN L S ((l % 5 + 4) % 5)) := by
    intro l hl25
    have term : ∀ z ∈ range 64, eqAt locPt (64 * l + z) *
        (laterWeights lanes (eqKernel a6)).getD (64 * l + z) 0 =
        fL l * (L l * (eqAt a6 ((z + kRho l) % 64) * fZ z) +
          ∑ y ∈ range 5, L ((l % 5 + 1) % 5 + 5 * y) *
            (eqAt a6 ((z + kRho ((l % 5 + 1) % 5 + 5 * y)) % 64) * fZ z) +
          ∑ y ∈ range 5, L ((l % 5 + 4) % 5 + 5 * y) *
            (eqAt a6 ((z + (kRho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64) % 64) * fZ z)) := by
      intro z hz
      have hz' := Finset.mem_range.1 hz
      have hd : (64 * l + z) / 64 = l := by omega
      have hm : (64 * l + z) % 64 = z := by omega
      have hsplit : eqAt locPt (64 * l + z) = fZ z * fL l := by
        have := eqAt_lz (locPt.take 6) (locPt.drop 6) h6 hz' l
        rwa [List.take_append_drop] at this
      rw [hsplit, laterWeights, keccakLinearTranspose_getD _ (by omega), thetaT, hd, hm,
        gOf_later lanes a6 ha hl25 hz', colL_later lanes a6 ha (by omega) hz',
        colL_later lanes a6 ha (by omega) (by omega)]
      have hshift : ∀ y, ((z + 1) % 64 + kRho ((l % 5 + 4) % 5 + 5 * y)) % 64 =
          (z + (kRho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64) % 64 := fun y ↦ by omega
      simp only [hshift, mul_add, Finset.mul_sum]
      exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (by ring)
        (Finset.sum_congr rfl fun y _ ↦ by ring)) (Finset.sum_congr rfl fun y _ ↦ by ring)
    rw [Finset.sum_congr rfl term, ← Finset.mul_sum]
    refine congrArg (fL l * ·) ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm,
      Finset.sum_comm (s := range 64) (t := range 5)]
    simp only [← Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl fun l hl ↦ lane l (Finset.mem_range.1 hl)]
  unfold formVal
  simp only [mul_add, Finset.sum_add_distrib, add_assoc]
  exact congrArg₂ (· + ·) rfl (congrArg₂ (· + ·) (sum25_mod fL (fun x ↦ colS L S ((x + 1) % 5)))
    (sum25_mod fL (fun x ↦ colN L S ((x + 4) % 5))))

/-- **`keccak_form`'s identity, for any lane and slice weights** (`fL ⊗ fZ` against `Lᵀ`). -/
theorem later_dot_gen (a6 lanes : List E) (ha : a6.length = 6) (fL fZ : ℕ → E) :
    ∑ l ∈ range 25, ∑ z ∈ range 64,
      fL l * fZ z * (laterWeights lanes (eqKernel a6)).getD (64 * l + z) 0 =
      formVal fL (kLane lanes) (fun r ↦ ∑ z ∈ range 64, eqAt a6 ((z + r) % 64) * fZ z) := by
  set L := kLane lanes with hL
  set S : ℕ → E := fun r ↦ ∑ z ∈ range 64, eqAt a6 ((z + r) % 64) * fZ z with hS
  have lane : ∀ l < 25, (∑ z ∈ range 64, fL l * fZ z *
      (laterWeights lanes (eqKernel a6)).getD (64 * l + z) 0) =
      fL l * (L l * S (kRho l) + colS L S ((l % 5 + 1) % 5) + colN L S ((l % 5 + 4) % 5)) := by
    intro l hl25
    have term : ∀ z ∈ range 64, fL l * fZ z *
        (laterWeights lanes (eqKernel a6)).getD (64 * l + z) 0 =
        fL l * (L l * (eqAt a6 ((z + kRho l) % 64) * fZ z) +
          ∑ y ∈ range 5, L ((l % 5 + 1) % 5 + 5 * y) *
            (eqAt a6 ((z + kRho ((l % 5 + 1) % 5 + 5 * y)) % 64) * fZ z) +
          ∑ y ∈ range 5, L ((l % 5 + 4) % 5 + 5 * y) *
            (eqAt a6 ((z + (kRho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64) % 64) * fZ z)) := by
      intro z hz
      have hz' := Finset.mem_range.1 hz
      have hd : (64 * l + z) / 64 = l := by omega
      have hm : (64 * l + z) % 64 = z := by omega
      rw [mul_comm (fL l) (fZ z), laterWeights, keccakLinearTranspose_getD _ (by omega), thetaT,
        hd, hm, gOf_later lanes a6 ha hl25 hz', colL_later lanes a6 ha (by omega) hz',
        colL_later lanes a6 ha (by omega) (by omega)]
      have hshift : ∀ y, ((z + 1) % 64 + kRho ((l % 5 + 4) % 5 + 5 * y)) % 64 =
          (z + (kRho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64) % 64 := fun y ↦ by omega
      simp only [hshift, mul_add, Finset.mul_sum]
      exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (by ring)
        (Finset.sum_congr rfl fun y _ ↦ by ring)) (Finset.sum_congr rfl fun y _ ↦ by ring)
    rw [Finset.sum_congr rfl term, ← Finset.mul_sum]
    refine congrArg (fL l * ·) ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm,
      Finset.sum_comm (s := range 64) (t := range 5)]
    simp only [← Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl fun l hl ↦ lane l (Finset.mem_range.1 hl)]
  unfold formVal
  simp only [mul_add, Finset.sum_add_distrib, add_assoc]
  exact congrArg₂ (· + ·) rfl (congrArg₂ (· + ·) (sum25_mod fL (fun x ↦ colS L S ((x + 1) % 5)))
    (sum25_mod fL (fun x ↦ colN L S ((x + 4) % 5))))

end
end LeanVM.Guest.B1.VerifySub
