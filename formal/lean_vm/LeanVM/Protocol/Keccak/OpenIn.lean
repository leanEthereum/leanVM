/-
  LeanVM.Protocol.Keccak.OpenIn

  Opening the committed inputs: the claim at depth `12` as a sum over the instances, then over
  the slots and slices of `q_keccak`, down to the `64` bit-slice claims.
-/

module

public import LeanVM.Protocol.Keccak.OpenOut

/-!
# The inputs' opening

The claim at depth `12` is on the committed inputs, slot `25m + ℓ` of `q_keccak` holding lane
`ℓ` of segment `m`'s input (`doc/leanvm` eq. `keccak:eq:in` with §`keccak:segments`). With
`Φ(i)` the claim's sum restricted to instance `i`:

* the instance rounds (`crates/verifier/src/keccak.rs:280`):
  `Fl acc = Σ_u μ̃(acc ++ u)·Φ̃(acc ++ u)`, a plain family of degree two on four bits, `claimSum`
  before (`Fl_nil`);
* the slot rounds (`keccakOpen` with `first = 0, count = 2`): with the instance point `λ`,
  `Fs acc = μ̃(λ) · Σ_u Σ_z W̃_z(acc ++ u)·S̃_z(acc ++ u)`, `W_z(o)` the slot weights
  (`slotW`), `S_z(o)` slice `z` of slot `o` at the point `(λ, r_pack)` (`sliceMle`); before,
  `μ̃(λ)·Φ̃(λ)` (`Fs_nil`, by `phi_eq`: the claim's positions are the slots' slices);
* `S̃_z(ρ)` is slice `z`'s multilinear extension at `(λ, r_pack, ρ)`, the slice claims.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

@[expose] public section

variable (P : ℕ)

/-- The claim at depth `12` restricted to instance `i`. -/
noncomputable def PhiI (col : ℕ → K) (claim : KeccakClaim) (i : ℕ) : E :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAt claim.point z *
    ∑ j ∈ range 1600, claim.weights.getD j 0 * bitE (stAt (statesAt (P + 4) col 12) P z i j)

/-- The instance weights, extended over the four instance bits. -/
noncomputable def MuT (mu pt : List E) : E := ∑ i ∈ range (2 ^ 4), eqAt pt i * mu.getD i 0

/-- `Φ`, extended over the four instance bits. -/
noncomputable def PhiT (col : ℕ → K) (claim : KeccakClaim) (pt : List E) : E :=
  ∑ i ∈ range (2 ^ 4), eqAt pt i * PhiI P col claim i

/-- The instance rounds' family. -/
noncomputable def Fl (col : ℕ → K) (claim : KeccakClaim) (acc : List E) : E :=
  cubeSum (fun pt ↦ MuT claim.mu pt * PhiT P col claim pt) 4 acc

theorem Fl_plainFamily {β : Type} (qk : β → ℕ → K) (claim : KeccakClaim) :
    PlainFamily (fun q acc ↦ Fl P (qk q) claim acc) 2 4 :=
  cube_plainFamily (fun q pt ↦ MuT claim.mu pt * PhiT P (qk q) claim pt) 4
    fun _ pre post ↦ polyLE_mle_mul _ _ _ _ pre post

theorem Fl_nil (col : ℕ → K) (claim : KeccakClaim) :
    Fl P col claim [] = claimSum (statesAt (P + 4) col 12) P claim.point claim.mu claim.weights := by
  rw [Fl, cubeSum_nil]
  have hu : ∀ u ∈ range (2 ^ 4), MuT claim.mu (bitsE u 4) * PhiT P col claim (bitsE u 4) =
      claim.mu.getD u 0 * PhiI P col claim u := by
    intro u hu
    rw [MuT, PhiT, sum_eqAt_bitsE (Finset.mem_range.1 hu), sum_eqAt_bitsE (Finset.mem_range.1 hu)]
  rw [Finset.sum_congr rfl hu, claimSum]
  simp only [PhiI, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ by ring

/-- Slice `z` of slot `o` at the steps' point `a`. -/
noncomputable def sliceMle (col : ℕ → K) (a : List E) (o z : ℕ) : E :=
  ∑ x ∈ range (2 ^ (P + 4)), eqAt a x * bitE ((col (x + 2 ^ (P + 4) * o)).toBitVec.getLsbD z)

/-- The slot weights of the claim at depth `12`, slice `z`, extended over the slot bits. -/
noncomputable def Ws (claim : KeccakClaim) (z : ℕ) (pt : List E) : E :=
  ∑ o ∈ range (2 ^ 6), eqAt pt o * slotW (eqKernel (claim.point.drop P)) claim.weights 0 2 o z

/-- Slice `z` at `(λ, r_pack)`, extended over the slot bits. -/
noncomputable def Qs (col : ℕ → K) (a : List E) (z : ℕ) (pt : List E) : E :=
  ∑ o ∈ range (2 ^ 6), eqAt pt o * sliceMle P col a o z

/-- The slot rounds' family, at the instance point `low`. -/
noncomputable def Fs (col : ℕ → K) (claim : KeccakClaim) (low : List E) (acc : List E) : E :=
  cubeSum (fun pt ↦ MuT claim.mu low * ∑ z ∈ range 64,
    Ws P claim z pt * Qs P col (low ++ claim.point.take P) z pt) 6 acc

theorem Fs_plainFamily {β : Type} (qk : β → ℕ → K) (claim : KeccakClaim) (low : List E) :
    PlainFamily (fun q acc ↦ Fs P (qk q) claim low acc) 2 6 :=
  cube_plainFamily (fun q pt ↦ MuT claim.mu low * ∑ z ∈ range 64,
      Ws P claim z pt * Qs P (qk q) (low ++ claim.point.take P) z pt) 6
    fun _ pre post ↦ PolyLE.const_mul (PolyLE.sum _ fun _ _ ↦
      polyLE_mle_mul _ _ _ _ pre post) _

/-- The states at depth `12` are the committed inputs' bits. -/
theorem statesAt_12 (col : ℕ → K) (m x : ℕ) {j : ℕ} (hj : j < 1600) :
    statesAt (P + 4) col 12 m x j =
      (col (x + 2 ^ (P + 4) * (25 * m + j / 64))).toBitVec.getLsbD (j % 64) := by
  rw [statesAt, Nat.sub_self, segState, roundsFrom_zero, sbit, lane_inState _ _ _ _ (by omega)]
  rfl

/-- The claim at depth `12` on segment `m` and step `x`. -/
noncomputable def Gin (col : ℕ → K) (claim : KeccakClaim) (m x : ℕ) : E :=
  ∑ j ∈ range 1600, claim.weights.getD j 0 *
    bitE ((col (x + 2 ^ (P + 4) * (25 * m + j / 64))).toBitVec.getLsbD (j % 64))

theorem Gin_eq (col : ℕ → K) (claim : KeccakClaim) (m x : ℕ) :
    Gin P col claim m x = ∑ l ∈ range 25, ∑ z ∈ range 64, claim.weights.getD (64 * l + z) 0 *
      bitE ((col (x + 2 ^ (P + 4) * (25 * m + l))).toBitVec.getLsbD z) := by
  rw [Gin, show 1600 = 25 * 64 from rfl, sum_range_mul 25 64]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega]

/-- **The claim's positions are the slots' slices**: `Φ̃(λ)` is the slot-weighted sum of the
slices at `(λ, r_pack)`. -/
theorem phi_eq (col : ℕ → K) (claim : KeccakClaim) (hshape : ClaimShape P claim) {low : List E}
    (hlow : low.length = 4) :
    PhiT P col claim low = ∑ o ∈ range (2 ^ 6), ∑ z ∈ range 64,
      slotW (eqKernel (claim.point.drop P)) claim.weights 0 2 o z *
        sliceMle P col (low ++ claim.point.take P) o z := by
  have hb : (claim.point.take P).length = P := by simp [hshape.2.1]
  have hsd : (claim.point.drop P).length = 1 := by simp [hshape.2.1]
  have hX : ∀ z i, ∑ j ∈ range 1600, claim.weights.getD j 0 *
      bitE (stAt (statesAt (P + 4) col 12) P z i j) =
        Gin P col claim (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) := fun z i ↦
    Finset.sum_congr rfl fun j hj ↦ by
      rw [stAt, statesAt_12 P col _ _ (Finset.mem_range.1 hj)]
  have hphi : PhiT P col claim low = ∑ z ∈ range (2 ^ (P + 1)),
      eqAt (claim.point.take P ++ claim.point.drop P) z *
        ∑ i ∈ range 16, eqAt low i * Gin P col claim (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) := by
    rw [List.take_append_drop, PhiT]
    simp only [PhiI, hX]
    rw [show (2 : ℕ) ^ 4 = 16 from rfl]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hphi, sum_split hlow hb (Gin P col claim)]
  -- the slots: `o = 25m + ℓ` for `o < 50`, nothing above
  rw [show 2 ^ 6 = 2 * 25 + 14 from rfl, Finset.sum_range_add, sum_range_mul 2 25]
  have hzero : ∑ x ∈ range 14, ∑ z ∈ range 64,
      slotW (eqKernel (claim.point.drop P)) claim.weights 0 2 (2 * 25 + x) z *
        sliceMle P col (low ++ claim.point.take P) (2 * 25 + x) z = 0 :=
    Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun z _ ↦ by
      rw [slotW, ite_eq_right (by omega), zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  simp only [Gin_eq, sliceMle, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z hz ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  have hl' := Finset.mem_range.1 hl
  have hz' := Finset.mem_range.1 hz
  rw [slotW, ite_eq_left (show 25 * 0 ≤ 25 * m + l ∧ 25 * m + l < 25 * (0 + 2) ∧ z < 64 by
    omega)]
  have e3 : (25 * m + l) / 25 - 0 = m := by omega
  have e4 : (25 * m + l) % 25 = l := by omega
  rw [e3, e4, eqKernel_getD, hsd, ite_eq_left (by omega)]
  ring

theorem Fs_nil (col : ℕ → K) (claim : KeccakClaim) (hshape : ClaimShape P claim) {low : List E}
    (hlow : low.length = 4) :
    Fs P col claim low [] = MuT claim.mu low * PhiT P col claim low := by
  rw [Fs, cubeSum_nil, ← Finset.mul_sum, phi_eq P col claim hshape hlow]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun u hu ↦ Finset.sum_congr rfl fun z _ ↦ ?_)
  rw [Ws, Qs, sum_eqAt_bitsE (Finset.mem_range.1 hu), sum_eqAt_bitsE (Finset.mem_range.1 hu)]

/-- **The verifier's slot weights** after the fold are `W̃_z(ρ)`. -/
theorem fold_in (claim : KeccakClaim) {slot : List E} (hslot : slot.length = 6) {z : ℕ}
    (hz : z < 64) :
    ((foldAll slot (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD []).getD z 0 =
      Ws P claim z slot := by
  have hrows := slotWeights_length (P + 4) claim 0 keccakSegments (by decide)
  obtain ⟨-, -, h3⟩ := foldAll_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeights_row_length _ _ 0 keccakSegments (by decide) (by omega)
  rw [h3 z hz, Ws, hslot]
  refine Finset.sum_congr rfl fun o ho ↦ ?_
  rw [slotWeights_getD _ _ 0 keccakSegments (by decide) (Finset.mem_range.1 ho),
    show P + 4 - 4 = P by omega]
  rfl

theorem fold_in_length (claim : KeccakClaim) {slot : List E} (hslot : slot.length = 6) :
    ((foldAll slot (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD []).length = 64 := by
  have hrows := slotWeights_length (P + 4) claim 0 keccakSegments (by decide)
  exact (foldAll_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeights_row_length _ _ 0 keccakSegments (by decide) (by omega)).2.1

/-- The slices at `(λ, r_pack, ρ)` are `S̃_z(ρ)`. -/
theorem slices_eq (col : ℕ → K) {a slot : List E} (ha : a.length = P + 4) (hslot : slot.length = 6)
    (z : ℕ) :
    ∑ n ∈ range (2 ^ (P + 4 + 6)), eqAt (a ++ slot) n * bitE ((col n).toBitVec.getLsbD z) =
      Qs P col a z slot := by
  rw [← hslot, col_split ha, Qs, hslot]
  rfl

end
end LeanVM.Protocol.KeccakGkr
