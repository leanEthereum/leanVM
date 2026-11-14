/-
  LeanVM.Protocol.Keccak.LayerAlg

  The algebra of a layer's first two steps: a claim on the states after a round, the honest
  product polynomial `G`, its projection (the round's χ and ι on the claim), and its value at
  the evaluation point.
-/

module

public import LeanVM.Protocol.Keccak.Rmfe

/-!
# A layer: the product polynomial

States are given by segment `m`, step `x` and position `j` (`States`). A claim
`(value, μ, point, w)` on states `st` (`ClaimTrue`, `doc/leanvm` eq. `keccak:eq:claim` with the
segment coordinate of §`keccak:segments`) is

  `value = Σ_{z < 2^(P+1)} eq(point, z) Σ_{i < 16} μ_i Σ_{j < 1600} w_j · st(m, x, j)`,

`z = y + 2^P·m` (pack `y`, segment `m`), step `x = i + 16y`. For a layer at `step`, the states
after the round are `roundB (layerRC step m)` of the states `T` before it (`afterRound`); with
`b = L(T)` the bits entering χ and `S_{z,j} = Σ_i b(z, i, j)·emb_i` the honest product polynomial
is (`Gpoly`, eq. `keccak:eq:product`)

  `G = Σ_z eq(point, z) Σ_j w_j (κ·S_{z,j} + (κ + S_{z,j+1})·S_{z,j+2})`,  `κ = Σ_i emb_i`.

* `claimSum_round`: the claim's sum on the states after the round is
  `Σ_i μ_i · projE_i(G) + (Σ_m eq(point_P, m)·ι_m(w)) · Σ_i μ_i` (eq. `keccak:eq:projection`);
* `iota_eq`: the verifier's `iota` is `Σ_m eq(point_P, m)·ι_m(w)`;
* `eval_Gpoly`: `G(s)` is the χ of the packs' states at `s` (eq. `keccak:eq:at-s`);
* `natDegree_Gpoly`: `G` has degree at most `46`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete Finset Polynomial

@[expose] public section

/-! ## Claims -/

/-- States by segment, step and position. -/
abbrev States : Type := ℕ → ℕ → ℕ → Bool

/-- The state of the index `z` (pack `z mod 2^P`, segment `z / 2^P`) and instance `i`. -/
def stAt (st : States) (P z i : ℕ) : ℕ → Bool := st (z / 2 ^ P) (i + 16 * (z % 2 ^ P))

/-- A claim's sum on the states `st`. -/
def claimSum (st : States) (P : ℕ) (point mu w : List E) : E :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ i ∈ range 16, mu.getD i 0 *
    ∑ j ∈ range 1600, w.getD j 0 * bitE (stAt st P z i j)

/-- **A true claim** on the states `st`. -/
def ClaimTrue (st : States) (P : ℕ) (c : KeccakClaim) : Prop :=
  c.value = claimSum st P c.point c.mu c.weights

/-- A claim's sum reads the states at segments `0, 1` and positions below `1600` only. -/
theorem claimSum_congr {st st' : States} (P : ℕ)
    (h : ∀ m x j, m < 2 → j < 1600 → st m x j = st' m x j) (point mu w : List E) :
    claimSum st P point mu w = claimSum st' P point mu w := by
  unfold claimSum
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hm : z / 2 ^ P < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have := Finset.mem_range.1 hz
    rw [pow_succ] at this
    linarith
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun i _ ↦ congrArg (HMul.hMul _)
    (Finset.sum_congr rfl fun j hj ↦ ?_))
  rw [stAt, stAt, h _ _ _ hm (Finset.mem_range.1 hj)]

/-- The round constant of segment `m` at layer `step` (`crates/verifier/src/keccak.rs`): round
`12(m + 1) - step - 1`. -/
def layerRC (step m : ℕ) : UInt64 := keccakRC.getD (keccakDepth * (m + 1) - step - 1) 0

/-- The states after the layer's round. -/
def afterRound (T : States) (step : ℕ) : States := fun m x j ↦ roundB (layerRC step m) (T m x) j

/-! ## The product polynomial -/

/-- A pack's bits entering χ at position `j`, embedded: `Σ_i b(z, i, j)·emb_i`. -/
noncomputable def SP (T : States) (P z j : ℕ) : E[X] :=
  ∑ i ∈ range 16, C (bitE (Lb (stAt T P z i) j)) * embP i

/-- `κ = emb(1, …, 1)`. -/
noncomputable def kP : E[X] := ∑ i ∈ range 16, C 1 * embP i

/-- χ on the packs' embeddings at position `j`. -/
noncomputable def Gterm (T : States) (P z j : ℕ) : E[X] :=
  kP * SP T P z j + (kP + SP T P z (keccakAlong j 1)) * SP T P z (keccakAlong j 2)

/-- **The honest product polynomial**. -/
noncomputable def Gpoly (T : States) (P : ℕ) (point w : List E) : E[X] :=
  ∑ z ∈ range (2 ^ (P + 1)), C (eqAt point z) *
    ∑ j ∈ range 1600, C (w.getD j 0) * Gterm T P z j

theorem kP_add_SP (T : States) (P z j : ℕ) :
    kP + SP T P z j = ∑ i ∈ range 16, C (1 + bitE (Lb (stAt T P z i) j)) * embP i := by
  rw [kP, SP, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [C_add]; ring

/-- The projection of χ on the embeddings is χ on bits. -/
theorem projE_Gterm (T : States) (P z j : ℕ) {i : ℕ} (hi : i < 16) :
    projE (rmfeProject.getD i 0) (Gterm T P z j) = bitE (chiB (Lb (stAt T P z i)) j) := by
  rw [Gterm, projE_add, kP_add_SP, kP, SP, SP, projE_bilin hi, projE_bilin hi, chiB, bitE_xor,
    bitE_and, bitE_not, one_mul]

theorem projE_Gpoly (T : States) (P : ℕ) (point w : List E) {i : ℕ} (hi : i < 16) :
    projE (rmfeProject.getD i 0) (Gpoly T P point w) =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z *
        ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) := by
  rw [Gpoly, projE_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [projE_C_mul, projE_sum]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [projE_C_mul, projE_Gterm T P z j hi]

theorem natDegree_SP (T : States) (P z j : ℕ) : (SP T P z j).natDegree ≤ 23 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_le _ _).trans (embP_natDegree i)

theorem natDegree_kP : kP.natDegree ≤ 23 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_le _ _).trans (embP_natDegree i)

theorem natDegree_Gterm (T : States) (P z j : ℕ) : (Gterm T P z j).natDegree ≤ 46 := by
  unfold Gterm
  refine natDegree_add_le_of_degree_le ?_ ?_
  · exact natDegree_mul_le_of_le natDegree_kP (natDegree_SP T P z j)
  · exact natDegree_mul_le_of_le (natDegree_add_le_of_degree_le natDegree_kP (natDegree_SP _ _ _ _))
      (natDegree_SP T P z _)

theorem natDegree_Gpoly (T : States) (P : ℕ) (point w : List E) :
    (Gpoly T P point w).natDegree ≤ 46 :=
  natDegree_sum_le_of_forall_le _ _ fun z _ ↦ (natDegree_C_mul_le _ _).trans
    (natDegree_sum_le_of_forall_le _ _ fun j _ ↦ (natDegree_C_mul_le _ _).trans
      (natDegree_Gterm T P z j))

/-! ## The projection check -/

/-- ι's weight: `Σ_{z < 64, RC bit z} w_z`. -/
def iotaW (rc : UInt64) (w : List E) : E :=
  ∑ z ∈ range 64, if rc.toNat.testBit z then w.getD z 0 else 0

theorem sum_iotaB (rc : UInt64) (w : List E) :
    ∑ j ∈ range 1600, w.getD j 0 * bitE (iotaB rc j) = iotaW rc w := by
  rw [show 1600 = 64 + 1536 from rfl, Finset.sum_range_add]
  have h2 : ∑ x ∈ range 1536, w.getD (64 + x) 0 * bitE (iotaB rc (64 + x)) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by simp [iotaB]
  rw [h2, add_zero, iotaW]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have e : rc.toNat.testBit z = rc.toBitVec.getLsbD z := rfl
  rw [iotaB, e]
  cases rc.toBitVec.getLsbD z <;> simp [hz']

/-- A sum over the (pack, segment) indices of a function of the segment. -/
theorem sum_segment {P : ℕ} {point : List E} (hpt : point.length = P + 1) (f : ℕ → E) :
    ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * f (z / 2 ^ P) =
      ∑ m ∈ range 2, eqAt (point.drop P) m * f m := by
  have hsplit : point = point.take P ++ point.drop P := (List.take_append_drop P point).symm
  have htl : (point.take P).length = P := by simp [hpt]
  rw [pow_succ, mul_comm, sum_range_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  have h1 : ∀ y ∈ range (2 ^ P), eqAt point (2 ^ P * m + y) * f ((2 ^ P * m + y) / 2 ^ P) =
      eqAt (point.take P) y * (eqAt (point.drop P) m * f m) := by
    intro y hy
    have hy' := Finset.mem_range.1 hy
    have hd : (2 ^ P * m + y) / 2 ^ P = m := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hy', zero_add]
    conv_lhs => rw [hsplit]
    rw [eqAt_append, htl, hd, eqAt_mod (point.take P), htl,
      Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
    ring
  have hs : ∑ y ∈ range (2 ^ P), eqAt (point.take P) y = 1 := by
    have := sum_eqAt (point.take P); rwa [htl] at this
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, hs, one_mul]

/-- The claim's sum after the round: the projection of `G` and ι's known bits
(eq. `keccak:eq:projection`). -/
theorem claimSum_round (T : States) (step P : ℕ) (point mu w : List E)
    (hpt : point.length = P + 1) :
    claimSum (afterRound T step) P point mu w =
      ∑ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) +
        (∑ m ∈ range 2, eqAt (point.drop P) m * iotaW (layerRC step m) w) *
          ∑ i ∈ range 16, mu.getD i 0 := by
  have hb : ∀ z i j, bitE (stAt (afterRound T step) P z i j) =
      bitE (chiB (Lb (stAt T P z i)) j) + bitE (iotaB (layerRC step (z / 2 ^ P)) j) := by
    intro z i j
    rw [stAt, afterRound, roundB, bitE_xor]
    rfl
  have e1 : claimSum (afterRound T step) P point mu w =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ i ∈ range 16, mu.getD i 0 *
        ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) +
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * (∑ i ∈ range 16, mu.getD i 0) *
        iotaW (layerRC step (z / 2 ^ P)) w := by
    rw [claimSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have : ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
          bitE (stAt (afterRound T step) P z i j) =
        ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
          bitE (chiB (Lb (stAt T P z i)) j) +
        (∑ i ∈ range 16, mu.getD i 0) * iotaW (layerRC step (z / 2 ^ P)) w := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [hb, mul_add, Finset.sum_add_distrib, sum_iotaB]
    rw [this]
    ring
  have p1 : ∑ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ i ∈ range 16, mu.getD i 0 *
        ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) := by
    have h : ∀ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) =
        mu.getD i 0 * ∑ z ∈ range (2 ^ (P + 1)), eqAt point z *
          ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) :=
      fun i hi ↦ by rw [projE_Gpoly T P point w (Finset.mem_range.1 hi)]
    rw [Finset.sum_congr rfl h]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ by ring
  have p2 : ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * (∑ i ∈ range 16, mu.getD i 0) *
        iotaW (layerRC step (z / 2 ^ P)) w =
      (∑ m ∈ range 2, eqAt (point.drop P) m * iotaW (layerRC step m) w) *
        ∑ i ∈ range 16, mu.getD i 0 := by
    rw [← sum_segment hpt (fun m ↦ iotaW (layerRC step m) w), Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  rw [e1, p1, p2]

/-- **The verifier's `iota`** (`keccak.rs`). -/
theorem iota_eq (step P : ℕ) (point w : List E) (hpt : point.length = P + 1) :
    sumE ((List.range keccakSegments).map fun segment ↦
      (eqKernel (point.drop P)).getD segment 0 *
        sumE ((List.range 64).filterMap fun z ↦
          if (keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0).toNat.testBit z then
            some (w.getD z 0) else none)) =
      ∑ m ∈ range 2, eqAt (point.drop P) m * iotaW (layerRC step m) w := by
  have hl : (point.drop P).length = 1 := by simp [hpt]
  rw [sumE_eq_sum, list_sum_range, show keccakSegments = 2 from rfl]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [eqKernel_getD, hl, ite_eq_left (by simpa using hm), sumE_filterMap_range]
  rfl

/-! ## The value at the evaluation point -/

/-- A pack's state entering χ at `s`: `Σ_i emb_i(s)·b(z, i, j)`. -/
noncomputable def Shat0 (T : States) (P : ℕ) (s : E) (z j : ℕ) : E :=
  ∑ i ∈ range 16, (embP i).eval s * bitE (Lb (stAt T P z i) j)

/-- `κ(s) = Σ_i emb_i(s)`. -/
noncomputable def kappaAt (s : E) : E := ∑ i ∈ range 16, (embP i).eval s

/-- **`G(s)`** is χ of the packs' states at `s` (eq. `keccak:eq:at-s`). -/
theorem eval_Gpoly (T : States) (P : ℕ) (point w : List E) (s : E) :
    (Gpoly T P point w).eval s =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ j ∈ range 1600, w.getD j 0 *
        (kappaAt s * Shat0 T P s z j + (kappaAt s + Shat0 T P s z (keccakAlong j 1)) *
          Shat0 T P s z (keccakAlong j 2)) := by
  simp only [Gpoly, Gterm, kP, SP, eval_finsetSum, eval_mul, eval_C, eval_add,
    one_mul, Shat0, kappaAt]
  refine Finset.sum_congr rfl fun z _ ↦ congrArg (HMul.hMul _) (Finset.sum_congr rfl fun j _ ↦
    congrArg (HMul.hMul _) ?_)
  simp only [mul_comm]

/-- The coefficients of `G`, as the honest prover sends them. -/
@[irreducible] noncomputable def gList (G : E[X]) : List E := (List.range 47).map G.coeff

theorem gList_length (G : E[X]) : (gList G).length = 47 := by simp [gList]

theorem gList_getD (G : E[X]) {c : ℕ} (hc : c < 47) : (gList G).getD c 0 = G.coeff c := by
  simp [gList, List.getD_eq_getElem?_getD, hc]

theorem polyEval_gList {G : E[X]} (hG : G.natDegree ≤ 46) (s : E) :
    polyEval (gList G) s = G.eval s := by
  rw [polyEval_eq_sum, gList_length, eval_eq_sum_range' (n := 47) (by omega)]
  exact Finset.sum_congr rfl fun c hc ↦ by rw [gList_getD G (Finset.mem_range.1 hc)]

end
end LeanVM.Protocol.KeccakGkr
