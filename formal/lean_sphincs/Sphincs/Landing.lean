import Sphincs.Uniform

/-! Exact probability that a fresh message digest lands in the kept subtree. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs

variable [Params]

theorem subtreePosition_lt (parameter : PublicParameter) :
    subtreePosition parameter < 2 ^ (totalHeight - subtreeHeight) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem subtree_size_mul : 2 ^ (totalHeight - subtreeHeight) * 2 ^ subtreeHeight =
    (2 : Nat) ^ totalHeight := by
  rw [← pow_add, Nat.sub_add_cancel Params.subtreeHeight_le]

/-- Local leaf numbers enumerate exactly the leaves accepted by the grinding test. -/
def keptLeafEquiv (parameter : PublicParameter) :
    Fin (2 ^ subtreeHeight) ≃ {i : Index // Landed parameter i} where
  toFun j := ⟨⟨subtreePosition parameter * 2 ^ subtreeHeight + j.val, by
    have hj := j.isLt
    have hs := subtreePosition_lt parameter
    have hmul := Nat.mul_le_mul_right (2 ^ subtreeHeight) (Nat.succ_le_of_lt hs)
    rw [subtree_size_mul] at hmul
    rw [Nat.succ_mul] at hmul
    omega⟩, by
      change (subtreePosition parameter * 2 ^ subtreeHeight + j.val) / 2 ^ subtreeHeight = _
      rw [Nat.mul_comm (subtreePosition parameter), Nat.mul_add_div (Nat.two_pow_pos _),
        Nat.div_eq_of_lt j.isLt, Nat.add_zero]⟩
  invFun i := ⟨i.val.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  left_inv j := by
    apply Fin.ext
    change (subtreePosition parameter * 2 ^ subtreeHeight + j.val) % 2 ^ subtreeHeight = j.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change subtreePosition parameter * 2 ^ subtreeHeight + i.val.val % 2 ^ subtreeHeight = _
    rw [← i.property, Nat.mul_comm, Nat.div_add_mod]

theorem landed_card (parameter : PublicParameter) :
    (Finset.univ.filter (Landed parameter)).card = 2 ^ subtreeHeight := by
  rw [← Fintype.card_subtype]
  rw [← Fintype.card_congr (keptLeafEquiv parameter), Fintype.card_fin]

omit [Params] in
theorem evalDist_blockIndex_uniform :
    (Concrete.blockIndex <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ Index : ProbComp Index) := by
  have heq : Concrete.blockIndex <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      BitVec.toFin <$> ((fun u : HashOutput => u.extractLsb' Concrete.indexOffset totalHeight) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) := by rw [Functor.map_map]; rfl
  rw [heq]
  exact ((evalDist_hashOutput_extractAt_uniform (by decide)).map BitVec.toFin).trans
    (SampleableType.map_uniformSample_evalDistEq_of_bijective (α := BitVec totalHeight) (β := Index)
      ⟨fun _ _ h => congrArg BitVec.ofFin h, fun i => ⟨BitVec.ofFin i, rfl⟩⟩)

/-- A fresh first message-digest block lands with probability exactly `2^b / 2^26`. -/
theorem fresh_landing_probability (parameter : PublicParameter) :
    Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[Landed parameter (Concrete.blockIndex u)] =
      ((2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ totalHeight : Nat) : ℝ≥0∞) := by
  rw [← prEvent_map, evalDist_blockIndex_uniform.prEvent_eq,
    SampleableType.prEvent_uniformSample, landed_card, Fintype.card_fin]

/-- Equivalently, the fresh landing probability is the reciprocal number of subtrees. -/
theorem fresh_landing_probability_inv (parameter : PublicParameter) :
    Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[Landed parameter (Concrete.blockIndex u)] =
      ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ := by
  rw [fresh_landing_probability, ← subtree_size_mul, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
    mul_comm ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹,
    ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

end Sphincs
