import FORS.Scheme.Uniform

/-! Exact probability that a fresh message digest lands in the kept subtree. -/

open OracleComp OracleSpec ENNReal

namespace FORS

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

theorem evalDist_blockIndex_uniform :
    𝒟[Concrete.blockIndex <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
    𝒟[($ᵗ Index : ProbComp Index)] := by
  have heq : Concrete.blockIndex <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      BitVec.toFin <$> ((fun u : HashOutput => u.extractLsb' 0 totalHeight) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) := by rw [Functor.map_map]; rfl
  rw [heq, evalDist_map, evalDist_hashOutput_extract_uniform totalHeight_le_hashOutput, ← evalDist_map]
  exact evalDist_map_bijective_uniform_cross (α := BitVec totalHeight) (β := Index) BitVec.toFin
    ⟨fun _ _ h => congrArg BitVec.ofFin h, fun i => ⟨BitVec.ofFin i, rfl⟩⟩

end FORS
