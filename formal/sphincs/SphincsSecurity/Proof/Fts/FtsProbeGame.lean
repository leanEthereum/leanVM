import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeSimulation
namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

theorem sibling_node_bound (height leaf level : Nat)
    (hlevel : level < height) (hleaf : leaf < 2 ^ height) :
    2 ^ level * (Nat.xor (leaf / 2 ^ level) 1 + 1) ≤ 2 ^ height := by
  let bound := 2 ^ (height - level)
  have hquotient : leaf / 2 ^ level < bound := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos level)).2
    change leaf < 2 ^ (height - level) * 2 ^ level
    rw [← pow_add]
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hlevel)] using hleaf
  have hboundEven : ∃ half, bound = 2 * half := by
    refine ⟨2 ^ (height - level - 1), ?_⟩
    change 2 ^ (height - level) = _
    rw [show height - level = (height - level - 1) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  have hsibling : Nat.xor (leaf / 2 ^ level) 1 < bound := by
    obtain ⟨parent, hcase⟩ := index_sibling_cases (leaf / 2 ^ level)
    obtain ⟨half, hbound⟩ := hboundEven
    rcases hcase with hcase | hcase <;> omega
  calc
    2 ^ level * (Nat.xor (leaf / 2 ^ level) 1 + 1) ≤ 2 ^ level * bound :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hsibling)
    _ = 2 ^ height := by
      change 2 ^ level * 2 ^ (height - level) = _
      rw [← pow_add]
      congr 1
      omega

end SphincsSecurity.Concrete.FtsProbeSimulation
