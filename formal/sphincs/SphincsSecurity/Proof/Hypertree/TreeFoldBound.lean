import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity.Concrete

theorem fold_node_bound (height level index : Nat) (hlevel : level < height) (hindex : index < 2 ^ height) :
    2 ^ (level + 1) * (index / 2 ^ (level + 1) + 1) ≤ 2 ^ height := by
  have hpow : (2 : Nat) ^ height = 2 ^ (level + 1) * 2 ^ (height - (level + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt hlevel)]
  have hdiv : index / 2 ^ (level + 1) < 2 ^ (height - (level + 1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [hpow, Nat.mul_comm] using hindex
  exact (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hdiv)).trans_eq hpow.symm

end SphincsSecurity.Concrete
