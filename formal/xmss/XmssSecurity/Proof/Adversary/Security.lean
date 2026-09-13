import XmssSecurity.Proof.Adversary.Embedding
import XmssSecurity.Proof.Deterministic.Security

open OracleComp OracleSpec ENNReal
namespace XmssSecurity.Security

set_option backward.isDefEq.respectTransparency false

/-- The embedding preserves both the winning event and the complete hash-query budget. -/
theorem security127 : HasClassicalSecurityBits 127 := by
  intro q hq adversary hbound
  rw [← advantage_embed]
  apply Seeded.scheme_has_127_bits_of_classical_security q hq
  change ∀ result ∈ support ((simulateQ countedRomImpl
    (XmssSecurity.gameCore Seeded.scheme (embed adversary))).run.run' ∅), result.2 ≤ q
  rw [experiment_embed]
  exact hbound

attribute [local irreducible] experiment

/-- Sampling a deterministic strategy independently of the experiment preserves the security bound. -/
theorem randomized_security127 (strategies : ProbComp Adversary) (q : Nat) (hq : 1 ≤ q)
    (hbound : ∀ result ∈ support (strategies >>= experiment), result.2 ≤ q) :
    Pr[fun result => result.1 = true | strategies >>= experiment] ≤
      q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  apply probEvent_bind_le_of_forall_le
  intro adversary ha
  apply security127 q hq adversary
  intro result hr
  apply hbound result
  rw [mem_support_bind_iff]
  exact ⟨adversary, ha, hr⟩

end XmssSecurity.Security
