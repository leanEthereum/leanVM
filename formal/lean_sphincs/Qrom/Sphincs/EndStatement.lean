module

public import Qrom.Sphincs.Numeric
public import Qrom.Sphincs.StatementGame

@[expose] public section

/-!
# The end statement in the quantum random-oracle model

`Sphincs.QuantumRandomOracleModel.LeanSphincsQromStronglyUnforgeable`
(`Statement/LeanSphincsQrom.lean`): the statement's game is at most the proof's on the translated
adversary (`Qrom.Sphincs.winProb_le_qrom`), which makes the same calls
(`Qrom.Sphincs.isTotalQueryBound_toQromAdversary`) and forges with probability at most
`((n + 2048) / 2^61.8)²` (`Qrom.Sphincs.winProb_le_h26`).
-/

namespace Qrom.Sphincs

/-- **leanSPHINCS in the quantum random-oracle model**, the end statement. -/
theorem leanSphincsQrom :
    _root_.Sphincs.QuantumRandomOracleModel.LeanSphincsQromStronglyUnforgeable := by
  intro A adv n hadv ρ
  exact (winProb_le_qrom adv ρ).trans
    (winProb_le_h26 (toQromAdversary adv) (isTotalQueryBound_toQromAdversary hadv) ρ)

end Qrom.Sphincs
