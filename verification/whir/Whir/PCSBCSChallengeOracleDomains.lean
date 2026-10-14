import Whir.PCSBCSChallengeOracleSource

/-! Separate ideal challenge/Merkle domains are proved from the actual #552
node tag, not inferred from a purpose label. Actual tag-zero Merkle compression
inputs use the independent simulator seed table, never a challenge packet RO
request. Arbitrary other primitive observations are still allowed. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle
open FiatShamirGame DuplexFraming DuplexModeGame DuplexPublicSimulator

/-- Tag zero cannot be a #552 output/commitment/PoW terminal. -/
theorem merkle_tag_zero_not_terminal (input : Node) (zero : tag input = 0) :
    ¬isTerminal input := by
  simp [isTerminal, zero]

/-- For all logs, including malformed/adversarial logs, a Merkle node cannot
recognize a challenge construction key. Cache hits remain ordinary replays. -/
theorem merkle_no_challenge_key (Q : Nat) (log : PublicLog) (input : Node)
    (zero : tag input = 0) : privateKey Q log input = none := by
  have notTerminal := merkle_tag_zero_not_terminal input zero
  simp [privateKey, recognized, notTerminal]

/-- Fresh Merkle-domain calls query only the independent seed table. They
contribute zero PRIVATE challenge-RO requests, but still cost one PUBLIC
compression call and retain their entire observed 256-bit answer. -/
theorem fresh_merkle_ideal_answer (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : Seed) (log : PublicLog) (input : Node)
    (zero : tag input = 0) (fresh : lookup log input = none) :
    runRO ro ((simulator Q).answer ⟨seed,log⟩ input) =
      ((⟨seed,observe log input (seed input)⟩,seed input),0) := by
  simp [simulator, fresh, merkle_no_challenge_key Q log input zero, runRO]

open Classical in
/-- The whole ideal mixed table splits exactly into an independent seed table
and a challenge raw RO, preserving arbitrary payoffs of both domains. -/
theorem separate_domain_table (Q : Nat)
    (payoff : Seed × (RawKey Q → Digest32) → ℚ) :
    letI := seedFintype
    letI := rawOracleFintype Q
    letI := PublicCompressionCouplingMixed.mixedKeyFintype Q
    average (fun table : PublicCompressionCouplingMixed.Key Q → Digest32 =>
      payoff (PublicCompressionCouplingMixed.tableEquiv Q table)) = average payoff := by
  let := seedFintype
  let := rawOracleFintype Q
  let := PublicCompressionCouplingMixed.mixedKeyFintype Q
  exact RawOracleCoupling.average_equiv (PublicCompressionCouplingMixed.tableEquiv Q) payoff

#print axioms merkle_no_challenge_key
#print axioms fresh_merkle_ideal_answer
#print axioms separate_domain_table
end Whir.PCSBCSChallengeOracle
