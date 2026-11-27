module

public import XmssSecurity.Model
public import XmssSecurity.Game
import EthLib.Cryptography.Proofs.Xmss.Correctness

/-!
# leanXMSS in the random-permutation model

The statement's leanXMSS is EthLib's, and so is its theorem. With the stateless signer, an
adversary making at most `q` own calls of a random permutation of EthLib's Keccak state and at most
`2^32` requests forges with probability at most `(q + 319) · 2^-127`
(`EthLib.Cryptography.Xmss.Unforgeability.stronglyUnforgeable_randomPermutationModel_stateless`).
The statement's adversary, its oracles relabelled, is an adversary of EthLib's game
(`toEthLibAdversary`): its game is EthLib's (`forgeryGame_eq`), run in leanVM's model with the law
of EthLib's (`runWithRandomPermutation_simulateQ_ethLibOracles`), its bounds carry over, and
`319 ≤ 2^10`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Common Common.SufCma
open EthLib.Cryptography.Hash.Keccak (State)

namespace XmssSecurity

/-- **leanXMSS is strongly unforgeable in the random-permutation model**
(`LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable`). -/
theorem leanXmss_rpm_security : LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable := by
  intro q adversary hq hn
  -- The statement's game is EthLib's game of the relabelled adversary, run in EthLib's model.
  have hmodel := runWithRandomPermutation_simulateQ_ethLibOracles
    (EthLib.Cryptography.SufCma.game EthLib.Cryptography.Xmss.Unforgeability.schemeRpmStateless
      (toEthLibAdversary adversary))
  rw [forgeryGame_eq, (EvalDistEq.of_evalDist_eq hmodel).prEvent_eq (fun b => b = true),
    ← EthLib.Cryptography.SufCma.advantage]
  -- EthLib's bound, and `319 ≤ 2^10`.
  refine
      (EthLib.Cryptography.Xmss.Unforgeability.stronglyUnforgeable_randomPermutationModel_stateless
    q _ (fun pk => isQueryBoundP_toEthLibAdversary_hash (hq pk))
    (fun pk => isQueryBoundP_toEthLibAdversary_request (hn pk))).trans ?_
  gcongr
  norm_num [LeanXmss.RandomPermutationModel.securitySlack]

/-- The hash `verifyWithKeccak` runs: EthLib's leanXMSS hash over Keccak-f[1600], in `Id`. -/
abbrev deployedXmssHash : Array UInt64 → EthLib.Cryptography.Hash.Keccak.Lanes4 :=
  fun lanes ↦ Id.run (LeanXmss.xmssHash (m := Id) LeanVM.Semantics.keccakF1600 lanes)

/-- **The statement's verifier accepts honest signatures**: a signature that the signer makes with
the key of key generation, both over Keccak-f[1600], verifies under the public key. So the bound
above is about a scheme whose verifier accepts every signature its signer returns (correctness). -/
theorem verifyWithKeccak_of_signWith {seed : EthLib.Cryptography.Xmss.Seed}
    {idx : EthLib.Cryptography.Xmss.LeafIndex} {message : EthLib.Cryptography.Xmss.Message}
    {signature : EthLib.Cryptography.Xmss.Signature}
    (hsign : (EthLib.Cryptography.Xmss.signWith
      (EthLib.Cryptography.HashSig.pureHash deployedXmssHash)
      (EthLib.Cryptography.Xmss.keyGenWith (EthLib.Cryptography.HashSig.pureHash deployedXmssHash)
        seed).run.2 idx message).run.1 = .ok signature) :
    LeanXmss.verifyWithKeccak
      (EthLib.Cryptography.Xmss.keyGenWith (EthLib.Cryptography.HashSig.pureHash deployedXmssHash)
        seed).run.1 message signature = true :=
  EthLib.Cryptography.Xmss.verifyWith_keyGenWith_signWith .keyGen hsign

end XmssSecurity

end
