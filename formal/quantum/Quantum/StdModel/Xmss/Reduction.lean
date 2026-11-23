module

public import Quantum.StdModel.Xmss.PrfRed
public import Quantum.StdModel.Xmss.EncRed
public import Quantum.StdModel.Xmss.CpreRed
public import Quantum.StdModel.Xmss.TcrRed

@[expose] public section

/-!
# Theorem 1: leanXMSS from four properties of Keccak-256, at every fixed table

For every oracle world `W`, every table `tab` and every quantum SUF-CMA adversary `A` with
classical signing queries, the winning probability of `A` against leanXMSS over the world's
Keccak-256 at `tab` is at most the sum of

* the KIM-PRF advantage of `prfRed W A` (design D1, composite key `S_0`, formats X2, X3, X4),
* the EncTCR$ success of `encRed W A` (design D5a, the WOTS+C encoding digest),
* the CPRE success of `cpreRed W A` (design D4, chains of length 3, adaptive openings),
* the SM-TCR-C success of `tcrRed W A` (design D3, the leaf compression and the node hash,
  with the chain step as evaluation function).

Each reduction runs `A` once, forwards its hash calls, answers its signing requests by classical
code, and makes `A`'s hash calls plus its honest work (`isChargeBound_slRed_hash`, and the
corollaries in the reduction files). At `tab = Keccak-f` (`keccakWorld`) this is the
standard-model statement (`xmss_suf_le_props_keccak`).
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props

theorem probAt_le_one (W : OracleWorld) (tab : W.Tab)
    (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) : W.probAt tab x ≤ 1 :=
  QuantumRuntime.outcomeLawWith_le_one _ _ x _ _ _

theorem succAt_ne_top {W : OracleWorld} {Q Pub Out : Type} {R : OracleSpec.{0, 0} Q}
    (E : Experiment W R Pub Out) (tab : W.Tab) (B : Adversary W R Pub Out) :
    E.succAt tab B ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (probAt_le_one W tab _)

/-- **Theorem 1 at a fixed table** of a world with fair coins. -/
theorem xmss_suf_le_props (W : OracleWorld) (hW : W.CoinsFair) (tab : W.Tab)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    (winProbAt W (xmssScheme W) tab A).toReal ≤
      xmssPrfAdv W tab (prfRed W A) +
        (encTcrSaltSucc W xmssEnc tab (encRed W A)).toReal +
        (cpreSucc W xmssChains noEval tab (cpreRed W A)).toReal +
        (smTcrSucc W xmssTcrC xmssTcrD tab (tcrRed W A)).toReal := by
  have hi := (idealProb_win_le W tab A).trans (add_le_add (add_le_add
    (idealProb_enc_le W hW tab A) (idealProb_tcr_le W hW tab A))
    (idealProb_cpre_le W hW tab A))
  rw [← prfIdeal_prfRed W hW] at hi
  have he := succAt_ne_top (encTcrSalt W xmssEnc) tab (encRed W A)
  have hc := succAt_ne_top (cpre W xmssChains noEval) tab (cpreRed W A)
  have ht := succAt_ne_top (smTcr W xmssTcrC xmssTcrD) tab (tcrRed W A)
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨he, ht⟩, hc⟩)
    hi
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨he, ht⟩) hc, ENNReal.toReal_add he ht] at hr
  rw [xmssPrfAdv, derivedKimPrfAdv, prfAdv, prfReal_prfRed W hW]
  linarith

/-- **Theorem 1 in the standard model**: the same bound at `keccakWorld`, whose hash is the
statement's Keccak-256 over Keccak-f[1600] (`keccakWorld_hashOf_eq_keccak256`). -/
theorem xmss_suf_le_props_keccak
    (A : SufAdversary keccakWorld PublicKey SigningRequest (Option Signature) Forgery) :
    (winProbAt keccakWorld (xmssScheme keccakWorld) () A).toReal ≤
      xmssPrfAdv keccakWorld () (prfRed keccakWorld A) +
        (encTcrSaltSucc keccakWorld xmssEnc () (encRed keccakWorld A)).toReal +
        (cpreSucc keccakWorld xmssChains noEval () (cpreRed keccakWorld A)).toReal +
        (smTcrSucc keccakWorld xmssTcrC xmssTcrD () (tcrRed keccakWorld A)).toReal :=
  xmss_suf_le_props keccakWorld keccakWorld_coinsFair () A

section Deployed

open LeanVM.Semantics (KeccakState keccakF1600)

/-- The statement's permutation `π = Keccak-f[1600]`, deterministically. -/
def keccakPi (s : KeccakState) : Id KeccakState :=
  pure (keccakF1600 s)

/-- **The scheme of Theorem 1 is the deployed leanXMSS**: in the standard model, key generation
of `xmssScheme keccakWorld` returns the statement's key generation over Keccak-f[1600]. -/
theorem keccak_generateKeys (S0 : MasterSeed) :
    simulateQ (keccakWorld.eager ()) ((xmssScheme keccakWorld).generateKeys S0) =
      pure (KeyGenerationAndSigning.keygenFromSeed keccakPi S0) :=
  (simulateQ_xmssOver_generateKeys keccakWorld () S0).trans
    (congrArg pure (Qrom.Xmss.keygenFromSeed_keccakHash keccakPi S0))

/-- The signer of `xmssScheme keccakWorld` is the statement's signer over Keccak-f[1600]. -/
theorem keccak_sign (sk : SecretKey) (req : SigningRequest) :
    simulateQ (keccakWorld.eager ()) ((xmssScheme keccakWorld).sign sk req) =
      pure (KeyGenerationAndSigning.sign keccakPi sk req.leafIndex req.message) :=
  (simulateQ_xmssOver_sign keccakWorld () sk req).trans
    (congrArg pure (Qrom.Xmss.sign_keccakHash keccakPi sk req.leafIndex req.message))

/-- The verifier of `xmssScheme keccakWorld` is the statement's verifier over Keccak-f[1600]. -/
theorem keccak_verify (pk : PublicKey) (F : Forgery) :
    simulateQ (keccakWorld.eager ()) ((xmssScheme keccakWorld).verify pk F) =
      pure (Verification.verify keccakPi pk F.message F.signature) :=
  (simulateQ_xmssOver_verify keccakWorld () pk F).trans
    (congrArg pure (Qrom.Xmss.verify_keccakHash keccakPi pk F.message F.signature))

end Deployed

end Quantum.StdModel.Xmss

end
