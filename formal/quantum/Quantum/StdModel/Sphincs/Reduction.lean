module

public import Quantum.StdModel.Sphincs.Prf
public import Quantum.StdModel.Sphincs.ItsrHop
public import Quantum.StdModel.Sphincs.EncHop
public import Quantum.StdModel.Sphincs.CpreHop
public import Quantum.StdModel.Sphincs.TcrHop

@[expose] public section

/-!
# Theorem 2: leanSPHINCS from six properties of Keccak-256, at every fixed table

For every oracle world `W` with fair coins, every table `tab` and every quantum SUF-CMA adversary
`A` with classical signing queries, the winning probability of `A` against leanSPHINCS over the
world's Keccak-256 at `tab` is at most the sum of

* the KIM-PRF advantage of `B1 W A` (design D1, key `SK.seed`, formats S1, S2, S3),
* the PRF_msg advantage of `B2 W A` (design D2, key `SK.prf`),
* the ITSR success of `itsrRed W A` (design D6, the message hash `H_msg`),
* the EncTCR+C success of `encRed W A` (design D5b, the WOTS+C encoding),
* the CPRE success of `cpreRed W A` (design D4, WOTS chains of length 3 with selective openings,
  FORS leaves with adaptive openings),
* the SM-TCR-C success of `tcrRed W A` (design D3, targets on `T_v`, `H` and `T_k`, with every
  tweakable hash, the chain step `F` included, as evaluation collection).

Each reduction runs `A` once, forwards its hash calls, answers its signing requests by classical
code, and makes `A`'s hash calls plus its honest work (the charge lemmas of the reduction files).
At `tab = Keccak-f` (`keccakWorld`) this is the standard-model statement
(`sphincs_suf_le_props_keccak`), and the scheme is the deployed leanSPHINCS
(`keccak_generateKeys`, `keccak_sign`, `keccak_verify`).
-/

open OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Qrom.Sphincs (sphincsOver)

namespace Quantum.StdModel.Sphincs

open Quantum.StdModel Props

private theorem probAt_le_one' (W : OracleWorld) (tab : W.Tab)
    (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) : W.probAt tab x ≤ 1 :=
  QuantumRuntime.outcomeLawWith_le_one _ _ x _ _ _

private theorem succAt_ne_top' {W : OracleWorld} {Q Pub Out : Type} {R : OracleSpec.{0, 0} Q}
    (E : Experiment W R Pub Out) (tab : W.Tab) (B : Adversary W R Pub Out) :
    E.succAt tab B ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (probAt_le_one' W tab _)

/-- **Theorem 2 at a fixed table** of a world with fair coins. -/
theorem sphincs_suf_le_props (W : OracleWorld) (hW : W.CoinsFair) (tab : W.Tab) (A : SAdv W) :
    (winProbAt W (sphincsOver W.hash) tab A).toReal ≤
      kimPrfAdv W (Key := MasterSeed) kimFmt (littleEndianBytes 32) kimTrunc tab (B1 W A) +
        prfMsgAdv W (Key := HashOutput) msgBytes (littleEndianBytes 32) truncateHash tab
          (B2 W A) +
        (itsrSucc W itsrMap tab (itsrRed W A)).toReal +
        (encTcrCtrSucc W encCtr slotColl tab (encRed W A)).toReal +
        (cpreSucc W cpreChains slotColl tab (cpreRed W A)).toReal +
        (smTcrSucc W tcrColl slotColl tab (tcrRed W A)).toReal := by
  have hi := (ideal_win_le W tab A).trans (add_le_add (add_le_add (add_le_add
    (ideal_itsr_le W tab A hW) (ideal_enc_le W tab A hW)) (ideal_tcr_le W tab A hW))
    (ideal_cpre_le W tab A hW))
  have h1 := succAt_ne_top' (itsr W itsrMap) tab (itsrRed W A)
  have h2 := succAt_ne_top' (encTcrCtr W encCtr slotColl) tab (encRed W A)
  have h3 := succAt_ne_top' (smTcr W tcrColl slotColl) tab (tcrRed W A)
  have h4 := succAt_ne_top' (cpre W cpreChains slotColl) tab (cpreRed W A)
  have h12 := ENNReal.add_ne_top.mpr ⟨h1, h2⟩
  have h123 := ENNReal.add_ne_top.mpr ⟨h12, h3⟩
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h123, h4⟩) hi
  rw [ENNReal.toReal_add h123 h4, ENNReal.toReal_add h12 h3, ENNReal.toReal_add h1 h2] at hr
  have hk := kimPrfAdv_B1 W tab hW A
  have hm := prfMsgAdv_B2 W tab hW A
  simp only [itsrSucc, encTcrCtrSucc, cpreSucc, smTcrSucc] at hr ⊢
  linarith

/-- **Theorem 2 in the standard model**: the same bound at `keccakWorld`, whose hash is the
statement's Keccak-256 over Keccak-f[1600] (`keccakWorld_hashOf_eq_keccak256`). -/
theorem sphincs_suf_le_props_keccak (A : SAdv keccakWorld) :
    (winProbAt keccakWorld (sphincsOver keccakWorld.hash) () A).toReal ≤
      kimPrfAdv keccakWorld (Key := MasterSeed) kimFmt (littleEndianBytes 32) kimTrunc ()
          (B1 keccakWorld A) +
        prfMsgAdv keccakWorld (Key := HashOutput) msgBytes (littleEndianBytes 32) truncateHash
          () (B2 keccakWorld A) +
        (itsrSucc keccakWorld itsrMap () (itsrRed keccakWorld A)).toReal +
        (encTcrCtrSucc keccakWorld encCtr slotColl () (encRed keccakWorld A)).toReal +
        (cpreSucc keccakWorld cpreChains slotColl () (cpreRed keccakWorld A)).toReal +
        (smTcrSucc keccakWorld tcrColl slotColl () (tcrRed keccakWorld A)).toReal :=
  sphincs_suf_le_props keccakWorld keccakWorld_coinsFair () A

section Deployed

open LeanVM.Semantics (KeccakState keccakF1600)
open HashSig.OverPermutation (keccakHash)

/-- The statement's permutation `π = Keccak-f[1600]`, deterministically. -/
def keccakPi (s : KeccakState) : Id KeccakState :=
  pure (keccakF1600 s)

/-- The world's hash at `keccakWorld` is Keccak-256 over `keccakPi`. -/
theorem keccakHash_keccakPi :
    (fun l ↦ keccakWorld.hashOf () l : HashInput → Id HashOutput) = keccakHash keccakPi :=
  funext fun _ ↦ rfl

/-- **The scheme of Theorem 2 is the deployed leanSPHINCS**: in the standard model, key generation
of `sphincsOver keccakWorld.hash` returns the statement's key generation over Keccak-f[1600]. -/
theorem keccak_generateKeys (S0 : MasterSeed) :
    simulateQ (keccakWorld.eager ()) ((sphincsOver keccakWorld.hash).generateKeys S0) =
      pure (KeyGenerationAndSigning.keygenFromSeed keccakPi S0) := by
  have h1 : Qrom.Sphincs.LeanSphincsOver.keygenFromSeed (m := Id)
      (fun l ↦ keccakWorld.hashOf () l) S0 = pure ((realTable keccakWorld () S0).publicKey, S0) :=
    keygenFromSeed_seedTable (m := Id) (h := keccakWorld.hashOf ()) (fun _ ↦ rfl) S0
  rw [keccakHash_keccakPi, Qrom.Sphincs.LeanSphincsOver.keygenFromSeed_keccakHash] at h1
  exact (simulateQ_generateKeys_eager keccakWorld () S0).trans (congrArg pure h1.symm)

/-- The signer of `sphincsOver keccakWorld.hash` is the statement's signer over
Keccak-f[1600]. -/
theorem keccak_sign (sk : SecretKey) (M : Message) :
    simulateQ (keccakWorld.eager ()) ((sphincsOver keccakWorld.hash).sign sk M) =
      pure (KeyGenerationAndSigning.sign keccakPi sk M) := by
  have h1 : Qrom.Sphincs.LeanSphincsOver.sign (m := Id) (fun l ↦ keccakWorld.hashOf () l) sk M =
      pure ((realTable keccakWorld () sk).signature (cellHash (keccakWorld.hashOf ())) M) :=
    sign_seedTable (m := Id) (h := keccakWorld.hashOf ()) (fun _ ↦ rfl) sk M
  rw [keccakHash_keccakPi, Qrom.Sphincs.LeanSphincsOver.sign_keccakHash] at h1
  exact (simulateQ_sign_eager keccakWorld () sk M).trans (congrArg pure h1.symm)

/-- The verifier of `sphincsOver keccakWorld.hash` is the statement's verifier over
Keccak-f[1600]. -/
theorem keccak_verify (pk : PublicKey) (F : Forgery) :
    simulateQ (keccakWorld.eager ()) ((sphincsOver keccakWorld.hash).verify pk F) =
      pure (Verification.verify keccakPi pk F.message F.signature) :=
  (simulateQ_verify_eager keccakWorld () pk F).trans (congrArg pure
    (congrFun (congrFun (congrFun (Qrom.Sphincs.LeanSphincsOver.verify_keccakHash keccakPi) pk)
      F.message) F.signature))

end Deployed

end Quantum.StdModel.Sphincs

end
