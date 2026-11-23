module

public import Quantum.StdModel.Qrom.CorollarySphincs
public import Quantum.StdModel.Qrom.SphincsItsr

@[expose] public section

/-!
# leanSPHINCS in the QROM through its standard-model properties

Theorem 2 over the restricted games, averaged over the QROM's tables, with each of its six
property terms bounded in the QROM at the reduction that uses it: the ITSR term at B3
(`SphItsr.probAvg_itsrRed_le_closed`) closes `leanSphincs_qrom_security_props_of_itsr_value`.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs

open Quantum.StdModel Props

/-- **leanSPHINCS's SUF-CMA in the QROM through its six named properties**: an adversary with `q`
hash calls and at most `signatureLimit` signing requests. -/
theorem leanSphincs_qrom_security_props_closed
    (A : Quantum.Qrom.SufCma.Adversary PublicKey Message (Option Signature) Forgery) {q : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
    (hs : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) signatureLimit) :
    Quantum.Qrom.SufCma.winProb Quantum.Qrom.Sphincs.sphincsRom A ≤
      ENNReal.ofReal (((5.86 * q + 2 ^ 33) ^ 2 + (2.45 * q + 21.01) ^ 2 +
        (5.001 * q + 3645) ^ 2 + (3.001 * q + 35451) ^ 2 + 10 * q + 2 ^ 68 + 2 ^ 67) /
          2 ^ 128) :=
  leanSphincs_qrom_security_props_of_itsr_value A hq hs (by norm_num [signatureLimit])
    (SphItsr.probAvg_itsrRed_le_closed A hq hs)

end Quantum.StdModel.Sphincs

end
