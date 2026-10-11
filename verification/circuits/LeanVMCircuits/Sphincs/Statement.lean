module

public import LeanVMCircuits.Xmss.Statement

@[expose] public section

/-!
# The statement of one leanSPHINCS signature

Signature `j`'s four statement words, in the order the circuit exposes them: the key's root, its public parameter
and the message's two halves, each an `E` word of two 64-bit limbs, a zero third limb and a zero top limb.
-/

namespace LeanVMCircuits.Sphincs

open LeanVMCircuits.Rec
open LeanVMCircuits.Xmss (limbs3)
open LeanVMCircuits.Xmss.Words (W Dig)

/-- Statement words `4j .. 4j + 3` are signature `j`'s root, public parameter and message. -/
def Encodes (st : ℕ → Fin 4 → K) (j : ℕ) (root pp : Dig) (msg : W × W × W × W) : Prop :=
  st (4 * j) = limbs3 root.1 root.2 0 ∧ st (4 * j + 1) = limbs3 pp.1 pp.2 0 ∧
  st (4 * j + 2) = limbs3 msg.1 msg.2.1 0 ∧ st (4 * j + 3) = limbs3 msg.2.2.1 msg.2.2.2 0

end LeanVMCircuits.Sphincs
