module

public import LeanVMCircuits.Xmss.Words

@[expose] public section

/-!
# The statement of one signature

Signature `j`'s five statement words, as the circuit exposes them: the public parameter, the message's two halves,
the epoch and the root, each an `E` word of up to three 64-bit limbs and a zero top limb.
-/

namespace LeanVMCircuits.Xmss

open LeanVMCircuits.Rec Words

/-- Three 64-bit words as the four `K` limbs of a statement word, the top limb zero. -/
noncomputable def limbs3 (a b c : W) : Fin 4 → K := ![ofWord a.toNat, ofWord b.toNat, ofWord c.toNat, 0]

/-- Statement words `5j .. 5j + 4` are signature `j`'s public parameter, message, epoch and root. -/
def Encodes (st : ℕ → Fin 4 → K) (j : ℕ) (pp root : Dig) (msg : W × W × W × W) (epoch : ℕ) : Prop :=
  epoch < 2 ^ 32 ∧ st (5 * j) = limbs3 pp.1 pp.2 0 ∧ st (5 * j + 1) = limbs3 msg.1 msg.2.1 0 ∧
  st (5 * j + 2) = limbs3 msg.2.2.1 msg.2.2.2 0 ∧ st (5 * j + 3) = limbs3 (BitVec.ofNat 64 epoch) 0 0 ∧
  st (5 * j + 4) = limbs3 root.1 root.2 0

end LeanVMCircuits.Xmss
