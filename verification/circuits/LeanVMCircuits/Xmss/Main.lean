import LeanVMCircuits.Xmss.Sound
import LeanVMCircuits.Xmss.Complete
import LeanVMCircuits.Xmss.Spec

/-!
# The leanXMSS circuit accepts exactly the specification's valid signatures

The circuit of `n` signatures (`Circuit.circuit n`) has a satisfying assignment for statement words `st` exactly when
for every `j < n` statement words `5j .. 5j + 4` state a public key, a message and an epoch for which some signature
passes the Ethereum XMSS specification's `verify` (`accepted_iff`). A statement word holds 64-bit words, and the
specification reads their little-endian bytes (`Spec.pk`, `Spec.message`); the epoch is its word.

The three layers meet at `Words.verify`: `sound` and `complete` relate the circuit to it, `Spec.verify_eq` relates it
to the specification, and the decoding lemmas (`Spec.signature_onto`, `Spec.publicKey_onto`, `Spec.message_onto`)
make every specification signature reachable.

This file imports the vendored specification, so it is not a module.
-/

namespace LeanVMCircuits.Xmss

open LeanVMCircuits.Rec LeanVMCircuits.Rec.Model EthCryptographySpecs.Xmss

/-- Statement words `5j .. 5j + 4` of `st` state the public key `p`, the message `m` and the epoch `e`: they encode
words whose bytes are `p` and `m`, and an epoch below `2 ^ 32` that is `e`. -/
def Statement (st : ℕ → Fin 4 → K) (j : ℕ) (p : PublicKey) (m : Message) (e : Epoch) : Prop :=
  ∃ pp root msg epoch, Encodes st j pp root msg epoch ∧ Spec.pk pp root = p ∧ Spec.message msg = m ∧
    UInt32.ofNat epoch = e

/-- The circuit of `n` signatures is satisfiable under statement words `st` exactly when each of its `n` statements
states a public key, a message and an epoch under which some signature passes the specification's `verify`. -/
theorem accepted_iff (n : ℕ) (st : ℕ → Fin 4 → K) :
    (∃ val, Sat st ((Circuit.circuit n).run {}).2 val) ↔
      ∀ j < n, ∃ (p : PublicKey) (m : Message) (e : Epoch), Statement st j p m e ∧
        ∃ s : Signature, EthCryptographySpecs.Xmss.verify p m s e = true := by
  constructor
  · rintro ⟨val, h⟩ j hj
    obtain ⟨pp, root, msg, epoch, he, sig, hv⟩ := sound n st val h j hj
    refine ⟨Spec.pk pp root, Spec.message msg, UInt32.ofNat epoch, ⟨pp, root, msg, epoch, he, rfl, rfl, rfl⟩,
      Spec.signature sig, ?_⟩
    rw [← Spec.verify_eq pp root msg epoch sig he.1, hv]
  · intro h
    apply complete n st
    intro j hj
    obtain ⟨p, m, e, ⟨pp, root, msg, epoch, he, rfl, rfl, rfl⟩, s, hv⟩ := h j hj
    obtain ⟨sig, rfl⟩ := Spec.signature_onto s
    exact ⟨pp, root, msg, epoch, he, sig, by rw [Spec.verify_eq pp root msg epoch sig he.1, hv]⟩

end LeanVMCircuits.Xmss
