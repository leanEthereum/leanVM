import LeanVMCircuits.Sphincs.Sound
import LeanVMCircuits.Sphincs.Complete
import LeanVMCircuits.Sphincs.Spec

/-!
# The leanSPHINCS circuit accepts exactly the specification's valid signatures

The circuit of `n` signatures (`Sphincs.Circuit.circuit n`) has a satisfying assignment for statement words `st`
exactly when for every `j < n` statement words `4j .. 4j + 3` state a public key and a message for which some
signature passes the leanSPHINCS specification's `verify`, the Lean transcription of the guest's verifier
(`accepted_iff`). A statement word holds 64-bit words, and the specification reads their little-endian bytes
(`Spec.pk`, `Spec.message`).

The three layers meet at `Sphincs.Words.verify`: `sound` and `complete` relate the circuit to it, `Spec.verify_eq`
relates it to the specification for counters below `2 ^ 32` (the only ones word verification accepts,
`Spec.counters_lt`), and the decoding lemmas (`Spec.signature_onto`, `Spec.publicKey_onto`, `Spec.message_onto`)
make every specification signature reachable.

This file imports the specification, so it is not a module.
-/

namespace LeanVMCircuits.Sphincs

open LeanVMCircuits.Rec LeanVMCircuits.Rec.Model

/-- Statement words `4j .. 4j + 3` of `st` state the public key `p` and the message `m`: they encode words whose
bytes are `p` and `m`. -/
def Statement (st : ℕ → Fin 4 → K) (j : ℕ) (p : LeanSphincs.PublicKey) (m : LeanSphincs.Message) : Prop :=
  ∃ root pp msg, Encodes st j root pp msg ∧ Spec.pk root pp = p ∧ Spec.message msg = m

/-- The circuit of `n` signatures is satisfiable under statement words `st` exactly when each of its `n` statements
states a public key and a message under which some signature passes the specification's `verify`. -/
theorem accepted_iff (n : ℕ) (st : ℕ → Fin 4 → K) :
    (∃ val, Sat st ((Sphincs.Circuit.circuit n).run {}).2 val) ↔
      ∀ j < n, ∃ (p : LeanSphincs.PublicKey) (m : LeanSphincs.Message), Statement st j p m ∧
        ∃ s : LeanSphincs.Signature, LeanSphincs.verify p m s = true := by
  constructor
  · rintro ⟨val, h⟩ j hj
    obtain ⟨root, pp, msg, he, sig, hv⟩ := sound n st val h j hj
    refine ⟨Spec.pk root pp, Spec.message msg, ⟨root, pp, msg, he, rfl, rfl⟩, Spec.signature sig, ?_⟩
    rw [← Spec.verify_eq root pp msg sig (Spec.counters_lt root pp msg sig hv), hv]
  · intro h
    apply complete n st
    intro j hj
    obtain ⟨p, m, ⟨root, pp, msg, he, rfl, rfl⟩, s, hv⟩ := h j hj
    obtain ⟨sig, hc, rfl⟩ := Spec.signature_onto s
    exact ⟨root, pp, msg, he, sig, by rw [Spec.verify_eq root pp msg sig hc, hv]⟩

end LeanVMCircuits.Sphincs
