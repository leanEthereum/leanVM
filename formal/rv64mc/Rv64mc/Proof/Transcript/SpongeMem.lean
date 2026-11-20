/-
  Rv64mc.Proof.Transcript.SpongeMem

  What `Sponge::duplex`'s and `Sponge::new`'s proofs share: a slot of the stack as a number (`slot_toNat`), the
  ground challenge read back from words that agree (`OptionEAt.congr`).
-/

import Rv64mc.Proof.Transcript.Common

namespace Rv64mc.Proof.Transcript

open RiscvZkvm.Rv64 Rv64mc.Spec.Transcript

/-- `t - k`, as a stack slot's literal offset. -/
theorem slot_toNat {t c : Word} {k : Nat} (hc : c = BitVec.ofNat 64 (2 ^ 64 - k)) (hk : k ≤ t.toNat) (hk0 : 0 < k) :
    (t + c).toNat = t.toNat - k := by
  rw [hc]; exact toNat_sub_lit hk hk0

/-- **An `Option<E>` read back from words that agree.** -/
theorem OptionEAt.congr {m M : MachineState} {a : Word} {o : Option LeanVM.Parameters.E} (h : OptionEAt m a o)
    (hk : ∀ k, k < 24 → M.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k)) :
    OptionEAt M a o := by
  cases o with
  | none =>
    simp only [OptionEAt, Layouts.OptionE.tagOffset, Layouts.OptionE.None.tag] at h ⊢
    rw [hk 0 (by decide)]; exact h
  | some e =>
    simp only [OptionEAt, EAt, Layouts.OptionE.tagOffset, Layouts.OptionE.Some.tag, Layouts.OptionE.Some.f0,
      Layouts.E.c0, Layouts.E.c1] at h ⊢
    have h1 := h.2.1; have h2 := h.2.2
    simp only [add_ofNat_lit] at h1 h2 ⊢
    exact ⟨by rw [hk 0 (by decide)]; exact h.1, by rw [hk _ (by decide)]; exact h1, by rw [hk _ (by decide)]; exact h2⟩

end Rv64mc.Proof.Transcript
