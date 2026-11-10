import Rv64Verifier.Proofs.Pcs.ExtendStoreVal

/-!
# `Vec<StackClaim>::extend_desugared`: the loop

`push_step`: a push, from `Push` to the next `Head` or `Exit`; `loop`: from any `Head` to `Exit`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs LeanVM.Parameters

theorem push_step (hS : MultilinearContracts.SelectorSpec)
    (hC : MultilinearContracts.SliceConcatSpec) (hG : GrowSpec) {s u : MachineState} {k : Nat}
    (hpre : Walk.ExtendPreE s) (hp : Push s u k) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ Exit s v ∨ Head s v (k + 1)) := by
  obtain ⟨t₁, hr₁, hd₁ | ha⟩ := sel_step hS hpre hp
  · exact ⟨t₁, hr₁, Or.inl hd₁⟩
  obtain ⟨t₂, hr₂, hd₂ | hm⟩ := concat_step hC hpre hp ha
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd₂⟩
  obtain ⟨t₃, hr₃, hB, h0, h8, hpc⟩ := d34_step hpre hp hm
  have hroom : ∃ w, Reaches Image.code t₃ w ∧ (Dead Image.code w ∨ Room s u w k) := by
    rcases hpc with ⟨hpc, hne⟩ | ⟨hpc, hfull⟩
    · exact ⟨t₃, Reaches.refl _, Or.inr (room_nogrow hp hB h0 h8 hpc hne)⟩
    · exact room_grow hG hpre hp hB h0 h8 hpc hfull
  obtain ⟨w, hrw, hdw | hr⟩ := hroom
  · exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans hrw)), Or.inl hdw⟩
  obtain ⟨t, hrt, hs⟩ := store_blk hpre hp hr
  have hI := store_inv hpre (sctx hpre hp hr hs)
  refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hrw.trans hrt))), Or.inr ?_⟩
  rcases hs.pc with ⟨he, hpc⟩ | ⟨hlt, hpc⟩
  · exact Or.inl ⟨he ▸ hI, hpc⟩
  · exact Or.inr ⟨hI, hpc, (hs.keep .x25 (by decide)).trans hr.x25, hlt⟩

theorem loop (hS : MultilinearContracts.SelectorSpec) (hC : MultilinearContracts.SliceConcatSpec)
    (hG : GrowSpec) {s : MachineState} (hpre : Walk.ExtendPreE s) :
    ∀ n j u, itCount s - j ≤ n → Head s u j →
      ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ Exit s v) := by
  intro n
  induction n with
  | zero => intro j u hn hh; have := hh.lt; omega
  | succ n ih =>
    intro j u hn hh
    obtain ⟨v, hr, hd | he | ⟨k, hk, hp⟩⟩ := head_step hpre hh
    · exact ⟨v, hr, Or.inl hd⟩
    · exact ⟨v, hr, Or.inr he⟩
    obtain ⟨w, hrw, hd | he | hh'⟩ := push_step hS hC hG hpre hp
    · exact ⟨w, hr.trans hrw, Or.inl hd⟩
    · exact ⟨w, hr.trans hrw, Or.inr he⟩
    obtain ⟨x, hrx, hx⟩ := ih (k + 1) w (by omega) hh'
    exact ⟨x, hr.trans (hrw.trans hrx), hx⟩

end Rv64Verifier.Proofs.Pcs.Extend
