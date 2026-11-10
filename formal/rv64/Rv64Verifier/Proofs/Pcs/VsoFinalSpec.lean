import Rv64Verifier.Proofs.Pcs.VsoFinalIn

/-!
# `verify_stacked_opening`'s contract, from the level loop and the final level's tail

`exitR` returns from `0x8000a0bc` with the root written. The level loop (`LoopSpec`) ends in an
`Err` or in the final level's tail (`VsoFinalIn`); the tail (`TailSpec`) ends in an `Err` or in
`Ok` (`OkR`), on the mirror's `Ok` for every transcript whose openings `OA` places in memory.
`vso_of` assembles `VsoSpec OA` from the two.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- **The exit, the root written**: from `0x8000a0bc` the function returns `a0`, memory as it was
there, changed since the entry only where the contract allows. -/
theorem exitR {s u : MachineState} {nx : Word} (hpre : VsoPre s) (h : InvR s u nx)
    (hpc : u.pc = 0x8000a0bc) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getReg .x10 = u.getReg .x10 ∧ (∀ a, t.getMem a = u.getMem a) ∧ HeapOk t ∧
      heapNext s ≤ heapNext t ∧
      DFrame s t fun a ↦ Within a (s.getReg .x10 + 8) 352 ∨ Within a (s.getReg .x11) 32 ∨
        Within a (stackLo s vsoStack) vsoStack ∨ Within a nextAddr 8 ∨ Fresh s t a := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.sp
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000a0bc_spec hpc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have hm := b8000a0bc_mem_same ht
  have hrest (o : Nat) (r : Reg) (ho : (o, r) ∈ slots) (k : Word)
      (hk : u.getReg .x2 + k = s.getReg .x2 - BitVec.ofNat 64 o) :
      u.getMem (u.getReg .x2 + k) = s.getReg r := by
    rw [hk]; exact h.slots _ ho
  have hn : heapNext t = heapNext u := by simp only [heapNext, hm]
  have hnu : heapNext u = nx.toNat := by simp only [heapNext, h.next]
  have hu := h.heap hpre.heap
  refine ⟨t, hr, ?_, ?_, ?_, hm, ⟨by rw [hn]; exact hu.lo, by rw [hn]; exact hu.hi⟩,
    by rw [hn, hnu]; exact h.mono, ?_⟩
  · rw [b8000a0bc_pc ht, returnAddress_eq, hrest 8 .x1 (by decide) _ (by rw [hsp]; rv_eval [])]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b8000a0bc_x2 ht, hsp]; rv_eval []
    · rw [b8000a0bc_x8 ht]; exact hrest 16 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x9 ht]; exact hrest 24 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x18 ht]; exact hrest 32 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x19 ht]; exact hrest 40 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x20 ht]; exact hrest 48 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x21 ht]; exact hrest 56 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x22 ht]; exact hrest 64 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x23 ht]; exact hrest 72 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x24 ht]; exact hrest 80 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x25 ht]; exact hrest 88 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x26 ht]; exact hrest 96 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x27 ht]; exact hrest 104 _ (by decide) _ (by rw [hsp]; rv_eval [])
  · exact b8000a0bc_keeps ht .x10 (by decide)
  · intro a ha
    rw [hm a]
    refine h.mem a fun i hi hw ↦ ha i hi ?_
    rcases hw with (hw | hw) | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw.1, by rw [hn, hnu]; exact hw.2⟩)))

/-- `Ok` at the exit: on every transcript whose openings `OA` places in memory, the mirror returns
`Ok` on the transcript `v` stands for. -/
structure OkR (OA : MachineState → Word → Model.TState → Prop) (s v : MachineState) : Prop where
  pc : v.pc = 0x8000a0bc
  ok : v.getReg .x10 = okTag
  inv : ∃ nx, InvR s v nx
  value : ∀ T, TranscriptAt s (s.getReg .x10) T → OA s (s.getReg .x10) T →
    T.roots = [(digestAt s (s.getReg .x11),
      Model.stackShape (s.getReg .x12).toNat (s.getReg .x13).toNat)] →
    ∃ T', (Model.Pcs.verifyStackedOpeningRust (s.getReg .x12).toNat (s.getReg .x13).toNat
      (claimsOf s)).run T = some ((), T') ∧ TranscriptAt v (s.getReg .x10) T'

/-- The level loop: from the entry to an `Err` or the final level's tail. -/
def LoopSpec (OA : MachineState → Word → Model.TState → Prop) : Prop :=
  ∀ s, s.pc = 0x80009db8 → VsoPre s → ∃ u, Reaches Image.code s u ∧
    (FailR s u ∨ ∃ x Wl residual, VsoFinalIn OA s x u Wl residual)

/-- The final level's tail: to an `Err` or `Ok`. -/
def TailSpec (OA : MachineState → Word → Model.TState → Prop) : Prop :=
  ∀ s x u Wl residual, VsoPre s → VsoFinalIn OA s x u Wl residual →
    ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ OkR OA s v)

theorem claimsOf_eq (s : MachineState) :
    claimsOf s = claimsAt s (s.getReg .x14) (s.getReg .x15).toNat := rfl

/-- `TranscriptAt` reads only memory. -/
theorem tr_congr {u t : MachineState} {p : Word} {T : Model.TState} (h : TranscriptAt u p T)
    (hm : ∀ a, t.getMem a = u.getMem a) : TranscriptAt t p T :=
  ⟨by simp only [streamPtr, streamLen, proofAt, vecPtr, vecLen, Rv64Verifier.eListAt,
      Rv64Verifier.eAt, hm]; exact h.stream,
    by simp only [spongeAt, stateAt, pendingAt, nPending, Rv64Verifier.eAt, hm]; exact h.sponge,
    by rw [hm]; exact h.streamOffset, by rw [hm]; exact h.openingOffset⟩

/-- An `Err`, returned. -/
theorem vso_fail {OA : MachineState → Word → Model.TState → Prop} {s v : MachineState}
    (hpre : VsoPre s) (h : FailR s v) : ∃ t, Reaches Image.code v t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ VsoPost OA s t) ∨ Dead Image.code t) := by
  rcases h with h | ⟨hpc, hne, nx, hinv⟩
  · exact ⟨v, .refl _, Or.inr h⟩
  obtain ⟨t, hr, hpc', hps, hx, -, hh, hmono, hfr⟩ := exitR hpre hinv hpc
  exact ⟨t, hr, Or.inl ⟨hpc', hps, hh, hmono, fun hok ↦ absurd (hx ▸ hok) hne, hfr⟩⟩

/-- **`verify_stacked_opening`'s contract**, from the level loop and the tail. -/
theorem vso_of {OA : MachineState → Word → Model.TState → Prop} (hL : LoopSpec OA)
    (hT : TailSpec OA) : VsoSpec OA := by
  intro s hpc hpre
  obtain ⟨u, hu, hout⟩ := hL s hpc hpre
  rcases hout with hf | ⟨x, Wl, residual, hin⟩
  · obtain ⟨t, ht, h⟩ := vso_fail (OA := OA) hpre hf
    exact ⟨t, hu.trans ht, h⟩
  obtain ⟨v, hv, hout⟩ := hT s x u Wl residual hpre hin
  rcases hout with hf | hok
  · obtain ⟨t, ht, h⟩ := vso_fail (OA := OA) hpre hf
    exact ⟨t, hu.trans (hv.trans ht), h⟩
  obtain ⟨nx, hinv⟩ := hok.inv
  obtain ⟨t, ht, hpc', hps, -, hm, hh, hmono, hfr⟩ := exitR hpre hinv hok.pc
  refine ⟨t, hu.trans (hv.trans ht), Or.inl ⟨hpc', hps, hh, hmono, fun _ T hT hO hr ↦ ?_, hfr⟩⟩
  obtain ⟨T', e, hT'⟩ := hok.value T hT hO hr
  exact ⟨T', by rw [← claimsOf_eq]; exact e, tr_congr hT' hm⟩

end Rv64Verifier.Proofs.Pcs.Vso
