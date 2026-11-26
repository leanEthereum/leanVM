/-
  Rv64mc.Proof.Transcript.NextSafeT

  `Transcript::next`'s second total contract (`specT`), beside `NextT.specT`: from a transcript `TranscriptT`
  (`TranscriptReprT`) with no functional ghost, and a result's slot in a window apart from it and from its proof, it
  returns with the transcript `TranscriptT` again and its proof's address kept, writing at most the slot and the
  stream offset. `NextT.specT` asks the transcript `TranscriptAt` at a ghost state, which a transcript whose sponge
  went through a permutation no longer has (`SpongeReprT`), so the total contracts of `next`'s callers use this one.
  Its precondition is `NextT.PreT`'s window and alignment conjuncts on the same objects, without `Next.Pre`
  (`preT_of_nextT`).

  ## Main definitions

  * `PreT`, `PostT`, `specT`

  ## Main results

  * `preS_of_nextT`, `safe`, `total`
-/

import Rv64mc.Proof.Transcript.TranscriptReprT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Transcript.NextSafeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.WinT
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Gen.Verifier.Transcript.Transcript.Next (Link tmpl)

/-- The total precondition: the transcript `TranscriptT` and owned with its proof (`OwnedT`), the result's slot in a
    window, 8-byte aligned, apart from the transcript and its proof. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptT env m (regs .x11) ∧ OwnedT env m (regs .x2) (regs .x11) ∧
    InWin env (regs .x10) Layouts.ResultE.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    Apart (regs .x10) Layouts.ResultE.byteSize (regs .x11) Layouts.Transcript.byteSize ∧
    Apart (regs .x10) Layouts.ResultE.byteSize (proofAddr m (regs .x11)) Layouts.Proof.byteSize

/-- The total postcondition: the transcript `TranscriptT` and owned again, its proof's address kept. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  TranscriptT env m' (regs .x11) ∧ OwnedT env m' (regs .x2) (regs .x11) ∧
    proofAddr m' (regs .x11) = proofAddr m (regs .x11)

/-- **`Transcript::next`'s second total contract**: `PreT` to `PostT`, writing at most the slot and the stream
    offset (`Next.Out`). -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Next.Out

/-- What `next`'s accesses need: `NextT.PreT`'s windows and alignments, without `Next.Pre`. -/
def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x11) Layouts.Transcript.byteSize ∧ (regs .x11).toNat % 8 = 0 ∧
    InWin env (regs .x10) Layouts.ResultE.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    InWin env (m.getMem (regs .x11 + 0x148#64)) Layouts.Proof.byteSize ∧
    (m.getMem (regs .x11 + 0x148#64)).toNat % 8 = 0 ∧ NextT.StreamWin env m (m.getMem (regs .x11 + 0x148#64))

/-- `NextT.PreT` without `Next.Pre` is `PreS`. -/
theorem preS_of_nextT {env : Env} {t : Model.TState} {regs : Reg → Word} {m : MachineState}
    (h : NextT.PreT env t regs m) : PreS env regs m :=
  h.2

/-- A store into `out` that misses `NEXT` stays in the frame. -/
theorem frame_out_setMem {env : Env} {top b v : Word} {out : Word → Prop} {m M : MachineState}
    (h : env.Frame top out m M) (hb : out b) (hn : b ≠ env.nextAddr) : env.Frame top out m (M.setMem b v) :=
  h.trans (Env.Frame.setMem_out h.2.1 hb hn) (Nat.le_refl _) fun _ ha => Or.inr (Or.inr (Or.inr ha))

set_option rv_sym.heap true in
/-- **`Transcript::next` is safe and returns**, from `PreS`: `NextT.safe`'s proof without `Next.Pre`. -/
theorem safe (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    HoldsT env p i need (PreS env) (fun _ _ _ _ => True) Next.Out := by
  rv_autoT hp
  all_goals
    simp only [Layouts.ResultE.byteSize, Layouts.Transcript.byteSize] at hpre_6 hpre_8
    have hW : InWin env (regs .x10) 24 := hpre_8
    have hT : InWin env (regs .x11) 360 := hpre_6
    have hlt := hW.lt
    have n0 : regs .x10 ≠ env.nextAddr := hW.ne_next (Nat.le_refl _) (by omega)
    have n8 : regs .x10 + 8#64 ≠ env.nextAddr := hW.ne_next_add (by omega)
    have o0 : Next.Out regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by simp only [Layouts.ResultE.byteSize]; omega⟩
    have o8 : Next.Out regs m (regs .x10 + 8#64) := Or.inl (by
      simp only [InRange, Layouts.ResultE.byteSize]; rw [toNat_add_ofNat (by omega)]; omega)
  -- past the stream: `Err` stored
  · exact frame_out_setMem (frame_out_setMem (Env.Frame.refl hpre_5) o0 n0) o8 n8
  -- within it: the element's two doublewords, then `Ok` and the offset stored
  all_goals
    have hlt : (MachineState.getMem m (regs .x11 + 336#64)).toNat <
        (MachineState.getMem m (MachineState.getMem m (regs .x11 + 328#64) + 16#64)).toNat := by
      rw [BitVec.lt_def] at hc; omega
    obtain ⟨hS, hSa⟩ := hpre_12.resolve_left (by omega)
    have hx := elem_toNat (s := 4) (q := MachineState.getMem m (MachineState.getMem m (regs .x11 + 328#64) + 8#64))
      (o := MachineState.getMem m (regs .x11 + 336#64)) (by have := hS.lt; omega)
    have hd0 := hS.dword hpre_14 hSa hx (by omega) (by omega)
    have hd8 := hS.dword_add hpre_14 hSa hx (k := 8) (by omega) (by omega)
  · exact hd8.1
  · exact hd8.2
  · exact hd0.1
  · exact hd0.2
  · have o16 : Next.Out regs m (regs .x10 + 16#64) := Or.inl (by
      simp only [InRange, Layouts.ResultE.byteSize]; rw [toNat_add_ofNat (by omega)]; omega)
    exact frame_out_setMem (frame_out_setMem (frame_out_setMem (frame_out_setMem (Env.Frame.refl hpre_5)
      (Or.inr rfl) (hT.ne_next_add (by omega))) o16 (hW.ne_next_add (by omega))) o0 n0) o8 n8

/-- `Next.Out` misses the five words `TranscriptT` reads, the slot apart from the transcript and its proof. -/
theorem out_miss {env : Env} {regs : Reg → Word} {m : MachineState} (h : PreT env regs m) :
    (∀ k, (k = 0 ∨ k = 320 ∨ k = 328) → ¬ Next.Out regs m (regs .x11 + BitVec.ofNat 64 k)) ∧
      ∀ k, (k = 8 ∨ k = 16) →
        ¬ Next.Out regs m (m.getMem (regs .x11 + 328#64) + BitVec.ofNat 64 k) := by
  obtain ⟨⟨_, hT, hA, _, hQ, _⟩, _, _, _, hR, hP⟩ := h
  have ha := hT.lt
  have hq := hQ.lt
  simp only [Apart, proofAddr, Layouts.Transcript.proof, Layouts.Transcript.byteSize, Layouts.Proof.byteSize,
    Layouts.ResultE.byteSize] at hA hq hR hP ha ⊢
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;>
    simp only [Next.Out, InRange, Layouts.ResultE.byteSize, Layouts.Transcript.stream_offset, not_or] <;>
    refine ⟨?_, fun he => ?_⟩
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at this; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at this; omega

/-- **`Transcript::next` keeps an owned `TranscriptT`**, from `safe` and `Next.Out`'s frame (`TranscriptT.frame`). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    specT env p i need :=
  Isa.TContract.mono (safe env p i L hp need)
    (fun _ _ regs m ⟨⟨he, hs, hst, hn, hP, hal⟩, hW⟩ => ⟨⟨he, hs, hst, hn,
      ⟨hP.1.2.1, hP.1.1.1, hP.2.2.1, hP.2.2.2.1, hP.1.2.2.2.2.1, hP.1.2.2.2.1, hP.1.2.2.2.2.2⟩, hal⟩, hW⟩)
    (fun _ top regs m _ m' ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hf, hst', _⟩, hc⟩ => by
      have hT := hP.1.frame (he.2 ▸ hP.2.1) hf hn (by omega) (out_miss hP).1 (out_miss hP).2
      exact ⟨⟨ha, hf, hst', hT.1, he.2 ▸ hT.2.1, hT.2.2⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Transcript.NextSafeT

/-- info: 'Rv64mc.Proof.Transcript.NextSafeT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.NextSafeT.total
