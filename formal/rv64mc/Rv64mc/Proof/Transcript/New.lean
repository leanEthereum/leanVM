/-
  Rv64mc.Proof.Transcript.New

  `Transcript::new` keeps its contract (`Spec.Transcript.New.spec`), from `Sponge::new`'s. The stack's alignment
  comes from the first store into the frame (`safe_aligned_store`), the digests reach `Sponge::new` through the
  prologue's stores (`digest_keep`, each digest safe from the call), and the four stores of the other fields
  (`fields`) keep the sponge, the proof and everything below the slot.
-/

import Rv64mc.Spec.Transcript.New
import Rv64mc.Spec.Transcript.SpongeNew
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Transcript.Trap
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.New
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.New

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Protocol LeanVM.Protocol.Compile Rv64mc.Spec.Transcript
open Rv64mc.Spec.Transcript.New Rv64mc.Proof.Transcript
open Rv64mc.Gen.Verifier.Transcript.Transcript.New (Link tmpl)

/-- A digest read through stores that keep its doublewords. -/
theorem digest_keep {m P : MachineState} {x : Word} {d : List (BitVec 8)} (hd : DigestAt m x d)
    (h : ∀ y : Word, (alignToDword x).toNat ≤ y.toNat → y.toNat < x.toNat + 32 → P.getMem y = m.getMem y) :
    DigestAt P x d := by
  obtain ⟨hl, hb⟩ := hd
  refine ⟨hl, hb.keep fun k hk => getByte_congr (h _ ?_ ?_)⟩
  · rw [toNat_alignToDword, toNat_alignToDword, toNat_add_ofNat (by have := hb.1; omega)]; omega
  · rw [toNat_alignToDword, toNat_add_ofNat (by have := hb.1; omega)]
    simp only [Layouts.Digest.byteSize] at hl; omega

/-- The four stores of `new`'s fields, past the sponge. -/
abbrev fields (m1 : MachineState) (x w : Word) : MachineState :=
  (((m1.setMem (x + 328#64) w).setMem (x + 336#64) 0#64).setMem (x + 344#64) 0#64).setByte (x + 352#64)
    (BitVec.truncate 8 1#64)

theorem fields_get {m1 : MachineState} {x w b : Word} (hx : x.toNat % 8 = 0) (hxn : x.toNat + 360 < 2 ^ 64)
    (hb : ¬ InRange x 360 b) : (fields m1 x w).getMem b = m1.getMem b := by
  have ne : ∀ k, k < 360 → b ≠ x + BitVec.ofNat 64 k := fun k hk he =>
    hb (he ▸ inRange_add hxn hk)
  simp only [fields]
  rw [getMem_setByte_ne (by rw [alignToDword_of_aligned hx (by decide) (by omega)]; exact ne 352 (by decide)),
    MachineState.getMem_setMem_ne (ne 344 (by decide)), MachineState.getMem_setMem_ne (ne 336 (by decide)),
    MachineState.getMem_setMem_ne (ne 328 (by decide))]

theorem fields_keeps {m1 : MachineState} {x w : Word} (hx : x.toNat % 8 = 0) (hxn : x.toNat + 360 < 2 ^ 64) :
    Keeps m1 (fields m1 x w) x 328 := fun b hb => by
  have ne : ∀ k, 328 ≤ k → k < 360 → b ≠ x + BitVec.ofNat 64 k := fun k hk hk' he => by
    rw [he, InRange, toNat_add_ofNat (by omega)] at hb; omega
  simp only [fields]
  have n352 := ne 352 (by decide) (by decide)
  rw [getMem_setByte_ne (by rw [alignToDword_of_aligned hx (by decide) (by omega)]; exact n352),
    MachineState.getMem_setMem_ne (ne 344 (by decide) (by decide)),
    MachineState.getMem_setMem_ne (ne 336 (by decide) (by decide)),
    MachineState.getMem_setMem_ne (ne 328 (by decide) (by decide))]

theorem fields_next {env : Env} {m1 : MachineState} {x w : Word} (hx : x.toNat % 8 = 0)
    (hxn : x.toNat + 360 < 2 ^ 64) (hl : env.stackLimit.toNat ≤ x.toNat) :
    env.next (fields m1 x w) = env.next m1 := by
  have := env.layout
  unfold Env.next
  exact fields_get hx hxn fun h => by unfold InRange at h; omega

/-- **`Transcript::new` keeps its contract**, for one proof and pair of digests. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 32 + needS ≤ need)
    (hsn : Spec.Transcript.SpongeNew.spec env p L.new.idx needS) (pf : Proof) (iv pi : Digest) :
    Holds env p i need (Pre env pf iv pi) (Post env pf iv pi) (Spec.Whir.SretOut Layouts.Transcript.byteSize) := by
  rv_auto hp stop [3] with [hL] using [hsn (Model.digestBits iv) (Model.digestBits pi)]
  refine safe_aligned_store (x := top + 18446744073709551584#64 + 24#64) hp rfl rfl fun hal => ?_
  rv_sym hp with [hL] using [hsn (Model.digestBits iv) (Model.digestBits pi)]
  all_goals
    have hS : env.stackLimit.toNat + 32 ≤ top.toNat := by omega
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_9 hpre_14 hpre_15 hpre_16
    simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize, Layouts.Digest.byteSize,
      Layouts.Sponge.byteSize] at *
    have hst : ∀ c : Word, Tactic.slotOk 32 c = true → (top + c).toNat < top.toNat := fun c hc => Tactic.slot_lt hS hc
    have hlo : ∀ c : Word, Tactic.slotOk 32 c = true → env.stackLimit.toNat ≤ (top + c).toNat :=
      fun c hc => Tactic.slot_ge hS hc
    have hNs : (env.next m).toNat < env.stackLimit.toNat := by have := env.layout; omega
    have htop : top.toNat % 8 = 0 := by
      rw [BitVec.add_assoc, show (18446744073709551584#64 + 24#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 8) by decide,
        toNat_sub_lit (by omega) (by decide)] at hal
      omega
  -- the digests and the slot, for `Sponge::new`
  iterate 2
    · refine digest_keep (by assumption) fun y h1 h2 => ?_
      first
        | (rcases hpre_15 with hl | hf
           · unfold Env.Live at hl
             simp (disch := (refine Nat.lt_of_lt_of_le ?_ (hlo _ rfl); omega)) only [getMem_setMem_gt]
           · have := toNat_alignToDword (regs .x12)
             simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) (by omega)) only [getMem_setMem_lt])
        | (rcases hpre_16 with hl | hf
           · unfold Env.Live at hl
             simp (disch := (refine Nat.lt_of_lt_of_le ?_ (hlo _ rfl); omega)) only [getMem_setMem_gt]
           · have := toNat_alignToDword (regs .x13)
             simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) (by omega)) only [getMem_setMem_lt])
  · exact Nat.le_trans (Tactic.slot_le hS rfl) hpre_9
  · omega
  · omega
  · omega
  -- the digests safe from `Sponge::new`
  iterate 2
    · first
        | (rcases hpre_15 with hl | hl
           · left
             unfold Env.Live Env.next at hl ⊢
             simp (disch := exact Nat.lt_of_lt_of_le (by have := env.layout; omega) (hlo _ rfl)) only
               [getMem_setMem_gt]
             exact hl
           · right; exact Nat.le_trans (Tactic.slot_le hS rfl) hl)
        | (rcases hpre_16 with hl | hl
           · left
             unfold Env.Live Env.next at hl ⊢
             simp (disch := exact Nat.lt_of_lt_of_le (by have := env.layout; omega) (hlo _ rfl)) only
               [getMem_setMem_gt]
             exact hl
           · right; exact Nat.le_trans (Tactic.slot_le hS rfl) hl)
  all_goals
    have hx := hret1_16.aligned
    simp only [Layouts.Sponge.byteAlign] at hx
    have hagree : ∀ b : Word, b.toNat < top.toNat → (fields m1 (regs .x10) (regs .x11)).getMem b = m1.getMem b :=
      fun b hb => fields_get hx hpre_10 fun h => by unfold InRange at h; omega
    have hnot : ∀ c : Word, Tactic.slotOk 32 c = true →
        ¬ Spec.Whir.SretOut 328 (updReg (Tactic.rf (regs .x0) L.s0.hi (top + 18446744073709551584#64) (regs .x3)
          (regs .x4) (regs .x5) (regs .x6) (regs .x7) (regs .x11) (regs .x10) (regs .x10) (regs .x12) (regs .x13)
          (regs .x13) (regs .x14) (regs .x15) (regs .x16) (regs .x17) (regs .x18) (regs .x19) (regs .x20)
          (regs .x21) (regs .x22) (regs .x23) (regs .x24) (regs .x25) (regs .x26) (regs .x27) (regs .x28)
          (regs .x29) (regs .x30) (regs .x31)) .x1 (L.base + 40#64)) m (top + c) := fun c hc h => by
      have := hst c hc
      simp only [Spec.Whir.SretOut, InRange, Lprog.updReg_apply, Tactic.rf] at h
      exact absurd h.1 (by simp only [reduceCtorEq, ↓reduceIte]; omega)
    have hF : env.Frame top (InRange (regs .x10) 360) m m1 := by
      refine Env.Frame.trans ?_ hret1_14 (Tactic.slot_le hS rfl) fun b hb => Or.inr (Or.inr (Or.inr ?_))
      · rv_close
      · simp only [Spec.Whir.SretOut, InRange, Lprog.updReg_apply, Tactic.rf] at hb
        simp only [reduceCtorEq, ↓reduceIte] at hb
        exact ⟨hb.1, by omega⟩
    have hal352 := alignToDword_of_aligned (k := 352) hx (by decide) (by omega)
  -- the saved registers
  · change (fields m1 (regs .x10) (regs .x11)).getMem _ = _
    rw [hagree _ (hst _ rfl), hret1_14.getMem_above (a := top + 18446744073709551608#64) (Tactic.slot_ge hS rfl)
      (slot_mono hS rfl rfl rfl) (hnot _ rfl)]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  · change (fields m1 (regs .x10) (regs .x11)).getMem _ = _
    rw [hagree _ (hst _ rfl), hret1_14.getMem_above (a := top + 18446744073709551600#64) (Tactic.slot_ge hS rfl)
      (slot_mono hS rfl rfl rfl) (hnot _ rfl)]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  · change (fields m1 (regs .x10) (regs .x11)).getMem _ = _
    rw [hagree _ (hst _ rfl), hret1_14.getMem_above (a := top + 18446744073709551592#64) (Tactic.slot_ge hS rfl)
      (slot_mono hS rfl rfl rfl) (hnot _ rfl)]
    simp only [MachineState.getMem_setMem_eq]
  -- the frame, the static data
  · change env.Frame top _ m (fields m1 (regs .x10) (regs .x11))
    simp only [fields]
    refine frame_store_byte (frame_store_obj (frame_store_obj (frame_store_obj hF hlim hpre_9
      hpre_10 (k := 328) (by decide) ?_) hlim hpre_9 hpre_10 (k := 336) (by decide) ?_) hlim hpre_9 hpre_10
      (k := 344) (by decide) ?_) hlim ?_ ?_
    all_goals first
      | (show InRange _ 360 _; exact inRange_add hpre_10 (by decide))
      | (rw [hal352]; exact Nat.le_trans hpre_9 (toNat_le_add hpre_10 (by decide)))
      | (rw [hal352]; show InRange _ 360 _; exact inRange_add hpre_10 (by decide))
  · change env.Static (fields m1 (regs .x10) (regs .x11))
    simp only [fields]
    exact static_store_byte (static_store_obj (static_store_obj (static_store_obj hret1_15 hlim hpre_9 hpre_10
      (k := 328) (by decide)) hlim hpre_9 hpre_10 (k := 336) (by decide)) hlim hpre_9 hpre_10 (k := 344)
      (by decide)) hlim (by rw [hal352]; exact Nat.le_trans hpre_9 (toNat_le_add hpre_10 (by decide)))
  -- the transcript
  · change TranscriptAt env (fields m1 (regs .x10) (regs .x11)) (regs .x10) _
    have hq : (fields m1 (regs .x10) (regs .x11)).getMem (regs .x10 + BitVec.ofNat 64 328) = regs .x11 := by
      simp only [fields]
      rw [getMem_setByte_ne (by rw [hal352]; exact add_ne_add (n := 360) hpre_10 (by decide) (by decide) (by decide)),
        MachineState.getMem_setMem_ne (add_ne_add (n := 360) hpre_10 (by decide) (by decide) (by decide)),
        MachineState.getMem_setMem_ne (add_ne_add (n := 360) hpre_10 (by decide) (by decide) (by decide))]
      exact MachineState.getMem_setMem_eq
    have hheap : HeapKept env m (fields m1 (regs .x10) (regs .x11)) :=
      ⟨by rw [fields_next hx hpre_10 (by omega)]; exact hF.1, fun b hb => by
        rw [fields_get hx hpre_10 fun h => by unfold InRange at h; omega]
        exact hF.getMem_below_next hpre_5 hb fun h => by unfold InRange at h; omega⟩
    refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Layouts.Transcript.sponge, Layouts.Transcript.proof, Layouts.Transcript.stream_offset,
        Layouts.Transcript.opening_offset, Layouts.Transcript.checked, Layouts.Proof.byteSize,
        Layouts.Transcript.byteSize, hq]
    · rw [show regs .x10 + BitVec.ofNat 64 0 = regs .x10 by simp]
      exact hret1_16.keep (by simp only [Layouts.Sponge.byteSize]; omega) (fields_keeps hx hpre_10)
    · refine hpre_6.keep hheap fun b hb => ?_
      simp only [Layouts.Proof.byteSize] at hb
      rw [fields_get hx hpre_10 fun h => by unfold InRange at h hb; omega]
      rcases hpre_14 with hl | hf
      · exact hF.getMem_below_next hpre_5 (by unfold Env.Live at hl; unfold InRange at hb; omega)
          fun h => by unfold InRange at h hb; unfold Env.Live at hl; omega
      · exact hF.getMem_above hlim (by unfold InRange at hb; omega) fun h => by unfold InRange at h hb; omega
    · unfold Apart; omega
    · simp only [fields]
      rw [getMem_setByte_ne (by rw [hal352]; exact add_ne_add (n := 360) hpre_10 (by decide) (by decide) (by decide)),
        MachineState.getMem_setMem_ne (add_ne_add (n := 360) hpre_10 (by decide) (by decide) (by decide)),
        MachineState.getMem_setMem_eq]
      rfl
    · simp only [fields]
      rw [getMem_setByte_ne (by rw [hal352]; exact add_ne_add (n := 360) hpre_10 (by decide) (by decide) (by decide)),
        MachineState.getMem_setMem_eq]
      rfl
    · simp only [fields]
      rw [getByte_setByte_eq]
      rfl

/-- **`Transcript::new` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 32 + needS ≤ need)
    (hsn : Spec.Transcript.SpongeNew.spec env p L.new.idx needS) : spec env p i need :=
  ok_at env p i L hp hL hnS hsn

end Rv64mc.Proof.Transcript.New
