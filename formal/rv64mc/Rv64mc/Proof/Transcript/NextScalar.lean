/-
  Rv64mc.Proof.Transcript.NextScalar

  `Transcript::next_scalar` keeps its contract (`Spec.Transcript.NextScalar.spec`), from the contracts of `next`
  and `Sponge::absorb`. `next`'s result, in the function's own stack, decides the path: `Ok` observes the scalar
  (`absorb` with tag `1`), and both copy the result into the caller's slot. The transcript reaches `next` through
  the prologue's stores (`TranscriptAt.stack`), and its sponge after `absorb` is the mirror's
  (`TranscriptAt.through`).
-/

import Rv64mc.Spec.Transcript.NextScalar
import Rv64mc.Spec.Transcript.Next
import Rv64mc.Spec.Transcript.Absorb
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Transcript.Next
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.NextScalar
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.NextScalar

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.NextScalar
open Rv64mc.Proof.Transcript
open Rv64mc.Gen.Verifier.Transcript.Transcript.NextScalar (Link tmpl)

theorem nextScalar_none {t : Model.TState} (h : t.proof.stream.length ≤ t.streamOffset) :
    Model.TM.nextScalar.run t = none := by
  simp only [StateT.run, Model.TM.nextScalar, List.getElem?_eq_none h]

theorem nextScalar_some {t : Model.TState} (h : t.streamOffset < t.proof.stream.length) {s : Model.SpongeRust}
    (hs : t.sponge.absorb t.proof.stream[t.streamOffset] 1#64 = some s) :
    Model.TM.nextScalar.run t =
      some (t.proof.stream[t.streamOffset], { { t with streamOffset := t.streamOffset + 1 } with sponge := s }) := by
  simp only [StateT.run, Model.TM.nextScalar, List.getElem?_eq_getElem h, Model.SpongeRust.observe,
    Model.dsObserveR, hs, Option.map_some]

theorem tag_some {M : MachineState} {a : Word} {v : E} (h : ResultEAt M a (some v)) : M.getMem a = 0#64 := by
  simpa [ResultEAt, Layouts.ResultE.tagOffset, Layouts.ResultE.Ok.tag] using h.1

theorem tag_none {M : MachineState} {a : Word} (h : ResultEAt M a none) : M.getMem a = 1#64 := by
  simpa [ResultEAt, Layouts.ResultE.tagOffset, Layouts.ResultE.Err.tag] using h

theorem limbs_some {M : MachineState} {a : Word} {v : E} (h : ResultEAt M a (some v)) :
    M.getMem (a + 8#64) = (Model.limbs v).1 ∧ M.getMem (a + 16#64) = (Model.limbs v).2 := by
  obtain ⟨-, h0, h1⟩ := h
  simp only [Layouts.ResultE.Ok.f0, Layouts.E.c0, Layouts.E.c1] at h0 h1
  exact ⟨by simpa using h0, by rw [← h1, BitVec.add_assoc]; rfl⟩

/-- **`Transcript::next_scalar` keeps its contract**, for one transcript state. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN needA : Nat} (hnN : 64 + needN ≤ need) (hnA : 64 + needA ≤ need)
    (hnext : Spec.Transcript.Next.spec env p L.next.idx needN)
    (habs : Spec.Transcript.Absorb.spec env p L.absorb.idx needA) (t : Model.TState) :
    Holds env p i need (Pre env t) (Post env t) (Out Layouts.ResultE.byteSize) := by
  rv_auto hp with [hL] using [hnext t, habs t.sponge ((t.proof.stream[t.streamOffset]?).getD 0)]
  all_goals
    have hS : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_7 hpre_9 hpre_11
    simp only [Layouts.Transcript.byteSize, Layouts.ResultE.byteSize,
      Layouts.Proof.byteSize] at hpre_8 hpre_10 hpre_12 hpre_13
    have hst : ∀ c : Word, Tactic.slotOk 64 c = true → (top + c).toNat < top.toNat := fun c hc => Tactic.slot_lt hS hc
    have hlo : ∀ c : Word, Tactic.slotOk 64 c = true → env.stackLimit.toNat ≤ (top + c).toNat :=
      fun c hc => Tactic.slot_ge hS hc
    have hsp : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by
      rw [show (18446744073709551552#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 64) by decide]
      exact toNat_sub_lit (by omega) (by decide)
    have h328 : top.toNat ≤ (regs .x11 + 328#64).toNat := Nat.le_trans hpre_7 (toNat_le_add hpre_8 (by decide))
    have h8 := toNat_le_add (k := 8) hpre_10 (by decide)
    have h16 := toNat_le_add (k := 16) hpre_10 (by decide)
    have hlay := env.layout
  -- `next`'s precondition: the transcript through the prologue's stores, the slot in the frame
  all_goals try
    refine hpre_6.stack hpre_8 hpre_7 hpre_11 hpre_5 fun b hb => ?_
    rcases hb with hb | hb
    · simp (disch := exact Nat.lt_of_lt_of_le hb (hlo _ rfl)) only [getMem_setMem_gt]
    · simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) hb) only [getMem_setMem_lt]
  all_goals try (unfold proofAddr at hpre_11 hpre_13 ⊢
                 simp only [Layouts.ResultE.byteSize, Layouts.Proof.byteSize] at hpre_11 ⊢
                 simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) h328) only [getMem_setMem_lt]
                 rcases hpre_11 with hl | hl
                 · unfold Env.Live at hl; omega
                 · omega)
  all_goals try (simp only [Layouts.ResultE.byteSize, Layouts.Transcript.byteSize, Layouts.Sponge.byteSize]
                 rw [hsp]; omega)
  all_goals try (simp only [Layouts.Sponge.byteSize]; omega)
  all_goals try exact Nat.le_trans (Tactic.slot_le hS rfl) hpre_7
  all_goals try exact hret1_14.2.1
  -- the path `next` took
  all_goals
    rcases Nat.lt_or_ge t.streamOffset t.proof.stream.length with ho | ho
    all_goals first
      | (rw [Rv64mc.Proof.Transcript.Next.next_some ho] at hret1_16
         obtain ⟨hres, ht1⟩ := hret1_16
         try exact absurd (tag_some hres) hc)
      | (rw [Rv64mc.Proof.Transcript.Next.next_none ho] at hret1_16
         try exact absurd ((tag_none hret1_16).symm.trans hc) (by decide))
  -- `absorb`'s precondition
  all_goals try simpa using ht1.sponge
  all_goals try
    rw [List.getElem?_eq_getElem ho, Option.getD_some]
    have h0 := limbs_some hres
    rw [BitVec.add_assoc, BitVec.add_assoc, show (18446744073709551552#64 + 8#64 : Word) = 18446744073709551560#64
      by decide, show (18446744073709551552#64 + 16#64 : Word) = 18446744073709551568#64 by decide] at h0
    first | rw [h0.1] | rw [h0.2]
  -- after the calls: the saved registers, through the slot's stores and the callees' frames
  all_goals
    have hS40 : env.stackLimit.toNat + 40 ≤ top.toNat := by omega
  all_goals
    have hm1 := fun (c : Word) (hc : Tactic.slotOk 40 c = true) =>
      hret1_14.getMem_above (a := top + c) (Tactic.slot_ge hS rfl)
        (by have := slot_ge_sub (k := 40) hS (by decide) hc; rw [hsp]; omega) fun h => by
          have := Tactic.slot_lt hS40 hc
          have := slot_ge_sub (k := 40) hS (by decide) hc
          simp only [Spec.Transcript.Next.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
            ↓reduceIte, Layouts.ResultE.byteSize] at h
          rcases h with h | h
          · rw [hsp] at h; omega
          · have := congrArg BitVec.toNat h
            rw [toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)] at this
            omega
  all_goals try
    have hm2 := fun (c : Word) (hc : Tactic.slotOk 40 c = true) =>
      hret2_14.getMem_above (a := top + c) (Tactic.slot_ge hS rfl)
        (by have := slot_ge_sub (k := 40) hS (by decide) hc; rw [hsp]; omega) fun h => by
          have := Tactic.slot_lt hS40 hc
          simp only [Spec.Transcript.Absorb.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
            ↓reduceIte, Layouts.Sponge.byteSize] at h
          omega
  all_goals try
    simp (disch := first
      | exact Nat.lt_of_lt_of_le (hst _ rfl) hpre_9
      | exact Nat.lt_of_lt_of_le (hst _ rfl) (Nat.le_trans hpre_9 h8)
      | exact Nat.lt_of_lt_of_le (hst _ rfl) (Nat.le_trans hpre_9 h16)) only [getMem_setMem_gt]
    first
      | (simp (disch := decide) only [hm2, hm1]
         simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq])
      | (simp (disch := decide) only [hm1]
         simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq])
  -- the frame and the static data
  all_goals
    have hF1 : env.Frame top (Out Layouts.ResultE.byteSize regs m) m m1 := by
      refine Env.Frame.trans ?_ hret1_14 (Tactic.slot_le hS rfl) fun b hb => ?_
      · rv_close
      · simp only [Spec.Transcript.Next.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
          ↓reduceIte, Layouts.ResultE.byteSize] at hb
        rcases hb with hb | hb
        · exact Or.inl ⟨by have := hlo (18446744073709551552#64) rfl; omega, by rw [hsp] at hb; omega⟩
        · subst hb
          exact Or.inr (Or.inr (Or.inr (Or.inr (inRange_add hpre_8 (by decide)))))
  all_goals try
    have hF2 : env.Frame top (Out Layouts.ResultE.byteSize regs m) m m2 :=
      hF1.trans hret2_14 (Tactic.slot_le hS rfl) fun b hb => Or.inr (Or.inr (Or.inr (Or.inr (by
        simp only [Spec.Transcript.Absorb.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
          ↓reduceIte, Layouts.Sponge.byteSize] at hb
        exact ⟨hb.1, by simp only [Layouts.Transcript.byteSize]; omega⟩))))
  all_goals try
    refine frame_store_obj (k := 16) (frame_store_obj (k := 8) (frame_store_out ?_ hlim hpre_9
      (Or.inl (inRange_self (by decide)))) hlim hpre_9 hpre_10 (by decide) (Or.inl (inRange_add hpre_10 (by decide))))
      hlim hpre_9 hpre_10 (by decide) (Or.inl (inRange_add hpre_10 (by decide)))
    first | exact hF2 | exact hF1
  all_goals try
    refine static_store_obj (k := 16) (static_store_obj (k := 8) (static_store ?_ hlim hpre_9) hlim hpre_9 hpre_10
      (by decide)) hlim hpre_9 hpre_10 (by decide)
    first | exact hret2_15 | exact hret1_15
  -- the result: `Err`
  all_goals try
    rw [nextScalar_none ho]
    simp only [ResultEAt, Layouts.ResultE.tagOffset, Layouts.ResultE.Err.tag, BitVec.add_zero]
    rw [MachineState.getMem_setMem_ne (ne_add_self (k := 16) hpre_10 (by decide) (by decide)),
      MachineState.getMem_setMem_ne (ne_add_self (k := 8) hpre_10 (by decide) (by decide)),
      MachineState.getMem_setMem_eq]
  -- the result: `Ok`, the scalar observed
  focus
    have hx : (t.proof.stream[t.streamOffset]?).getD 0 = t.proof.stream[t.streamOffset] := by
      rw [List.getElem?_eq_getElem ho]; rfl
    rw [hx] at hret2_16 hret2_17
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hret2_16
    rw [hs, Option.getD_some] at hret2_17
    rw [nextScalar_some ho hs]
    have h0 := limbs_some hres
    rw [BitVec.add_assoc, BitVec.add_assoc, show (18446744073709551552#64 + 8#64 : Word) = 18446744073709551560#64
      by decide, show (18446744073709551552#64 + 16#64 : Word) = 18446744073709551568#64 by decide] at h0
    have hq1 : m1.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64) := by
      rw [hret1_14.getMem_above (a := regs .x11 + 328#64) (Tactic.slot_ge hS rfl) (by rw [hsp]; omega) fun h => by
        simp only [Spec.Transcript.Next.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
          ↓reduceIte, Layouts.ResultE.byteSize] at h
        rcases h with h | h
        · rw [hsp] at h; omega
        · exact absurd h (add_ne_add (n := 360) hpre_8 (by decide) (by decide) (by decide))]
      simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) h328) only [getMem_setMem_lt]
    have hnA : ∀ b : Word, ¬ InRange (regs .x11) 328 b → (top + 18446744073709551552#64).toNat ≤ b.toNat ∨
        b.toNat < (env.next m1).toNat → m2.getMem b = m1.getMem b := fun b hb hb' => by
      rcases hb' with hb' | hb'
      · exact hret2_14.getMem_above (Tactic.slot_ge hS rfl) hb' fun h => by
          simp only [Spec.Transcript.Absorb.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
            ↓reduceIte, Layouts.Sponge.byteSize] at h
          exact hb h
      · exact hret2_14.getMem_below_next hret1_14.2.1 hb' fun h => by
          simp only [Spec.Transcript.Absorb.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
            ↓reduceIte, Layouts.Sponge.byteSize] at h
          exact hb h
    have hq2 : m2.getMem (regs .x11 + 328#64) = m1.getMem (regs .x11 + 328#64) :=
      hnA _ (fun h => by unfold InRange at h; rw [toNat_add_ofNat (by omega)] at h; omega)
        (Or.inl (by rw [hsp]; omega))
    have hn1 : (env.next m).toNat ≤ (env.next m1).toNat := by
      have := hret1_14.1
      unfold Env.next at this ⊢
      simp (disch := exact Nat.lt_of_lt_of_le (by omega) (hlo _ rfl)) only [getMem_setMem_gt] at this
      exact this
    have hsafe1 : ProofSafe env m1 top (regs .x11) := by
      unfold ProofSafe
      unfold proofAddr at hpre_11 ⊢
      simp only [Layouts.Transcript.proof, Layouts.Proof.byteSize] at hpre_11 ⊢
      rw [hq1]
      rcases hpre_11 with hl | hl
      · left; unfold Env.Live at hl ⊢; omega
      · right; exact hl
    have T2 := ht1.through (M := m2) (s := s) (by simpa using hret2_17) hpre_8 hpre_7 hsafe1 hret2_14.1
      hret1_14.2.1 hlim fun b hb hb' => hnA b hb (hb'.elim Or.inr fun h => Or.inl (by rw [hsp]; omega))
    have hne8 := ne_add_self (k := 8) hpre_10 (by decide) (by decide)
    have hne16 := ne_add_self (k := 16) hpre_10 (by decide) (by decide)
    have hne816 := add_ne_add (j := 16) (k := 8) (n := 24) hpre_10 (by decide) (by decide) (by decide)
    dsimp only
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [Layouts.ResultE.tagOffset, Layouts.ResultE.Ok.tag, BitVec.add_zero]
      rw [MachineState.getMem_setMem_ne hne16, MachineState.getMem_setMem_ne hne8, MachineState.getMem_setMem_eq]
    · simp only [Layouts.ResultE.Ok.f0, Layouts.E.c0, BitVec.add_zero]
      rw [MachineState.getMem_setMem_ne hne816.symm, MachineState.getMem_setMem_eq, h0.1]
    · simp only [Layouts.ResultE.Ok.f0, Layouts.E.c1]
      rw [show regs .x10 + 8#64 + 8#64 = regs .x10 + 16#64 by rw [BitVec.add_assoc]; rfl,
        MachineState.getMem_setMem_eq, h0.2]
    · refine T2.keep hpre_8 ?_ ?_ ?_
      · exact keeps_store (keeps_store (keeps_store keeps_refl (not_inRange_apart0 hpre_12 (by decide)))
          (not_inRange_apart' hpre_12 hpre_10 (by decide))) (not_inRange_apart' hpre_12 hpre_10 (by decide))
      · unfold proofAddr at hpre_13
        simp only [Layouts.Transcript.proof] at hpre_13 ⊢
        rw [hq2, hq1]
        exact keeps_store (keeps_store (keeps_store keeps_refl (not_inRange_apart0 hpre_13 (by decide)))
          (not_inRange_apart' hpre_13 hpre_10 (by decide))) (not_inRange_apart' hpre_13 hpre_10 (by decide))
      · exact heapKept_store (heapKept_store (heapKept_store heapKept_refl hlim hpre_9 hret2_14.2.1) hlim
          (Nat.le_trans hpre_9 h8) hret2_14.2.1) hlim (Nat.le_trans hpre_9 h16) hret2_14.2.1

/-- **`Transcript::next_scalar` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN needA : Nat} (hnN : 64 + needN ≤ need) (hnA : 64 + needA ≤ need)
    (hnext : Spec.Transcript.Next.spec env p L.next.idx needN)
    (habs : Spec.Transcript.Absorb.spec env p L.absorb.idx needA) : spec env p i need :=
  ok_at env p i L hp hL hnN hnA hnext habs

end Rv64mc.Proof.Transcript.NextScalar
