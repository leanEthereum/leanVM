/-
  Rv64mc.Proof.Transcript.AbsorbNonce

  `Sponge::absorb_nonce` keeps its contract (`Spec.Transcript.AbsorbNonce.spec`), from the contracts of `absorb`
  and `duplex`: the nonce absorbed with its tag, the state permuted, its first two lanes stored as the ground
  challenge (`SpongeAt.setGround`) and its third returned.
-/

import Rv64mc.Spec.Transcript.AbsorbNonce
import Rv64mc.Spec.Transcript.Absorb
import Rv64mc.Spec.Transcript.Duplex
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Transcript.Sample
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Sponge.AbsorbNonce
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.AbsorbNonce

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript
open Rv64mc.Spec.Transcript.AbsorbNonce Rv64mc.Proof.Transcript
open Rv64mc.Gen.Verifier.Transcript.Sponge.AbsorbNonce (Link tmpl)

theorem absorbNonce_eq {r r1 : Model.SpongeRust} {nc : E} (h : r.absorb nc 4#64 = some r1) :
    r.absorbNonce nc = some (r1.duplex.state.getD 2 0,
      { r1.duplex with ground := some (Model.challengeRust r1.duplex.state) }) := by
  simp [Model.SpongeRust.absorbNonce, Model.dsPowNonceR, h]

/-- Lane `2` of a sponge's state, at the address the code reads it. -/
theorem lane2 {m : MachineState} {a : Word} {r : Model.SpongeRust} (h : SpongeAt m a r) :
    m.getMem (a + 40#64) = r.state.getD 2 0 := by
  have hl := h.inv.1
  have h2 := h.state.2 2 (by omega)
  simp only [Layouts.Sponge.state] at h2
  rw [List.getD_eq_getElem _ _ (by omega), ← h2, BitVec.add_assoc]; rfl

/-- **`Sponge::absorb_nonce` keeps its contract**, for one sponge and nonce. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needD : Nat} (hnA : 16 + needA ≤ need) (hnD : 16 + needD ≤ need)
    (habs : Spec.Transcript.Absorb.spec env p L.absorb.idx needA)
    (hdup : Spec.Transcript.Duplex.spec env p L.duplex.idx needD) (r : Model.SpongeRust) (nc : E) :
    Holds env p i need (Pre r nc) (Post r nc) Out := by
  rv_auto hp with [hL] using [habs r nc, hdup ((r.absorb nc 4#64).getD r)]
  all_goals
    have hS : env.stackLimit.toNat + 16 ≤ top.toNat := by omega
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_7
    simp only [Layouts.Sponge.byteSize] at hpre_8
    have hst : ∀ c : Word, Tactic.slotOk 16 c = true → (top + c).toNat < top.toNat := fun c hc => Tactic.slot_lt hS hc
    have hkP : ∀ b, InRange (regs .x10) 328 b → ∀ c, Tactic.slotOk 16 c = true → (top + c).toNat < b.toNat :=
      fun b hb c hc => Nat.lt_of_lt_of_le (hst c hc) (Nat.le_trans hpre_7 hb.1)
    have h8 := toNat_le_add (k := 8) hpre_8 (by decide)
    have h16 := toNat_le_add (k := 16) hpre_8 (by decide)
    have hsp : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
      rw [show (18446744073709551600#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 16) by decide]
      exact toNat_sub_lit (by omega) (by decide)
  -- `absorb`'s and `duplex`'s preconditions
  all_goals try
    refine hpre_6.keep hpre_8 fun b hb => ?_
    simp (disch := exact hkP b hb _ rfl) only [getMem_setMem_lt]
  all_goals try exact Nat.le_trans (Tactic.slot_le hS rfl) hpre_7
  all_goals try exact hret1_14.2.1
  -- after the calls
  all_goals
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 hret1_16
    rw [hr1, Option.getD_some] at hret2_16
  all_goals
    have hm1 := fun (c : Word) (hc : Tactic.slotOk 16 c = true) =>
      hret1_14.getMem_above (a := top + c) (Tactic.slot_ge hS rfl)
        (by have := slot_ge_sub (k := 16) hS (by decide) hc; rw [hsp]; omega) fun h => by
        simp only [Spec.Transcript.Absorb.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
          ↓reduceIte, Layouts.Sponge.byteSize] at h
        have := hst c hc; omega
  all_goals
    have hm2 := fun (c : Word) (hc : Tactic.slotOk 16 c = true) =>
      hret2_14.getMem_above (a := top + c) (Tactic.slot_ge hS rfl)
        (by have := slot_ge_sub (k := 16) hS (by decide) hc; rw [hsp]; omega) fun h => by
        simp only [Spec.Transcript.Duplex.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
          ↓reduceIte, Layouts.Sponge.byteSize] at h
        have := hst c hc; omega
  all_goals try
    simp (disch := first
      | exact Nat.lt_of_lt_of_le (hst _ rfl) hpre_7
      | exact Nat.lt_of_lt_of_le (hst _ rfl) (Nat.le_trans hpre_7 h8)
      | exact Nat.lt_of_lt_of_le (hst _ rfl) (Nat.le_trans hpre_7 h16)) only [getMem_setMem_gt]
    simp (disch := decide) only [hm2, hm1]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  -- the frame, the static data
  · refine frame_store_obj (k := 16) (frame_store_obj (k := 8) (frame_store_out ?_ hlim hpre_7
      (inRange_self (by decide))) hlim hpre_7 hpre_8 (by decide) (inRange_add hpre_8 (by decide))) hlim hpre_7 hpre_8
      (by decide) (inRange_add hpre_8 (by decide))
    refine Env.Frame.trans (Env.Frame.trans ?_ hret1_14 (Tactic.slot_le hS rfl) fun b hb => ?_) hret2_14
      (Tactic.slot_le hS rfl) fun b hb => ?_
    · rv_close
    all_goals
      simp only [Spec.Transcript.Absorb.Out, Spec.Transcript.Duplex.Out, InRange, Lprog.updReg_apply, Tactic.rf,
        reduceCtorEq, ↓reduceIte, Layouts.Sponge.byteSize] at hb
      exact Or.inr (Or.inr (Or.inr hb))
  · exact static_store_obj (k := 16) (static_store_obj (k := 8) (static_store hret2_15 hlim hpre_7) hlim hpre_7
      hpre_8 (by decide)) hlim hpre_7 hpre_8 (by decide)
  -- the result: the third lane, the first two as the ground challenge
  · rw [absorbNonce_eq hr1]; rfl
  · rw [absorbNonce_eq hr1, Option.getD_some, lane2 hret2_16]
  · rw [absorbNonce_eq hr1, Option.getD_some]
    have hc01 := Sample.challenge_at hret2_16
    refine hret2_16.setGround (fun k hk hk' => ?_) ?_
    · rw [MachineState.getMem_setMem_ne (add_ne_add (n := 328) hpre_8 (by omega) (by decide) (by omega)),
        MachineState.getMem_setMem_ne (add_ne_add (n := 328) hpre_8 (by omega) (by decide) (by omega)),
        MachineState.getMem_setMem_ne (by
          have := add_ne_add (j := k) (k := 0) (n := 328) hpre_8 (by omega) (by decide) (by omega)
          simpa using this)]
    · simp only [OptionEAt, EAt, Layouts.Sponge.ground, Layouts.OptionE.tagOffset, Layouts.OptionE.Some.tag,
        Layouts.OptionE.Some.f0, Layouts.E.c0, Layouts.E.c1, BitVec.add_zero]
      refine ⟨?_, ?_, ?_⟩
      · rw [MachineState.getMem_setMem_ne (ne_add_self (k := 16) hpre_8 (by decide) (by decide)),
          MachineState.getMem_setMem_ne (ne_add_self (k := 8) hpre_8 (by decide) (by decide)),
          MachineState.getMem_setMem_eq]
      · rw [MachineState.getMem_setMem_ne (add_ne_add (j := 8) (k := 16) (n := 328) hpre_8 (by decide) (by decide)
          (by decide)), MachineState.getMem_setMem_eq, hc01.1]
      · rw [show regs .x10 + 8#64 + 8#64 = regs .x10 + 16#64 by rw [BitVec.add_assoc]; rfl,
          MachineState.getMem_setMem_eq, hc01.2]

/-- **`Sponge::absorb_nonce` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needD : Nat} (hnA : 16 + needA ≤ need) (hnD : 16 + needD ≤ need)
    (habs : Spec.Transcript.Absorb.spec env p L.absorb.idx needA)
    (hdup : Spec.Transcript.Duplex.spec env p L.duplex.idx needD) : spec env p i need :=
  ok_at env p i L hp hL hnA hnD habs hdup

end Rv64mc.Proof.Transcript.AbsorbNonce
