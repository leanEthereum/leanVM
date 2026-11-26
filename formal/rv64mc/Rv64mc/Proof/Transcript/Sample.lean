/-
  Rv64mc.Proof.Transcript.Sample

  `Sponge::sample` keeps its contract (`Spec.Transcript.Sample.spec`), over any program holding its template, from
  `duplex`'s. The ground's tag is cleared on both paths (`SpongeAt.clearGround`); with a ground challenge it is
  returned, without one the sponge is permuted and its first two lanes returned.
-/

import Rv64mc.Spec.Transcript.Sample
import Rv64mc.Spec.Transcript.Duplex
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Model.Extra.Transcript
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Sponge.Sample
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.Sample

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.Sample
open Rv64mc.Proof.Transcript
open Rv64mc.Gen.Verifier.Transcript.Sponge.Sample (Link tmpl)

/-- The ground's tag, `0` or `1`, says whether a challenge waits. -/
theorem ground_tag {m : MachineState} {a : Word} {r : Model.SpongeRust} (h : SpongeAt m a r) :
    (m.getMem a &&& 1#64 = 0#64 ∧ r.ground = none) ∨
      ∃ e, m.getMem a &&& 1#64 ≠ 0#64 ∧ r.ground = some e ∧ m.getMem (a + 8#64) = (Model.limbs e).1 ∧
        m.getMem (a + 16#64) = (Model.limbs e).2 := by
  have hg := h.ground
  cases hr : r.ground with
  | none =>
    rw [hr] at hg
    simp only [OptionEAt, Layouts.Sponge.ground, Layouts.OptionE.tagOffset, Layouts.OptionE.None.tag] at hg
    rw [show a + BitVec.ofNat 64 0 + BitVec.ofNat 64 0 = a by simp] at hg
    exact Or.inl ⟨by rw [hg]; rfl, rfl⟩
  | some e =>
    rw [hr] at hg
    simp only [OptionEAt, EAt, Layouts.Sponge.ground, Layouts.OptionE.tagOffset, Layouts.OptionE.Some.tag,
      Layouts.OptionE.Some.f0, Layouts.E.c0, Layouts.E.c1] at hg
    rw [show a + BitVec.ofNat 64 0 + BitVec.ofNat 64 0 = a by simp,
      show a + BitVec.ofNat 64 0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 0 = a + 8#64 by simp,
      show a + BitVec.ofNat 64 0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 by
        simp [BitVec.add_assoc]] at hg
    exact Or.inr ⟨e, by rw [hg.1]; decide, rfl, hg.2.1, hg.2.2⟩

theorem sample_none {r : Model.SpongeRust} (hg : r.ground = none) :
    r.sample = (Model.challengeRust r.duplex.state, r.duplex) := by
  simp [Model.SpongeRust.sample, hg]

theorem sample_some {r : Model.SpongeRust} {e : E} (hg : r.ground = some e) :
    r.sample = (e, { r with ground := none }) := by
  simp [Model.SpongeRust.sample, hg]

theorem with_none {r : Model.SpongeRust} (hg : r.ground = none) : { r with ground := none } = r := by
  cases r; simp_all

/-- Lanes `0` and `1` of a sponge's state, at the addresses the code reads them. -/
theorem lanes01 {m : MachineState} {a : Word} {r : Model.SpongeRust} (h : SpongeAt m a r) :
    m.getMem (a + 24#64) = r.state.getD 0 0 ∧ m.getMem (a + 32#64) = r.state.getD 1 0 := by
  have hl := h.inv.1
  have h0 := h.state.2 0 (by omega)
  have h1 := h.state.2 1 (by omega)
  simp only [Layouts.Sponge.state] at h0 h1
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact ⟨by simpa using h0, by rw [← h1, BitVec.add_assoc]; rfl⟩

/-- The challenge a permuted sponge gives, at the addresses the code reads its lanes. -/
theorem challenge_at {m : MachineState} {a : Word} {r : Model.SpongeRust} (h : SpongeAt m a r) :
    m.getMem (a + 24#64) = (Model.limbs (Model.challengeRust r.state)).1 ∧
      m.getMem (a + 32#64) = (Model.limbs (Model.challengeRust r.state)).2 := by
  rw [Model.limbs_challengeRust]; exact lanes01 h

/-- **`Sponge::sample` keeps its contract**, for one sponge. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needD : Nat} (hnD : 16 + needD ≤ need)
    (hdup : Spec.Transcript.Duplex.spec env p L.duplex.idx needD) (r : Model.SpongeRust) :
    Holds env p i need (Pre r) (Post r) Out := by
  rv_auto hp with [hL] using [hdup r]
  all_goals
    have hS : env.stackLimit.toNat + 16 ≤ top.toNat := by omega
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_7
    simp only [Layouts.Sponge.byteSize] at hpre_8
    have hb : ∀ (c : Word) (k : Nat), Tactic.slotOk 16 c = true → Nat.ble k 328 = true →
        (top + c).toNat < (regs .x10 + BitVec.ofNat 64 k).toNat := fun c k hc hk => slot_below hS hc hpre_7 hpre_8 hk
    have hb0 : ∀ c : Word, Tactic.slotOk 16 c = true → (top + c).toNat < (regs .x10).toNat :=
      fun c hc => slot_below0 hS hc hpre_7
    simp (disch := first | exact hb0 _ rfl | exact hb _ _ rfl rfl) only [getMem_setMem_lt] at *
    have hkP : ∀ b, InRange (regs .x10) 328 b → ∀ c, Tactic.slotOk 16 c = true → (top + c).toNat < b.toNat :=
      fun b hb c hc => Nat.lt_of_lt_of_le (hb0 c hc) hb.1
  -- a ground challenge: taken
  iterate 2
    · simp (disch := exact hb0 _ rfl) only [getMem_setMem_gt]
      simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  · refine frame_store_out ?_ hlim hpre_7 (show InRange _ 328 _ from inRange_self (by decide))
    rv_close
  · refine static_store ?_ hlim hpre_7
    rv_close
  iterate 3
    · rcases ground_tag hpre_6 with ⟨h0, -⟩ | ⟨e, -, hg, he0, he1⟩
      · exact absurd h0 hc
      first
        | (rw [sample_some hg]; exact he0)
        | (rw [sample_some hg]; exact he1)
        | (rw [sample_some hg]
           exact SpongeAt.clearGround (hpre_6.keep hpre_8 fun b hb => by
             simp (disch := exact hkP b hb _ rfl) only [getMem_setMem_lt]) hpre_8)
  -- none: permuted, lanes `0` and `1`
  all_goals
    rcases ground_tag hpre_6 with ⟨-, hg⟩ | ⟨e, h1, -⟩
    rotate_left
    · exact absurd hc h1
  · refine static_store ?_ hlim hpre_7
    rv_close
  · rw [Env.next_setMem_stack (Nat.le_trans hlim hpre_7)]
    rv_close
  · rw [← with_none hg]
    exact SpongeAt.clearGround (hpre_6.keep hpre_8 fun b hb => by
      simp (disch := exact hkP b hb _ rfl) only [getMem_setMem_lt]) hpre_8
  · exact Nat.le_trans (Tactic.slot_le hS rfl) hpre_7
  · rw [hret1_14.getMem_above (a := top + 18446744073709551608#64) (Tactic.slot_ge hS rfl)
      (slot_mono hS rfl rfl rfl) fun h => absurd h.1 (Nat.not_le.2 (hb0 _ rfl))]
    simp (disch := exact hb0 _ rfl) only [getMem_setMem_gt]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  · rw [hret1_14.getMem_above (a := top + 18446744073709551600#64) (Tactic.slot_ge hS rfl)
      (slot_mono hS rfl rfl rfl) fun h => absurd h.1 (Nat.not_le.2 (hb0 _ rfl))]
    simp (disch := exact hb0 _ rfl) only [getMem_setMem_gt]
    simp only [MachineState.getMem_setMem_eq]
  · refine Env.Frame.trans ?_ hret1_14 (Tactic.slot_le hS rfl) fun b hb => Or.inr (Or.inr (Or.inr hb))
    refine frame_store_out ?_ hlim hpre_7 (show InRange _ 328 _ from inRange_self (by decide))
    rv_close
  · rw [sample_none hg]; exact (challenge_at hret1_16).1
  · rw [sample_none hg]; exact (challenge_at hret1_16).2
  · rw [sample_none hg]; exact hret1_16

/-- **`Sponge::sample` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needD : Nat} (hnD : 16 + needD ≤ need)
    (hdup : Spec.Transcript.Duplex.spec env p L.duplex.idx needD) : spec env p i need :=
  ok_at env p i L hp hL hnD hdup

end Rv64mc.Proof.Transcript.Sample
