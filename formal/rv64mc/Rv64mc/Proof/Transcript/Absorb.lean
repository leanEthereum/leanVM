/-
  Rv64mc.Proof.Transcript.Absorb

  `Sponge::absorb` keeps its contract (`Spec.Transcript.Absorb.spec`), over any program holding its template, from
  the contracts of `duplex` and of the panics. `rv_auto` runs every path; the ground challenge's and the slot's
  bound checks end in panics. What is left on the two paths that return (a full queue permuted first, or not) is
  the same store of the slot and the count over a base memory: the prologue's, or `duplex`'s. The sponge there is
  `SpongeAt.push`'s; the reads of the sponge through the function's own stack stores, which `rv_sym` does not pass,
  are passed by `getMem_setMem_lt` (a slot of the stack lies below the sponge, `slot_below`).
-/

import Rv64mc.Spec.Transcript.Absorb
import Rv64mc.Spec.Transcript.Duplex
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Sponge.Absorb
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.Absorb

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.Absorb
open Rv64mc.Spec.Runtime Rv64mc.Proof.Transcript
open Rv64mc.Gen.Verifier.Transcript.Sponge.Absorb (Link tmpl)

theorem absorb_eq {r : Model.SpongeRust} (hg : r.ground = none) (h4 : r.nPending ≠ 4) (v : E) (t : Word) :
    r.absorb v t = some (r.push (v, t)) := by
  simp [Model.SpongeRust.absorb, hg, h4]

theorem absorb_eq4 {r : Model.SpongeRust} (hg : r.ground = none) (h4 : r.nPending = 4) (v : E) (t : Word) :
    r.absorb v t = some (r.duplex.push (v, t)) := by
  simp [Model.SpongeRust.absorb, hg, h4]

/-- No ground challenge where the tag reads `0`. -/
theorem ground_none {m : MachineState} {a : Word} {r : Model.SpongeRust} (h : SpongeAt m a r)
    (h0 : m.getMem a = 0#64) : r.ground = none := by
  have hg := h.ground
  cases hr : r.ground with
  | none => rfl
  | some e =>
    rw [hr] at hg
    simp only [OptionEAt, Layouts.Sponge.ground, Layouts.OptionE.tagOffset, Layouts.OptionE.Some.tag] at hg
    rw [show a + BitVec.ofNat 64 0 + BitVec.ofNat 64 0 = a by simp, h0] at hg
    exact absurd hg.1 (by decide)

theorem ne_slot {a : Word} {n : Nat} (ha : a.toNat + 328 < 2 ^ 64) (hn : n ≤ 3) :
    a + 320#64 ≠ a + BitVec.ofNat 64 (24 * n) + 224#64 := by
  rw [add_ofNat_lit]; exact add_ne_add (n := 328) ha (by decide) (by omega) (by omega)

theorem count_eq {m : MachineState} {a : Word} {r : Model.SpongeRust} (h : SpongeAt m a r) :
    m.getMem (a + 320#64) = BitVec.ofNat 64 r.nPending := by
  simpa [Layouts.Sponge.n_pending] using h.nPending

/-- **`Sponge::absorb` keeps its contract**, for one sponge and value. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needD needP needB : Nat} (hnD : 48 + needD ≤ need) (hnP : 48 + needP ≤ need)
    (hnB : 48 + needB ≤ need) (hdup : Spec.Transcript.Duplex.spec env p L.duplex.idx needD)
    (hpf : NoReturn env p L.panicFmt.idx needP) (hpb : NoReturn env p L.panicBoundsCheck.idx needB)
    (r : Model.SpongeRust) (v : E) : Holds env p i need (Pre r v) (Post r v) Out := by
  rv_auto hp with [hL] using [hdup r, hpf, hpb]
  all_goals
    have hS : env.stackLimit.toNat + 48 ≤ top.toNat := by omega
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_7
    simp only [Layouts.Sponge.byteSize] at hpre_8
    have hb : ∀ (c : Word) (k : Nat), Tactic.slotOk 48 c = true → Nat.ble k 328 = true →
        (top + c).toNat < (regs .x10 + BitVec.ofNat 64 k).toNat := fun c k hc hk => slot_below hS hc hpre_7 hpre_8 hk
    have hb0 : ∀ c : Word, Tactic.slotOk 48 c = true → (top + c).toNat < (regs .x10).toNat :=
      fun c hc => slot_below0 hS hc hpre_7
    simp (disch := first | exact hb0 _ rfl | exact hb _ _ rfl rfl) only [getMem_setMem_lt] at *
    have hn4 := hpre_6.inv.2.2
    have hg := ground_none hpre_6 hc_1
    rw [count_eq hpre_6] at *
    have hb' : ∀ (c : Word) (k : Nat), Tactic.slotOk 48 c = true → k ≤ 328 →
        (top + c).toNat < (regs .x10 + BitVec.ofNat 64 k).toNat :=
      fun c k hc hk => slot_below (K := 328) hS hc hpre_7 hpre_8 (by simp [hk])
    have hkP : ∀ b, InRange (regs .x10) 328 b → ∀ c, Tactic.slotOk 48 c = true → (top + c).toNat < b.toNat :=
      fun b hb c hc => Nat.lt_of_lt_of_le (hb0 c hc) hb.1
  -- each path's facts: the queue not full, or full and permuted first
  all_goals try
    have hn3 : r.nPending ≤ 3 := (ofNat_le_iff (by omega) (by decide)).1 hc
    have h4 : r.nPending ≠ 4 := fun h => hc_2 (by rw [h])
  all_goals try
    have h4 : r.nPending = 4 := by simpa using (ofNat_inj (by omega) (by decide)).1 hc_2
    have hd := hret3_16
  -- the slot's address and the count, as `pushMem` states them
  all_goals try rw [count_eq hret3_16]
  all_goals try rw [slot24 (by omega)]
  all_goals try rw [slot24 (by simp)]
  all_goals try rw [MachineState.getMem_setMem_ne (ne_slot hpre_8 (by omega))]
  all_goals try rw [MachineState.getMem_setMem_ne (ne_slot hpre_8 (by simp))]
  all_goals try simp (disch := first | exact hb0 _ rfl | exact hb _ _ rfl rfl) only [getMem_setMem_lt]
  all_goals try rw [count_eq hpre_6]
  all_goals try rw [count_eq hret3_16]
  all_goals try simp only [add_ofNat_lit]
  -- the result
  all_goals try (rw [absorb_eq hg h4 v _]; rfl)
  all_goals try (rw [absorb_eq4 hg h4 v _]; rfl)
  all_goals try
    rw [absorb_eq hg h4 v _]
    refine SpongeAt.push (hpre_6.keep hpre_8 fun b hb => ?_) hpre_8 (by omega) v _
    simp (disch := exact hkP b hb _ rfl) only [getMem_setMem_lt]
  all_goals try (rw [absorb_eq4 hg h4 v _]; exact SpongeAt.push hd hpre_8 (by simp) v _)
  -- `duplex`'s precondition
  all_goals try (exact hpre_6.keep hpre_8 fun b hb => by simp (disch := exact hkP b hb _ rfl) only [getMem_setMem_lt])
  all_goals try exact Nat.le_trans (Tactic.slot_le hS rfl) hpre_7
  all_goals try exact hret3_14.2.1
  -- the saved registers, past the slot's stores (and `duplex`'s frame)
  all_goals try
    simp (disch := (refine hb' _ _ rfl ?_; omega)) only [getMem_setMem_gt]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  all_goals try
    simp (disch := (refine hb' _ _ rfl ?_; simp)) only [getMem_setMem_gt]
    rw [hret3_14.getMem_above (Tactic.slot_ge (c := 18446744073709551568#64) hS rfl)
      (slot_mono hS rfl rfl rfl) fun h => absurd h.1 (Nat.not_le.2 (hb0 _ rfl))]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  -- the frame and the static data
  all_goals try
    refine frame_store_obj (frame_store_obj (frame_store_obj (frame_store_obj ?_ hlim hpre_7 hpre_8 ?_ ?_)
      hlim hpre_7 hpre_8 ?_ ?_) hlim hpre_7 hpre_8 ?_ ?_) hlim hpre_7 hpre_8 ?_ ?_
    all_goals first
      | (show InRange _ 328 _; exact inRange_add hpre_8 (by first | omega | simp))
      | (refine Env.Frame.trans ?_ hret3_14 (Tactic.slot_le hS rfl) fun b hb => Or.inr (Or.inr (Or.inr hb))
         rv_close)
      | omega
      | simp
      | rv_close
  all_goals
    refine static_store_obj (static_store_obj (static_store_obj (static_store_obj ?_ hlim hpre_7 hpre_8 ?_)
      hlim hpre_7 hpre_8 ?_) hlim hpre_7 hpre_8 ?_) hlim hpre_7 hpre_8 ?_
    all_goals first | exact hret3_15 | omega | simp | rv_close

/-- **`Sponge::absorb` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needD needP needB : Nat} (hnD : 48 + needD ≤ need) (hnP : 48 + needP ≤ need)
    (hnB : 48 + needB ≤ need) (hdup : Spec.Transcript.Duplex.spec env p L.duplex.idx needD)
    (hpf : NoReturn env p L.panicFmt.idx needP) (hpb : NoReturn env p L.panicBoundsCheck.idx needB) :
    spec env p i need :=
  ok_at env p i L hp hL hnD hnP hnB hdup hpf hpb

end Rv64mc.Proof.Transcript.Absorb
