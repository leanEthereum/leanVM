module

public import NativeVm.Code.Phase3.Inv
public import NativeVm.Code.Phase3.LayoutSpec
public import NativeVm.Code.Phase3.Checks

/-!
# Phase 3's first steps

The sides' placements and the push side's depth (`layoutCode`, `F1`), the depth's check, the grind,
the slot weights at `wR` and `β` at `betaR` (`FB`), each a step of `Inv`'s run.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters
open LeanVM.Protocol.Verifier (busBits busGrindingBits)

variable {env : Env} {inp : Input} {s0 : QState} {layout : LayoutW} {rate : Nat}

/-- The push side's depth. -/
abbrev dep (layout : LayoutW) : Nat := (sideLayout layout 0).depth

/-- The sides' placements and the push side's depth. -/
def F1 (env : Env) (layout : LayoutW) (s : QState) : Prop :=
  SidesAt s.mem env.work layout ∧ NatAt s.mem (depthR.at env.work) (dep layout)

/-- … and the depth below `64`. -/
def F3 (env : Env) (layout : LayoutW) (s : QState) : Prop := F1 env layout s ∧ dep layout < 64

/-- … and the slot weights. -/
def FW (env : Env) (layout : LayoutW) (w : Array EW) (s : QState) : Prop :=
  F3 env layout s ∧ w.size = 2 ^ busBits ∧ EWArr s.mem (wR.at env.work) w

/-- … and `β`. -/
def FB (env : Env) (layout : LayoutW) (w : Array EW) (b : EW) (s : QState) : Prop :=
  FW env layout w s ∧ EWAt s.mem (betaR.at env.work) b

section carry

variable {regs : List Reg64} {ws : List Region} {s s' : QState}

theorem Step3.sameR (hs : Step3 env regs ws s s') (hi : Inputs env inp s.mem)
    (hws : ∀ r ∈ ws, Ok3 r) {q : Region} (hc : Clear ws q.off q.stop) :
    Same s.mem s'.mem (q.at env.work) q.size := fun k hk ↦ by
  rw [Region.at, wd_wd]
  exact hs.word hi hws hc (by omega) (by unfold Region.stop; omega)

theorem F1.carry (h : F1 env layout s) (hs : Step3 env regs ws s s') (hi : Inputs env inp s.mem)
    (hws : ∀ r ∈ ws, Ok3 r) (hc : ∀ side < 3, Clear ws (placeR side).off (placeR side).stop)
    (hd : Clear ws depthR.off (depthR.off + 1)) : F1 env layout s' :=
  ⟨h.1.congr fun side hs' ↦ hs.sameR hi hws (hc side hs'), hs.natAtR hi hws hd h.2⟩

theorem F3.carry (h : F3 env layout s) (hs : Step3 env regs ws s s') (hi : Inputs env inp s.mem)
    (hws : ∀ r ∈ ws, Ok3 r) (hc : ∀ side < 3, Clear ws (placeR side).off (placeR side).stop)
    (hd : Clear ws depthR.off (depthR.off + 1)) : F3 env layout s' :=
  ⟨h.1.carry hs hi hws hc hd, h.2⟩

theorem FW.carry {w : Array EW} (h : FW env layout w s) (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r)
    (hc : ∀ side < 3, Clear ws (placeR side).off (placeR side).stop)
    (hd : Clear ws depthR.off (depthR.off + 1)) (hw : Clear ws wR.off wR.stop) : FW env layout w s' :=
  ⟨h.1.carry hs hi hws hc hd, h.2.1, hs.ewarrR hi hws hw (by rw [h.2.1]; decide) h.2.2⟩

theorem FB.carry {w : Array EW} {b : EW} (h : FB env layout w b s) (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r)
    (hc : ∀ side < 3, Clear ws (placeR side).off (placeR side).stop)
    (hd : Clear ws depthR.off (depthR.off + 1)) (hw : Clear ws wR.off wR.stop)
    (hb : Clear ws betaR.off (betaR.off + 2)) : FB env layout w b s' :=
  ⟨h.1.carry hs hi hws hc hd hw, hs.ewatR hi hws hb h.2⟩

end carry

/-- **The placements and the depth.** -/
theorem layout_pre : ∀ t s, Base env inp s0 layout rate t s ∧ True →
    WP layoutCode s (fun s' ↦ Base env inp s0 layout rate t s' ∧ F1 env layout s') fun _ ↦ False :=
  pre3 ok3_layoutWs (fun _ _ hb _ ↦ WP.mono (layout_spec hb.rdi hb.wp hb.hin hb.lay)
    (fun _ ⟨h1, h2, h3⟩ ↦ ⟨⟨h1, h2⟩, h3⟩) fun _ h ↦ h) fun _ _ _ _ _ h ↦ h

/-- **The depth's check.** -/
theorem checkDepth_ref :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ F1 env layout s) checkDepth
      (Model.require (decide (dep layout < 64)))
      (fun _ t s ↦ Base env inp s0 layout rate t s ∧ F3 env layout s ∧
        s.reg .rsi = (dep layout).toUInt64) (Kept env rs3 s0) := by
  refine Refines.require ?_
  rintro t s ⟨hb, hf⟩
  refine WP.mono (checkDepth_spec hb.rel hf.2) ?_ ?_
  · rintro s' ⟨hd, hrsi, hm, hr⟩
    have hw : Wrote env [] s s' := wrote_regs hm (hr .rdi (by decide))
    refine ⟨decide_eq_true hd, hb.wrote ok3_nil hw, ⟨?_, hd⟩, hrsi⟩
    exact ⟨hf.1.congr fun side _ k _ ↦ by rw [hm], hf.2.congr (by rw [hm])⟩
  · rintro s' ⟨hd, hm, hr⟩
    exact ⟨decide_eq_false hd, (hb.wrote ok3_nil (wrote_regs hm (hr .rdi (by decide)))).kept⟩

/-- **The grind.** -/
theorem grind_ref :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ (F3 env layout s ∧
        s.reg .rsi = (dep layout).toUInt64)) grindBus (Model.grind (busGrindingBits (dep layout)))
      (fun _ t s ↦ Base env inp s0 layout rate t s ∧ F3 env layout s) (Kept env rs3 s0) :=
  ref3 (Q := fun _ _ ↦ True) ok3_nil
    (fun _ _ hb hp ↦ WP.mono (grindBus_spec hb.rel hp.1.2 hp.2)
      (fun _ ⟨t', hr, hc, hs⟩ ↦ ⟨(), t', hr, hc, trivial, hs⟩) fun _ h ↦ h)
    fun _ _ _ hi hp hs _ ↦ hp.1.carry hs hi ok3_nil (by decide) (by decide)

/-- A count into `r12`. -/
theorem movi12_pre {P : QState → Prop} (k : Int64) (n : Nat) (hk : k.toUInt64 = n.toUInt64)
    (hP : ∀ s v, P s → P (s.setReg .r12 v)) :
    ∀ t s, Base env inp s0 layout rate t s ∧ P s →
      WP (I (.movi .r12 k)) s (fun s' ↦ Base env inp s0 layout rate t s' ∧
        (P s' ∧ s'.reg .r12 = n.toUInt64)) fun _ ↦ False := by
  rintro t s ⟨hb, hp⟩
  refine WP.ins rfl ⟨hb.wrote ok3_nil ((Wrote.refl env [] s).setReg (by decide) _), hP _ _ hp, ?_⟩
  rsimp
  exact hk

/-- **The slot weights.** -/
theorem weights_ref :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ (F3 env layout s ∧
        s.reg .r12 = (2 ^ busBits : Nat).toUInt64)) (samplesTo wR.off)
      (sampleChallenges (2 ^ busBits))
      (fun w t s ↦ Base env inp s0 layout rate t s ∧ FW env layout w s) (Kept env rs3 s0) :=
  ref3 (Q := fun w s ↦ w.size = 2 ^ busBits ∧ EWArr s.mem (wR.at env.work) w)
    (ws := [wR]) (fun r hr ↦ by rw [List.mem_singleton.mp hr]; exact ok3_sreg (by norm_num))
    (fun _ _ hb hp ↦ WP.mono (samplesTo_spec (ok3_sreg (by norm_num)) le_rfl
        (by simp [wR, sreg, Region.stop, busBits]) hb.rel hb.hin hp.2)
      (fun _ ⟨xs, t', hr, hc, hsz, ha, hs⟩ ↦ ⟨xs, t', hr, hc, ⟨hsz, ha⟩, hs⟩) fun _ h ↦ h.elim)
    fun _ _ _ hi hp hs hq ↦
      ⟨hp.1.carry hs hi (fun r hr ↦ by rw [List.mem_singleton.mp hr]; exact ok3_sreg (by norm_num))
        (by decide) (by decide), hq⟩

/-- **`β`.** -/
theorem beta_ref {w : Array EW} :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ FW env layout w s) (sampleTo betaR.off)
      Model.sampleChallenge
      (fun b t s ↦ Base env inp s0 layout rate t s ∧ FB env layout w b s) (Kept env rs3 s0) :=
  ref3 (Q := fun b s ↦ EWAt s.mem (betaR.at env.work) b)
    (ws := [betaR]) (fun r hr ↦ by rw [List.mem_singleton.mp hr]; exact ok3_sreg (by norm_num))
    (fun _ _ hb _ ↦ WP.mono (sampleTo_spec (ok3_sreg (by norm_num)) le_rfl
        (by simp [betaR, sreg, Region.stop]) hb.rel hb.hin)
      (fun _ ⟨x, t', hr, hc, ha, hs⟩ ↦ ⟨x, t', hr, hc, ha, hs⟩) fun _ h ↦ h.elim)
    fun _ _ _ hi hp hs hq ↦
      ⟨hp.carry hs hi (fun r hr ↦ by rw [List.mem_singleton.mp hr]; exact ok3_sreg (by norm_num))
        (by decide) (by decide) (by decide), hq⟩

end NativeVm.Code.P3
