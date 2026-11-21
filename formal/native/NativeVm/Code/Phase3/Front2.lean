module

public import NativeVm.Code.Phase3.Front1
public import NativeVm.Code.Phase3.Gkr

/-!
# Phase 3's GKR walk and reads

The GKR walk (`gkrCode`: count root, point, trees' values, `FG`), the count root's check, the
memory's two limbs and the two final counters (`FC`), each a step of `Inv`'s run.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters
open LeanVM.Protocol.Verifier (busBits)

variable {env : Env} {inp : Input} {s0 : QState} {layout : LayoutW} {rate : Nat}

/-- … and the GKR walk's count root, point and trees' values. -/
def FG (env : Env) (layout : LayoutW) (w : Array EW) (b c : EW) (p tv : Array EW) (s : QState) :
    Prop :=
  FB env layout w b s ∧ EWAt s.mem (countR.at env.work) c ∧ p.size = dep layout ∧
    EWArr s.mem (pointR.at env.work) p ∧ tv.size = 3 ∧ EWArr s.mem (treeR.at env.work) tv

/-- … and the memory's limbs and final counter, the bytecode's final counter. -/
def FC (env : Env) (layout : LayoutW) (w : Array EW) (b c : EW) (p tv m : Array EW) (mf bf : EW)
    (s : QState) : Prop :=
  FG env layout w b c p tv s ∧ m.size = 2 ∧ EWArr s.mem (memR.at env.work) m ∧
    EWAt s.mem (memFinalR.at env.work) mf ∧ EWAt s.mem (bcFinalR.at env.work) bf

section carry

variable {regs : List Reg64} {ws : List Region} {s s' : QState}

/-- The words of `FG`'s regions apart from `ws`. -/
def ClearG (ws : List Region) : Prop :=
  (∀ side < 3, Clear ws (placeR side).off (placeR side).stop) ∧
    Clear ws depthR.off (depthR.off + 1) ∧ Clear ws wR.off wR.stop ∧
    Clear ws betaR.off (betaR.off + 2) ∧ Clear ws countR.off (countR.off + 2) ∧
    Clear ws pointR.off pointR.stop ∧ Clear ws treeR.off treeR.stop

instance (ws : List Region) : Decidable (ClearG ws) := by unfold ClearG; infer_instance

theorem FG.carry {w p tv : Array EW} {b c : EW} (h : FG env layout w b c p tv s)
    (hs : Step3 env regs ws s s') (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r)
    (hc : ClearG ws) : FG env layout w b c p tv s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h
  have hd : dep layout < 64 := g1.1.1.2
  refine ⟨g1.carry hs hi hws h1 h2 h3 h4, hs.ewatR hi hws h5 g2, g3, hs.ewarrR hi hws h6 ?_ g4, g5,
    hs.ewarrR hi hws h7 (by rw [g5]; decide) g6⟩
  rw [g3]; change 2 * dep layout ≤ 128; omega

theorem FC.carry {w p tv m : Array EW} {b c mf bf : EW} (h : FC env layout w b c p tv m mf bf s)
    (hs : Step3 env regs ws s s') (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r)
    (hc : ClearG ws) (hm : Clear ws memR.off memR.stop)
    (hmf : Clear ws memFinalR.off (memFinalR.off + 2))
    (hbf : Clear ws bcFinalR.off (bcFinalR.off + 2)) : FC env layout w b c p tv m mf bf s' :=
  ⟨h.1.carry hs hi hws hc, h.2.1, hs.ewarrR hi hws hm (by rw [h.2.1]; decide) h.2.2.1,
    hs.ewatR hi hws hmf h.2.2.2.1, hs.ewatR hi hws hbf h.2.2.2.2⟩

end carry

theorem ok3_one {r : Region} (h : Ok3 r) : ∀ q ∈ [r], Ok3 q := fun q hq ↦ by
  rw [List.mem_singleton.mp hq]; exact h

theorem ok3_gkr : ∀ r ∈ [pointR, treeR, countR, tmpR], Ok3 r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact ok3_sreg (by norm_num)

/-- **The GKR walk.** -/
theorem gkr_ref {w : Array EW} {b : EW} :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ FB env layout w b s) gkrCode
      (verifyGkrGrandProducts (dep layout))
      (fun r t s ↦ Base env inp s0 layout rate t s ∧ FG env layout w b r.1 r.2.1 r.2.2 s)
      (Kept env rs3 s0) :=
  ref3 (Q := fun r s ↦ EWAt s.mem (countR.at env.work) r.1 ∧ r.2.1.size = dep layout ∧
      EWArr s.mem (pointR.at env.work) r.2.1 ∧ r.2.2.size = 3 ∧ EWArr s.mem (treeR.at env.work) r.2.2)
    ok3_gkr
    (fun _ _ hb hp ↦ WP.mono (gkr_spec hb.rel hb.hin hp.1.1.2 hp.1.1.1.2)
      (fun _ ⟨r, t', hr, hc, h1, h2, h3, h4, h5, hs⟩ ↦ ⟨r, t', hr, hc, ⟨h1, h2, h3, h4, h5⟩, hs⟩)
      fun _ h ↦ h)
    fun _ _ _ hi hp hs hq ↦ ⟨hp.carry hs hi ok3_gkr (by decide) (by decide) (by decide)
      (by decide), hq⟩

/-- **The count root's check.** -/
theorem checkCount_ref {w p tv : Array EW} {b c : EW} :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ FG env layout w b c p tv s) checkCount
      (Model.require (c != 0))
      (fun _ t s ↦ Base env inp s0 layout rate t s ∧ FG env layout w b c p tv s) (Kept env rs3 s0) := by
  refine Refines.require ?_
  rintro t s ⟨hb, hf⟩
  refine WP.mono (checkCount_spec hb.rel hf.2.1) ?_ ?_
  · rintro s' ⟨hc, hm, hr⟩
    have hw : Wrote env [] s s' := wrote_regs hm (hr .rdi (by decide))
    exact ⟨hc, hb.wrote ok3_nil hw, hf.carry hw.step hb.hin ok3_nil (by decide)⟩
  · rintro s' ⟨hc, hm, hr⟩
    exact ⟨hc, (hb.wrote ok3_nil (wrote_regs hm (hr .rdi (by decide)))).kept⟩

theorem ok3_memR : Ok3 memR := ok3_sreg (by norm_num)
theorem ok3_memFinalR : Ok3 memFinalR := ok3_sreg (by norm_num)
theorem ok3_bcFinalR : Ok3 bcFinalR := ok3_sreg (by norm_num)

/-- **The memory's limbs.** -/
theorem mem_ref {w p tv : Array EW} {b c : EW} :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ (FG env layout w b c p tv s ∧
        s.reg .r12 = (2 : Nat).toUInt64)) (readsTo memR.off) (readScalars 2)
      (fun m t s ↦ Base env inp s0 layout rate t s ∧ (FG env layout w b c p tv s ∧ m.size = 2 ∧
        EWArr s.mem (memR.at env.work) m)) (Kept env rs3 s0) :=
  ref3 (Q := fun m s ↦ m.size = 2 ∧ EWArr s.mem (memR.at env.work) m) (ok3_one ok3_memR)
    (fun _ _ hb hp ↦ WP.mono (readsTo_spec ok3_memR le_rfl (by decide) hb.rel hb.hin hp.2)
      (fun _ ⟨xs, t', hr, hc, hsz, ha, hs⟩ ↦ ⟨xs, t', hr, hc, ⟨hsz, ha⟩, hs⟩) fun _ h ↦ h)
    fun _ _ _ hi hp hs hq ↦ ⟨hp.1.carry hs hi (ok3_one ok3_memR) (by decide), hq⟩

/-- **The memory's final counter.** -/
theorem memFinal_ref {w p tv m : Array EW} {b c : EW} :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ (FG env layout w b c p tv s ∧ m.size = 2 ∧
        EWArr s.mem (memR.at env.work) m)) (readTo memFinalR.off) Model.readScalar
      (fun mf t s ↦ Base env inp s0 layout rate t s ∧ (FG env layout w b c p tv s ∧ m.size = 2 ∧
        EWArr s.mem (memR.at env.work) m ∧ EWAt s.mem (memFinalR.at env.work) mf))
      (Kept env rs3 s0) :=
  ref3 (Q := fun mf s ↦ EWAt s.mem (memFinalR.at env.work) mf) (ok3_one ok3_memFinalR)
    (fun _ _ hb _ ↦ WP.mono (readTo_spec ok3_memFinalR le_rfl (by decide) hb.rel hb.hin)
      (fun _ ⟨x, t', hr, hc, ha, hs⟩ ↦ ⟨x, t', hr, hc, ha, hs⟩) fun _ h ↦ h)
    fun _ _ _ hi hp hs hq ↦ ⟨hp.1.carry hs hi (ok3_one ok3_memFinalR) (by decide), hp.2.1,
      hs.ewarrR hi (ok3_one ok3_memFinalR) (by decide) (by rw [hp.2.1]; decide) hp.2.2, hq⟩

/-- **The bytecode's final counter.** -/
theorem bcFinal_ref {w p tv m : Array EW} {b c mf : EW} :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ (FG env layout w b c p tv s ∧ m.size = 2 ∧
        EWArr s.mem (memR.at env.work) m ∧ EWAt s.mem (memFinalR.at env.work) mf))
      (readTo bcFinalR.off) Model.readScalar
      (fun bf t s ↦ Base env inp s0 layout rate t s ∧ FC env layout w b c p tv m mf bf s)
      (Kept env rs3 s0) :=
  ref3 (Q := fun bf s ↦ EWAt s.mem (bcFinalR.at env.work) bf) (ok3_one ok3_bcFinalR)
    (fun _ _ hb _ ↦ WP.mono (readTo_spec ok3_bcFinalR le_rfl (by decide) hb.rel hb.hin)
      (fun _ ⟨x, t', hr, hc, ha, hs⟩ ↦ ⟨x, t', hr, hc, ha, hs⟩) fun _ h ↦ h)
    fun _ _ _ hi hp hs hq ↦ ⟨hp.1.carry hs hi (ok3_one ok3_bcFinalR) (by decide), hp.2.1,
      hs.ewarrR hi (ok3_one ok3_bcFinalR) (by decide) (by rw [hp.2.1]; decide) hp.2.2.1,
      hs.ewatR hi (ok3_one ok3_bcFinalR) (by decide) hp.2.2.2, hq⟩

end NativeVm.Code.P3
