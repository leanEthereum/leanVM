module

public import NativeVm.Code.Phase3.Front2
public import NativeVm.Code.Phase3.Share
public import NativeVm.Code.Phase3.BcMle

/-!
# Phase 3's bytecode share

The share, its sumcheck and value (`shareCode`, `FS`), the value checked against the bytecode's
multilinear extension (`bcCode`), each a step of `Inv`'s run.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters
open LeanVM.Protocol.Verifier (busBits)

variable {env : Env} {inp : Input} {s0 : QState} {layout : LayoutW} {rate : Nat}

/-- … and the share, its value and the share's slot point. -/
def FS (env : Env) (layout : LayoutW) (w : Array EW) (b c : EW) (p tv m : Array EW) (mf bf : EW)
    (r : EW × Array EW × EW) (s : QState) : Prop :=
  FC env layout w b c p tv m mf bf s ∧ EWAt s.mem (shareR.at env.work) r.1 ∧
    EWAt s.mem (valueR.at env.work) r.2.2 ∧
    ∃ slot, r.2.1 = p.extract 0 layout.logBytecode ++ slot ∧ slot.size = busBits ∧
      EWArr s.mem (slotR.at env.work) slot

theorem ok3_share : ∀ r ∈ [shareR, valueR, slotR, tmpR], Ok3 r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact ok3_sreg (by norm_num)

theorem ok3_tmp : ∀ r ∈ [tmpR], Ok3 r := ok3_one (ok3_sreg (by norm_num))

/-- **The bytecode share.** -/
theorem share_ref {w p tv m : Array EW} {b c mf bf : EW} :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ FC env layout w b c p tv m mf bf s)
      shareCode (bytecodeShare w (p.extract 0 layout.logBytecode))
      (fun r t s ↦ Base env inp s0 layout rate t s ∧ FS env layout w b c p tv m mf bf r s)
      (Kept env rs3 s0) :=
  ref3 (Q := fun r s ↦ EWAt s.mem (shareR.at env.work) r.1 ∧ EWAt s.mem (valueR.at env.work) r.2.2 ∧
      ∃ slot, r.2.1 = p.extract 0 layout.logBytecode ++ slot ∧ slot.size = busBits ∧
        EWArr s.mem (slotR.at env.work) slot)
    ok3_share
    (fun _ _ hb hp ↦ WP.mono (share_spec _ hb.rel hb.hin hp.1.1.1.2.2 hp.1.1.1.2.1)
      (fun _ ⟨r, t', hr, hc, h1, h2, h3, hs⟩ ↦ ⟨r, t', hr, hc, ⟨h1, h2, h3⟩, hs⟩) fun _ h ↦ h)
    fun _ _ _ hi hp hs hq ↦ ⟨hp.carry hs hi ok3_share (by decide) (by decide) (by decide)
      (by decide), hq⟩

/-- **The bytecode's value.** -/
theorem bc_ref {w p tv m : Array EW} {b c mf bf : EW} {r : EW × Array EW × EW} :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ FS env layout w b c p tv m mf bf r s)
      bcCode (computedBytecodeValue layout.bytecode r.2.1 r.2.2)
      (fun _ t s ↦ Base env inp s0 layout rate t s ∧ (FC env layout w b c p tv m mf bf s ∧
        EWAt s.mem (shareR.at env.work) r.1))
      (Kept env rs3 s0) := by
  rintro t s ⟨hb, hf, hsh, hv, slot, hr, hss, hsl⟩
  have hps : p.size < 64 := by rw [hf.1.2.2.1]; exact hf.1.1.1.1.2
  have hdw : NatAt s.mem (depthR.at env.work) p.size := by rw [hf.1.2.2.1]; exact hf.1.1.1.1.1.2
  rw [hr, hb.lay.bytecode]
  refine WP.mono (bc_spec hb.rel hb.hin hb.lay hdw hps hf.1.2.2.2.1 hsl hss hv) ?_ ?_
  · rintro s' ⟨t', hrun, hc, hs⟩
    exact ⟨(), t', hrun, hb.step ok3_tmp hs hc, hf.carry hs hb.hin ok3_tmp (by decide) (by decide)
      (by decide) (by decide), hs.ewatR hb.hin ok3_tmp (by decide) hsh⟩
  · rintro s' ⟨hrun, hs⟩
    exact ⟨hrun, hb.fail ok3_tmp hs⟩

end NativeVm.Code.P3
