module

public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.FrameRun

/-!
# Footprints passed to a callee of a transcript function

A function with an `F`-byte frame at the top of its `n` bytes of stack calls a function using `n'`
bytes below the frame (`n' ≤ n - F`): the `TState`'s footprint (`TStateOk.callee`) and an output
in the frame (`OutOk.frame`) hold for the callee.
-/

namespace NativeRustcVmArm.Transcript

open NativeRustcArm NativeRustcVm.Transcript

public section

variable [Labels] {m0 d : MachineData} {n F n' : Nat} {t : BitVec 64} {a : DecArea}

theorem TStateOk.callee (h : TStateOk m0 t a n) (hsp : d.regs.SP.toBitVec = frameBase m0 F)
    (hn : n ≤ m0.regs.SP.toNat) (hF : F ≤ n) (hn' : n' ≤ n - F) : TStateOk d t a n' :=
  ⟨apart_callee h.1 hsp hn hF hn', apart_callee h.2.1 hsp hn hF hn', h.2.2⟩

/-- An output of `l` bytes at offset `ob` of the frame, for a callee using `n'` bytes below it. -/
theorem OutOk.frame (hst : StackOk m0 n) (hF : F ≤ n) (hn' : n' ≤ n - F)
    (hsp : d.regs.SP.toBitVec = frameBase m0 F) (hk : Kept m0.dmem d.dmem) {ob l : Nat}
    (hob : ob + l ≤ F) (h : TStateOk m0 t a n) (hrc : RcAt m0 n) :
    OutOk d t a (off (frameBase m0 F) ob) l n' := by
  have hn := hst.2.1
  have hlt := m0.regs.SP.toNat_lt
  have hfb := frameBase_toNat (m0 := m0) hn hF
  have hsb := toNat_stackBelow (m := m0) hn
  have hdsp : d.regs.SP.toNat = m0.regs.SP.toNat - F := by
    rw [← UInt64.toNat_toBitVec, hsp, hfb]
  have hsb' : (stackBelow d n').toNat = m0.regs.SP.toNat - F - n' := by
    rw [toNat_stackBelow (by omega), hdsp]
  have ho : (off (frameBase m0 F) ob).toNat = m0.regs.SP.toNat - F + ob := by
    rw [toNat_off (by omega), hfb]
  have h1 : t.toNat + tstateBytes ≤ (stackBelow m0 n).toNat ∨
      (stackBelow m0 n).toNat + n ≤ t.toNat := h.1
  have h2 : a.words.toNat + 8 * a.len ≤ (stackBelow m0 n).toNat ∨
      (stackBelow m0 n).toNat + n ≤ a.words.toNat := h.2.1
  have h3 : rcAddr.toNat + 192 ≤ (stackBelow m0 n).toNat ∨
      (stackBelow m0 n).toNat + n ≤ rcAddr.toNat := hrc.2.2
  rw [hsb] at h1 h2 h3
  refine ⟨Mapped.keeps (mapped_off (frame_mapped hst hF) hob) hk, ?_, ?_, ?_, ?_, ?_⟩
  · show (off (frameBase m0 F) ob).toNat + l ≤ 2 ^ 64
    omega
  · show _ + l ≤ t.toNat ∨ t.toNat + tstateBytes ≤ _
    rw [ho]; omega
  · show _ + l ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ _
    rw [ho]; omega
  · show _ + l ≤ (stackBelow d n').toNat ∨ (stackBelow d n').toNat + n' ≤ _
    rw [ho, hsb']; omega
  · show _ + l ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ _
    rw [ho]; omega

end

end NativeRustcVmArm.Transcript
