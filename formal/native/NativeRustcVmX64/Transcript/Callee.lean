module

public import NativeRustcVmX64.Transcript.Frame

/-!
# Footprints passed to a callee of a transcript function (x86-64)

A function with an `F`-byte frame at the top of its `n` bytes of stack (RSP at the frame's base at
the call, the return address pushed there) calls a function using `n'` bytes below it
(`F + n' ≤ n`): the `TState`'s footprint (`TStateOk.callee`) and an output in the frame above the
return address (`OutOk.frame`) hold for the callee.
-/

namespace NativeRustcVmX64.Transcript

open NativeRustcX64 NativeRustcVm.Transcript

public section

variable [Labels] {m0 d : MachineData} {n F n' : Nat} {t : BitVec 64} {a : DecArea}

theorem TStateOk.callee (h : TStateOk m0 t a n) (hsp : rspOf d = stackBelow m0 F)
    (hn : n ≤ (rspOf m0).toNat) (hn' : F + n' ≤ n) : TStateOk d t a n' :=
  ⟨apart_callee h.1 hsp hn hn', apart_callee h.2.1 hsp hn hn', h.2.2⟩

/-- An output of `l` bytes at offset `ob` of the frame (above the callee's return address), for a
callee using `n'` bytes below it. -/
theorem OutOk.frame (hst : StackOk m0 n) (hn' : F + n' ≤ n) (hsp : rspOf d = stackBelow m0 F)
    (hk : Kept m0.dmem d.dmem) {ob l : Nat} (hob8 : 8 ≤ ob) (hob : ob + l ≤ F)
    (h : TStateOk m0 t a n) (hrc : RcAt m0 n) :
    OutOk d t a (off (stackBelow m0 F) ob) l n' := by
  have hn := hst.1
  have h8 := hst.2.1
  have hfb := stackBelow_toNat (m := m0) (n := F) (by omega)
  have hsb := stackBelow_toNat (m := m0) (n := n) hn
  have hsb' : (stackBelow d n').toNat = (rspOf m0).toNat - F - n' := by
    rw [stackBelow_callee hsp (by omega), stackBelow_toNat (by omega)]
    omega
  have ho : (off (stackBelow m0 F) ob).toNat = (rspOf m0).toNat - F + ob := by
    rw [toNat_off (by omega), hfb]
  have h1 : t.toNat + tstateBytes ≤ (stackBelow m0 n).toNat ∨
      (stackBelow m0 n).toNat + (n + 8) ≤ t.toNat := h.1
  have h2 : a.words.toNat + 8 * a.len ≤ (stackBelow m0 n).toNat ∨
      (stackBelow m0 n).toNat + (n + 8) ≤ a.words.toNat := h.2.1
  have h3 : rcAddr.toNat + 192 ≤ (stackBelow m0 n).toNat ∨
      (stackBelow m0 n).toNat + (n + 8) ≤ rcAddr.toNat := hrc.2.2
  rw [hsb] at h1 h2 h3
  refine ⟨Mapped.keeps (mapped_off (frame_mapped hst (by omega)) (by omega)) hk, ?_, ?_, ?_, ?_, ?_⟩
  · show (off (stackBelow m0 F) ob).toNat + l ≤ 2 ^ 64
    omega
  · show _ + l ≤ t.toNat ∨ t.toNat + tstateBytes ≤ _
    rw [ho]; omega
  · show _ + l ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ _
    rw [ho]; omega
  · show _ + l ≤ (stackBelow d n').toNat ∨ (stackBelow d n').toNat + (n' + 8) ≤ _
    rw [ho, hsb']; omega
  · show _ + l ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ _
    rw [ho]; omega

end

end NativeRustcVmX64.Transcript
