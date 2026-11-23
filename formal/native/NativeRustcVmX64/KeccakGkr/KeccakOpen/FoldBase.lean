module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Step

/-! # `keccak_open`: the inner fold's memory frames -/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr DecArea Touch)

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 d d' : MachineData}

theorem frame_keep (h : PreOk a s c m0) {o o' : Nat} (hf : Frame m0 2208 slots o d)
    (hsp : rspOf d' = off (fbA m0) o') (hk : Kept d.dmem d'.dmem)
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (off (fbA m0) 2160) 56 q) :
    Frame m0 2208 slots o' d' := by
  have hn := nums h
  have := hn.r1; have := hn.r2
  have h2160 := fb_off h (j := 2160) (by decide)
  have hin : ∀ {j : Nat}, 2160 ≤ j → j < 2216 →
      NativeRustcVm.InRange (off (fbA m0) 2160) 56 (off (fbA m0) j) := by
    intro j hj hj'
    rw [show j = 2160 + (j - 2160) by omega, ← off_off]
    exact NativeRustcVm.Transcript.inRange_off_self (by omega) (by omega)
  refine ⟨hsp, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hk, ?_⟩
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at hi
    rw [off_add]
    exact hs _ fun hr ↦ hR _ hr (hin (by have := slots_le p hp; omega)
      (by have := slots_le p hp; omega))
  · rw [hs _ fun hr ↦ hR _ hr (hin (by omega) (by omega))]
    exact hf.ret j hj
  · intro r hr hnot
    have hall : ∀ r, calleeSaved r = true → slots.any (·.2 == r) = true := by
      intro r
      cases r <;> decide
    rw [hall r hr] at hnot
    cases hnot

theorem frame_low (h : PreOk a s c m0) {o o' : Nat} (hf : Frame m0 2208 slots o d)
    (hsp : rspOf d' = off (fbA m0) o') (hk : Kept d.dmem d'.dmem)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fbA m0) 8)) :
    Frame m0 2208 slots o' d' := by
  refine frame_keep h hf hsp hk hs fun q hq ↦ ?_
  have := (nums h).r1; have := (nums h).r2
  have hfb := fbA_toNat h
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hfb] at hq
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [fb_off h (by decide)]; omega),
    fb_off h (by decide)]
  omega

@[expose] def MulRange (m0 : MachineData) (q : BitVec 64) : Prop :=
  (rspOf m0).toNat - 3200 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 2208 + 8

theorem low_range (h : PreOk a s c m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fbA m0) 8 q) : MulRange m0 q := by
  have := (nums h).r1; have := (nums h).r2
  have hfb := fbA_toNat h
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hfb] at hq
  exact ⟨by omega, by omega⟩

theorem mul_range (h : PreOk a s c m0) (hsp : rspOf d = fbA m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d ewMulStack) ewMulStack q) : MulRange m0 q := by
  have := (nums h).r1; have := (nums h).r2
  have hc : (stackBelow d ewMulStack).toNat = (rspOf m0).toNat - 2352 := by
    rw [stackBelow_callee hsp (by change 2352 ≤ _; omega),
      stackBelow_toNat (by change 2352 ≤ _; omega)]
    rfl
  have hnw : NativeRustcVm.NoWrap (stackBelow d ewMulStack) ewMulStack := by
    change (stackBelow d ewMulStack).toNat + 144 ≤ 2 ^ 64
    rw [hc]; omega
  rw [inRange_iff' hnw, hc] at hq
  change (rspOf m0).toNat - 2352 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 2352 + 144 at hq
  exact ⟨by omega, by omega⟩

omit [Labels] in
theorem mulRange_safe {q : BitVec 64} (hq : MulRange m0 q) : Safe m0 q :=
  .inl ⟨hq.1, by have := hq.2; omega⟩

theorem low_safe (h : PreOk a s c m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fbA m0) 8 q) : Safe m0 q :=
  mulRange_safe (low_range h hq)

theorem mul_safe (h : PreOk a s c m0) (hsp : rspOf d = fbA m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d ewMulStack) ewMulStack q) : Safe m0 q :=
  mulRange_safe (mul_range h hsp hq)

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
