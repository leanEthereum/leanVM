module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldMul
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldStore

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' bytesAt_congr DecArea)

public section

@[expose] def FoldTouch (m0 : MachineData) (n : Nat) (q : BitVec 64) : Prop :=
  MulRange m0 q ∨ NativeRustcVm.InRange (off (rwA m0) (16 * n)) 16 q

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 d d' : MachineData}

theorem fold_touch_frame (h : PreOk a s c m0) {n : Nat} (hn : n < 4096) {q : BitVec 64}
    (hq : FoldTouch m0 n q) :
    q.toNat < (rspOf m0).toNat - 2208 + 16 ∨ (rspOf m0).toNat - 2208 + 2160 ≤ q.toNat := by
  rcases hq with hq | hq
  · exact .inl (by have := hq.2; omega)
  · have := (nums h).sw; have := (nums h).r1; have := (nums h).r2; have := (nums h).w
    have hr := row_off h hn
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hr] at hq
    omega

theorem keep_buffer (h : PreOk a s c m0) {n start : Nat} (hn : n < 4096)
    (hstart : 112 ≤ start) (hend : start + 1024 ≤ 2160) {f : Nat → EW}
    (hb : ElemsAt d.dmem (off (fbA m0) start) f 64)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (FoldTouch m0 n)) :
    ElemsAt d'.dmem (off (fbA m0) start) f 64 := by
  intro j hj
  refine bytesAt_congr (hb j hj) fun i hi ↦ hs _ fun hq ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hi
  have hx := fold_touch_frame h hn hq
  rw [off_off, off_add, fb_off h (by omega)] at hx
  omega

theorem keep_words (h : PreOk a s c m0) {n : Nat} (hn : n < 4096)
    {vars : Nat → BitVec 64} {ws : List (Nat × Sym)}
    (hw : Words m0 vars ws d)
    (hws : ws.all (fun p ↦ decide (16 ≤ p.1) && decide (p.1 + 8 ≤ 64)) = true)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (FoldTouch m0 n)) : Words m0 vars ws d' :=
  hw.keep h hws hs fun _ hq ↦ by
    have hx := fold_touch_frame h hn hq
    omega

theorem rows_low (h : PreOk a s c m0) {f : Nat → EW}
    (hr : ElemsAt d.dmem (rwA m0) f 4096)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (MulRange m0)) :
    ElemsAt d'.dmem (rwA m0) f 4096 := by
  have := (nums h).sw; have := (nums h).r1; have := (nums h).w
  intro j hj
  refine bytesAt_congr (hr j hj) fun i hi ↦ hs _ fun hq ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hi
  have he : (off (rwA m0) (16 * j) + BitVec.ofNat 64 i).toNat =
      (rwA m0).toNat + 16 * j + i := by
    rw [off_add, toNat_off (by omega)]
    omega
  unfold MulRange at hq
  rw [he] at hq
  omega

theorem rows_step (h : PreOk a s c m0) {sl : Array EW} {rows : Array (Array EW)}
    {t i j : Nat} (hi : i < 64) (hj : j < 64)
    (hr : ElemsAt d.dmem (rwA m0) (F sl rows t i j) 4096)
    (hv : NativeRustcVm.EWAt d'.dmem (off (rwA m0) (16 * (64 * i + j))) (W sl rows (t + 1) i j))
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (NativeRustcVm.InRange (off (rwA m0) (16 * (64 * i + j))) 16)) :
    ElemsAt d'.dmem (rwA m0) (F sl rows t i (j + 1)) 4096 := by
  have := (nums h).w
  have hn : 64 * i + j < 4096 := by omega
  have hn' := row_off h hn
  intro z hz
  rw [F_step hj]
  split_ifs with he
  · subst z
    exact hv
  · refine bytesAt_congr (hr z hz) fun b hb ↦ hs _ fun hq ↦ ?_
    rw [NativeRustcVm.length_ewBytes] at hb
    have hzb : (off (rwA m0) (16 * z) + BitVec.ofNat 64 b).toNat =
        (rwA m0).toNat + 16 * z + b := by
      rw [off_add, toNat_off (by omega)]
      omega
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hn', hzb] at hq
    omega

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
