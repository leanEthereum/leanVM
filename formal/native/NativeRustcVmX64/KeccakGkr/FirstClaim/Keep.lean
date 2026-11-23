module

public import NativeRustcVmX64.KeccakGkr.FirstClaim.Loop

/-!
# `first_claim`: bytes kept, the arguments and the callees' stacks (x86-64)

Frame bytes a block's writes at offsets `W` miss (`keep_W`), a callee writing frame bytes and
`Low` misses (`keep_fcall`); the entry's bytes off `Out` (`keep_in`), the bit weights (`w_keep`),
bytes off the result or at other offsets of it (`keep_offout`, `keep_outout`); a callee's stack
below the frame (`sb_call`); the result's bytes as a callee's region (`out_D`); a `Buf<EW, N>`
copied (`BufEWAt.copy`) and read (`bufEWOf_eq`); AL's test (`al_test`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.FirstClaim
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self Touch)

public section

theorem extract_zero (xs : Array EW) (n : Nat) : xs.extract 0 n = (xs.toList.take n).toArray := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

theorem extract_from (xs : Array EW) (n : Nat) :
    xs.extract n xs.size = (xs.toList.drop n).toArray := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

/-- `testb %al, %al`'s zero flag. -/
theorem al_test (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x x) (BitVec.ofNat 64 0) =
      decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply, BinOp.apply]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, toNat_low, toNat_low,
    toNat_ext, BitVec.toNat_and, toNat_low, Nat.and_self]
  simp [Width.bits]

/-- `cmpq $4, x; cmovb`: `min x 4`. -/
theorem min4_eval (x : BitVec 64) :
    (if CmpOp.apply .ult .W64 x (BitVec.ofNat 64 4) = true then x else BitVec.ofNat 64 4).toNat =
      min 4 x.toNat := by
  simp only [CmpOp.apply, low_W64]
  by_cases hc : x.toNat < 4
  · rw [ite_eq_left (by simp [BitVec.ult]; omega)]; omega
  · rw [ite_eq_right (by simp [BitVec.ult]; omega)]; simp; omega

/-- **Bytes copied**: what `memcpy` wrote at `dst` holds the bytes the source held. -/
theorem bytes_copy {d d' : DataMem} {src dst : BitVec 64} {n o : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d (src + BitVec.ofNat 64 o) bs)
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcX64.bytesOf d src n)) (hle : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (dst + BitVec.ofNat 64 o) bs := by
  intro i hi
  have := hc (o + i) (by simp [NativeRustcX64.bytesOf]; omega)
  rw [NativeRustcVm.addr_add_add, this]
  simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
  rw [← NativeRustcVm.addr_add_add, h i hi, Option.getD_some]

/-- **A `Buf<EW, N>` copied.** -/
theorem BufEWAt.copy {d d' : DataMem} {src dst : BitVec 64} {N : Nat} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d src N xs)
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcX64.bytesOf d src (8 + 16 * N))) :
    NativeRustcVm.BufEWAt d' dst N xs := by
  obtain ⟨hl, hw, he⟩ := h
  refine ⟨hl, ?_, ?_⟩
  · have := bytes_copy (o := 0) (by rw [NativeRustcVm.addr_add_zero]; exact hw) hc
      (by rw [NativeRustcVm.length_wordBytes]; omega)
    rwa [NativeRustcVm.addr_add_zero] at this
  · exact bytes_copy (o := 8) he hc (by rw [NativeRustcVm.length_ewsBytes]; omega)

/-- A `Buf<EW, N>`'s elements as `bufEWOf` reads them. -/
theorem bufEWOf_eq {d : DataMem} {p : BitVec 64} {N : Nat} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d p N xs) (hN : N < 2 ^ 64) : NativeRustcVm.bufEWOf d p = xs := by
  obtain ⟨hl, hw, he⟩ := h
  unfold NativeRustcVm.bufEWOf
  rw [NativeRustcVm.wordOf_of_wordAt hw, Nat.toUInt64,
    UInt64.toNat_ofNat_of_lt' (show xs.length < UInt64.size by simp [UInt64.size]; omega)]
  exact NativeRustcVm.ewsOf_of_ewsAt he

/-- The 8-byte words of `zeros` are zero. -/
theorem zeros_spec {S : SState} {lo n : Nat} (h : zeros S lo n = true) {q : Nat} (hq : q < n) :
    ∀ t < 8, findWrite 0 (lo + 8 * q + t) S.mem = some (.lit 0, t) := by
  intro t ht
  unfold zeros at h
  have := List.all_eq_true.mp (List.all_eq_true.mp h q (List.mem_range.mpr hq)) t
    (List.mem_range.mpr ht)
  exact beq_iff_eq.mp this

variable {inst segment lanePoint output : Array EW} {m0 : MachineData}

/-- A frame word loaded. -/
theorem load_frame [Labels] {d : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {o : Nat} {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (off (fbA m0) o) w) :
    (frameEnv m0 d 1376 [(argA m0, 24)] vars ret).load 0 o 8 = w.toBitVec :=
  load_of_wordAt h

/-- A callee's stack from RSP at the frame's base. -/
theorem sb_call (h : PreOk inst segment lanePoint output m0) {st : MachineData}
    (hsp : rspOf st = fbA m0) {s : Nat} (hs : s ≤ 256) :
    (stackBelow st s).toNat = (rspOf m0).toNat - 1376 - s := by
  have := (nums h).r1
  rw [stackBelow_toNat (by rw [hsp, fbA_toNat h]; omega), hsp, fbA_toNat h]

/-- Frame bytes kept by a block's writes at frame offsets `W` they miss. -/
theorem keep_W (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem} {W : Nat → Prop}
    {o : Nat} {bs : List UInt8}
    (hs : NativeRustcVm.SameOutside d₁ d₂ (fun q ↦ Touch (fbA m0) (1376 + 8) W q))
    (hle : o + bs.length ≤ 1384) (hd : ∀ i < bs.length, ¬ W (o + i))
    (hb : NativeRustcVm.BytesAt d₁ (off (fbA m0) o) bs) :
    NativeRustcVm.BytesAt d₂ (off (fbA m0) o) bs :=
  keep_loc hs (fun i hi ⟨j, hj, hW, e⟩ ↦ by
    have e' := NativeRustcVm.Transcript.off_inj (frame_noWrap h.st (by rw [stack_eq]; decide)) hj
      (show o + i < 1376 + 8 by omega) e
    rw [← e'] at hW
    exact hd i hi hW) hb

/-- Frame bytes kept by a call changing the frame bytes `[o', o' + n')` and `Low`. -/
theorem keep_fcall (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem}
    {o o' n' : Nat} {bs : List UInt8}
    (hs : NativeRustcVm.SameOutside d₁ d₂
      (fun q ↦ NativeRustcVm.InRange (off (fbA m0) o') n' q ∨ Low m0 q))
    (hle : o + bs.length ≤ 1384) (ho' : o' + n' ≤ 1384) (hd : o + bs.length ≤ o' ∨ o' + n' ≤ o)
    (hb : NativeRustcVm.BytesAt d₁ (off (fbA m0) o) bs) :
    NativeRustcVm.BytesAt d₂ (off (fbA m0) o) bs := by
  have h1 := (nums h).r1
  have h2 := (nums h).r2
  refine keep_loc hs (fun i hi hq ↦ ?_) hb
  rcases hq with hq | hq
  · have e := fb_off h (j := o') (by omega)
    have e2 := fb_off h (j := o + i) (by omega)
    have hr := inR (by rw [e]; omega) hq
    rw [e, e2] at hr
    omega
  · rw [low_iff h, fb_off h (by omega)] at hq
    omega

/-- **Bytes off `Out` kept** from the entry. -/
theorem keep_in (h : PreOk inst segment lanePoint output m0) {d : DataMem}
    (hs : NativeRustcVm.SameOutside m0.dmem d (Out m0)) {a : BitVec 64} {bs : List UInt8}
    (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (ho : a.toNat + bs.length ≤ (outA m0).toNat ∨ (outA m0).toNat + 776 ≤ a.toNat)
    (hw : a.toNat + bs.length ≤ (wA m0).toNat ∨ (wA m0).toNat + 25600 ≤ a.toNat)
    (hk : a.toNat + bs.length ≤ (rspOf m0).toNat - 1632 ∨ (rspOf m0).toNat ≤ a.toNat)
    (hb : NativeRustcVm.BytesAt m0.dmem a bs) : NativeRustcVm.BytesAt d a bs :=
  bytesAt_congr hb fun i hi ↦ hs _ fun hO ↦ by
    rw [out_iff h, show a + BitVec.ofNat 64 i = off a i from rfl, toNat_off (by omega)] at hO
    omega

/-- **The bit weights kept** where memory changed off them. -/
theorem w_keep (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem} {f : Nat → EW}
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d₁ d₂ R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (wA m0) 25600 q)
    (hw : ElemsAt d₁ (wA m0) f 1600) : ElemsAt d₂ (wA m0) f 1600 :=
  hw.keep hs (fun q hq hr ↦ hR q hr hq)
    (by unfold NativeRustcVm.NoWrap; have := (nums h).w; omega)

/-- What the stack holds is not the bit weights'. -/
theorem stk_w (h : PreOk inst segment lanePoint output m0) {R : BitVec 64 → Prop}
    (hR : ∀ q, R q → Stk m0 q) : ∀ q, R q → ¬ NativeRustcVm.InRange (wA m0) 25600 q :=
  fun q hq hw ↦ w_not_stk h hw (hR q hq)

/-- A frame region's byte is the stack's. -/
theorem fd_stk (h : PreOk inst segment lanePoint output m0) {o n : Nat} (hon : o + n ≤ 1376)
    {q : BitVec 64} (hq : NativeRustcVm.InRange (off (fbA m0) o) n q) : Stk m0 q :=
  frame_stk h (off_in (by
    unfold NativeRustcVm.NoWrap; have := (nums h).r1; have := (nums h).r2
    rw [fbA_toNat h]; omega) hon hq)

/-- The result's bytes `[o, o + n)` as a callee's region. -/
theorem out_D (h : PreOk inst segment lanePoint output m0) {o n : Nat} (ho : o < 776)
    (hon : o + n ≤ 776) :
    ∀ q, NativeRustcVm.InRange (off (outA m0) o) n q →
      Out m0 q ∧ ∀ j, 1328 ≤ j → j < 1384 → q ≠ off (fbA m0) j := by
  intro q hq
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.o; have := hn.os
  have e : (off (outA m0) o).toNat = (outA m0).toNat + o := toNat_off (by omega)
  have hr := inR (by rw [e]; omega) hq
  rw [e] at hr
  refine ⟨by rw [out_iff h]; omega, fun j hj hj' he ↦ ?_⟩
  rw [he, fb_off h (by omega)] at hr
  omega

/-- Bytes off the result kept by a change in its bytes `[o', o' + n')`. -/
theorem keep_offout (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem} {o' n' : Nat}
    (ho' : o' < 776) (hon' : o' + n' ≤ 776)
    (hs : NativeRustcVm.SameOutside d₁ d₂ (NativeRustcVm.InRange (off (outA m0) o') n'))
    {a : BitVec 64} {bs : List UInt8} (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (hap : a.toNat + bs.length ≤ (outA m0).toNat ∨ (outA m0).toNat + 776 ≤ a.toNat)
    (hb : NativeRustcVm.BytesAt d₁ a bs) : NativeRustcVm.BytesAt d₂ a bs :=
  bytesAt_congr hb fun i hi ↦ hs _ fun hq ↦ by
    have := (nums h).o
    have e : (off (outA m0) o').toNat = (outA m0).toNat + o' := toNat_off (by omega)
    have hr := inR (by rw [e]; omega) hq
    rw [e, show a + BitVec.ofNat 64 i = off a i from rfl, toNat_off (by omega)] at hr
    omega

/-- The result's bytes `[o, o + l)` kept by a change in its bytes `[o', o' + n')`. -/
theorem keep_outout (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem}
    {o o' n' : Nat} {bs : List UInt8} (hle : o + bs.length ≤ 776) (ho' : o' < 776)
    (hon' : o' + n' ≤ 776)
    (hd : o + bs.length ≤ o' ∨ o' + n' ≤ o)
    (hs : NativeRustcVm.SameOutside d₁ d₂ (NativeRustcVm.InRange (off (outA m0) o') n'))
    (hb : NativeRustcVm.BytesAt d₁ (off (outA m0) o) bs) :
    NativeRustcVm.BytesAt d₂ (off (outA m0) o) bs :=
  bytesAt_congr hb fun i hi ↦ hs _ fun hq ↦ by
    have := (nums h).o
    have e : (off (outA m0) o').toNat = (outA m0).toNat + o' := toNat_off (by omega)
    have hr := inR (by rw [e]; omega) hq
    rw [e, show off (outA m0) o + BitVec.ofNat 64 i = off (outA m0) (o + i) from
      NativeRustcVm.Transcript.off_add _ _ _, toNat_off (by omega)] at hr
    omega

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
