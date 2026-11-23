module

public import NativeRustcVmX64.Sumcheck.RoundPoly.None
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# `sumcheck_round_poly` in plain mode, after `read_scalar` (x86-64)

From `b10` (`none_b10`): `read_scalar`'s tag tested (a rejection at `.L8`), the constant into
`msg[0]`, the claim's limb `1` saved and `read_scalars` of the tail into `msg[2..]` (`b11`); its
test (`b12`, a rejection at `.L9`); the claim's limb `0` saved and the tail's sum (`sum_e`,
`b13`); then `none_b14`.
-/

namespace NativeRustcVmX64.Sumcheck.RoundPoly

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateSumcheckRoundPoly
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

public section

/-- `x - 1` as `sub` computes it. -/
theorem toNat_sub_one' {x : BitVec 64} (h : 1 ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 1)).toNat = x.toNat - 1 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `x - 2` as `add $-2` computes it. -/
theorem toNat_add_neg2 {x : BitVec 64} (h : 2 ≤ x.toNat) :
    (BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551614) x).toNat = x.toNat - 2 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **After `read_scalar`** in plain mode, at `b10`: a rejection, or the constant, the tail, its
sum, then `none_b14`. -/
theorem none_b10 (hp : Placed code k)
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (h : RoundPolyPre a s none m0) {d : MachineData} (hN : NoneAt m0 a s d) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        RoundPolyPost a s none m0 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b10Offset)⟩ := by
  have c := ctx_of h
  have hc2 : 2 ≤ cnt m0 := h.2.2.2.2.1
  have hc5 : cnt m0 ≤ 5 := h.2.2.2.2.2.1
  have hl9 : Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset) :=
    hp.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9_at
  have hl8 : Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_8 = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b18Offset) :=
    hp.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_8_at
  -- `b10`: `read_scalar`'s tag.
  have hwf3 := wf_envB h hN.rf.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b11Offset + b11.length)).toBitVec
  refine exec_then (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf3 nofun
    (match_bodyS hN.rf _) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hk3⟩ := ok_b10
  have hf3 : RF m0 8 st3.data := (RF.block h hN.rf hm3 hmid3 (KeepsR.rbx hk3)).1
  have hd3 : st3.data.dmem = d.dmem := hm3.dmem_eq hwf3 hmem3
  have hout := hN.out
  have hnext := hN.next
  simp only [PcOk] at hpc3
  cases hr0 : readScalar.run s with
  | none =>
    rw [hr0] at hout
    have h0 : NativeRustcVm.WordAt d.dmem (off (fa m0) 40) 0 := hout
    have ht0 : (envB m0 d (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b11Offset + b11.length)).toBitVec).load 0 40 4 =
        BitVec.ofNat 64 0 := load4_of_tag (Or.inl rfl) h0
    have hc : c10.eval (envB m0 d (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b11Offset + b11.length)).toBitVec) = true := by
      show (!(CmpOp.apply .eq .W32
        ((envB m0 d (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b11Offset + b11.length)).toBitVec).load 0 40 4)
        (BitVec.ofNat 64 1))) = true
      rw [ht0]; decide
    rw [hc] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    rw [hl8] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3
    subst hpc3
    refine Eventually.mono (fail_spec hp h hf3) fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_⟩
    exact post_none (by simp [runR, roundPoly_none_run, hr0]) h3
      (by rw [h4]; exact hf3.same) h5
  | some p0 =>
  obtain ⟨x0, s0⟩ := p0
  rw [hr0] at hout
  obtain ⟨ht1, hel⟩ := (hout : OptEWAt d.dmem (off (fa m0) 40) (some x0))
  rw [ewAt_iff, off_off, off_off] at hel
  have ts3 : TStateAt d.dmem (tAt m0) a s0 := hnext x0 s0 hr0
  have ht1' : (envB m0 d (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b11Offset + b11.length)).toBitVec).load 0 40 4 =
      BitVec.ofNat 64 1 := load4_of_tag (Or.inr rfl) ht1
  have hc : c10.eval (envB m0 d (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b11Offset + b11.length)).toBitVec) = false := by
    show (!(CmpOp.apply .eq .W32
      ((envB m0 d (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b11Offset + b11.length)).toBitVec).load 0 40 4)
      (BitVec.ofNat 64 1))) = false
    rw [ht1']; decide
  rw [hc] at hpc3
  simp (config := { decide := true }) only [↓reduceIte] at hpc3
  -- `b11`: the constant into `msg[0]`, `read_scalars(t, msg + 32, count - 2)`.
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf3 (fun _ _ ↦ rfl)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b10_next)) hm3 fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hw4, hW0, hW8, hW16, hrdi4, hrsi4, hrdx4, hr13_4, hr14_4, hk4⟩ := ok_b11
  have hf4 : RF m0 0 st4.data := (RF.block h hN.rf hm4 hmid4 (KeepsR.rbx hk4)).1
  have hs4 : NativeRustcVm.SameOutside d.dmem st4.data.dmem (fun q ↦
      NativeRustcVm.InRange (fa m0) 112 q ∨ NativeRustcVm.InRange (msgAt m0) 16 q) :=
    fun q hq ↦ hm4.get?_mem0 hwf3 fun hw ↦ hq (written_frame_hi (msg_noWrap h) (by omega)
      c.noWrap_frame (fun w hw' ↦ by
        rcases hw4 w hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, by rcases h2 with h2 | h2 <;> omega⟩
        · exact Or.inr ⟨h1, h2⟩) hw)
  have hin4 := writesIn_of_mid hmid4
  have hmiss4 : ∀ o, 16 ≤ o → o + 8 ≤ 16 ∨ 24 ≤ o → ∀ w ∈ (after b11 (after b10 bodyS)).mem,
      w.r = 0 → w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 h2 w hw hr ↦ by
    rcases hw4 w hw with ⟨-, h3⟩ | ⟨h3, -⟩
    · rcases h3 with h3 | h3 <;> omega
    · omega
  have hhead4 : NativeRustcVm.EWsAt st4.data.dmem (off (msgAt m0) 0) [x0] := by
    refine ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩, ewsAt_nil _ _⟩
    · exact wordAt_written hm4 (r := 1) (o := 0) rfl (by omega) hW0
        (load_ofMachine (o := 48) rfl hel.1)
    · rw [off_off]
      exact wordAt_written hm4 (r := 1) (o := 8) rfl (by omega) hW8
        (load_ofMachine (o := 56) rfl hel.2)
  have w16_4 : NativeRustcVm.WordAt st4.data.dmem (off (fa m0) 16) (claimOf m0).c1 :=
    wordAt_written hm4 (r := 0) rfl (by omega) hW16 (by
      show reg d .r14 = _
      rw [hN.r14])
  have ts4 : TStateAt st4.data.dmem (tAt m0) a s0 :=
    tstate_keep h hs4 (hm4.kept hwf3) (fun q hq ↦ hq.elim (fun hq ↦ Or.inr (frame_in h hq))
      fun hq ↦ Or.inl (inRange_mono hq (by omega))) ts3
  have hat4 := hf4.at h
  have hrdi4' : reg st4.data .rdi = tAt m0 := (hm4.regs .rdi _ hrdi4).trans hN.r12
  have hrsi4' : reg st4.data .rsi = off (msgAt m0) 32 := (hm4.regs .rsi _ hrsi4).trans (eval_ptr1 32)
  have hrdx4' : (reg st4.data .rdx).toNat = cnt m0 - 2 := by
    rw [show reg st4.data .rdx = _ from hm4.regs .rdx _ hrdx4, ← hN.r13]
    exact toNat_add_neg2 (x := reg d .r13) (by rw [hN.r13]; omega)
  have hr13_4' : (reg st4.data .r13).toNat = cnt m0 - 2 := by
    rw [show reg st4.data .r13 = _ from hm4.regs .r13 _ hr13_4, ← hN.r13]
    exact toNat_add_neg2 (x := reg d .r13) (by rw [hN.r13]; omega)
  have hr14_4' : reg st4.data .r14 = off (msgAt m0) 32 :=
    (hm4.regs .r14 _ hr14_4).trans (eval_ptr1 32)
  have hr15_4 : reg st4.data .r15 = reg m0 .rdx :=
    (hm4.regs .r15 _ (KeepsR.reg hk4 (by simp))).trans hN.r15
  have hr12_4 : reg st4.data .r12 = tAt m0 :=
    (hm4.regs .r12 _ (KeepsR.reg hk4 (by simp))).trans hN.r12
  refine call_then hpc4 (hrss a s0) ?pre fun st5 hpc5 hrsp5 hpost5 ↦ ?_
  case pre =>
    unfold ReadScalarsPre
    rw [hrdi4', hrsi4', hrdx4']
    refine ⟨c.stackOk hat4 (by decide), c.rcAt hat4 (by decide), ts4,
      c.tstateOk hat4 (by decide), msgOut h hat4 (by decide) (by omega) (by omega), ?_⟩
    apply hf4.gotAt h (by decide)
    intro l hl x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact got_area h hl (by simp)
    · exact got_area h hl (by simp)
    · exact got_msg h hl (by omega) (by omega)
    · exact got_area h hl (by simp)
  simp only [ReadScalarsPost, hrdi4', hrsi4', hrdx4'] at hpost5
  obtain ⟨hok5, hxs5, hnext5, hs5, hsv5⟩ := hpost5
  have hR5 : ∀ q, (NativeRustcVm.InRange (off (msgAt m0) 32) (16 * (cnt m0 - 2)) q ∨
      NativeRustcVm.InRange (tAt m0) tstateBytes q) → Chg m0 q ∧ NotHigh m0 q := by
    rintro q (hq | hq)
    · have hq' := msg_part h (by omega) (by omega) hq
      exact ⟨Or.inl hq', notHigh_of_not_frame h (not_frame_msg h hq')⟩
    · exact ⟨Or.inr (Or.inl hq), notHigh_of_not_frame h (not_frame_t h hq)⟩
  have hs5' : NativeRustcVm.SameOutside st4.data.dmem st5.data.dmem (fun q ↦
      (NativeRustcVm.InRange (off (msgAt m0) 32) (16 * (cnt m0 - 2)) q ∨
        NativeRustcVm.InRange (tAt m0) tstateBytes q) ∨
      NativeRustcVm.InRange (stackBelow st4.data readScalarsStack) readScalarsStack q) :=
    fun q hq ↦ hs5 q fun h' ↦ hq (or_assoc.mpr h')
  have hf5 : RF m0 8 st5.data :=
    hf4.call h (Nc := readScalarsStack) (by decide) hsv5 hrsp5 hR5 hs5'
  have w16_5 := keepW_call h hat4 (Nc := readScalarsStack) (by decide)
    (fun q hq ↦ hq.elim (fun hq ↦ not_frame_msg h (msg_part h (by omega) (by omega) hq))
      (fun hq ↦ not_frame_t h hq)) hs5' (by omega) (by omega) w16_4
  have hR5' : ∀ q, ((NativeRustcVm.InRange (off (msgAt m0) 32) (16 * (cnt m0 - 2)) q ∨
      NativeRustcVm.InRange (tAt m0) tstateBytes q) ∨
      NativeRustcVm.InRange (stackBelow st4.data readScalarsStack) readScalarsStack q) →
      NativeRustcVm.InRange (off (msgAt m0) 16) 64 q ∨ NativeRustcVm.InRange (tAt m0) tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q := by
    rintro q ((hq | hq) | hq)
    · exact Or.inl (msg_sub h (by omega) (by omega) (by omega) (by omega) hq)
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr (callee_in h hat4 (by decide) hq))
  have hhead5 := keep_head h hs5' hR5' hhead4
  have hr12_5 : reg st5.data .r12 = tAt m0 := (hsv5.1 .r12 rfl).trans hr12_4
  have hr13_5 : (reg st5.data .r13).toNat = cnt m0 - 2 := by
    rw [show reg st5.data .r13 = _ from hsv5.1 .r13 rfl]; exact hr13_4'
  have hr14_5 : reg st5.data .r14 = off (msgAt m0) 32 := (hsv5.1 .r14 rfl).trans hr14_4'
  have hr15_5 : reg st5.data .r15 = reg m0 .rdx := (hsv5.1 .r15 rfl).trans hr15_4
  -- `b12`: `read_scalars`' test.
  have hwf5 := wf_envB h hf5.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b13Offset + b13.length)).toBitVec
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf5 nofun
    (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b11_next)) (match_bodyS hf5 _) fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hmem6, hrbp6, hk6⟩ := ok_b12
  have hf6 : RF m0 8 st6.data := (RF.block h hf5 hm6 hmid6 (KeepsR.rbx hk6)).1
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq hwf5 hmem6
  simp only [PcOk, eval_cAl] at hpc6
  cases hr1 : (readScalars (cnt m0 - 2)).run s0 with
  | none =>
    rw [hr1] at hok5
    have hal5 : (reg st5.data .rax).toNat % 256 = 0 := hok5
    have hpc : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset) := by
      rw [hpc6, show (envB m0 st5.data _).regs .rax = reg st5.data .rax from rfl, hal5]
      exact (ite_eq_left_iff.mpr (fun h ↦ absurd (by decide) h)).trans hl9
    obtain ⟨d6, pc6⟩ := st6
    simp only at hpc
    subst hpc
    refine Eventually.mono (exit_spec hp h hf6) fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_⟩
    refine post_none ?_ ?_ (by rw [h4]; exact hf6.same) h5
    · simp [runR, roundPoly_none_run, hr0, hr1]
    · rw [h3, show reg d6 .rbp = _ from hm6.regs .rbp _ hrbp6]
      rfl
  | some p =>
  obtain ⟨tail, s1⟩ := p
  rw [hr1] at hok5
  have hal5 : (reg st5.data .rax).toNat % 256 = 1 := hok5
  have hsz : tail.size = cnt m0 - 2 := readScalars_size hr1
  have htl' : 32 + 16 * tail.toList.length ≤ 80 := by simp; omega
  have tl5 : NativeRustcVm.EWsAt st5.data.dmem (off (msgAt m0) 32) tail.toList :=
    hxs5 tail s1 hr1
  have ts5 : TStateAt st5.data.dmem (tAt m0) a s1 := hnext5 tail s1 hr1
  have hpc : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b13Offset) := by
    rw [hpc6, show (envB m0 st5.data _).regs .rax = reg st5.data .rax from rfl, hal5]
    rfl
  -- `b13`: the claim's limb `0` saved, `sum_e(tail)`.
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf5 (fun _ _ ↦ rfl) hpc hm6
    fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hw7, hW8_7, hrbp7, hrdi7, hrsi7, hk7⟩ := ok_b13
  have hf7 : RF m0 0 st7.data := (RF.block h hf5 hm7 hmid7 (KeepsR.rbx hk7)).1
  have hs7 : NativeRustcVm.SameOutside st5.data.dmem st7.data.dmem
      (NativeRustcVm.InRange (fa m0) 112) :=
    sameOutside_low hwf5 hm7 (r := 0) rfl (hi := 112) (by omega) fun w hw ↦
      ⟨(hw7 w hw).1, by rcases (hw7 w hw).2 with h' | h' <;> omega⟩
  have hin7 := writesIn_of_mid hmid7
  have hRf : ∀ q, NativeRustcVm.InRange (fa m0) 112 q →
      NativeRustcVm.InRange (off (msgAt m0) 16) 64 q ∨ NativeRustcVm.InRange (tAt m0) tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q :=
    fun q hq ↦ Or.inr (Or.inr (frame_in h hq))
  obtain ⟨ts7, tl7⟩ := keep_ts_tail h hs7 (hm7.kept hwf5) (o0 := 32)
    (fun q hq ↦ Or.inr (frame_in h hq)) htl' (by omega) ts5 tl5
  have hhead7 := keep_head h hs7 hRf hhead5
  have w16_7 := keepW hwf5 hm7 hin7 (by omega) (fun w hw _ ↦ by
    rcases (hw7 w hw).2 with h' | h' <;> omega) w16_5
  have w8_7 : NativeRustcVm.WordAt st7.data.dmem (off (fa m0) 8) (claimOf m0).c0 :=
    wordAt_written hm7 (r := 0) rfl (by omega) hW8_7 (by
      show reg st5.data .r15 = _
      rw [hr15_5])
  have hat7 := hf7.at h
  have hrdi : reg st7.data .rdi = off (msgAt m0) 32 := (hm7.regs .rdi _ hrdi7).trans hr14_5
  have hrsi : (reg st7.data .rsi).toNat = cnt m0 - 2 := by
    rw [show reg st7.data .rsi = _ from hm7.regs .rsi _ hrsi7]; exact hr13_5
  have ho := msgOut h hat7 (Nc := sumEStack) (by decide) (o := 32) (n := 16 * (cnt m0 - 2))
    (by omega) (by omega)
  refine call_then hpc7 hsum ?pre fun st8 hpc8 hrsp8 ⟨hsumv, hs8, hsv8⟩ ↦ ?_
  case pre =>
    unfold SumEPre
    rw [hrdi, hrsi]
    exact ⟨c.stackOk hat7 (by decide), by omega, ho.1, ho.2.1⟩
  have hsl : slice st7.data (reg st7.data .rdi) (reg st7.data .rsi) = tail := by
    unfold slice
    rw [hrsi, hrdi, show cnt m0 - 2 = tail.toList.length by simp [hsz],
      NativeRustcVm.ewsOf_of_ewsAt tl7]
  rw [hsl] at hsumv
  have hs8' : NativeRustcVm.SameOutside st7.data.dmem st8.data.dmem (fun q ↦
      NativeRustcVm.InRange 0 0 q ∨
        NativeRustcVm.InRange (stackBelow st7.data sumEStack) sumEStack q) := hs8
  have hR0 : ∀ q, NativeRustcVm.InRange 0 0 q → False := fun q hq ↦ by
    unfold NativeRustcVm.InRange at hq; omega
  have hf8 : RF m0 8 st8.data :=
    hf7.call h (Nc := sumEStack) (by decide) hsv8 hrsp8 (fun q hq ↦ (hR0 q hq).elim) hs8'
  have kc8 := fun {o : Nat} {w : UInt64} (ho : 8 ≤ o) (hon : o + 8 ≤ 112) ↦
    keepW_call (w := w) h hat7 (Nc := sumEStack) (by decide) (R := NativeRustcVm.InRange 0 0)
      (fun q hq ↦ (hR0 q hq).elim) hs8' ho hon
  have hR8 : ∀ q, (NativeRustcVm.InRange 0 0 q ∨
      NativeRustcVm.InRange (stackBelow st7.data sumEStack) sumEStack q) →
      NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q :=
    fun q hq ↦ hq.elim (fun hq ↦ (hR0 q hq).elim) fun hq ↦ callee_in h hat7 (by decide) hq
  obtain ⟨ts8, tl8⟩ := keep_ts_tail h hs8' hsv8.2 (o0 := 32) (fun q hq ↦ Or.inr (hR8 q hq))
    htl' (by omega) ts7 tl7
  have hhead8 := keep_head h hs8' (fun q hq ↦ Or.inr (Or.inr (hR8 q hq))) hhead7
  have hr12_8 : reg st8.data .r12 = reg st5.data .r12 :=
    (hsv8.1 .r12 rfl).trans (hm7.regs .r12 _ (KeepsR.reg hk7 (by simp)))
  have hr13_8 : reg st8.data .r13 = reg st5.data .r13 :=
    (hsv8.1 .r13 rfl).trans (hm7.regs .r13 _ (KeepsR.reg hk7 (by simp)))
  obtain ⟨d8, pc8⟩ := st8
  simp only at hpc8
  subst hpc8
  rw [NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b13_length]
  exact none_b14 hp hbl hgr h hr0 hr1 ⟨hf8, hr12_8.trans hr12_5,
    by rw [hr13_8]; exact hr13_5,
    (hsv8.1 .rbp rfl).trans (hm7.regs .rbp _ hrbp7),
    by rw [← hsumv]; rfl, by rw [← hsumv]; rfl,
    kc8 (by omega) (by omega) w8_7, kc8 (by omega) (by omega) w16_7, ts8, hhead8, tl8⟩

end

end NativeRustcVmX64.Sumcheck.RoundPoly
