module

public import NativeRustcVmX64.Layout.ReadAnnouncedSizes.Tail
public import NativeRustcVmX64.Code.Vm.BuildLayout.Names

/-!
# `read_announced_sizes` after the high limbs' checks (x86-64)

`from10`: `b10` copies the six row counts to the frame's bytes `136`-`184`, keeps the rate in R15,
`log_memory` in RSI and returns `0` (`b14`) unless `1 ≤ rate ≤ 4`; `b11` calls
`build_layout(bytecode_len, log_memory, rows, layout)`, then `from12`.
-/

namespace NativeRustcVmX64.Layout.ReadAnnouncedSizes

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReadAnnouncedSizes NativeVm.Model
open NativeRustcVm.Layout NativeRustcVm.Transcript NativeRustcVmX64.Transcript
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck
open NativeVm.Math.Layout (lmA rowsA rateA ite_false_of)

public section

variable [Host] {k : Nat} {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}

/-- **After the checks** (`b10`, `b11`, `build_layout`). -/
theorem from10 (hp : Placed code k)
    (hbl : ∀ bc, Spec (Labels.label NativeRustcVmX64.Vm.BuildLayout.entryLabel) (BuildLayoutPre bc) (BuildLayoutPost bc))
    (h : ReadAnnouncedSizesPre bc a s m0) {xs : Array EW} {s1 : TState}
    (hrs : (readScalars 8).run s = some (xs, s1)) (hall : (xs.all fun x ↦ x.c1 == 0) = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b10Offset)) (hM : Mid a m0 xs s1 st.data) :
    Eventually (step1 Host.exe) (Goal bc a s m0) st := by
  obtain ⟨-, -, -, -, -, -, hsize, hlr, hlo, hlrod, -⟩ := pre_parts h
  have c := ctx h
  have hsz := hM.size
  have hrun := run_tail bc hrs
  rw [tailP_of bc hall] at hrun
  -- `b10`: the rows copied, the rate's check.
  have hwf := wf0 h hM.bd.fr.kept 0
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf nofun hpc
    (match_mid hM.bd 0) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, -, hv1, x15, xsi, hk1⟩ := ok_b10
  have hb1 : Bod m0 8 st1.data :=
    hM.bd.step c.stack F_le hwf hm1 hmid1 slots_le hW1 (fun _ h ↦ nomatch h)
  have hs1 := same_block hwf hm1 (writesIn_of_mid hmid1) (belowRet_of_mid hmid1) hW1
    (X := fun _ ↦ False) (fun _ h ↦ nomatch h)
  have w0 := (hM.word (i := 0) (by omega)).1
  have w7 := (hM.word (i := 7) (by omega)).1
  have g15 : reg st1.data .r15 = (xs[7]'(by omega)).c0.toBitVec :=
    (hm1.regs .r15 _ x15).trans (ld0 w7)
  have gsi : reg st1.data .rsi = (xs[0]'(by omega)).c0.toBitVec :=
    (hm1.regs .rsi _ xsi).trans (ld0 w0)
  have hrow : ∀ t (ht : t < 6), NativeRustcVm.WordAt st1.data.dmem (off (fb m0) (136 + 8 * t))
      (xs[1 + t]'(by omega)).c0 := by
    intro t ht
    have hw := wordAt_write hm1 (r := 0) (o := 136 + 8 * t) rfl (by omega) (hv1 t ht)
    have hv : (Sym.load 0 (24 + 16 * t) 8).eval (frameEnv m0 st.data 208 [] (fun _ ↦ 0) 0) =
        (xs[1 + t]'(by omega)).c0.toBitVec := by
      have := (hM.word (i := 1 + t) (by omega)).1
      rw [show 16 * (1 + t) + 8 = 24 + 16 * t by omega] at this
      exact ld0 this
    rw [hv, UInt64.ofBitVec_toBitVec] at hw
    exact hw
  have hts1 : TStateAt st1.data.dmem (tA m0) a s1 :=
    ts_keep h hM.ts (hm1.kept hwf) hs1 fun q hq ↦ .inl (hq.elim c.inRange_frame False.elim)
  have hc10 : c10.eval (frameEnv m0 st.data 208 [] (fun _ ↦ 0) 0) = true ↔
      ¬(1 ≤ rateA xs ∧ rateA xs ≤ 4) := by
    rw [c10_eval, show (frameEnv m0 st.data 208 [] (fun _ ↦ 0) 0).load 0 120 8 = _ from ld0 w7,
      UInt64.toNat_toBitVec, ← rateA_get hsz]
  simp only [PcOk] at hpc1
  by_cases hrate : 1 ≤ rateA xs ∧ rateA xs ≤ 4
  swap
  · refine fail75 hp h hb1 ((pc_true hpc1 (hc10.mpr hrate)).trans (lbl_13 hp)) ?_
    rw [hrun, ite_false_of hrate]; rfl
  have hpc63 : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b11Offset) :=
    (pc_false hpc1 (Bool.eq_false_iff.mpr fun h' ↦ hc10.mp h' hrate)).trans
      (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b10_next]))
  -- `b11`: `build_layout(bytecode_len, log_memory, rows, layout)`.
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b11Offset + b11.length)).toBitVec
  have hwf2 := wf0 h hb1.fr.kept ra
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf2 (fun _ _ ↦ rfl) hpc63
    (match_mid hb1 ra) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hW2, hw2, xdx, xdi, xcx, hk2⟩ := ok_b11
  have hb2 : Bod m0 0 st2.data :=
    hb1.step c.stack F_le hwf2 hm2 hmid2 slots_le hW2 (fun _ h ↦ nomatch h)
  have hs2 := same_block hwf2 hm2 (writesIn_of_mid hmid2) (belowRet_of_mid hmid2) hW2
    (X := fun _ ↦ False) (fun _ h ↦ nomatch h)
  have hrow2 : ∀ t (ht : t < 6), NativeRustcVm.WordAt st2.data.dmem (off (fb m0) (136 + 8 * t))
      (xs[1 + t]'(by omega)).c0 := fun t ht ↦
    keepW hwf2 hm2 (writesIn_of_mid hmid2) (by omega)
      (fun w hw _ ↦ .inl (by have := (hw2 w hw).2; omega)) (hrow t ht)
  have e15 : reg st2.data .r15 = (xs[7]'(by omega)).c0.toBitVec :=
    (keeps_reg hm2 hk2 (by simp)).trans g15
  have esi : reg st2.data .rsi = (xs[0]'(by omega)).c0.toBitVec :=
    (keeps_reg hm2 hk2 (by simp)).trans gsi
  have ebx1 : reg st1.data .rbx = lA m0 := (keeps_reg hm1 hk1 (by simp)).trans hM.rbx
  have ebx : reg st2.data .rbx = lA m0 := (keeps_reg hm2 hk2 (by simp)).trans ebx1
  have edi : reg st2.data .rdi = reg m0 .rsi :=
    (hm2.regs .rdi _ xdi).trans ((keeps_reg hm1 hk1 (r := .r14) (by simp)).trans hM.r14)
  have ecx : reg st2.data .rcx = lA m0 := (hm2.regs .rcx _ xcx).trans ebx1
  have edx : reg st2.data .rdx = off (fb m0) 136 := (hm2.regs .rdx _ xdx).trans (eval_ptr0 136)
  have hts2 : TStateAt st2.data.dmem (tA m0) a s1 :=
    ts_keep h hts1 (hm2.kept hwf2) hs2 fun q hq ↦ .inl (hq.elim c.inRange_frame False.elim)
  have hat := at0 h hb2
  have hout := c.outOk_frame hat le_bl (o := 136) (n := 8 * nTables) (by omega) (by decide)
  have hpre : BuildLayoutPre bc st2.data := by
    simp only [BuildLayoutPre]
    rw [edx, ecx, edi]
    refine ⟨c.stackOk hat le_bl, rodata_call h hb2 le_bl, hsize, ⟨hout.1, hout.2.1⟩,
      hout.2.2.2.2.1, ⟨Mapped.keeps hlr.1 hat.kept, hlr.2⟩, c.apart hat le_bl hlo, hlrod,
      Apart.symm' (c.apart_of_stack hlo (o := 136) (k := 8 * nTables) (by decide)), ?_⟩
    apply got_callee ((pre_got h).symbols (by decide : ["memset"].Sublist ["memcpy", "memset"]))
      (fun l hl => got_bytes h hb2 l (by simp_all)) hat.sp c.spN le_bl
    intro l hl a' ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact got_apart_frame (pre_got h) c.stack (by simp_all) F_le (by dsimp only; decide)
    · exact ((pre_got h).1 l (by simp_all)).2.2.2 _ (by simp)
  refine call_then hpc2 (hbl bc) hpre fun st3 hpc3 hrsp3 hq3 ↦ ?_
  simp only [BuildLayoutPost] at hq3
  rw [edx, ecx, esi] at hq3
  obtain ⟨hok3, hL3, hch3, hsv3⟩ := hq3
  have hnats : natsOf st2.data (off (fb m0) 136) nTables = rowsA xs :=
    natsOf_rows hsz fun t ht ↦ by rw [off_add]; exact hrow2 t ht
  have hlm : ((xs[0]'(by omega)).c0.toBitVec).toNat = lmA xs := by
    rw [UInt64.toNat_toBitVec, lmA_get hsz]
  rw [hnats, hlm] at hok3 hL3
  have hch3' : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange (lA m0) layoutBytes q ∨
        NativeRustcVm.InRange (stackBelow st2.data buildLayoutStack) buildLayoutStack q) := hch3
  have hb3 : Bod m0 8 st3.data :=
    hb2.call_apart_at c.stack F_le (Nat.zero_le _) hsv3 hrsp3 (by simpa using le_bl) hch3'
      (fun q hq ↦ .inl (.inl hq)) (fun q hq ↦ outs_not_frame h (.inl hq))
      (fun p hp ↦ ⟨Nat.zero_le _, slots_le p hp⟩)
  have hts3 : TStateAt st3.data.dmem (tA m0) a s1 := by
    refine ts_keep h hts2 hsv3.2 hch3' fun q hq ↦ ?_
    rcases hq with hq | hq
    · exact .inr hq
    · exact .inl (callee_stack h hb2 le_bl hq)
  exact from12 hp h hrs hsz hall hrate
    (hpc3.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b11_next]))) hb3
    ((hsv3.1 .rbx rfl).trans ebx) ((hsv3.1 .r15 rfl).trans e15) hok3 hL3 hts3

end

end NativeRustcVmX64.Layout.ReadAnnouncedSizes
