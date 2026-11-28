module

public import NativeRustcVmX64.Wire.PhaseM.Wide
public import NativeRustcVmX64.Code.Vm.WriteOpenings.Names

/-! # `phase_m`: write the openings, restore the frame, and return -/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after frame_noWrap sameOutside_low
  load_ofMachine)
open NativeRustcVmX64.Sumcheck (wordAt_written)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

public section

variable [Host] {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c k : Nat}

/-- The caller's preserved data and the ten concrete `write_openings` arguments. -/
structure OpenCall (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k count : Nat)
    (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 : Nat)
    (sl : List (List (Nat × Digest))) (cf : Nat) (st : MachineState) : Prop where
  pc : st.pc = Labels.label NativeRustcVmX64.Vm.WriteOpenings.entryLabel
  ret : retOf st.data = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b37Offset)
  fr : Frame m0 192 slotsW 0 st.data
  chg : NativeRustcVm.SameOutside m0.dmem st.data.dmem (Chg m0)
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  model : climbM B height (nodes0 qs lw rows) c6 = some (sl, cf)
  sll : sl.length = height
  sibs : SibsAt st.data.dmem (wa m0 24832) (wa m0 24576) sl
  rd : ReaderAt st.data.dmem (RD m0) bp B cf
  di : reg st.data .rdi = WK m0
  si : (reg st.data .rsi).toNat = count
  dx : reg st.data .rdx = wa m0 2048
  cx : (reg st.data .rcx).toNat = (sortD qs).length
  r8 : reg st.data .r8 = wa m0 352512
  r9 : (reg st.data .r9).toNat = lw
  a0 : (stackArg st.data 0).toNat = height
  a1 : stackArg st.data 1 = wa m0 24832
  a2 : stackArg st.data 2 = wa m0 24576
  a3 : stackArg st.data 3 = OUT m0

/-- Push the four stack arguments and enter `write_openings`. -/
theorem openings_args (hp : Placed code k) (G : Geo m0 bp B.length)
    {count : Nat} {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 : Nat}
    {sl : List (List (Nat × Digest))} {cf : Nat} {st : MachineState}
    (h : Pre36 m0 bp B c k count qs height lw rows c6 sl cf st) :
    Eventually (step1 Host.exe) (OpenCall m0 bp B c k count qs height lw rows c6 sl cf) st := by
  obtain ⟨hpc, hbod, hM, hmod, hsl, hsb, hrd, hbp, hcx, h9, h10, h11, h15⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hon := G.oNw
  have hsW := G.sW
  have hsO := G.sO
  have h32 := hM.h32
  have h64 := hM.lw64
  have hcnt := hM.cnt
  have hps := hM.ps256
  have hfr := frame_widen G (by omega) hbod.fr
  have hwf := wide_wf G hbod.fr.kept (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b36Offset + b36.length)).toBitVec
  have hm : Match (frameEnv m0 st.data 192 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b36Offset + b36.length)).toBitVec) woS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hfr.rsp_eval, trivial⟩ trivial trivial trivial
  obtain ⟨hmid, hw, w8, w16, w24, w32, rdi, rsi, rdx, rcx, r8, r9⟩ := ok_b36
  refine exec_at (infix_of b36_in_code (by simp [b36]) hp) exit_b36 hwf
    (fun _ _ ↦ rfl) hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hf1 : Frame m0 192 slotsW 0 s1.data := Frame.of_block hfr hwf hm1 hmid slotsW_le
  have hsp1 : rspOf s1.data = stackBelow m0 192 := by rw [hf1.sp, off_zero]
  have hs192 := stackBelow_toNat (m := m0) (n := 192) (by omega)
  have hs1 : NativeRustcVm.SameOutside st.data.dmem s1.data.dmem (fun q ↦
      SP0 m0 - 192 ≤ q.toNat ∧ q.toNat < SP0 m0 - 152) :=
    (sameOutside_low hwf hm1 (r := 0) rfl (hi := 40) (by omega) hw).mono fun q hq ↦ by
      have := iv_of_inRange (by rw [hs192]; omega) hq
      rw [hs192] at this
      omega
  have hM1 : Mid m0 B c count qs height lw rows c6 s1.data.dmem :=
    hM.keep G hs1 fun q hq ↦ by unfold Wr; exact .inl (by omega)
  have hrd1 := reader_sw G hrd hs1 (fun q hq ↦ .inl (by omega))
  have hwS := G.wa (o := 24832) (by omega)
  have hwC := G.wa (o := 24576) (by omega)
  have hsb1 : SibsAt s1.data.dmem (wa m0 24832) (wa m0 24576) sl :=
    sibs_keep hsb hs1 (by rw [hwS, hsl]; omega) (by rw [hwC, hsl]; omega)
      (fun q hq ↦ by rw [hwS, hsl]; omega) (fun q hq ↦ by rw [hwC, hsl]; omega)
  have hdi1 : reg s1.data .rdi = WK m0 := (hm1.regs .rdi _ rdi).trans hbod.r14
  have hsi1 : (reg s1.data .rsi).toNat = count := by
    rw [show reg s1.data .rsi = _ from hm1.regs .rsi _ rsi]
    show ((frameEnv m0 st.data 192 []).load 0 72 8).toNat = _
    rw [load_ofMachine (o := 72) rfl (show NativeRustcVm.WordAt st.data.dmem
      (off (stackBelow m0 192) 72) count.toUInt64 by
        rw [wide_addr G (j := 40) (by omega)]; exact hM.f40)]
    rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have hdx1 : reg s1.data .rdx = wa m0 2048 := (hm1.regs .rdx _ rdx).trans hcx
  have hcx1 : (reg s1.data .rcx).toNat = (sortD qs).length := by
    rw [show reg s1.data .rcx = _ from hm1.regs .rcx _ rcx]; exact hbp
  have hr81 : reg s1.data .r8 = wa m0 352512 := by
    rw [show reg s1.data .r8 = _ from hm1.regs .r8 _ r8]
    show (frameEnv m0 st.data 192 []).load 0 88 8 = _
    exact load_ofMachine (o := 88) rfl (show NativeRustcVm.WordAt st.data.dmem
      (off (stackBelow m0 192) 88) (UInt64.ofBitVec (wa m0 352512)) by
        rw [wide_addr G (j := 56) (by omega)]; exact hM.f56)
  have hr91 : (reg s1.data .r9).toNat = lw := by
    rw [show reg s1.data .r9 = _ from hm1.regs .r9 _ r9]; exact h9
  have ha0 : stackArg s1.data 0 = reg st.data .r10 :=
    wide_word hsp1 (i := 0) (wordAt_written hm1 (r := 0) (o := 8) rfl (by omega) w8
      (w := UInt64.ofBitVec (reg st.data .r10)) rfl)
  have ha0n : (stackArg s1.data 0).toNat = height := by rw [ha0]; exact h10
  have ha1 : stackArg s1.data 1 = wa m0 24832 :=
    (wide_word hsp1 (i := 1) (wordAt_written hm1 (r := 0) (o := 16) rfl (by omega) w16
      (w := UInt64.ofBitVec (reg st.data .r11)) rfl)).trans h11
  have ha2 : stackArg s1.data 2 = wa m0 24576 := by
    apply wide_word hsp1 (i := 2) (w := UInt64.ofBitVec (wa m0 24576))
    refine wordAt_written hm1 (r := 0) (o := 24) rfl (by omega) w24 ?_
    show BinOp.apply .add .W64 (reg st.data .r14) (BitVec.ofNat 64 24576) = _
    rw [hbod.r14, add_off]
  have ha3 : stackArg s1.data 3 = OUT m0 :=
    (wide_word hsp1 (i := 3) (wordAt_written hm1 (r := 0) (o := 32) rfl (by omega) w32
      (w := UInt64.ofBitVec (reg st.data .r15)) rfl)).trans h15
  have hchg1 : NativeRustcVm.SameOutside m0.dmem s1.data.dmem (Chg m0) :=
    (hbod.chg.trans hs1).mono fun q hq ↦ hq.elim id (fun hq ↦ .inl (by omega))
  simp only [PcOk] at hpc1
  exact .done _ ⟨hpc1.1, hpc1.2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b36_next), hf1, hchg1,
    hM1, hmod, hsl, hsb1, hrd1, hdi1, hsi1, hdx1, hcx1, hr81, hr91, ha0n, ha1, ha2, ha3⟩

/-- Apply `write_openings` and restore the caller's frame. -/
theorem openings_return (hp : Placed code k) (G : Geo m0 bp B.length)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c)
    (hwo : Spec (Labels.label NativeRustcVmX64.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost)
    {count : Nat} {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 : Nat}
    {sl : List (List (Nat × Digest))} {cf : Nat} {s1 : MachineState}
    (h : OpenCall m0 bp B c k count qs height lw rows c6 sl cf s1) :
    Eventually (step1 Host.exe) (Post m0) s1 := by
  obtain ⟨hpc1, hret1, hf1, hchg1, hM, hmod, hsl, hsb1, hrd1, hdi1, hsi1, hdx1,
    hcx1, hr81, hr91, ha0n, ha1, ha2, ha3⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hon := G.oNw
  have hsO := G.sO
  have hsp1 : rspOf s1.data = stackBelow m0 192 := by rw [hf1.sp, off_zero]
  have hs192 := stackBelow_toNat (m := m0) (n := 192) (by omega)
  have hpre := openings_pre G hf1.kept hsp1 hM.cnt hM.ps256 hM.lw64 hM.h32 hM.cnt0 hM.ps0
    hdi1 hsi1 hdx1 hcx1 hr81 hr91 ha0n ha1 ha2 ha3
  refine Eventually.bind (Spec.apply hwo hpc1 hpre) fun s2 ⟨hpc2, hrsp2, hres2, hso2, hsv2⟩ ↦ ?_
  rw [hret1] at hpc2
  simp only [hdi1, hsi1, hdx1, hcx1, hr81, hr91, ha0n, ha1, ha2, ha3] at hres2
  have hres := hres2 qs (sortD qs) (leavesOf lw rows) sl hM.len
    (fun q hq ↦ ⟨hM.qlt q hq, ((sortD_aux qs [] List.Pairwise.nil).2 q).mpr (.inl hq)⟩)
    (by simpa only [wa, off_zero] using hM.qsW) rfl
    (fun q hq ↦ by have := sortD_lt hM.qlt q hq; omega) hM.psW
    (by simp only [leavesOf, List.length_map]; exact hM.rlen)
    (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact length_paddedLeaf (hM.rw r hr)) hM.lvW hsl hsb1
  have hWS : writeOpeningsStack = 160 := rfl
  obtain ⟨hcs, -⟩ := callee_toNat (n := writeOpeningsStack) hsp1 (by rw [hWS]; omega)
  have hs2 : NativeRustcVm.SameOutside s1.data.dmem s2.data.dmem (fun q ↦
      ((OUT m0).toNat ≤ q.toNat ∧ q.toNat < (OUT m0).toNat + 395288) ∨
      (SP0 m0 - 352 ≤ q.toNat ∧ q.toNat < SP0 m0 - 192)) := by
    refine hso2.mono fun q ⟨R, hR, hq⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · have hq' : NativeRustcVm.InRange (stackArg s1.data 3) phaseBytes q := hq
      rw [ha3, phaseBytes_eq] at hq'
      exact .inl (iv_of_inRange G.oNw hq')
    · have hq' : NativeRustcVm.InRange (stackBelow s1.data writeOpeningsStack) writeOpeningsStack q := hq
      have := iv_of_inRange (by rw [hcs, hWS]; omega) hq'
      rw [hcs, hWS] at this
      exact .inr (by omega)
  have hf2 : Frame m0 192 slotsW 8 s2.data := Frame.call hf1 hsv2 hrsp2 hs2
    (fun q hq hq' ↦ by
      have := iv_of_inRange (by rw [hs192]; omega) hq'
      rw [hs192] at this
      omega) (frame_noWrap G.st (by decide)) slotsW_le
  have hchg2 : NativeRustcVm.SameOutside m0.dmem s2.data.dmem (Chg m0) :=
    (hchg1.trans hs2).mono fun q hq ↦ by
      rcases hq with hq | hq
      · exact hq
      · rcases hq with hq | hq
        · exact .inr (.inr (.inl hq))
        · exact .inl ⟨le_trans (Nat.sub_le_sub_left (show 352 ≤ 1216 by decide) _) hq.1,
            lt_of_lt_of_le hq.2 (Nat.sub_le _ _)⟩
  have hrd2 : ReaderAt s2.data.dmem (RD m0) bp B cf :=
    reader_keep hrd1 hs2 (fun q hq ↦ by
      have hsR := G.sR; have hrO := G.rO; clear * - hq hsR hrO hsp; omega)
      (fun q hq ↦ by
        have hsB := G.sB; have hbO := G.bO; clear * - hq hsB hbO hsp; omega)
  have hwf2 := wide_wf G hf2.kept
  have hm2 : Match (frameEnv m0 s2.data 192 []) woS' s2.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial trivial
  obtain ⟨hmid37, hmem37, hrax37⟩ := ok_b37
  refine exec_at (infix_of b37_in_code (by simp [b37]) hp) exit_b37 hwf2 nofun
    hpc2 hm2 fun s3 hm3 hpc3 ↦ ?_
  have hf3 := Frame.of_block hf2 hwf2 hm3 hmid37 slotsW_le
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq hwf2 hmem37
  have ha3' : reg s3.data .rax = reg s2.data .rax := hm3.regs .rax _ hrax37
  refine fin hp G (hpc3.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_24_at))
    (frame_narrow G (o := 112) (by omega) hf3)
    (by rw [hd3]; exact hchg2) fun bp' B' c' hR' ↦ ?_
  obtain ⟨rfl, rfl, rfl⟩ := hR0.unique hR'
  unfold Res
  rw [hM.model, climbFin, hmod]
  refine ⟨?_, ?_, ?_⟩
  · unfold boolRet at hres ⊢
    rw [ha3']; exact hres.1
  · rw [hd3]; exact hres.2
  · rw [hd3]; exact hrd2

/-- The successful climb's openings, followed by the common epilogue. -/
theorem openings_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c)
    (hwo : Spec (Labels.label NativeRustcVmX64.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost)
    {count : Nat} {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 : Nat}
    {sl : List (List (Nat × Digest))} {cf : Nat} {st : MachineState}
    (h : Pre36 m0 bp B c k count qs height lw rows c6 sl cf st) :
    Eventually (step1 Host.exe) (Post m0) st :=
  Eventually.bind (openings_args hp G h) fun _ h' ↦ openings_return hp G hR0 hwo h'

end

end NativeRustcVmX64.Wire.PhaseM
