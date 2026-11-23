module

public import NativeRustcVmArm.Code.Vm.Kinv.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.SubspaceTable.Inv

/-!
# `subspace_table`'s table start

From the initialized layer (`Init μ`, `b11`): the table's `Buf` zeroed past the layer, `kinv(1)`,
the pair `(1, kinv 1)` pushed (`b12`); for `μ = 0` that is the table (`Done`), else `b13` sets the
turns' registers (`OInv 0`).
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region WordAt WordsAt)

public section

variable [Host] {k : Nat}

/-- **The table's start.** -/
theorem start (hp : Placed code k) (hkinv : Spec (label NativeRustcVmArm.Vm.Kinv.entryLabel) KinvPre KinvPost)
    {m0 : MachineData} (hS : StackOk m0 subspaceTableStack) {st : MachineData}
    (hI : Init m0 (muOf m0) st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (OInv m0 0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset)) ∨
        (Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b21Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b11Offset)⟩ := by
  have hF : 864 ≤ subspaceTableStack := by decide
  have hkle : 864 + kinvStack ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfb : (fbOf m0).toNat + 864 ≤ 2 ^ 64 := hfnw
  have hmu := hI.hmu
  have hfr := hI.fr
  have hll : ((initL (muOf m0)).flatMap NativeRustcVm.wordBytes).length = 248 := by
    rw [NativeRustcVm.length_wordsBytes, initL_length]
  have hol : (NativeRustcVm.wordBytes m0.regs.X0).length = 8 := NativeRustcVm.length_wordBytes _
  -- `b11`: zero the table, `kinv(1)`
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine st [(fbOf m0, 864)]
  have hwf : env.WF := wf_one (hfr.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm : Match env frS st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  refine exec_then hk11 run_b11 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hb11 := after_eq run_b11 ▸ b11_keeps
  have hall : ∀ w ∈ (after b11 frS).mem, w.r = 0 ∧ 264 ≤ w.off ∧ w.off + w.n ≤ 768 :=
    b11_keeps.2
  rw [after_eq run_b11] at hall
  have hfr1 := hfr.of_block hm hm1 hwf rfl hb11.1 (r := 0) rfl (by decide)
    (fun w hw ↦ ⟨(hall w hw).1, (hall w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 0) (n := 768) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq i hi ↦ by
      have := not_inRange_slot hS hF (o := 0) (n := 768) (by omega) (slots_le q hq) hi
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)
  have hlay1 : WordsAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (initL (muOf m0)) :=
    bytesAt_keep hm1 hwf (r := 0) rfl (by rw [hll]; omega)
      (fun w hw ↦ ⟨(hall w hw).1, .inr (by rw [hll]; have := (hall w hw).2.1; omega)⟩) hI.layer
  have hout1 : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0 :=
    bytesAt_keep hm1 hwf (r := 0) rfl (by rw [hol]; omega)
      (fun w hw ↦ ⟨(hall w hw).1, .inr (by rw [hol]; have := (hall w hw).2.1; omega)⟩) hI.out
  have hx0 : s1.data.regs.X0 = 1 := UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
  have hx25 : s1.data.regs.X25 = 1 := UInt64.toBitVec_inj.mp (hm1.regs .X25 _ rfl)
  refine call_then hpc1 hkinv (hfr1.stackOk hS rfl hkle) fun s2 hpc2 ⟨hk2, hsame2, hsv2⟩ ↦ ?_
  have hfr2 := hfr1.call hS hkle slots_le hsame2 hsv2
  have hlay2 : WordsAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (initL (muOf m0)) :=
    hfr1.bytes_call hS hkle hsame2 (o := 16) (by rw [hll]; omega) hlay1
  have hout2 : WordAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0 :=
    hfr1.bytes_call hS hkle hsame2 (o := 8) (bs := NativeRustcVm.wordBytes m0.regs.X0)
      (by rw [hol]; omega) hout1
  have hinv : s2.data.regs.X0 = kinv 1 := by rw [hk2, hx0]
  have e20 : s2.data.regs.X20 = st.regs.X20 :=
    (hsv2.1 .X20 rfl).trans (Match.reg_eq (r := .X20) hm hm1 rfl rfl)
  have e24 : s2.data.regs.X24 = st.regs.X24 :=
    (hsv2.1 .X24 rfl).trans (Match.reg_eq (r := .X24) hm hm1 rfl rfl)
  have e25 : s2.data.regs.X25 = 1 := (hsv2.1 .X25 rfl).trans hx25
  -- `b12`: push `(1, kinv 1)`
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b12Offset) := b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b12Offset) := hpc2
  let env2 := Env.ofMachine s2.data [(fbOf m0, 864)]
  have hwf2 : env2.WF := wf_one (hfr2.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm2 : Match env2 frS s2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr2.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  refine exec_at hk12 run_b12 hwf2 hpc2' hm2 fun s3 hm3 hpc3 ↦ ?_
  have hall2 : ∀ w ∈ (after b12 frS).mem, w.r = 0 ∧ 272 ≤ w.off ∧ w.off + w.n ≤ 288 :=
    b12_keeps.2
  rw [after_eq run_b12] at hall2
  have hb12 := after_eq run_b12 ▸ b12_keeps
  have hfr3 := hfr2.of_block hm2 hm3 hwf2 rfl hb12.1 (r := 0) rfl (by decide)
    (fun w hw ↦ ⟨(hall2 w hw).1, (hall2 w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 0) (n := 288) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq i hi ↦ by
      have := not_inRange_slot hS hF (o := 0) (n := 288) (by omega) (slots_le q hq) hi
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)
  have hlay3 : WordsAt s3.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (initL (muOf m0)) :=
    bytesAt_keep hm3 hwf2 (r := 0) rfl (by rw [hll]; omega)
      (fun w hw ↦ ⟨(hall2 w hw).1, .inr (by rw [hll]; have := (hall2 w hw).2.1; omega)⟩) hlay2
  have hout3 : WordAt s3.data.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0 :=
    bytesAt_keep hm3 hwf2 (r := 0) rfl (by rw [hol]; omega)
      (fun w hw ↦ ⟨(hall2 w hw).1, .inr (by rw [hol]; have := (hall2 w hw).2.1; omega)⟩) hout2
  have htab : WordsAt s3.data.dmem (fbOf m0 + BitVec.ofNat 64 272)
      (pairWords (tableAt (muOf m0) 0)) := by
    have w0 := Match.wordAt_write hm3 (r := 0) (o := 272) rfl (by decide) (v := .reg .X25)
      (by decide)
    have w1 := Match.wordAt_write hm3 (r := 0) (o := 280) rfl (by decide) (v := .reg .X0)
      (by decide)
    have e25' : UInt64.ofBitVec ((Sym.reg .X25).eval env2) = 1 := e25
    have e0 : UInt64.ofBitVec ((Sym.reg .X0).eval env2) = kinv 1 := hinv
    rw [e25'] at w0
    rw [e0] at w1
    have hpw : pairWords [rootPair 1] = [1, kinv 1] := by
      simp only [pairWords, rootPair, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [tableAt_zero, hpw,
      NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_singleton_iff, addr_add]
    exact ⟨w0, w1⟩
  have h20 : st.regs.X20.toNat = muOf m0 := by rw [hI.x20]; rfl
  have e20' : (env2.regs .X20).toNat = muOf m0 := by
    show s2.data.regs.X20.toBitVec.toNat = _
    rw [e20]
    exact h20
  have e25' : s3.data.regs.X25 = 1 := (Match.reg_eq (r := .X25) hm2 hm3 rfl rfl).trans e25
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  simp only [bv_beq_toNat, e20', BitVec.toNat_ofNat, Nat.zero_mod] at hpc3
  by_cases hz : muOf m0 = 0
  · simp only [hz, decide_true, ↓reduceIte] at hpc3
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_16 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b21Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b21Offset) NativeRustcVmArm.Vm.SubspaceTable.label_16_at
    refine .done _ (.inr ⟨⟨hfr3, hout3, ?_, ?_, by omega⟩, hpc3.trans hl⟩)
    · rw [hz]; rw [hz] at htab; exact htab
    · rw [e25', hz]; rfl
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
    -- `b13`: the turns' registers
    have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
    have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b13Offset) := hpc3
    refine exec_at hk13 run_b13 (Env.wf_nil _) hpc3' (match_nil _) fun s4 hm4 hpc4 ↦ ?_
    have hb13 := after_eq run_b13 ▸ b13_keeps
    have hfr4 := hfr3.of_regs (match_nil _) hm4 (Env.wf_nil _) rfl hb13.1 hb13.2
    have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq (Env.wf_nil _) hb13.2
    have hsp3 : s3.data.regs.SP.toBitVec = fbOf m0 := hfr3.sp
    have e4 : ∀ r ∈ [XReg.X20, .X24], s4.data.regs.getXReg r = s2.data.regs.getXReg r :=
      fun r hr ↦ by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact (Match.reg_eq (r := .X20) (match_nil _) hm4 rfl rfl).trans
            (Match.reg_eq (r := .X20) hm2 hm3 rfl rfl)
        · exact (Match.reg_eq (r := .X24) (match_nil _) hm4 rfl rfl).trans
            (Match.reg_eq (r := .X24) hm2 hm3 rfl rfl)
    have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset) := hpc4
    refine .done _ (.inl ⟨⟨⟨hfr4, hd4 ▸ hout3, hd4 ▸ htab, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hmu⟩,
      ?_, ?_⟩, hpc4'⟩)
    · exact ((e4 .X20 (by simp)).trans e20).trans hI.x20
    · rw [show s4.data.regs.X24 = s2.data.regs.X24 from e4 .X24 (by simp), e24]; exact hI.x24
    · show (s4.data.regs.getXReg .X25).toBitVec.toNat = _
      rw [hm4.regs .X25 _ rfl]; rfl
    · show (s4.data.regs.getXReg .X26).toBitVec.toNat = _
      rw [hm4.regs .X26 _ rfl]; rfl
    · show (s4.data.regs.getXReg .X27).toBitVec = _
      rw [hm4.regs .X27 _ rfl]
      sym_simp
      rw [show (Env.ofMachine s3.data []).sp = s3.data.regs.SP.toBitVec from rfl, hsp3]
    · show (s4.data.regs.getXReg .X28).toBitVec = _
      rw [hm4.regs .X28 _ rfl]
      sym_simp
      rw [show (Env.ofMachine s3.data []).sp = s3.data.regs.SP.toBitVec from rfl, hsp3]
    · show s4.data.regs.getXReg .X21 = _
      exact UInt64.toBitVec_inj.mp (hm4.regs .X21 _ rfl)
    · rw [hd4, layerAt, ← initL_take hmu]
      exact NativeRustcVm.WordsAt.take hlay3 _

end

end NativeRustcVmArm.Whir.SubspaceTable
