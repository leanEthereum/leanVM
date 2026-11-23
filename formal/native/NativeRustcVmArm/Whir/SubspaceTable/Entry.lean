module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.SubspaceTable.Init
public import NativeRustcVmArm.Whir.SubspaceTable.Outer

/-!
# `subspace_table`'s entry

`b0` saves the callee-saved registers in its 864-byte frame and zeroes the layer (`memset`);
`b1` leaves for `μ > 31` (`b5`); `b2` spills the output; for `μ = 0` the layer is done, else
`b3` picks the unrolled initialization (`b6`, `μ ≥ 4`, then `b8`) or not (`b4`), the rest word by
word (`b9`, `b10`). It ends with `Init μ` at `b11`.
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region WordAt WordsAt)

public section

theorem toNat_take₃ {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `lsr x, #3`. -/
theorem evalUBFM_lsr3 (x : BitVec 64) :
    (evalUBFM (w := .W64) x 3 63 : BitVec 64).toNat = x.toNat / 8 := by
  have hb : RegWidth.W64.bits = 64 := rfl
  simp only [evalUBFM, hb, show 3 % 64 = 3 from rfl, show 63 % 64 = 63 from rfl,
    show 63 ≥ 3 from by omega, ↓reduceIte, BitVec.toNat_setWidth, toNat_take₃,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- `lsl x, #3`. -/
theorem evalUBFM_lsl3 (x : BitVec 64) :
    (evalUBFM (w := .W64) x 61 60 : BitVec 64) = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take₃, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The unrolled loop's count. -/
theorem and_mask (n : Nat) (h : n < 32) :
    (BitVec.ofNat 64 n &&& BitVec.ofNat 64 4611686018427387900).toNat = n / 4 * 4 := by
  have : ∀ n < 32,
      (BitVec.ofNat 64 n &&& BitVec.ofNat 64 4611686018427387900).toNat = n / 4 * 4 := by decide
  exact this n h

theorem wordBytes_zero : NativeRustcVm.wordBytes 0 = List.replicate 8 (0 : UInt8) := by decide

theorem zeros_eq : ∀ n, (List.replicate n (0 : UInt64)).flatMap NativeRustcVm.wordBytes =
    List.replicate (8 * n) (0 : UInt8)
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatMap_cons, zeros_eq n, wordBytes_zero,
      show 8 * (n + 1) = 8 + 8 * n by omega, List.replicate_add]

variable [Host] {k : Nat}

/-- **The word loop from word `i`** (`b9`, `b10`). -/
theorem words (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 subspaceTableStack)
    {i : Nat} {st : MachineData} (hI : Init m0 i st) (hi : i < muOf m0)
    (hx8 : st.regs.X8.toNat = i)
    (hx9 : st.regs.X9.toBitVec = fbOf m0 + BitVec.ofNat 64 (16 + 8 * i)) :
    Eventually (step1 Host.exe) (fun s ↦ Init m0 (muOf m0) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b11Offset))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b9Offset)⟩ := by
  have hF : 864 ≤ subspaceTableStack := by decide
  obtain ⟨-, hfnw, -⟩ := frame_ok hS hF
  have hfb : (fbOf m0).toNat + 864 ≤ 2 ^ 64 := hfnw
  have hmu := hI.hmu
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk9 run_b9 (Env.wf_nil _) (match_nil _) fun s1 hm1 hpc1 ↦ ?_
  have hb9 := after_eq run_b9 ▸ b9_keeps
  have hfr1 := hI.fr.of_regs (match_nil _) hm1 (Env.wf_nil _) rfl hb9.1 hb9.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq (Env.wf_nil _) hb9.2
  have hI1 : Init m0 i s1.data :=
    ⟨hfr1, hd1 ▸ hI.out, hd1 ▸ hI.layer,
      (Match.reg_eq (r := .X20) (match_nil _) hm1 rfl rfl).trans hI.x20,
      by rw [show s1.data.regs.X21 = st.regs.X21 from
        Match.reg_eq (r := .X21) (match_nil _) hm1 rfl rfl]; exact hI.x21,
      by rw [show s1.data.regs.X24 = st.regs.X24 from
        Match.reg_eq (r := .X24) (match_nil _) hm1 rfl rfl]; exact hI.x24, hmu⟩
  have hT : TInv m0 i s1.data := by
    refine ⟨hI1, ?_, ?_, ?_, ?_, hi⟩
    · rw [show s1.data.regs.X8 = st.regs.X8 from
        Match.reg_eq (r := .X8) (match_nil _) hm1 rfl rfl]; exact hx8
    · rw [show s1.data.regs.X9 = st.regs.X9 from
        Match.reg_eq (r := .X9) (match_nil _) hm1 rfl rfl]; exact hx9
    · have h24 : st.regs.X24.toBitVec = BitVec.ofNat 64 (8 * muOf m0) := by
        apply BitVec.eq_of_toNat_eq
        have := hI.x24
        rw [BitVec.toNat_ofNat]
        show st.regs.X24.toNat = _
        omega
      show (s1.data.regs.getXReg .X10).toBitVec = _
      rw [hm1.regs .X10 _ rfl]
      sym_simp
      show st.regs.X21.toBitVec + st.regs.X24.toBitVec = _
      rw [hI.x21, h24, addr_add]
    · exact UInt64.toBitVec_inj.mp (hm1.regs .X11 _ rfl)
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b10Offset) := hpc1
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ Init m0 (muOf m0) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b11Offset))
    (fun n s ↦ ∃ j, n = muOf m0 - j ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b10Offset) ∧ TInv m0 j s.data)
    (fun n s ⟨j, hn, hpc, hT⟩ ↦ by
      obtain ⟨d, pc⟩ := s
      simp only at hpc
      subst hpc
      refine (tail_step hp hS hT).mono fun s' h ↦ ?_
      rcases h with ⟨hT', hpc'⟩ | h
      · exact .inr ⟨muOf m0 - (j + 1), by have := hT.hi; omega, j + 1, rfl, hpc', hT'⟩
      · exact .inl h)
    (n := muOf m0 - i) ⟨i, rfl, hpc1', hT⟩
  exact hloop

/-- **The entry**: the layer initialized (`Init μ` at `b11`), or `μ > 31` at `b5`. -/
theorem entry (hp : Placed code k) (hmemset : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Init m0 (muOf m0) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b11Offset)) ∨
        (Fr m0 s.data ∧ s.data.regs.X19 = m0.regs.X0 ∧ 31 < muOf m0 ∧
          s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b5Offset)))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b0Offset)⟩ := by
  have hS := hpre.1
  have hF : 864 ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfb : (fbOf m0).toNat + 864 ≤ 2 ^ 64 := hfnw
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env0 := Env.ofMachine m0 [(fbOf m0, 864)]
  have hwf0 : env0.WF := wf_one hfmap hfnw
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  refine exec_then hk0 run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  have hb0 := after_eq run_b0 ▸ b0_frame
  have hfr1 : Fr m0 s1.data := Frame.of_entry hS hF hwf0 hm1 rfl hb0.1 hb0.2.2 hb0.2.1
  -- `memset` of the layer
  have hx0 : s1.data.regs.X0.toBitVec = fbOf m0 + BitVec.ofNat 64 16 :=
    (hm1.regs .X0 _ rfl).trans rfl
  have hx1 : s1.data.regs.X1 = 0 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  have hx2 : s1.data.regs.X2.toNat = 248 := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]
    rfl
  have hpre1 : MemsetPre s1.data := by
    unfold MemsetPre
    rw [hx0, hx2]
    exact hfr1.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  refine call_then hpc1 hmemset hpre1 fun s2 hpc2 ⟨_, hz, hsame2, hsv2⟩ ↦ ?_
  rw [hx0, hx2] at hsame2 hz
  rw [hx1] at hz
  have hfr2 := hfr1.change hsame2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 16) (n := 248) (by omega) h))
    (fun q hq j hj ↦ not_inRange_slot hS hF (by omega) (slots_le q hq) hj
      (.inl (by have := slots_ge q hq; omega)))
    (fun r hr _ ↦ hsv2.1 r hr) hsv2.2.1 hsv2.2.2
  have hlay2 : WordsAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (initL 0) := by
    rw [initL_zero]
    unfold WordsAt
    rw [zeros_eq 31]
    exact hz
  have e19 : s2.data.regs.X19 = m0.regs.X0 :=
    (hsv2.1 .X19 rfl).trans (UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl))
  have e20 : s2.data.regs.X20 = m0.regs.X1 :=
    (hsv2.1 .X20 rfl).trans (UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl))
  have e21 : s2.data.regs.X21.toBitVec = fbOf m0 + BitVec.ofNat 64 16 :=
    (congrArg UInt64.toBitVec (hsv2.1 .X21 rfl)).trans ((hm1.regs .X21 _ rfl).trans rfl)
  -- `b1`: `μ > 31`
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b1Offset) := hpc2
  refine exec_at hk1 run_b1 (Env.wf_nil _) hpc2' (match_nil _) fun s3 hm3 hpc3 ↦ ?_
  have hb1 := after_eq run_b1 ▸ b1_keeps
  have hfr3 := hfr2.of_regs (match_nil _) hm3 (Env.wf_nil _) rfl hb1.1 hb1.2
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) hb1.2
  have r3 : ∀ r, s3.data.regs.getXReg r = s2.data.regs.getXReg r := fun r ↦ by
    cases r <;> exact Match.reg_eq (match_nil _) hm3 rfl rfl
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  have h20 : (s2.data.regs.getXReg .X20).toBitVec.toNat = muOf m0 := by
    show s2.data.regs.X20.toNat = _; rw [e20]; rfl
  simp only [Env.ofMachine_regs, ult_ofNat (show 32 < 2 ^ 64 by decide), h20] at hpc3
  by_cases hbig : 31 < muOf m0
  · simp only [show ¬muOf m0 < 32 by omega, decide_false, Bool.not_false, ↓reduceIte] at hpc3
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b5Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b5Offset) NativeRustcVmArm.Vm.SubspaceTable.label_4_at
    exact .done _ (.inr ⟨hfr3, (r3 .X19).trans e19, hbig, hpc3.trans hl⟩)
  have hmu : muOf m0 ≤ 31 := by omega
  simp only [show muOf m0 < 32 by omega, decide_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] at hpc3
  -- `b2`: spill the output, `8μ`
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b2Offset) := hpc3
  let env4 := Env.ofMachine s3.data [(fbOf m0, 864)]
  have hwf4 : env4.WF := wf_one (hfr3.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm4 : Match env4 frS s3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr3.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  refine exec_at hk2 run_b2 hwf4 hpc3' hm4 fun s4 hm5 hpc4 ↦ ?_
  have hb2 := after_eq run_b2 ▸ b2_keeps
  have hfr4 := hfr3.of_block hm4 hm5 hwf4 rfl hb2.1 (r := 0) rfl (by decide) hb2.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 0) (n := 16) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq i hi ↦ by
      have := not_inRange_slot hS hF (o := 0) (n := 16) (by omega) (slots_le q hq) hi
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)
  have hll : ((initL 0).flatMap NativeRustcVm.wordBytes).length = 248 := by
    rw [NativeRustcVm.length_wordsBytes, initL_length]
  have hlay4 : WordsAt s4.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (initL 0) :=
    bytesAt_keep hm5 hwf4 (r := 0) rfl (by rw [hll]; omega)
      (fun w hw ↦ ⟨(hb2.2 w hw).1, .inl (by have := (hb2.2 w hw).2; omega)⟩)
      (show WordsAt s3.data.dmem _ _ by rw [hd3]; exact hlay2)
  have hout4 : WordAt s4.data.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0 := by
    have := Match.wordAt_write hm5 (r := 0) (o := 8) rfl (by decide) (v := .reg .X19) (by decide)
    convert this using 1
    show _ = UInt64.ofBitVec (s3.data.regs.getXReg .X19).toBitVec
    rw [r3 .X19, show s2.data.regs.getXReg .X19 = m0.regs.X0 from e19]
  have e24 : s4.data.regs.X24.toNat = 8 * muOf m0 := by
    show (s4.data.regs.getXReg .X24).toBitVec.toNat = _
    rw [hm5.regs .X24 _ rfl]
    simp only [Sym.eval, UnOp.apply, Sym.ext_W64, Sym.low_W64, evalUBFM_lsl3, BitVec.toNat_ofNat]
    show 8 * (s3.data.regs.getXReg .X20).toBitVec.toNat % 2 ^ 64 = _
    rw [r3 .X20, h20]
    omega
  have k4 : ∀ r ∈ [XReg.X20, .X21], s4.data.regs.getXReg r = s2.data.regs.getXReg r :=
    fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · exact (Match.reg_eq (r := .X20) hm4 hm5 rfl rfl).trans (r3 .X20)
      · exact (Match.reg_eq (r := .X21) hm4 hm5 rfl rfl).trans (r3 .X21)
  have hI0 : Init m0 0 s4.data :=
    ⟨hfr4, hout4, hlay4, (k4 .X20 (by simp)).trans e20,
      by rw [show s4.data.regs.X21 = s2.data.regs.X21 from k4 .X21 (by simp)]; exact e21,
      e24, hmu⟩
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  have h20' : (env4.regs .X20).toNat = muOf m0 := by
    show (s3.data.regs.getXReg .X20).toBitVec.toNat = _
    rw [r3 .X20, h20]
  simp only [bv_beq_toNat, h20', BitVec.toNat_ofNat, Nat.zero_mod] at hpc4
  by_cases hz : muOf m0 = 0
  · simp only [hz, decide_true, ↓reduceIte] at hpc4
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b11Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b11Offset) NativeRustcVmArm.Vm.SubspaceTable.label_10_at
    exact .done _ (.inl ⟨hz ▸ hI0, hpc4.trans hl⟩)
  simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
  -- `b3`: unrolled or not
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b3Offset) := hpc4
  refine exec_at hk3 run_b3 (Env.wf_nil _) hpc4' (match_nil _) fun s5 hm6 hpc5 ↦ ?_
  have hb3 := after_eq run_b3 ▸ b3_keeps
  have hfr5 := hfr4.of_regs (match_nil _) hm6 (Env.wf_nil _) rfl hb3.1 hb3.2
  have hd5 : s5.data.dmem = s4.data.dmem := hm6.dmem_eq (Env.wf_nil _) hb3.2
  have r5 : ∀ r ∈ [XReg.X20, .X21, .X24], s5.data.regs.getXReg r = s4.data.regs.getXReg r :=
    fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Match.reg_eq (r := .X20) (match_nil _) hm6 rfl rfl
      · exact Match.reg_eq (r := .X21) (match_nil _) hm6 rfl rfl
      · exact Match.reg_eq (r := .X24) (match_nil _) hm6 rfl rfl
  have hI5 : Init m0 0 s5.data :=
    ⟨hfr5, hd5 ▸ hI0.out, hd5 ▸ hI0.layer, (r5 .X20 (by simp)).trans hI0.x20,
      by rw [show s5.data.regs.X21 = s4.data.regs.X21 from r5 .X21 (by simp)]; exact hI0.x21,
      by rw [show s5.data.regs.X24 = s4.data.regs.X24 from r5 .X24 (by simp)]; exact hI0.x24,
      hmu⟩
  have hx8 : s5.data.regs.X8.toNat = 8 * muOf m0 - 8 := by
    show (s5.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hm6.regs .X8 _ rfl]
    sym_simp
    show (s4.data.regs.X24.toBitVec - BitVec.ofNat 64 8).toNat = _
    rw [toNat_sub_ofNat (by show 8 ≤ s4.data.regs.X24.toNat; omega)]
    show s4.data.regs.X24.toNat - 8 = _
    rw [e24]
  have hx9 : s5.data.regs.X9.toBitVec = fbOf m0 + BitVec.ofNat 64 16 := by
    show (s5.data.regs.getXReg .X9).toBitVec = _
    rw [hm6.regs .X9 _ rfl]
    sym_simp
    show s4.data.regs.SP.toBitVec + BitVec.ofNat 64 16 = _
    rw [hfr4.sp]
    rfl
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  have h8 : (Env.ofMachine s4.data []).regs .X24 - BitVec.ofNat 64 8 = s5.data.regs.X8.toBitVec := by
    show _ = (s5.data.regs.getXReg .X8).toBitVec
    rw [hm6.regs .X8 _ rfl]
    sym_simp
  rw [h8, ult_ofNat (show 24 < 2 ^ 64 by decide)] at hpc5
  rw [show s5.data.regs.X8.toBitVec.toNat = 8 * muOf m0 - 8 from hx8] at hpc5
  by_cases h4 : 4 ≤ muOf m0
  · -- `b6`: the unrolled loop
    simp only [show ¬8 * muOf m0 - 8 < 24 by omega, decide_false, Bool.not_false,
      ↓reduceIte] at hpc5
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b6Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b6Offset) NativeRustcVmArm.Vm.SubspaceTable.label_5_at
    have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk6 run_b6 (Env.wf_nil _) (hpc5.trans hl) (match_nil _) fun s6 hm7 hpc6 ↦ ?_
    have hb6 := after_eq run_b6 ▸ b6_keeps
    have hfr6 := hfr5.of_regs (match_nil _) hm7 (Env.wf_nil _) rfl hb6.1 hb6.2
    have hd6 : s6.data.dmem = s5.data.dmem := hm7.dmem_eq (Env.wf_nil _) hb6.2
    have r6 : ∀ r ∈ [XReg.X20, .X21, .X24], s6.data.regs.getXReg r = s5.data.regs.getXReg r :=
      fun r hr ↦ by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Match.reg_eq (r := .X20) (match_nil _) hm7 rfl rfl
        · exact Match.reg_eq (r := .X21) (match_nil _) hm7 rfl rfl
        · exact Match.reg_eq (r := .X24) (match_nil _) hm7 rfl rfl
    have hI6 : Init m0 (4 * 0) s6.data :=
      ⟨hfr6, hd6 ▸ hI5.out, hd6 ▸ hI5.layer, (r6 .X20 (by simp)).trans hI5.x20,
        by rw [show s6.data.regs.X21 = s5.data.regs.X21 from r6 .X21 (by simp)]; exact hI5.x21,
        by rw [show s6.data.regs.X24 = s5.data.regs.X24 from r6 .X24 (by simp)]; exact hI5.x24,
        hmu⟩
    -- `μ`, its multiple of `4`
    have hsh : (evalUBFM (w := .W64) s5.data.regs.X8.toBitVec 3 63 : BitVec 64) +
        BitVec.ofNat 64 1 = BitVec.ofNat 64 (muOf m0) := by
      have hl : (evalUBFM (w := .W64) s5.data.regs.X8.toBitVec 3 63 : BitVec 64) =
          BitVec.ofNat 64 (muOf m0 - 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [evalUBFM_lsr3, show s5.data.regs.X8.toBitVec.toNat = _ from hx8, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (show muOf m0 - 1 < 32 by omega) (by decide))]
        omega
      rw [hl, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add,
        show muOf m0 - 1 + 1 = muOf m0 by omega]
    have hn4 : (BitVec.ofNat 64 (muOf m0) &&& BitVec.ofNat 64 4611686018427387900).toNat =
        n4Of m0 := and_mask _ (by omega)
    have hn4v : n4Of m0 = muOf m0 / 4 * 4 := rfl
    have hV : VInv m0 0 s6.data := by
      refine ⟨hI6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · show (s6.data.regs.getXReg .X8).toBitVec.toNat = _
        rw [hm7.regs .X8 _ rfl]
        sym_simp
        rw [show (Env.ofMachine s5.data []).regs .X8 = s5.data.regs.X8.toBitVec from rfl, hsh, hn4]
      · show (s6.data.regs.getXReg .X9).toBitVec = _
        rw [hm7.regs .X9 _ rfl]
        sym_simp
        rw [show (Env.ofMachine s5.data []).regs .X8 = s5.data.regs.X8.toBitVec from rfl, hsh,
          show (Env.ofMachine s5.data []).regs .X9 = s5.data.regs.X9.toBitVec from rfl, hx9]
        rw [shl_ofNat hn4, addr_add]
        congr 2
        omega
      · show (s6.data.regs.getXReg .X10).toBitVec.toNat = _
        rw [hm7.regs .X10 _ rfl]
        sym_simp
        rw [show (Env.ofMachine s5.data []).regs .X8 = s5.data.regs.X8.toBitVec from rfl, hsh,
          BitVec.toNat_ofNat]
        omega
      · show (s6.data.regs.getXReg .X11).toBitVec = _
        rw [hm7.regs .X11 _ rfl]
        sym_simp
        rw [show (Env.ofMachine s5.data []).regs .X9 = s5.data.regs.X9.toBitVec from rfl, hx9,
          addr_add]
      · show (s6.data.regs.getXReg .X12).toBitVec.toNat = _
        rw [hm7.regs .X12 _ rfl]; rfl
      · exact UInt64.toBitVec_inj.mp (hm7.regs .X13 _ rfl)
      · exact UInt64.toBitVec_inj.mp (hm7.regs .X14 _ rfl)
      · exact UInt64.toBitVec_inj.mp (hm7.regs .X15 _ rfl)
      · exact UInt64.toBitVec_inj.mp (hm7.regs .X16 _ rfl)
      · show (s6.data.regs.getXReg .X17).toBitVec.toNat = _
        rw [hm7.regs .X17 _ rfl]
        sym_simp
        rw [show (Env.ofMachine s5.data []).regs .X8 = s5.data.regs.X8.toBitVec from rfl, hsh, hn4]
        rfl
    have hpc6' : s6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b7Offset) := hpc6
    have hloop := Sym.loop (tr := step1 Host.exe)
      (Q := fun s ↦ VDone m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b8Offset))
      (fun n s ↦ ∃ j, n = n4Of m0 - 4 * j ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b7Offset) ∧ VInv m0 j s.data)
      (fun n s ⟨j, hn, hpc, hV⟩ ↦ by
        obtain ⟨d, pc⟩ := s
        simp only at hpc
        subst hpc
        refine (vec_step hp hS hV).mono fun s' h ↦ ?_
        rcases h with ⟨hV', hpc'⟩ | h
        · exact .inr ⟨n4Of m0 - 4 * (j + 1), by have := hV.hj; omega, j + 1, rfl, hpc', hV'⟩
        · exact .inl h)
      (n := n4Of m0 - 4 * 0) ⟨0, rfl, hpc6', hV⟩
    refine hloop.bind fun s7 ⟨hD, hpc7⟩ ↦ ?_
    -- `b8`: done, or the rest word by word
    have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk8 run_b8 (Env.wf_nil _) hpc7 (match_nil _) fun s8 hm8 hpc8 ↦ ?_
    have hb8 := after_eq run_b8 ▸ b8_keeps
    have hfr8 := hD.init.fr.of_regs (match_nil _) hm8 (Env.wf_nil _) rfl hb8.1 hb8.2
    have hd8 : s8.data.dmem = s7.data.dmem := hm8.dmem_eq (Env.wf_nil _) hb8.2
    have r8 : ∀ r ∈ [XReg.X8, .X9, .X20, .X21, .X24],
        s8.data.regs.getXReg r = s7.data.regs.getXReg r := fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact Match.reg_eq (r := .X8) (match_nil _) hm8 rfl rfl
      · exact Match.reg_eq (r := .X9) (match_nil _) hm8 rfl rfl
      · exact Match.reg_eq (r := .X20) (match_nil _) hm8 rfl rfl
      · exact Match.reg_eq (r := .X21) (match_nil _) hm8 rfl rfl
      · exact Match.reg_eq (r := .X24) (match_nil _) hm8 rfl rfl
    have hI8 : Init m0 (n4Of m0) s8.data :=
      ⟨hfr8, hd8 ▸ hD.init.out, hd8 ▸ hD.init.layer, (r8 .X20 (by simp)).trans hD.init.x20,
        by rw [show s8.data.regs.X21 = s7.data.regs.X21 from r8 .X21 (by simp)]
           exact hD.init.x21,
        by rw [show s8.data.regs.X24 = s7.data.regs.X24 from r8 .X24 (by simp)]
           exact hD.init.x24,
        hmu⟩
    simp only [PcOk] at hpc8
    sym_simp at hpc8
    simp only [bv_beq_toNat] at hpc8
    rw [show (Env.ofMachine s7.data []).regs .X10 = s7.data.regs.X10.toBitVec from rfl,
      show (Env.ofMachine s7.data []).regs .X8 = s7.data.regs.X8.toBitVec from rfl,
      show s7.data.regs.X10.toBitVec.toNat = muOf m0 from hD.x10,
      show s7.data.regs.X8.toBitVec.toNat = n4Of m0 from hD.x8] at hpc8
    by_cases heq : muOf m0 = n4Of m0
    · simp only [heq, decide_true, ↓reduceIte] at hpc8
      have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b11Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b11Offset) NativeRustcVmArm.Vm.SubspaceTable.label_10_at
      exact .done _ (.inl ⟨heq ▸ hI8, hpc8.trans hl⟩)
    · simp only [heq, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc8
      have := n4Of_le m0
      obtain ⟨d, pc⟩ := s8
      simp only at hpc8
      subst hpc8
      refine (words hp hS hI8 (by omega) ?_ ?_).mono fun s h ↦ .inl h
      · rw [show d.regs.X8 = s7.data.regs.X8 from r8 .X8 (by simp)]; exact hD.x8
      · rw [show d.regs.X9 = s7.data.regs.X9 from r8 .X9 (by simp)]; exact hD.x9
  · -- `b4`: word by word from `0`
    simp only [show 8 * muOf m0 - 8 < 24 by omega, decide_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at hpc5
    have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk4 run_b4 (Env.wf_nil _) hpc5 (match_nil _) fun s6 hm7 hpc6 ↦ ?_
    have hb4 := after_eq run_b4 ▸ b4_keeps
    have hfr6 := hfr5.of_regs (match_nil _) hm7 (Env.wf_nil _) rfl hb4.1 hb4.2
    have hd6 : s6.data.dmem = s5.data.dmem := hm7.dmem_eq (Env.wf_nil _) hb4.2
    have r6 : ∀ r ∈ [XReg.X9, .X20, .X21, .X24], s6.data.regs.getXReg r = s5.data.regs.getXReg r :=
      fun r hr ↦ by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Match.reg_eq (r := .X9) (match_nil _) hm7 rfl rfl
        · exact Match.reg_eq (r := .X20) (match_nil _) hm7 rfl rfl
        · exact Match.reg_eq (r := .X21) (match_nil _) hm7 rfl rfl
        · exact Match.reg_eq (r := .X24) (match_nil _) hm7 rfl rfl
    have hI6 : Init m0 0 s6.data :=
      ⟨hfr6, hd6 ▸ hI5.out, hd6 ▸ hI5.layer, (r6 .X20 (by simp)).trans hI5.x20,
        by rw [show s6.data.regs.X21 = s5.data.regs.X21 from r6 .X21 (by simp)]; exact hI5.x21,
        by rw [show s6.data.regs.X24 = s5.data.regs.X24 from r6 .X24 (by simp)]; exact hI5.x24,
        hmu⟩
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b9Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b9Offset) NativeRustcVmArm.Vm.SubspaceTable.label_8_at
    have hpc6' : s6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b9Offset) := hpc6.trans hl
    obtain ⟨d6, pc6⟩ := s6
    simp only at hpc6'
    subst hpc6'
    refine (words hp hS hI6 (by omega) ?_ ?_).mono fun s h ↦ .inl h
    · show (d6.regs.getXReg .X8).toBitVec.toNat = 0
      rw [hm7.regs .X8 _ rfl]; rfl
    · rw [show d6.regs.X9 = s5.data.regs.X9 from r6 .X9 (by simp), hx9]

end

end NativeRustcVmArm.Whir.SubspaceTable
