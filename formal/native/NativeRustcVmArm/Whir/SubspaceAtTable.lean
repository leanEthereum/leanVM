module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmArm.Whir.SubspaceAtTable.Loop

/-!
# `subspace_at_table`

`b0` saves the callee-saved registers in its 336-byte frame and zeroes the `what` buffer's items
(`memset`); with no table entry (`b1`) it goes to the end, else `b2` starts the loop
(`SubspaceAtTable.step`, by `Sym.loop`). `b7` stores the count in the buffer's `len` and copies the
buffer to the output (`memcpy`), `b8` returns. The output holds `subspaceAtTable`.
-/

namespace NativeRustcVmArm.Whir.SubspaceAtTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceAtTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf)

public section

variable [Host] {k : Nat}

/-- **After the loop**: the count, the copy, the epilogue. -/
theorem finish (hp : Placed code k) (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 : MachineData} (hpre : SubspaceAtTablePre m0) {st : MachineData} (hD : Done m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ SubspaceAtTablePost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b7Offset)⟩ := by
  obtain ⟨hS, hn31, -, houtin, -⟩ := hpre
  have hn : nOf m0 ≤ 31 := hn31
  have hF : 336 ≤ subspaceAtTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hD.fr
  let fb := fbOf m0
  let out := m0.regs.X0.toBitVec
  have hwb : whatBytes = 256 := rfl
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env7 := Env.ofMachine st [(fb, 336)]
  have hwf7 : env7.WF := wf_one (hfr.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm7 : Match env7 exitS st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_then hk7 run_b7 hwf7 hm7 fun s1 hm1 hpc1 ↦ ?_
  have hb7 := after_eq run_b7 ▸ b7_keeps
  have hfr1 := hfr.of_block hm7 hm1 hwf7 rfl hb7.1 (r := 0) rfl (by decide) hb7.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 0) (n := 8) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq j hj ↦ by
      have := not_inRange_slot hS hF (o := 0) (n := 8) (by omega) (slots_le q hq) hj
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)
  have hsame1 := same_region_le hm1 hwf7 (r := 0) rfl (by decide) hb7.2
  -- the buffer in the frame: the count, the `What`s
  have hcount : NativeRustcVm.WordAt s1.data.dmem fb m0.regs.X2 := by
    have := Match.wordAt_write hm1 (r := 0) (o := 0) rfl (by decide) (v := .reg .X20) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    convert this using 1
    exact hD.x20.symm
  have hlist := subspaceAtTable_size (tbOf m0) m0.regs.X3
  rw [tbOf_size] at hlist
  have hwlen : ((subspaceAtTable (tbOf m0) m0.regs.X3).toList.flatMap
      NativeRustcVm.wordBytes).length = 8 * nOf m0 := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, hlist]
  have hwhat1 : NativeRustcVm.WordsAt s1.data.dmem (fb + BitVec.ofNat 64 8)
      (subspaceAtTable (tbOf m0) m0.regs.X3).toList := by
    refine NativeRustcVm.BytesAt.of_sameOutside_apart hD.what hsame1 ?_
      (NativeRustcVm.NoWrap.sub hfnw (by rw [hwlen]; omega)) (NativeRustcVm.NoWrap.sub hfnw
        (o := 0) (m := 8) (by omega) |> fun h ↦ by rwa [NativeRustcVm.addr_add_zero] at h)
    rw [hwlen]
    unfold NativeRustcVm.Apart NoWrap at *
    rw [toNat_add_ofNat' (by unfold fb fbOf; omega)]
    omega
  have hbuf : NativeRustcVm.WordsAt s1.data.dmem fb
      (m0.regs.X2 :: (subspaceAtTable (tbOf m0) m0.regs.X3).toList) :=
    NativeRustcVm.wordsAt_cons_iff.mpr ⟨hcount, hwhat1⟩
  -- `memcpy`
  have hx0 : s1.data.regs.X0.toBitVec = out := (hm1.regs .X0 _ rfl).trans rfl |>.trans
    (by show (st.regs.X19).toBitVec = _; rw [hD.x19])
  have hx1 : s1.data.regs.X1.toBitVec = fb := (hm1.regs .X1 _ rfl).trans (by simp [Sym.eval, env7])
  have hx2 : s1.data.regs.X2.toNat = 256 := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]
    rfl
  have hapo : NativeRustcVm.Apart out 256 fb 336 := apart_frame houtin.2 hF hS.2.1
  have hpre1 : MemcpyPre s1.data := by
    unfold MemcpyPre
    simp only [hx0, hx1, hx2]
    refine ⟨fun i hi ↦ hfr1.kept _ (houtin.1.1 i (by omega)),
      fun i hi ↦ hfr1.kept _ (hfmap i (by omega)), NativeRustcVm.NoWrap.mono houtin.1.2 (by omega),
      NativeRustcVm.NoWrap.mono hfnw (by omega), ?_⟩
    unfold NativeRustcVm.Apart at hapo
    unfold Apart
    omega
  refine call_then hpc1 hmemcpy hpre1 fun s2 hpc2 ⟨_, hcopy, hsame2, hsv2⟩ ↦ ?_
  simp only [hx0, hx1, hx2] at hcopy hsame2
  have hfr2 := hfr1.change hsame2 (fun p h ↦ .inl ⟨_, List.mem_singleton_self _, h⟩)
    (fun q hq j hj ↦ by
      rw [addr_add]
      have := slots_le q hq
      exact not_inRange_of_apart hapo.symm hfnw (NativeRustcVm.NoWrap.mono houtin.1.2 (by omega))
        (by omega))
    (fun r hr _ ↦ hsv2.1 r hr) hsv2.2.1 hsv2.2.2
  -- `b8`
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b8Offset) := hpc2
  let env8 := Env.ofMachine s2.data [(fb, 336)]
  have hwf8 : env8.WF := wf_one (hfr2.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm8 : Match env8 exitS s2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr2.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_at hk8 run_b8 hwf8 hpc2' hm8 fun s3 hm9 hpc3 ↦ .done _ ?_
  have hb8 := after_eq run_b8 ▸ b8_restores
  obtain ⟨hsaved, hx30⟩ := hfr2.ret hm9 hwf8 x30_mem hb8.1
  have hd3 : s3.data.dmem = s2.data.dmem := hm9.dmem_eq hwf8 hb8.2
  refine ⟨hpc3.trans (by simp only [retOf, hx30]), ?_, fun p hp ↦ ?_, hsaved⟩
  · -- the output
    have hlen8 : ((m0.regs.X2 :: (subspaceAtTable (tbOf m0) m0.regs.X3).toList).flatMap
        NativeRustcVm.wordBytes).length = 8 + 8 * nOf m0 := by
      rw [NativeRustcVm.length_wordsBytes, List.length_cons, Array.length_toList, hlist]; omega
    have hb := NativeRustcVm.BytesAt.take hcopy (8 + 8 * nOf m0)
    rw [bytesOf_take _ _ (by omega), ← hlen8, NativeRustcVmArm.bytesOf_eq hbuf] at hb
    have hw := NativeRustcVm.wordsAt_cons_iff.mp (show NativeRustcVm.WordsAt s3.data.dmem out _
      from hd3 ▸ hb)
    have hl2 : (subspaceAtTable (pairsOf m0.dmem m0.regs.X1.toBitVec m0.regs.X2.toNat).toArray
        m0.regs.X3).size = nOf m0 := hlist
    refine ⟨by rw [Array.length_toList, hl2]; exact hn, ?_, hw.2⟩
    rw [Array.length_toList, hl2, show (nOf m0).toUInt64 = m0.regs.X2 from
      UInt64.toNat.inj (natCast_toUInt64_toNat m0.regs.X2.toNat_lt)]
    exact hw.1
  · rw [hd3]; exact hfr2.same p hp

/-- **`subspace_at_table`'s contract.** -/
theorem subspaceAtTable_spec (hp : Placed code k)
    (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmemset : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (label NativeRustcVmArm.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost := by
  intro m0 hpre
  have hpre' := hpre
  obtain ⟨hS, hn31, htin, houtin, hap⟩ := hpre'
  have hn : nOf m0 ≤ 31 := hn31
  have hF : 336 ≤ subspaceAtTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  rw [show Labels.label NativeRustcVmArm.Vm.SubspaceAtTable.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b0Offset) from hp.label NativeRustcVmArm.Vm.SubspaceAtTable.entry_at]
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let fb := fbOf m0
  let env0 := Env.ofMachine m0 [(fb, 336)]
  have hwf0 : env0.WF := wf_one hfmap hfnw
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_then hk0 run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  have hb0 := after_eq run_b0 ▸ b0_frame
  have hfr1 : Frame m0 336 subspaceAtTableStack slots (outsOf m0) s1.data :=
    Frame.of_entry hS hF hwf0 hm1 rfl hb0.1 hb0.2.2 hb0.2.1
  -- `memset` of the items
  have hx0 : s1.data.regs.X0.toBitVec = fb + BitVec.ofNat 64 8 := (hm1.regs .X0 _ rfl).trans rfl
  have hx2 : s1.data.regs.X2.toNat = 248 := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]
    rfl
  have hpre1 : MemsetPre s1.data := by
    unfold MemsetPre
    rw [hx0, hx2]
    exact (hfr1.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega)))
  refine call_then hpc1 hmemset hpre1 fun s2 hpc2 ⟨_, _, hsame2, hsv2⟩ ↦ ?_
  rw [hx0, hx2] at hsame2
  have hfr2 := hfr1.change hsame2 (fun p h ↦ .inr (inRange_frame_sub hS hF (by omega) h))
    (fun q hq j hj ↦ not_inRange_slot hS hF (by omega) (slots_le q hq) hj
      (.inl (by have := slots_ge q hq; omega)))
    (fun r hr _ ↦ hsv2.1 r hr) hsv2.2.1 hsv2.2.2
  have e19 : s2.data.regs.X19 = m0.regs.X0 :=
    (hsv2.1 .X19 rfl).trans (UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl))
  have e20 : s2.data.regs.X20 = m0.regs.X2 :=
    (hsv2.1 .X20 rfl).trans (UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl))
  have e21 : s2.data.regs.X21.toBitVec = fb + BitVec.ofNat 64 8 :=
    (congrArg UInt64.toBitVec (hsv2.1 .X21 rfl)).trans ((hm1.regs .X21 _ rfl).trans rfl)
  have e22 : s2.data.regs.X22 = m0.regs.X3 :=
    (hsv2.1 .X22 rfl).trans (UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl))
  have e23 : s2.data.regs.X23 = m0.regs.X1 :=
    (hsv2.1 .X23 rfl).trans (UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl))
  -- `b1`: the count
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b1Offset) := hpc2
  refine exec_at hk1 run_b1 (Env.wf_nil _) hpc2' (match_nil _) fun s3 hm3 hpc3 ↦ ?_
  have hb1 := after_eq run_b1 ▸ b1_keeps
  have hfr3 := hfr2.of_regs (match_nil _) hm3 (Env.wf_nil _) rfl hb1.1 hb1.2
  have x19 : s3.data.regs.X19 = m0.regs.X0 := (Match.reg_eq (r := .X19) (match_nil _) hm3 rfl rfl).trans e19
  have x20 : s3.data.regs.X20 = m0.regs.X2 := (Match.reg_eq (r := .X20) (match_nil _) hm3 rfl rfl).trans e20
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs] at hpc3
  have hl3 : Labels.label NativeRustcVmArm.Vm.SubspaceAtTable.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b7Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceAtTable.b7Offset) NativeRustcVmArm.Vm.SubspaceAtTable.label_3_at
  have h20 : (s2.data.regs.getXReg .X20).toBitVec.toNat = nOf m0 := by
    show s2.data.regs.X20.toNat = _
    rw [e20]; rfl
  by_cases hn0 : nOf m0 = 0
  · have hz : ((s2.data.regs.getXReg .X20).toBitVec == BitVec.ofNat 64 0) = true := by
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [h20, hn0]
      rfl
    simp only [hz, ↓reduceIte, hl3] at hpc3
    obtain ⟨d3, pc3⟩ := s3
    simp only at hpc3
    subst hpc3
    refine finish hp hmemcpy hpre ⟨hfr3, x19, x20, ?_⟩
    rw [show subspaceAtTable (tbOf m0) m0.regs.X3 = #[] from
      Array.eq_empty_of_size_eq_zero (by rw [subspaceAtTable_size, tbOf_size, hn0])]
    exact NativeRustcVm.wordsAt_nil _ _
  · have hz : ((s2.data.regs.getXReg .X20).toBitVec == BitVec.ofNat 64 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      apply hn0
      rw [← h20, h]
      rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hpc3
    have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
    have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b2Offset) := hpc3
    refine exec_at hk2 run_b2 (Env.wf_nil _) hpc3' (match_nil _) fun s4 hm4 hpc4 ↦ ?_
    have hb2 := after_eq run_b2 ▸ b2_keeps
    have hfr4 := hfr3.of_regs (match_nil _) hm4 (Env.wf_nil _) rfl hb2.1 hb2.2
    have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b3Offset) := hpc4
    have hI0 : Inv m0 0 s4.data := by
      refine ⟨hfr4, (Match.reg_eq (r := .X19) (match_nil _) hm4 rfl rfl).trans x19,
        (Match.reg_eq (r := .X20) (match_nil _) hm4 rfl rfl).trans x20, ?_, ?_, ?_, ?_, ?_⟩
      · show (s4.data.regs.getXReg .X21).toBitVec = _
        rw [Match.reg_eq (r := .X21) (match_nil _) hm4 rfl rfl,
          Match.reg_eq (r := .X21) (match_nil _) hm3 rfl rfl]
        exact e21
      · show s4.data.regs.getXReg .X22 = _
        rw [Match.reg_eq (r := .X22) (match_nil _) hm4 rfl rfl,
          Match.reg_eq (r := .X22) (match_nil _) hm3 rfl rfl, atAfter_zero]
        exact e22
      · refine (hm4.regs .X25 _ rfl).trans ?_
        sym_simp
        rw [Env.ofMachine_regs, Match.reg_eq (r := .X23) (match_nil _) hm3 rfl rfl]
        show s2.data.regs.X23.toBitVec + _ = _
        rw [e23]
      · show (s4.data.regs.getXReg .X26).toBitVec.toNat = _
        rw [hm4.regs .X26 _ rfl]
        show (s3.data.regs.getXReg .X20).toBitVec.toNat = _
        rw [Match.reg_eq (r := .X20) (match_nil _) hm3 rfl rfl, h20]
        rfl
      · rw [atAfter_zero]
        exact NativeRustcVm.wordsAt_nil _ _
    have hloop := Sym.loop (tr := step1 Host.exe)
      (Q := fun s ↦ Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b7Offset))
      (fun n s ↦ ∃ i, n = nOf m0 - i ∧ i < nOf m0 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b3Offset) ∧
        Inv m0 i s.data)
      (fun n s ⟨i, hn', hi, hpc, hI⟩ ↦ by
        obtain ⟨d, pc⟩ := s
        simp only at hpc
        subst hpc
        refine (step hp hkmul hpre hi hI).mono fun s' h ↦ ?_
        rcases h with h | ⟨hI', hpc', hlt⟩
        · exact .inl h
        · exact .inr ⟨nOf m0 - (i + 1), by omega, i + 1, rfl, hlt, hpc', hI'⟩)
      (n := nOf m0) ⟨0, by omega, by omega, hpc4', hI0⟩
    refine hloop.bind fun s ⟨hD, hpc⟩ ↦ ?_
    obtain ⟨d, pc⟩ := s
    simp only at hpc
    subst hpc
    exact finish hp hmemcpy hpre hD

end

end NativeRustcVmArm.Whir.SubspaceAtTable
