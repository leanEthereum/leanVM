module

public import NativeRustcVmArm.Code.Vm.InducedWeight.Names
public import NativeRustcVmArm.Whir.InducedWeight.Entry

/-!
# `induced_weight` from `b3` to the queries' loop, and the store

From `b3` (`AtB3`): `b3` spills the queries' count (the smaller of the queries' and the weights')
and the table's count; with no query `b14` zeroes the sum (`Done`), else `b4` spills the cursors
and the table's slice and enters the queries' loop (`OInv m0 0`). After the loop (`finish`): `b15`
stores the sum, `b16` the tag `1` and returns.
-/

namespace NativeRustcVmArm.Whir.InducedWeight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf WordAt WordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

public section

variable [Host] {k : Nat}

/-- **After the loop**: `Some` of the sum, the epilogue. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : InducedWeightPre m0)
    (hmu : muOf m0 ≤ stackCap) {st : MachineData} (hD : Done m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ InducedWeightPost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b15Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := out_env hpre hD.fr hD.out
  have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk15 run_b15 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b16Offset) := hpc1
  refine exec_at hk16 run_b16 hwf hpc1' hm1 fun s2 hm2 hpc2 ↦ .done _ ?_
  have hb16 := after_eq run_b16 ▸ b16_restores
  obtain ⟨hsaved, hx30⟩ := hD.fr.ret hm2 hwf x30_mem hb16.1
  have hb1 : (Env.ofMachine st [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)]).regions[1]? =
      some (m0.regs.X0.toBitVec, 24) := rfl
  refine ⟨hpc2.trans (by simp only [retOf, hx30]), ?_, out_same hpre hD.fr hwf hm2 hb16.2, hsaved⟩
  show OptEWAt _ _ (if m0.regs.X1.toNat ≤ stackCap then _ else _)
  simp only [show m0.regs.X1.toNat ≤ stackCap from hmu, ↓reduceIte]
  show OptEWAt _ _ (some (inducedWeight (muOf m0) (qsOf m0) (wsOf m0) (ptOf m0)))
  rw [← totOf_cnt]
  refine ⟨?_, ?_⟩
  · have := Match.wordAt_write hm2 hb1 (o := 0) (by decide) (v := .lit 1) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  · rw [NativeRustcVm.ewAt_iff]
    refine ⟨?_, ?_⟩
    · have := Match.wordAt_write hm2 hb1 (o := 8) (by decide) (v := .reg .X19) (by decide)
      rw [show UInt64.ofBitVec ((Sym.reg .X19).eval
          (Env.ofMachine st [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)])) = st.regs.X19 from rfl,
        hD.x19] at this
      exact this
    · have := Match.wordAt_write hm2 hb1 (o := 16) (by decide) (v := .reg .X29) (by decide)
      rw [show UInt64.ofBitVec ((Sym.reg .X29).eval
          (Env.ofMachine st [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)])) = st.regs.X29 from rfl,
        hD.x29] at this
      rwa [off, addr_add]

/-- **From `b3`**: the queries' loop, or the sum `0` and `finish` with no query. -/
theorem start (hp : Placed code k) {m0 : MachineData} (hpre : InducedWeightPre m0)
    {st : MachineData} (hA : AtB3 m0 st)
    (hloop : ∀ st', OInv m0 0 st' → Eventually (step1 Host.exe)
      (fun s ↦ s.pc = retOf m0 ∧ InducedWeightPost m0 s.data) ⟨st', Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b6Offset)⟩) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ InducedWeightPost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b3Offset)⟩ := by
  have hS := hpre.1
  have hc64 : cntOf m0 < 2 ^ 64 := by unfold cntOf; have := m0.regs.X5.toNat_lt; omega
  have hcn : (cntOf m0).toUInt64.toBitVec.toNat = cntOf m0 := natCast_toUInt64_toNat hc64
  have hts := hA.tlen
  have hsz : (tbOf m0).size.toUInt64.toBitVec.toNat = (tbOf m0).size :=
    natCast_toUInt64_toNat (by omega)
  -- `b3`: the counts
  obtain ⟨hwf6, hm6⟩ := fr_env hS hA.fr
  let env6 := Env.ofMachine st [(fbOf m0, 1200)]
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk3 run_b3 hwf6 hm6 fun s6 hm6' hpc6 ↦ ?_
  have hb3 := after_eq run_b3 ▸ b3_keeps
  have hfr6 := fr_block hS hA.fr hm6 hm6' hwf6 hb3.1 hb3.2
  have h24 : (st.regs.getXReg .X24).toBitVec = m0.regs.X3.toBitVec := by
    rw [show st.regs.getXReg .X24 = st.regs.X24 from rfl, hA.x24]
  have h23 : (st.regs.getXReg .X23).toBitVec = m0.regs.X5.toBitVec := by
    rw [show st.regs.getXReg .X23 = st.regs.X23 from rfl, hA.x23]
  have hcnt : (Sym.eval env6 (Sym.ite (SBool.cmp .ult .W64 (.reg .X24) (.reg .X23)) (.reg .X24)
      (.reg .X23))).toNat = cntOf m0 := by
    sym_simp
    simp only [env6, Env.ofMachine_regs, h24, h23]
    rw [ite_min]
    exact Nat.min_comm _ _
  have w56 : WordAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 56) (cntOf m0).toUInt64 := by
    have := Match.wordAt_write hm6' (r := 0) rfl (o := 56) (by decide)
      (v := Sym.ite (SBool.cmp .ult .W64 (.reg .X24) (.reg .X23)) (.reg .X24) (.reg .X23))
      (by decide)
    rwa [show UInt64.ofBitVec (Sym.eval env6 (Sym.ite (SBool.cmp .ult .W64 (.reg .X24)
        (.reg .X23)) (.reg .X24) (.reg .X23))) = (cntOf m0).toUInt64 from
      UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (hcnt.trans hcn.symm))] at this
  have w88 : WordAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 88) (tbOf m0).size.toUInt64 := by
    have := Match.wordAt_write hm6' (r := 0) rfl (o := 88) (by decide) (v := .reg .X21)
      (by decide)
    rwa [show UInt64.ofBitVec ((Sym.reg .X21).eval env6) = st.regs.X21 from rfl, hA.x21] at this
  have hk6a := blk_keep hm6' hwf6 (lo := 96) (hi := 1200) (by omega) le_rfl (by decide)
  have hk6b := blk_keep hm6' hwf6 (lo := 64) (hi := 88) (by omega) (by omega) (by decide)
  have hk6c := blk_keep hm6' hwf6 (lo := 16) (hi := 56) (by omega) (by omega) (by decide)
  have r6 : ∀ r ∈ [XReg.X21, .X25, .X26], s6.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm6 hm6' rfl rfl
  have w16 : WordAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 16) m0.regs.X0 :=
    word_keep hA.out (lo := 16) (hi := 56) le_rfl (by omega) hk6c
  have hc : (SBool.cmp .eq .W64 (Sym.ite (SBool.cmp .ult .W64 (.reg .X24) (.reg .X23)) (.reg .X24)
      (.reg .X23)) (.lit 0)).eval env6 = decide (cntOf m0 = 0) := by
    show (_ == _) = _
    rw [bv_beq_toNat]
    simp only [Sym.low_W64]
    rw [hcnt]
    simp [Sym.eval]
  simp only [PcOk] at hpc6
  rw [hc] at hpc6
  by_cases hc0 : cntOf m0 = 0
  · -- no query: the sum `0`
    simp only [hc0, decide_true, ↓reduceIte] at hpc6
    rw [show Labels.label NativeRustcVmArm.Vm.InducedWeight.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b14Offset) from hp.label (j := NativeRustcVmArm.Vm.InducedWeight.b14Offset) NativeRustcVmArm.Vm.InducedWeight.label_7_at] at hpc6
    have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b14Offset) := b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk14 run_b14 (Env.wf_nil _) hpc6 (match_nil _) fun s7 hm7 hpc7 ↦ ?_
    have hb14 := after_eq run_b14 ▸ b14_keeps
    have hfr7 := hfr6.of_regs (match_nil _) hm7 (Env.wf_nil _) rfl hb14.1 hb14.2
    have hd7 : s7.data.dmem = s6.data.dmem := hm7.dmem_eq (Env.wf_nil _) hb14.2
    have ht0 : totOf m0 (cntOf m0) = 0 := by rw [hc0]; exact indTot_zero _ _ _ _
    have hpc7' : s7.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b15Offset) := hpc7
    obtain ⟨d7, pc7⟩ := s7
    simp only at hpc7'
    subst hpc7'
    refine finish hp hpre hA.mu ⟨hfr7, hd7 ▸ w16, ?_, ?_⟩
    · rw [ht0]; exact UInt64.toBitVec_inj.mp (hm7.regs .X19 _ rfl)
    · rw [ht0]; exact UInt64.toBitVec_inj.mp (hm7.regs .X29 _ rfl)
  simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc6
  -- `b4`: the cursors and the table's slice
  obtain ⟨hwf7, hm7⟩ := fr_env hS hfr6
  let env7 := Env.ofMachine s6.data [(fbOf m0, 1200)]
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc6' : s6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b4Offset) := hpc6
  refine exec_at hk4 run_b4 hwf7 hpc6' hm7 fun s7 hm7' hpc7 ↦ ?_
  have hb4 := after_eq run_b4 ▸ b4_keeps
  have hfr7 := fr_block hS hfr6 hm7 hm7' hwf7 hb4.1 hb4.2
  have hk7a := blk_keep hm7' hwf7 (lo := 56) (hi := 1200) (by omega) le_rfl (by decide)
  have hk7b := blk_keep hm7' hwf7 (lo := 16) (hi := 24) (by omega) (by omega) (by decide)
  have h21 : (s6.data.regs.getXReg .X21).toBitVec = (tbOf m0).size.toUInt64.toBitVec := by
    rw [r6 .X21 (by simp)]
    exact congrArg UInt64.toBitVec hA.x21
  have hlt32 : ((tbOf m0).size.toUInt64.toBitVec.ult 32#64) = true := by
    rw [bv_ult_toNat, hsz]
    simp
    omega
  have v24 : UInt64.ofBitVec ((Sym.bin .add .W64 (.reg .X25) (.lit 8)).eval env7) =
      m0.regs.X6 + 8 := by
    apply UInt64.toBitVec_inj.mp
    sym_simp
    simp only [env7, Env.ofMachine_regs]
    rw [r6 .X25 (by simp), show st.regs.getXReg .X25 = st.regs.X25 from rfl, hA.x25]
    rfl
  have v40 : UInt64.ofBitVec ((Sym.ite (SBool.cmp .ult .W64 (.reg .X21) (.lit 32)) (.reg .X21)
      (.lit 0)).eval env7) = (tbOf m0).size.toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    sym_simp
    simp only [env7, Env.ofMachine_regs, h21, hlt32, ↓reduceIte]
  have v48 : UInt64.ofBitVec ((Sym.ite (SBool.cmp .ult .W64 (.reg .X21) (.lit 32)) (.reg .X26)
      (.lit 8)).eval env7) = UInt64.ofBitVec (fbOf m0 + BitVec.ofNat 64 96) := by
    apply UInt64.toBitVec_inj.mp
    sym_simp
    simp only [env7, Env.ofMachine_regs, h21, hlt32, ↓reduceIte]
    rw [r6 .X26 (by simp)]
    exact hA.x26
  have w24 := Match.wordAt_write hm7' (r := 0) rfl (o := 24) (by decide)
    (v := .bin .add .W64 (.reg .X25) (.lit 8)) (by decide)
  have w32 := Match.wordAt_write hm7' (r := 0) rfl (o := 32) (by decide) (v := .ptr 0 600)
    (by decide)
  have w40 := Match.wordAt_write hm7' (r := 0) rfl (o := 40) (by decide)
    (v := Sym.ite (SBool.cmp .ult .W64 (.reg .X21) (.lit 32)) (.reg .X21) (.lit 0)) (by decide)
  have w48 := Match.wordAt_write hm7' (r := 0) rfl (o := 48) (by decide)
    (v := Sym.ite (SBool.cmp .ult .W64 (.reg .X21) (.lit 32)) (.reg .X26) (.lit 8)) (by decide)
  rw [v24] at w24
  rw [v40] at w40
  rw [v48] at w48
  have hargs : WordsAt s7.data.dmem (fbOf m0 + BitVec.ofNat 64 64)
      [m0.regs.X2, m0.regs.X4, m0.regs.X7] := by
    refine bytes_keep (bytes_keep hA.args (lo := 64) (hi := 88) le_rfl
      (by simp [NativeRustcVm.length_wordBytes]) hk6b)
      (lo := 56) (hi := 1200) (by omega) (by simp [NativeRustcVm.length_wordBytes]) hk7a
  have hpairs : PairsAt s7.data.dmem (fbOf m0 + BitVec.ofNat 64 96) (tbOf m0).toList := by
    have hl : 96 + ((pairWords (tbOf m0).toList).flatMap NativeRustcVm.wordBytes).length ≤ 1200 := by
      rw [pairs_len, Array.length_toList]; omega
    have hp0 := hA.pairs
    unfold PairsAt NativeRustcVm.WordsAt at hp0 ⊢
    exact bytes_keep (bytes_keep hp0 (lo := 96) (hi := 1200) le_rfl hl hk6a)
      (lo := 56) (hi := 1200) (by omega) hl hk7a
  simp only [PcOk] at hpc7
  rw [show Labels.label NativeRustcVmArm.Vm.InducedWeight.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b6Offset) from hp.label (j := NativeRustcVmArm.Vm.InducedWeight.b6Offset) NativeRustcVmArm.Vm.InducedWeight.label_4_at] at hpc7
  obtain ⟨d7, pc7⟩ := s7
  simp only at hpc7
  subst hpc7
  refine hloop d7 ⟨hfr7, ⟨word_keep w16 (lo := 16) (hi := 24) le_rfl (by omega) hk7b,
    words4 w24 w32 w40 w48, word_keep w56 (lo := 56) (hi := 1200) le_rfl (by omega) hk7a, hargs,
    ⟨by rw [Array.length_toList]; exact hts, ?_, ?_⟩⟩, ?_, ?_, ?_, by omega⟩
  · rw [Array.length_toList]
    exact word_keep w88 (lo := 56) (hi := 1200) (by omega) (by omega) hk7a
  · unfold PairsAt
    rw [off, addr_add]
    exact hpairs
  · show (d7.regs.getXReg .X22).toBitVec.toNat = 0
    rw [hm7'.regs .X22 _ rfl]
    rfl
  · show d7.regs.getXReg .X19 = (totOf m0 0).c0
    rw [show totOf m0 0 = 0 from indTot_zero _ _ _ _]
    exact UInt64.toBitVec_inj.mp (hm7'.regs .X19 _ rfl)
  · show d7.regs.getXReg .X29 = (totOf m0 0).c1
    rw [show totOf m0 0 = 0 from indTot_zero _ _ _ _]
    exact UInt64.toBitVec_inj.mp (hm7'.regs .X29 _ rfl)

end

end NativeRustcVmArm.Whir.InducedWeight
