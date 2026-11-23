module

public import NativeRustcVmArm.Code.Vm.FinalLevel.Names
public import NativeRustcVmArm.Whir.WhirLevels.Next

/-!
# `whir_levels`: the tail call of `final_level`

`b4` (`.LWhirLevels_3`) passes the `TState`, the last level's index and address, `μ`,
`laneFolds`, the basis and the state, restores the registers and SP (`Fr.exit`) and jumps to
`final_level`, whose contract ends the function (`final_tail`): from the entry's SP, its stack is
inside the function's, its outputs the function's.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder
open NativeRustcVmArm.Vm.WhirLevels

public section

/-- The variables left at the last level fit its lanes. -/
theorem lanes_fit {μ k : Nat} (h16 : 16 ≤ μ) (h30 : μ ≤ 30) (hk : k + 1 = nOf μ) :
    2 ^ (μ - alphasAt (k + 1)) + foldAt k ≤ laneCap := by
  have h5 := mu_final h16 h30
  rw [← hk] at h5
  have : 2 ^ (μ - alphasAt (k + 1)) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) h5
  have : foldAt k ≤ 6 := by unfold foldAt; split_ifs <;> omega
  unfold laneCap
  omega

section
variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **The tail call of `final_level`** at the last level `k`. -/
theorem final_tail (hp : Placed code k0)
    (hfl : ∀ a s level ba b w rounds, Spec (Labels.label NativeRustcVmArm.Vm.FinalLevel.entryLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds))
    (c : Ctx a s0 levels ba b claim m0 rate) {k : Nat} {s : TState} {w : WhirStateW}
    {rs : Array FoldRoundW} {st : MachineState} (hf : WFr m0 st.data)
    (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b4Offset)) (hts : TStateAt st.data.dmem (tA m0) a s)
    (hwa : WhirAt st.data.dmem (pA m0) w rs) (hk : k + 1 = levels.length)
    (ha : w.alphas.size = alphasAt (k + 1))
    (hrun : runAll s0 levels b claim m0 =
      (finalLevelM k (lvl (logN m0) rate k) (logN m0 - w.alphas.size) (lf m0) b w rs).run s)
    (h19 : st.data.regs.getXReg .X19 = m0.regs.X6) (h20 : st.data.regs.getXReg .X20 = m0.regs.X3)
    (h21 : st.data.regs.getXReg .X21 = m0.regs.X0) (h22 : st.data.regs.getXReg .X22 = m0.regs.X2)
    (h23 : (st.data.regs.getXReg .X23).toBitVec = lvA m0 + BitVec.ofNat 64 (levelBytes * k))
    (h24 : (st.data.regs.getXReg .X24).toNat = k)
    (h5 : st.data.regs.X5.toNat = logN m0 - w.alphas.size) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  obtain ⟨hv, -, -, hv3⟩ := stack_val
  have hle : 0 + finalLevelStack ≤ whirLevelsStack := by omega
  have hwf := frame_wf c hf
  have hm := frame_match c hf
  have hl6 := c.len_le.2
  have hadm := admissible_iff.mp c.adm
  have hlog := c.logN_le
  have hlv := level_le (show k < levels.length by omega)
  refine exec_at (inf hp b4_in_code (by simp [b4])) run_b4 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hret, hsv⟩ := hf.exit hm1 hwf (by decide)
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have e0 : st1.data.regs.X0 = m0.regs.X0 := (reg_of hm1 (r := .X0) rfl rfl).trans h21
  have e1 : st1.data.regs.X1.toNat = k := by rw [← h24]; exact congrArg _ (reg_of hm1 (r := .X1) rfl rfl)
  have e2 : st1.data.regs.X2.toBitVec = lvA m0 + BitVec.ofNat 64 (levelBytes * k) := by
    rw [← h23]; exact congrArg _ (reg_of hm1 (r := .X2) rfl rfl)
  have e3 : st1.data.regs.X3.toNat = logN m0 - w.alphas.size := by
    rw [← h5]; exact congrArg _ (reg_of hm1 (r := .X3) rfl rfl)
  have e4 : st1.data.regs.X4 = m0.regs.X2 := (reg_of hm1 (r := .X4) rfl rfl).trans h22
  have e5 : st1.data.regs.X5 = m0.regs.X3 := (reg_of hm1 (r := .X5) rfl rfl).trans h20
  have e6 : st1.data.regs.X6 = m0.regs.X6 := (reg_of hm1 (r := .X6) rfl rfl).trans h19
  have ht : st1.data.regs.X0.toBitVec = tA m0 := by rw [e0]
  have hpp : st1.data.regs.X6.toBitVec = pA m0 := by rw [e6]
  have hb : st1.data.regs.X5.toBitVec = bA m0 := by rw [e5]
  have hf0 : Fr m0 0 whirLevelsStack [] [] (outs m0) st1.data :=
    ⟨by rw [hsv.2.1]; simp [base], fun _ h ↦ absurd h List.not_mem_nil,
      fun _ h ↦ absurd h List.not_mem_nil, by rw [hd]; exact hf.same, hsv.2.2⟩
  simp only [PcOk] at hpc1
  have hpre : FinalLevelPre a s (lvl (logN m0) rate k) ba b w rs st1.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, qAt_le _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht]; exact c.whirT hf0 (by omega) rfl hle
    · rw [ht, hd]; exact hts
    · rw [hpp, hd]; exact hwa
    · rw [e2, hd]; exact c.levelAt hf (by omega)
    · rw [hb, hd]; exact c.basis_at hf
    · rw [e3]; omega
    · rw [e3, ha]; exact lanes_fit hlog.1 hlog.2 (hk.trans c.len_eq)
    · rw [e3, ha]
      have : alphasAt (k + 1) ≤ 26 := by unfold alphasAt; split_ifs <;> omega
      unfold stackCap; omega
    · show rate + 3 * k < 64
      omega
    · rw [ht, hpp]; exact c.whirOut hf0 (by omega) rfl hle c.pout
    · rw [e2]; exact c.whirIn hf0 hle (whirIn_sub c.lin hlv)
    · rw [e2, hpp]; exact apart_sub c.lp c.lin.1.2 hlv
    · rw [e2, ht]; exact apart_sub c.lt c.lin.1.2 hlv
    · rw [hb, hpp]; exact c.basisIn hf0 hle c.bp
    · rw [hb, ht]; exact c.basisIn hf0 hle c.bt
    · rw [hb]; exact c.bap
  refine Eventually.bind (Spec.apply (hfl a s _ ba b w rs) hpc1 hpre) fun st2 ⟨hpc2, hq⟩ ↦
    .done _ ?_
  obtain ⟨h0, hnext, hch, hsv2⟩ := hq
  rw [e1, e3, e4] at h0 hnext
  rw [ht] at hnext
  rw [← hrun] at h0 hnext
  refine ⟨hpc2.trans hret, h0, hnext, ?_, hsv.trans hsv2⟩
  have hs1 : SameOutside m0.dmem st1.data.dmem
      (fun q ↦ InRange (base m0 whirLevelsStack) whirLevelsStack q ∨ outs m0 q) := by
    rw [hd]; exact hf.same
  refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hs1 hch) fun q hq ↦ ?_
  rcases hq with (hq | hq | hq) | (⟨r, hr, hq⟩ | hq)
  · exact Or.inr hq
  · exact Or.inl ⟨_, List.mem_cons_self, hq⟩
  · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inl ⟨_, List.mem_cons_self, by rw [hpp] at hq; exact hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [ht] at hq; exact hq⟩
  · right
    have hN := c.hN
    rw [show stackBelow st1.data finalLevelStack = base m0 (0 + finalLevelStack) from
      stackBelow_eq hf0.sp (by omega)] at hq
    exact frame_sub hN hle hq

end

end

end NativeRustcVmArm.Whir.WhirLevels
