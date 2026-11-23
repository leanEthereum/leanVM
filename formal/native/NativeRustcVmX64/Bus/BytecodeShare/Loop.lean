module

public import NativeRustcVmX64.Bus.BytecodeShare.Copy

/-!
# `bytecode_share`: the copy's loop (x86-64)

`b12` sets the result's length (RAX) and the point's last slots (RCX) and skips an empty
`bytecode_low`; `b13` sends a single element to the odd one (`b14`, `NativeRustcVmX64.Vm.BytecodeShare.label_10`), more to
the pair loop (`b17`). The pair loop's head `NativeRustcVmX64.Vm.BytecodeShare.label_13` (`PH`): `b18` copies two
elements; at the even end `b19` goes to `b21`, else to the odd element (`b20`).
`copy_spec`: from `b12` to the return.
-/

namespace NativeRustcVmX64.Bus.BytecodeShare

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BytecodeShare NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Bus (busPointCap)

public section

variable [Host] {a : DecArea} {s0 s3 : TState} {m0 m : MachineData} {k : Nat} {v0 : BitVec 64}

/-- **A turn of the pair loop.** -/
theorem pair (hp : Placed code k) (h : BytecodeSharePre a s0 m0) (F : Fin' a s0 m0 m v0 k)
    {j : Nat} {st : MachineData} (hd : PH m0 m v0 j st) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s0 m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b18Offset) ∧ PH m0 m v0 (j + 2) st'.data))
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b18Offset)⟩ := by
  have c := ctx_of h
  have hlen := nB_le h
  have hnBe : nB m0 = (reg m0 .r8).toNat := rfl
  obtain ⟨hbm, hbnw, hbs⟩ := bOk h
  have hpo := pOk h
  have hc := hd.cp
  have hlt := hd.lt
  have hev := hd.even
  obtain ⟨hmB, hnB, hB⟩ := sub_ok (d := st.dmem) (o := 16 * j) (l := 32)
    (Mapped.keeps hbm hc.fr.frame.kept) hbnw (by omega) (by omega)
  obtain ⟨hmP, hnP, hP⟩ := sub_ok (d := st.dmem) (o := 16 * j) (l := 32)
    (Mapped.keeps hpo.1 hc.fr.frame.kept) hpo.2.1
    (by unfold ptBytes sharePointSlots busPointCap; omega) (by omega)
  let env := frameEnv m0 st 432 [(off (bAt m0) (16 * j), 32), (off (pAt m0) (16 * j), 32)]
    (fun _ ↦ 0) 0
  have hwf : env.WF :=
    frame_wf ⟨c.mapped_frame hc.fr.frame.kept, c.noWrap_frame⟩
      (rest2_ok (x := (off (bAt m0) (16 * j), 32)) (y := (off (pAt m0) (16 * j), 32))
        ⟨hmB, hnB⟩ ⟨hmP, hnP⟩ (fun _ h ↦ h))
      (pairwise3 (Apart.symm' (apart_sub (apart_frame hbs c.spN N_ge) hbnw (by omega) (by omega)))
        (Apart.symm' (apart_sub (apart_frame hpo.2.2.2.2.1 c.spN N_ge) hpo.2.1
          (by unfold ptBytes sharePointSlots busPointCap; omega) (by omega)))
        (apart_sub2 (Apart.symm' (pre_parts h).2.2.2.2.2.2.2.2.2.2.1) hbnw hpo.2.1 (by omega)
          (by omega) (by unfold ptBytes sharePointSlots busPointCap; omega) (by omega)))
  have h24 : ∀ x : BitVec 64, x + BitVec.ofNat 64 (16 * j + 24) =
      off x (16 * j) + BitVec.ofInt 64 24 := fun x ↦ by
    rw [show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, off_add]
  have hm : Match env pairS st :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hc.fr.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st .r13) (reg st .rdi) = _
        rw [add64, hc.fr.r13, hd.rdi, h24]
        rfl,
       by
        show BinOp.apply .add .W64 (reg st .r12) (reg st .rdi) = _
        rw [add64, hc.fr.r12, hd.rdi, h24]
        rfl, trivial⟩
  refine exec_then (infix_of b18_in_code (by simp [b18]) hp) exit_b18 hwf nofun hm
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid, hk, hrdx, hrdi, hcpw, hws⟩ := ok_b18
  have hs : NativeRustcVm.SameOutside st.dmem st2.data.dmem
      (NativeRustcVm.InRange (off (pAt m0) (16 * j)) 32) := fun q hq ↦
    hm2.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq (by
      obtain ⟨hr, hle⟩ := hws w hw
      rw [hr] at hb; cases hb
      rw [inRange_iff' hnP]; omega)
  have hcpy := copied_words hm2 (rd := 2) (rr := 1) (od := 0) (os := 0) (nw := 4) rfl rfl
    (by omega) (by rw [off_zero]; exact hmB) hcpw
  have hbk := b_kept h (fun _ h ↦ h) hc.fr
  have hc2 : Cp m0 m v0 (j + 2) st2.data := by
    refine ⟨⟨Frame.of_block hc.fr.frame hwf hm2 hmid slots_le,
        NativeRustcVm.SameOutside.mono (hc.fr.same.trans hs) fun q hq ↦ by
          rcases hq with hq | hq
          · exact hq
          · exact .inl (.inr (pt_sub h (by unfold ptBytes sharePointSlots busPointCap; omega) hq)),
        (hm2.regs .rbx _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.rbx,
        (hm2.regs .rbp _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.rbp,
        (hm2.regs .r12 _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.r12,
        (hm2.regs .r13 _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.r13,
        (hm2.regs .r14 _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.r14⟩,
      (hm2.regs .r15 _ (KeepsB.reg hk (by simp [six]))).trans hc.r15,
      (hm2.regs .rax _ (KeepsB.reg hk (by simp [six]))).trans hc.rax,
      (hm2.regs .rcx _ (KeepsB.reg hk (by simp [six]))).trans hc.rcx, by omega, fun i hi ↦ ?_,
      fun q hq ↦ ?_, kept_trans hc.kept (hm2.kept hwf)⟩
    · rcases Nat.lt_or_ge i (16 * j) with hi' | hi'
      · rw [hs _ (not_inRange_off hpo.2.1 (by unfold ptBytes sharePointSlots busPointCap; omega)
          hi'), hc.cpy i hi']
      · have e := hcpy (i - 16 * j) (by omega)
        simp only [Nat.zero_add, off_off] at e
        rw [show 16 * j + (i - 16 * j) = i by omega] at e
        rw [show pAt m0 + BitVec.ofNat 64 i = off (pAt m0) i from rfl, e]
        exact hbk i (by omega)
    · have h1 : ¬ NativeRustcVm.InRange (off (pAt m0) (16 * j)) 32 q := fun h' ↦
        hq (by
          rw [show 16 * (j + 2) = 16 * j + 32 by omega]
          exact inRange_join hpo.2.1 (by unfold ptBytes sharePointSlots busPointCap; omega) (.inr h'))
      have h2 : ¬ NativeRustcVm.InRange (pAt m0) (16 * j) q := fun h' ↦
        hq (inRange_mono h' (by omega))
      rw [hs q h1]
      exact hc.same q h2
  have e2dx : reg st2.data .rdx = BitVec.ofNat 64 (j + 2) := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hrdx]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 2) (reg st .rdx) = _
    rw [add64, hd.rdx, ← BitVec.ofNat_add, Nat.add_comm]
  have e2di : reg st2.data .rdi = BitVec.ofNat 64 (16 * (j + 2) + 24) := by
    rw [show reg st2.data .rdi = _ from hm2.regs .rdi _ hrdi]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 32) (reg st .rdi) = _
    rw [add64, hd.rdi, ← BitVec.ofNat_add]
    congr 1
    omega
  have e2si : reg st2.data .rsi = reg st .rsi := hm2.regs .rsi _ (KeepsB.reg hk (by simp [six]))
  have hc18 : c18.eval env = !decide (j + 2 = nB m0 - nB m0 % 2) := by
    show (!(CmpOp.apply .eq .W64 (reg st .rsi)
      (BinOp.apply .add .W64 (BitVec.ofNat 64 2) (reg st .rdx)))) = _
    rw [eq64, add64, hd.rdx, ← BitVec.ofNat_add]
    congr 1
    rw [decide_eq_decide]
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rw [hd.rsi, BitVec.toNat_ofNat] at this
      omega
    · intro e
      apply BitVec.eq_of_toNat_eq
      rw [hd.rsi, BitVec.toNat_ofNat]
      omega
  simp only [PcOk, hc18] at hpc2
  by_cases hlast : j + 2 = nB m0 - nB m0 % 2
  · -- out of the loop: `b19`.
    rw [decide_eq_true hlast] at hpc2
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    refine Eventually.mono (exec_at (infix_of b19_in_code (by simp [b19]) hp) exit_b19
      (wf_envB h hc2.fr.frame.kept 0) nofun (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.BytecodeShare.b18_next))
      (match_bodyS hc2.fr 0) fun st3 hm3 hpc3 ↦ ?_) fun _ h ↦ Or.inl h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hmid3, hmem3, hk3⟩ := ok_moves
    have hc3 := Cp.ofRun h hc2 hm3 hmid3 hmem3 (KeepsB.mono hk3 (by simp [six]))
    have hc19 : c19.eval (envB m0 st2.data 0) = decide (nB m0 % 2 = 0) := by
      show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st2.data .rbp) (BitVec.ofNat 64 1))
        (BitVec.ofNat 64 0) = _
      rw [and1_eq _ (by rw [hc2.fr.rbp]; omega), hc2.fr.rbp]
    simp only [PcOk, hc19] at hpc3
    by_cases hev' : nB m0 % 2 = 0
    · rw [decide_eq_true hev'] at hpc3
      simp only [↓reduceIte] at hpc3
      rw [hp.label NativeRustcVmX64.Vm.BytecodeShare.label_11_at] at hpc3
      obtain ⟨d3, pc3⟩ := st3
      simp only at hpc3
      subst hpc3
      exact F _ (by rw [show nB m0 = j + 2 by omega]; exact hc3)
    · rw [decide_eq_false hev'] at hpc3
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
      rw [NativeRustcVmX64.Vm.BytecodeShare.b19_length] at hpc3
      obtain ⟨d3, pc3⟩ := st3
      simp only at hpc3
      subst hpc3
      exact odd hp h F hc3 ((hm3.regs .rdx _ (KeepsB.reg hk3 (by simp [six]))).trans e2dx)
        (by omega)
  · rw [decide_eq_false hlast] at hpc2
    simp only [Bool.not_false, ↓reduceIte] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.BytecodeShare.label_13_at] at hpc2
    refine .done _ (.inr ⟨hpc2, hc2, by omega, by omega, by rw [e2si]; exact hd.rsi, e2dx, e2di⟩)

/-- **The copy**, from `b12`: every element of `bytecode_low`, then `b21`. -/
theorem copy_spec (hp : Placed code k) (h : BytecodeSharePre a s0 m0)
    (hf : BF m0 (OT m0) 8 m) (h15 : reg m .r15 = v0) (F : Fin' a s0 m0 m v0 k) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b12Offset)⟩ := by
  have hlen := nB_le h
  have hnBe : nB m0 = (reg m0 .r8).toNat := rfl
  have hwf := wf_envB h hf.frame.kept 0
  refine exec_then (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun
    (match_bodyS hf 0) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hk, hrax, hrcx⟩ := ok_b12
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq hwf hmem
  have hc1 : Cp m0 m v0 0 st1.data := by
    refine ⟨(BF.block h hf hm1 hmid (KeepsB.mono hk (by simp [six]))).1.mono OT_OP,
      (hm1.regs .r15 _ (KeepsB.reg hk (by simp [six]))).trans h15, ?_, ?_, Nat.zero_le _,
      fun i hi ↦ absurd hi (by omega), fun q _ ↦ by rw [hd1], by rw [hd1]; exact fun _ h ↦ h⟩
    · rw [show reg st1.data .rax = _ from hm1.regs .rax _ hrax]
      show BinOp.apply .add .W64 (reg m .rbp) (BitVec.ofNat 64 4) = _
      rw [add64, hf.rbp]
    · rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hrcx]
      show BinOp.apply .add .W64 (reg m .r12) (BinOp.apply .shl .W64 (reg m .rbp)
        (BitVec.ofNat 64 4)) = _
      rw [add64, hf.r12, hf.rbp, shl4 _ (by omega)]
  have c12 : c12.eval (envB m0 m 0) = decide (nB m0 = 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg m .rbp) (reg m .rbp))
      (BitVec.ofNat 64 0) = _
    rw [hf.rbp, andSelf_eq _ (by omega)]
  simp only [PcOk, c12] at hpc1
  by_cases h0 : nB m0 = 0
  · rw [decide_eq_true h0] at hpc1
    simp only [↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.BytecodeShare.label_11_at] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1
    subst hpc1
    exact F _ (by rw [h0]; exact hc1)
  rw [decide_eq_false h0] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  obtain ⟨hmid13, hmem13, hk13, hmid14, hmem14, hk14, hdx14, hmid17, hmem17, hk17, hdx17, hdi17,
    hsi17, -⟩ := ok_moves
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13
    (wf_envB h hc1.fr.frame.kept 0) nofun (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.BytecodeShare.b12_next))
    (match_bodyS hc1.fr 0) fun st2 hm2 hpc2 ↦ ?_
  have hc2 := Cp.ofRun h hc1 hm2 hmid13 hmem13 hk13
  have c13 : c13.eval (envB m0 st1.data 0) = !decide (nB m0 = 1) := by
    show (!(CmpOp.apply .eq .W64 (reg st1.data .rbp) (BitVec.ofNat 64 1))) = _
    rw [hc1.fr.rbp, eq1_eq _ (by omega)]
  simp only [PcOk, c13] at hpc2
  by_cases h1 : nB m0 = 1
  · rw [decide_eq_true h1] at hpc2
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    refine exec_at (infix_of b14_in_code (by simp [b14]) hp) exit_b14
      (wf_envB h hc2.fr.frame.kept 0) nofun (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.BytecodeShare.b13_next))
      (match_bodyS hc2.fr 0) fun st3 hm3 hpc3 ↦ ?_
    have hc3 := Cp.ofRun h hc2 hm3 hmid14 hmem14 hk14
    simp only [PcOk] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.BytecodeShare.label_10_at] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3
    subst hpc3
    exact odd hp h F hc3 (hm3.regs .rdx _ hdx14) (by omega)
  rw [decide_eq_false h1] at hpc2
  simp only [Bool.not_false, ↓reduceIte] at hpc2
  rw [hp.label NativeRustcVmX64.Vm.BytecodeShare.label_12_at] at hpc2
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) exit_b17
    (wf_envB h hc2.fr.frame.kept 0) nofun hpc2 (match_bodyS hc2.fr 0) fun st3 hm3 hpc3 ↦ ?_
  have hc3 := Cp.ofRun h hc2 hm3 hmid17 hmem17 hk17
  have hI : PH m0 m v0 0 st3.data := by
    refine ⟨hc3, rfl, by omega, ?_, hm3.regs .rdx _ hdx17, hm3.regs .rdi _ hdi17⟩
    rw [show reg st3.data .rsi = _ from hm3.regs .rsi _ hsi17]
    show (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (reg st2.data .rbp))
      (BitVec.ofNat 64 62)).toNat = _
    rw [and62 _ (by rw [hc2.fr.rbp]; omega), hc2.fr.rbp]
  simp only [PcOk] at hpc3
  rw [NativeRustcVmX64.Vm.BytecodeShare.b17_length] at hpc3
  refine Sym.loop (fun n (s : MachineState) ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b18Offset) ∧ ∃ j,
      nB m0 - j = n ∧ PH m0 m v0 j s.data)
    (fun n st' ⟨hpc', j, hn, hI'⟩ ↦ ?_) ⟨hpc3, 0, rfl, hI⟩
  obtain ⟨d', pc'⟩ := st'
  simp only at hpc'
  subst hpc'
  refine Eventually.mono (pair hp h F hI') fun st'' h ↦ ?_
  rcases h with h | ⟨hpc'', hI''⟩
  · exact .inl h
  · exact .inr ⟨nB m0 - (j + 2), by have := hI'.lt; omega, hpc'', j + 2, rfl, hI''⟩

end

end NativeRustcVmX64.Bus.BytecodeShare
