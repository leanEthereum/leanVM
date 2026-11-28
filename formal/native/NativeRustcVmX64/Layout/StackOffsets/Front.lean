module

public import NativeRustcVmX64.Layout.StackOffsets.Fill

/-!
# `stack_offsets` on x86-64: from the prologue to the sort (`b3` to `b7`, `fill`)

`b3` keeps `8 n` in RBP; `n = 0` goes to `b6`, which sets the sort's arguments at once. Else `b4`
splits at eight blocks: `b5` to the one-word loop (`l10`), `b7` to the eight-word loop
(`loop8`, then `l9`).
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.StackOffsets NativeRustcVmX64.Layout.BuildFrame

public section

variable [Host] {k : Nat} {m0 : MachineData}

/-- **The eight-word loop**, to `b9` and on to `b13`. -/
theorem loop8 (hp : Placed code k) (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {q : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b8Offset)) (hI : Inv8 m0 q st.data) :
    Eventually (step1 Host.exe) (At13 k m0) st := by
  refine Eventually.bind (Sym.loop (Q := At9 k m0)
    (fun r s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b8Offset) ∧ ∃ q, n m0 / 8 - q = r ∧ Inv8 m0 q s.data)
    (fun r s ⟨hpc, q, hr, hI⟩ ↦ ?_) ⟨hpc, q, rfl, hI⟩) fun s h ↦ l9 hp hst hn h
  refine Eventually.mono (step8 hp hst hn hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · have := hI.lt
    exact Or.inr ⟨n m0 / 8 - (q + 1), by omega, hpc', q + 1, rfl, hI'⟩

/-- `b7`: the eight-word loop's start. -/
theorem l7 (hp : Placed code k) (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b7Offset)) (hI : Init m0 0 st.data) (h8 : 8 ≤ n m0)
    (hrdx : (reg st.data .rdx).toNat = n m0) (hrax : (reg st.data .rax).toNat = n m0 % 8) :
    Eventually (step1 Host.exe) (At13 k m0) st := by
  obtain ⟨hok, hmem, hdx, h13, hcx, hK⟩ := ok_b7
  refine step0 hst (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b7 nofun hpc hI.b hok hmem
    fun st' hm' hpc' hb' hd ↦ loop8 (q := 0) hp hst hn hpc' ⟨hI.step hb' (kp hm' hK (by simp))
      (hd ▸ hI.ords) hI.le, by omega, ?_, ?_, ?_, ?_⟩
  · show (st'.data.regs.get64 .rcx).toNat = _
    rw [hm'.regs .rcx _ hcx]; rfl
  · rw [show ob m0 + BitVec.ofNat 64 (64 * 0) = ob m0 by simp]
    exact (hm'.regs .r13 _ h13).trans (eval_ptr0 16)
  · show (st'.data.regs.get64 .rdx).toNat = _
    rw [hm'.regs .rdx _ hdx]
    exact rdx7_eval hrdx hn
  · rw [kp hm' hK (rs' := [Reg64.rax]) (by simp) .rax (by simp)]; exact hrax

/-- **The order array written and the sort's arguments set**: from `b3` to `b13`. -/
theorem fill (hp : Placed code k) (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {st : MachineState}
    (h : Start k m0 st) : Eventually (step1 Host.exe) (At13 k m0) st := by
  obtain ⟨hpc, -, hb, hR, h13⟩ := h
  obtain ⟨hok, hmem, hbp, hK⟩ := ok_b3
  refine step0 hst (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b3 nofun hpc hb hok hmem
    fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  have hR1 : Regs m0 st1.data := hR.of (kp hm1 hK (by simp))
  have hbp1 : reg st1.data .rbp = BitVec.ofNat 64 (8 * n m0) :=
    (hm1.regs .rbp _ hbp).trans (e8n_eval (congrArg BitVec.toNat hR.r15))
  have hI1 : Init m0 0 st1.data := ⟨hb1, hR1, hbp1, ords_zero _ _, Nat.zero_le _⟩
  have h13' : reg st1.data .r13 = ob m0 :=
    (kp hm1 hK (rs' := [Reg64.r13]) (by simp) .r13 (by simp)).trans h13
  simp only [PcOk] at hpc1
  obtain ⟨hy, hno⟩ := pc_of (P := n m0 = 0) hpc1 (by
    rw [test_eval]
    show decide ((reg st.data .r15).toNat = 0) = _
    rw [hR.r15])
  by_cases h0 : n m0 = 0
  · -- `b6`: no block
    obtain ⟨hok6, hmem6, hx7, hx6, hx2, hx1, hK6⟩ := ok_b6
    refine step0 hst (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b6 nofun
      ((hy h0).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_6_at)) hb1 hok6 hmem6 fun st2 hm2 hpc2 hb2 hd2 ↦ .done _
      ⟨hpc2.trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_13_at), ?_, ?_, ?_, ?_, ?_⟩
    · rw [h0]
      exact hI1.step hb2 (kp hm2 hK6 (by simp [cs])) (ords_zero _ _) (Nat.zero_le _)
    · exact (hm2.regs .rdi _ hx7).trans (eval_ptr0 16)
    · show (st2.data.regs.get64 .rsi).toNat = _
      rw [hm2.regs .rsi _ hx6, h0]; rfl
    · exact (hm2.regs .rdx _ hx2).trans hR1.r12
    · show (st2.data.regs.get64 .rcx).toNat = _
      rw [hm2.regs .rcx _ hx1, h0]; rfl
  · -- `b4`: eight blocks or more?
    have h1 : 1 ≤ n m0 := by omega
    obtain ⟨hok4, hmem4, hax, hcx, hdx, hK4⟩ := ok_b4
    refine step0 hst (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b4 nofun (hno h0) hb1
      hok4 hmem4 fun st2 hm2 hpc2 hb2 hd2 ↦ ?_
    have hI2 : Init m0 0 st2.data := hI1.step hb2 (kp hm2 hK4 (by simp [cs])) (ords_zero _ _)
      (Nat.zero_le _)
    have hrax2 : (reg st2.data .rax).toNat = n m0 % 8 := by
      show (st2.data.regs.get64 .rax).toNat = _
      rw [hm2.regs .rax _ hax]
      exact rax4_eval hbp1 h1 hn
    have hrdx2 : (reg st2.data .rdx).toNat = n m0 := by
      show (st2.data.regs.get64 .rdx).toNat = _
      rw [hm2.regs .rdx _ hdx]
      exact eN_eval hbp1 h1 hn
    simp only [PcOk] at hpc2
    obtain ⟨hy2, hno2⟩ := pc_of (P := ¬ 8 * n m0 - 8 < 56) hpc2 (by
      rw [SBool.eval, ult_eval, eM8_eval hbp1 h1 hn, decide_not]; rfl)
    by_cases h8 : 8 ≤ n m0
    · exact l7 hp hst hn ((hy2 (by omega)).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_7_at)) hI2 h8 hrdx2 hrax2
    · -- `b5`: the one-word loop alone
      obtain ⟨hok5, hmem5, hcx5, hK5⟩ := ok_b5
      refine step0 hst (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b5 nofun
        (hno2 (by omega)) hb2 hok5 hmem5 fun st3 hm3 hpc3 hb3 hd3 ↦
          l10 (c := 0) hp hst hn (hpc3.trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_10_at))
            ⟨hI2.step hb3 (kp hm3 hK5 (by simp [cs])) (ords_zero _ _) (Nat.zero_le _), h1, ?_, ?_, ?_⟩
      · show (st3.data.regs.get64 .rcx).toNat = _
        rw [hm3.regs .rcx _ hcx5]; rfl
      · rw [show ob m0 + BitVec.ofNat 64 (8 * 0) = ob m0 by simp,
          kp hm3 hK5 (rs' := [Reg64.r13]) (by simp [cs]) .r13 (by simp)]
        show reg st2.data .r13 = _
        rw [kp hm2 hK4 (rs' := [Reg64.r13]) (by simp [cs]) .r13 (by simp)]
        exact h13'
      · rw [kp hm3 hK5 (rs' := [Reg64.rax]) (by simp) .rax (by simp)]
        show (reg st2.data .rax).toNat = _
        rw [hrax2]; omega

end

end NativeRustcVmX64.Layout.StackOffsets
