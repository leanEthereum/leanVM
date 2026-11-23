module

public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Col

/-!
# `linear_transpose`: the columns

From `g` done (`.LLinearTranspose_7`), each column's set-up block (`b10`, `b12`, `b14`, `b16`,
`b18`) and loop: the five columns of `g` summed (`columns`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters

public section

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

/-- **A column loop** of the common shape, to its end. -/
theorem col_loop (hpre : LinearTransposePre ws m0) {blk : List Directive} {j x n : Nat}
    {S' : SState} {lbl : Label} (hblk : blk.IsInfixAt Host.prog (k + j))
    (hlbl : Labels.label lbl = Host.addrOf (k + j)) (hx : x < 5) (hn : n = 1024 * x + 20496)
    (he : exec blk (colS n) = some (S', .cond (.not (.cmp .eq .W64 (.reg .X9) (.lit 1))) lbl))
    (hmem : S'.mem = [⟨1, 8, 8, tree x 8⟩, ⟨1, 0, 8, tree x 0⟩])
    (h8 : S'.reg .X8 = some (.ptr 1 24))
    (h9 : S'.reg .X9 = some (.bin .sub .W64 (.reg .X9) (.lit 1)))
    (h10 : S'.reg .X10 = some (.ptr 0 16))
    (hk : keepsRegs (colS n) S' [.X27, .X28, .X29] = true)
    (hk' : [XReg.X19, .X20, .X21, .X22].all
      (fun r ↦ ((colS n).reg r).isSome && S'.reg r == (colS n).reg r) = true)
    {z : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf (k + j)) (hI : Col m0 ws x z s.data) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (k + j + blk.length) ∧ ColDone m0 ws x s'.data) s :=
  Sym.loop (fun c s ↦ ∃ z, c = 64 - z ∧ s.pc = Host.addrOf (k + j) ∧ Col m0 ws x z s.data)
    (fun _ s ⟨z, hc, hpc, hI⟩ ↦ (col_step hpre hblk hlbl hx hn he hmem h8 h9 h10 hk hk' hpc hI).mono
      fun s' h ↦ by
        rcases h with ⟨hpc', hI'⟩ | h
        · exact Or.inr ⟨64 - (z + 1), by have := hI.z_lt; omega, z + 1, rfl, hpc', hI'⟩
        · exact Or.inl h)
    ⟨z, rfl, hpc, hI⟩

/-- **Column `2`'s loop**, to its end. -/
theorem col2_loop (hp : Placed code k) (hpre : LinearTransposePre ws m0) {z : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b15Offset)) (hI : Col2 m0 ws z s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b16Offset) ∧ ColDone m0 ws 2 s'.data)
      s :=
  Sym.loop (fun c s ↦ ∃ z, c = 64 - z ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b15Offset) ∧ Col2 m0 ws z s.data)
    (fun _ s ⟨z, hc, hpc, hI⟩ ↦ (col2_step hp hpre hpc hI).mono fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨64 - (z + 1), by have := hI.z_lt; omega, z + 1, rfl, hpc', hI'⟩
      · exact Or.inl h)
    ⟨z, rfl, hpc, hI⟩

theorem ColMem.of_dmem {s s' : MachineData} {x z : Nat} (h : ColMem m0 ws x z s)
    (hd : s'.dmem = s.dmem) : ColMem m0 ws x z s' :=
  ⟨by rw [hd]; exact h.g, by rw [hd]; exact h.c⟩

theorem colMem_next {s : MachineData} {x : Nat} (h : ColMem m0 ws x 64 s) :
    ColMem m0 ws (x + 1) 0 s :=
  ⟨h.g, by rw [show 64 * (x + 1) + 0 = 64 * x + 64 by omega]; exact h.c⟩

/-- **A column's set-up** of the common shape: X8 the column's first element plus `8`, X9 `64`,
X10 `g`. -/
theorem col_setup {blk : List Directive} {j x : Nat} {S' : SState}
    (hblk : blk.IsInfixAt Host.prog (k + j)) (he : exec blk regsS = some (S', .fall))
    (h8 : S'.reg .X8 = some (.bin .add .W64 (.reg .X19) (.lit (8 + 1024 * x))))
    (h9 : S'.reg .X9 = some (.lit 64)) (h10 : S'.reg .X10 = some (.reg .X20))
    (hk : keepsAll regsS S' [.X27, .X28, .X29] = true)
    (hk' : [XReg.X19, .X20, .X21, .X22].all
      (fun r ↦ (regsS.reg r).isSome && S'.reg r == regsS.reg r) = true)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + j)) (hctx : Ctx m0 s.data)
    (hmem : ColMem m0 ws x 0 s.data) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (k + j + blk.length) ∧ Col m0 ws x 0 s'.data) s := by
  refine exec_at hblk he (Env.wf_nil _) hpc (match_nil _) fun s' hm' hpc' ↦ .done _ ⟨hpc', ?_⟩
  have hb := hctx.body.of_block (match_nil _) hm' (Env.wf_nil _) rfl free_ok hk
  have hctx' := ctx_keep hctx hb (KeccakGkr.Match.regs_keep (match_nil _) hm' _ hk')
  have hr8 := hm'.regs .X8 _ h8
  have hr9 := hm'.regs .X9 _ h9
  have hr10 := hm'.regs .X10 _ h10
  sym_simp at hr8 hr9
  have hmem0 : S'.mem = [] := by
    simp only [keepsAll, Bool.and_eq_true, List.isEmpty_iff] at hk; exact hk.2
  refine ⟨hctx', hmem.of_dmem (hm'.dmem_eq (Env.wf_nil _) hmem0), by decide, ?_, ?_, ?_⟩
  · show (s'.data.regs.getXReg .X8).toBitVec = _
    rw [hr8, Env.ofMachine_regs, show (s.data.regs.getXReg .X19) = m0.regs.X2 from hctx.x19,
      Nat.mul_zero, Nat.add_zero]
  · show (s'.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [hr9]; rfl
  · show (s'.data.regs.getXReg .X10).toBitVec = _
    rw [hr10]
    show (s.data.regs.getXReg .X20).toBitVec = _
    rw [show (s.data.regs.getXReg .X20) = m0.regs.X1 from hctx.x20, Nat.mul_zero,
      show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]

/-- **The columns**: from `g` done, every column. -/
theorem columns (hp : Placed code k) (hpre : LinearTransposePre ws m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b10Offset)) (hI : GDone m0 ws s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b20Offset) ∧ ColDone m0 ws 4 s'.data)
      s := by
  have blk : ∀ {b : List Directive} {j : Nat}, b.IsInfixAt code j → b ≠ [] →
      b.IsInfixAt Host.prog (k + j) := fun h hne ↦ h.trans hp.1 hne
  refine (col_setup (x := 0) (blk b10_in_code (by simp [b10])) e10 rfl rfl rfl (by decide) (by decide)
    hpc hI.ctx ⟨hI.g, fun _ h ↦ absurd h (by omega)⟩).bind fun s1 ⟨hpc1, hI1⟩ ↦ ?_
  refine (col_loop hpre (blk b11_in_code (by simp [b11])) (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b11Offset) NativeRustcVmArm.Vm.LinearTranspose.label_8_at) (x := 0)
    (by decide) rfl e11 rfl rfl rfl rfl (by decide) (by decide) hpc1 hI1).bind
    fun s2 ⟨hpc2, hI2⟩ ↦ ?_
  refine (col_setup (x := 1) (blk b12_in_code (by simp [b12])) e12 rfl rfl rfl (by decide) (by decide)
    hpc2 hI2.ctx (colMem_next hI2.mem)).bind fun s3 ⟨hpc3, hI3⟩ ↦ ?_
  refine (col_loop hpre (blk b13_in_code (by simp [b13])) (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b13Offset) NativeRustcVmArm.Vm.LinearTranspose.label_10_at) (x := 1)
    (by decide) rfl e13 rfl rfl rfl rfl (by decide) (by decide) hpc3 hI3).bind
    fun s4 ⟨hpc4, hI4⟩ ↦ ?_
  -- column `2`
  refine exec_at (blk b14_in_code (by simp [b14])) e14 (Env.wf_nil _) hpc4 (match_nil _)
    fun s5 hm5 hpc5 ↦ ?_
  have hb5 := hI4.ctx.body.of_block (match_nil _) hm5 (Env.wf_nil _) rfl free_ok (by decide)
  have hctx5 := ctx_keep hI4.ctx hb5 (KeccakGkr.Match.regs_keep (match_nil _) hm5 _ (by decide))
  have hr8 := hm5.regs .X8 _ rfl
  have hr9 := hm5.regs .X9 _ rfl
  sym_simp at hr8 hr9
  refine (col2_loop hp hpre (z := 0) hpc5 ⟨hctx5,
      (colMem_next hI4.mem).of_dmem (hm5.dmem_eq (Env.wf_nil _) rfl), by decide, ?_, ?_⟩).bind
    fun s6 ⟨hpc6, hI6⟩ ↦ ?_
  · show (s5.data.regs.getXReg .X8).toBitVec = _
    rw [hr8, Env.ofMachine_regs, show (s4.data.regs.getXReg .X19) = m0.regs.X2 from hI4.ctx.x19]
  · show (s5.data.regs.getXReg .X9).toBitVec = _
    rw [hr9]; rfl
  refine (col_setup (x := 3) (blk b16_in_code (by simp [b16])) e16 rfl rfl rfl (by decide) (by decide)
    hpc6 hI6.ctx (colMem_next hI6.mem)).bind fun s7 ⟨hpc7, hI7⟩ ↦ ?_
  refine (col_loop hpre (blk b17_in_code (by simp [b17])) (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b17Offset) NativeRustcVmArm.Vm.LinearTranspose.label_14_at) (x := 3)
    (by decide) rfl e17 rfl rfl rfl rfl (by decide) (by decide) hpc7 hI7).bind
    fun s8 ⟨hpc8, hI8⟩ ↦ ?_
  refine (col_setup (x := 4) (blk b18_in_code (by simp [b18])) e18 rfl rfl rfl (by decide) (by decide)
    hpc8 hI8.ctx (colMem_next hI8.mem)).bind fun s9 ⟨hpc9, hI9⟩ ↦ ?_
  exact col_loop hpre (blk b19_in_code (by simp [b19])) (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b19Offset) NativeRustcVmArm.Vm.LinearTranspose.label_16_at) (x := 4)
    (by decide) rfl e19 rfl rfl rfl rfl (by decide) (by decide) hpc9 hI9

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
