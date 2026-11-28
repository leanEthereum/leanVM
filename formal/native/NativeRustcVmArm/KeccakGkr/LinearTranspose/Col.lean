module

public import NativeRustcVmArm.KeccakGkr.LinearTranspose.ColMem

/-!
# `linear_transpose`: a column loop

The loops of columns `0`, `1`, `3`, `4` (`b11`, `b13`, `b17`, `b19`) have one shape (`col_step`,
over the block's run): X10 the elements' address in `g` (`g + 16 z`), X8 the column element's
plus `8`, X9 the elements left; column `2`'s (`b15`) counts X9 up from `-1024` (`col2_step`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (gW colW outW weightsBytes)

@[expose] public section

/-- **Column `x`'s loop head** after `z` elements. -/
structure Col [Labels] (m0 : MachineData) (ws : Array EW) (x z : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  mem : ColMem m0 ws x z st
  z_lt : z < 64
  x8 : st.regs.X8.toBitVec = cA m0 + BitVec.ofNat 64 (8 + 1024 * x + 16 * z)
  x9 : st.regs.X9.toNat = 64 - z
  x10 : st.regs.X10.toBitVec = gA m0 + BitVec.ofNat 64 (16 * z)

/-- **Column `2`'s loop head** after `z` elements. -/
structure Col2 [Labels] (m0 : MachineData) (ws : Array EW) (z : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  mem : ColMem m0 ws 2 z st
  z_lt : z < 64
  x8 : st.regs.X8.toBitVec = cA m0 + BitVec.ofNat 64 2048
  x9 : st.regs.X9.toBitVec = BitVec.ofNat 64 (2 ^ 64 - 1024 + 16 * z)

/-- **Column `x` done**. -/
structure ColDone [Labels] (m0 : MachineData) (ws : Array EW) (x : Nat) (st : MachineData) :
    Prop where
  ctx : Ctx m0 st
  mem : ColMem m0 ws x 64 st

end

public section

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

omit [NativeRustcArm.Host] in
theorem ctx_keep {s s' : MachineData} (h : Ctx m0 s) (hb : Body m0 s')
    (e : ∀ r ∈ [XReg.X19, .X20, .X21, .X22], s'.regs.getXReg r = s.regs.getXReg r) : Ctx m0 s' :=
  ⟨hb, (e .X19 (by simp)).trans h.x19, (e .X20 (by simp)).trans h.x20,
    (e .X21 (by simp)).trans h.x21, (e .X22 (by simp)).trans h.x22⟩

/-- The column element's and the `g` elements' regions: data memory, apart. -/
theorem col_env_wf (hpre : LinearTransposePre ws m0) {s : MachineData} (hb : Body m0 s)
    {x z n : Nat} (hn : 1024 * x + 20496 ≤ n) (hn' : 16 * z + n ≤ 25600)
    (hx : 64 * x + z < 320) :
    (Env.ofMachine s [(gA m0 + BitVec.ofNat 64 (16 * z), n),
      (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]).WF := by
  have hA := pre_areas hpre
  have hgok := Areas.ok hA (r := ⟨gA m0, weightsBytes⟩) (Or.inl (by simp [wsR]))
  have hcok := Areas.ok hA (r := ⟨cA m0, 5120⟩) (Or.inl (by simp [wsR]))
  have hgc := Areas.apart_ws hA (i := 0) (j := 1) (by simp [wsR]) (by simp [wsR]) (by decide)
  simp only [wsR, List.getElem_cons_zero, List.getElem_cons_succ] at hgc
  obtain ⟨hm0, hnw0⟩ := sub_ok hgok (o := 16 * z) (n := n) (by show 16 * z + n ≤ 25600; omega)
  obtain ⟨hm1, hnw1⟩ := sub_ok hcok (o := 16 * (64 * x + z)) (n := 16)
    (by show 16 * (64 * x + z) + 16 ≤ 5120; omega)
  exact Env.wf_of ⟨⟨Mapped.kept' hm0 hb.kept, hnw0⟩, ⟨Mapped.kept' hm1 hb.kept, hnw1⟩, trivial⟩
    (List.pairwise_pair.mpr (Apart.sub hgc hgok.2 hcok.2 (by show 16 * z + n ≤ 25600; omega)
      (by show 16 * (64 * x + z) + 16 ≤ 5120; omega) (by omega) (by show 0 < 16; decide)))

/-- **One element of a column loop** of the common shape. -/
theorem col_step (hpre : LinearTransposePre ws m0) {blk : List Directive} {j x n : Nat}
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
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + j) ∧ Col m0 ws x (z + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + j + blk.length) ∧ ColDone m0 ws x s'.data)) s := by
  subst hn
  have hS := hpre.1
  have hA := pre_areas hpre
  have hz := hI.z_lt
  have hcok := Areas.ok hA (r := ⟨cA m0, 5120⟩) (Or.inl (by simp [wsR]))
  have hnw1 := (sub_ok hcok (o := 16 * (64 * x + z)) (n := 16)
    (by show 16 * (64 * x + z) + 16 ≤ 5120; omega)).2
  have hwf := col_env_wf hpre hI.ctx.body (x := x) (z := z) (Nat.le_refl _) (by omega) (by omega)
  have hm : Match (Env.ofMachine s.data [(gA m0 + BitVec.ofNat 64 (16 * z), 1024 * x + 20496),
      (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]) (colS (1024 * x + 20496)) s.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s.data.regs.getXReg .X10).toBitVec = _ + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact hI.x10,
       by
        show (s.data.regs.getXReg .X8).toBitVec =
          (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z))) + BitVec.ofInt 64 8
        rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
        rw [show (s.data.regs.getXReg .X8) = s.data.regs.X8 from rfl, hI.x8]
        congr 2
        omega,
       trivial⟩ trivial trivial trivial
  refine exec_at hblk he hwf hpc hm fun s' hm' hpc' ↦ ?_
  have hmem' := col_mem hpre hz hI.mem (Nat.le_refl _) (by omega) hm' hwf hmem
  have hbody : Body m0 s'.data :=
    hI.ctx.body.write hS (by decide) slots_le (wsOff hpre) hm hm' hwf rfl free_ok hk
      fun p hw ↦ ⟨⟨cA m0, 5120⟩, by simp [wsR],
        inRange_mono (Written.inRange (r := 1) rfl hnw1 (by
          rw [hmem]; intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;> exact ⟨rfl, by simp⟩) hw)
          (by show 16 * (64 * x + z) + 16 ≤ 5120; omega)⟩
  have hctx := ctx_keep hI.ctx hbody (KeccakGkr.Match.regs_keep hm hm' _ hk')
  have hr8 := hm'.regs .X8 _ h8
  have hr9 := hm'.regs .X9 _ h9
  have hr10 := hm'.regs .X10 _ h10
  sym_simp at hr8 hr9 hr10
  have hx9 : (s.data.regs.getXReg .X9).toBitVec.toNat = 64 - z := hI.x9
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  simp only [Env.ofMachine_regs] at hr9 hpc'
  by_cases hlast : z = 63
  · subst hlast
    have hc : ((s.data.regs.getXReg .X9).toBitVec == 1#64) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hx9]; rfl
    simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    exact .done _ (Or.inr ⟨hpc', hctx, hmem'⟩)
  · have hc : ((s.data.regs.getXReg .X9).toBitVec == 1#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; rw [hx9] at this
      simp at this; omega
    simp only [hc, Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨hpc'.trans hlbl, hctx, hmem', by omega, ?_, ?_, ?_⟩)
    · show (s'.data.regs.getXReg .X8).toBitVec = _
      rw [hr8, show (Env.ofMachine s.data [(gA m0 + BitVec.ofNat 64 (16 * z), 1024 * x + 20496),
          (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]).base 1 =
          cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)) from rfl,
        show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add_add]
      congr 2; omega
    · show (s'.data.regs.getXReg .X9).toBitVec.toNat = _
      rw [hr9, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hx9]; simp; omega), hx9]; simp; omega
    · show (s'.data.regs.getXReg .X10).toBitVec = _
      rw [hr10, show (Env.ofMachine s.data [(gA m0 + BitVec.ofNat 64 (16 * z), 1024 * x + 20496),
          (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]).base 0 =
          gA m0 + BitVec.ofNat 64 (16 * z) from rfl,
        show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add]
      congr 2


omit [NativeRustcArm.Host] in
theorem ofInt_neg1024 : BitVec.ofInt 64 (-1024) = BitVec.ofNat 64 (2 ^ 64 - 1024) := by decide

/-- **One element of column `2`'s loop** (`b15`). -/
theorem col2_step (hp : Placed code k) (hpre : LinearTransposePre ws m0) {z : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b15Offset)) (hI : Col2 m0 ws z s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b15Offset) ∧ Col2 m0 ws (z + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b16Offset) ∧ ColDone m0 ws 2 s'.data)) s := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hz := hI.z_lt
  have hcok := Areas.ok hA (r := ⟨cA m0, 5120⟩) (Or.inl (by simp [wsR]))
  have hnw1 := (sub_ok hcok (o := 16 * (64 * 2 + z)) (n := 16)
    (by show 16 * (64 * 2 + z) + 16 ≤ 5120; omega)).2
  have hwf := col_env_wf hpre hI.ctx.body (x := 2) (z := z) (n := 22544) (by decide) (by omega)
    (by omega)
  have hx20 : (s.data.regs.getXReg .X20).toBitVec = gA m0 := congrArg UInt64.toBitVec hI.ctx.x20
  have hm : Match (Env.ofMachine s.data [(gA m0 + BitVec.ofNat 64 (16 * z), 22544),
      (cA m0 + BitVec.ofNat 64 (16 * (64 * 2 + z)), 16)]) col2S s.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (s.data.regs.getXReg .X20).toBitVec
          (s.data.regs.getXReg .X9).toBitVec = (gA m0 + BitVec.ofNat 64 (16 * z)) + BitVec.ofInt 64 (-1024)
        simp only [BinOp.apply, low_W64, ext_W64]
        rw [hx20, show (s.data.regs.getXReg .X9) = s.data.regs.X9 from rfl, hI.x9, ofInt_neg1024,
          NativeRustcVm.addr_add_add]
        congr 2; omega,
       by
        show BinOp.apply .add .W64 (s.data.regs.getXReg .X8).toBitVec
          (s.data.regs.getXReg .X9).toBitVec =
          (cA m0 + BitVec.ofNat 64 (16 * (64 * 2 + z))) + BitVec.ofInt 64 (-1024)
        simp only [BinOp.apply, low_W64, ext_W64]
        rw [show (s.data.regs.getXReg .X8) = s.data.regs.X8 from rfl, hI.x8,
          show (s.data.regs.getXReg .X9) = s.data.regs.X9 from rfl, hI.x9, ofInt_neg1024,
          NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
        congr 2; omega,
       trivial⟩
  refine exec_at (b15_in_code.trans hp.1 (by simp [b15])) e15 hwf hpc hm fun s' hm' hpc' ↦ ?_
  have hmem' := col_mem hpre hz hI.mem (by decide) (by omega) hm' hwf rfl
  have hbody : Body m0 s'.data :=
    hI.ctx.body.write hS (by decide) slots_le (wsOff hpre) hm hm' hwf rfl free_ok (by decide)
      fun p hw ↦ ⟨⟨cA m0, 5120⟩, by simp [wsR],
        inRange_mono (Written.inRange (r := 1) rfl hnw1 (by decide) hw)
          (by show 16 * (64 * 2 + z) + 16 ≤ 5120; omega)⟩
  have hctx := ctx_keep hI.ctx hbody (KeccakGkr.Match.regs_keep hm hm' _ (by decide))
  have hr9 := hm'.regs .X9 _ rfl
  have hr8 := hm'.regs .X8 _ rfl
  sym_simp at hr9 hpc'
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  simp only [Env.ofMachine_regs] at hr8 hr9 hpc'
  have hx9 : (s.data.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (2 ^ 64 - 1024 + 16 * z) := hI.x9
  simp only [hx9, BitVec.ofNat_add_ofNat] at hpc' hr9
  by_cases hlast : z = 63
  · subst hlast
    simp only [show (BitVec.ofNat 64 (2 ^ 64 - 1024 + 16 * 63 + 16) == 0#64) = true by decide,
      Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    exact .done _ (Or.inr ⟨hpc', hctx, hmem'⟩)
  · have hc : (BitVec.ofNat 64 (2 ^ 64 - 1024 + 16 * z + 16) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this; omega
    simp only [hc, Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨hpc'.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b15Offset) NativeRustcVmArm.Vm.LinearTranspose.label_12_at), hctx, hmem', by omega, ?_, ?_⟩)
    · show (s'.data.regs.getXReg .X8).toBitVec = _
      rw [hr8]; exact hI.x8
    · show (s'.data.regs.getXReg .X9).toBitVec = _
      rw [hr9]; congr 1

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
