module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.WeightsHead
public import NativeRustcVmX64.Code.Vm.VerifyLayer.Names

/-! # Loading the first neighboring equality-kernel value -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea)
open LeanVM.Protocol.Verifier

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {j k : Nat}

theorem weights_four (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) (hlp : lp.size = 11)
    {d : MachineData} (h : WHead m0 a c ch b pt lp t s6 j d)
    (hdi : reg d .rdi = BitVec.ofNat 64 (64 * alongRow j 4))
    (hsi : reg d .rsi = BitVec.ofNat 64 (j % 64)) {R : MachineState → Prop}
    (cont : ∀ d', WHead m0 a c ch b pt lp t s6 j d' →
      (∀ r ∈ [Reg64.rax, .rcx, .rsi], reg d' r = reg d r) →
      reg d' .r14 = ((eqKernel lp).getD (keccakAlong j 4) 0).c0.toBitVec →
      reg d' .r12 = ((eqKernel lp).getD (keccakAlong j 4) 0).c1.toBitVec →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b77Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b75Offset)⟩ := by
  have g := geo_of hpre
  have hi : keccakAlong j 4 < 1600 := by rw [along_eq]; have := alongRow_lt j 4 h.lt; omega
  have hwf := wfScratch hpre h.body (p := 107520 + 16 * keccakAlong j 4) (n := 16)
    (by omega) (by omega) (ret := 0)
  have hw56 := h.mem.fw (56, .ofBitVec (sA m0 + BitVec.ofNat 64 107520))
    (by apply List.mem_append_left; fw_mem)
  have halias : a75.eval (envB m0 d [(sA m0 + BitVec.ofNat 64 (107520 + 16 * keccakAlong j 4), 16)]
      (fun _ ↦ 0) 0) = sA m0 + BitVec.ofNat 64 (107520 + 16 * keccakAlong j 4) + BitVec.ofInt 64 0 := by
    simp only [a75, Sym.eval]
    rw [fload8 hw56]
    change BinOp.apply .add .W64
      (BinOp.apply .shl .W32 (UnOp.apply .trunc .W32 (reg d .rsi)) 4#64)
      (BinOp.apply .add .W64 (sA m0 + BitVec.ofNat 64 107520)
        (BinOp.apply .shl .W64 (reg d .rdi) 4#64)) = _
    rw [hdi, hsi, along_eq]
    norm_num [BinOp.apply, UnOp.apply, low, ext, shiftCount, Width.bits, shiftMask]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Width.bits, Nat.shiftLeft_eq]
    have hl := alongRow_lt j 4 h.lt
    omega
  have hm : Match (envB m0 d [(sA m0 + BitVec.ofNat 64 (107520 + 16 * keccakAlong j 4), 16)]
      (fun _ ↦ 0) 0) (fr 24 [16] [] [] [(a75, 1, 0)]) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial ⟨halias, trivial⟩
  have hl := scratchLoads (ret := 0) h.mem.eq (i := keccakAlong j 4)
    (by rw [NativeVm.Math.Keccak.eqKernel_size, hlp]; omega)
  refine Body.blk (o' := 24) g h.body hwf (blk hp b75_in_code (by simp [b75])) e75 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm' hpc hb _ ↦ ?_
  have hd : st.data.dmem = d.dmem := hm'.dmem_eq hwf rfl
  have hr : ∀ r ∈ [Reg64.rbp, .rbx, .r15, .r13], reg st.data r = reg d r :=
    keepR_regs hm' (by decide +kernel) fun _ ↦ rfl
  have hk : ∀ r ∈ [Reg64.rax, .rcx, .rsi], reg st.data r = reg d r :=
    keepR_regs hm' (by decide +kernel) fun _ ↦ rfl
  have h14 := (hm'.regs .r14 _ rfl).trans hl.1
  have h12 := (hm'.regs .r12 _ rfl).trans hl.2
  simp only [PcOk] at hpc
  rw [lbl hp b77_in_code rfl] at hpc
  exact at_pc hpc (cont st.data (h.read hb hd hr) hk h14 h12)

theorem weights_three_index (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    {d : MachineData} (h : WHead m0 a c ch b pt lp t s6 j d)
    (hc : reg d .rcx = BitVec.ofNat 64 (j / 64 % 5))
    (ha : reg d .rax = BitVec.ofNat 64 (5 * (j / 320))) {R : MachineState → Prop}
    (cont : ∀ d', WHead m0 a c ch b pt lp t s6 j d' →
      (∀ r ∈ [Reg64.r14, .r12, .rsi], reg d' r = reg d r) →
      reg d' .rax = BitVec.ofNat 64 (64 * alongRow j 3) →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b70Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b77Offset)⟩ := by
  have g := geo_of hpre
  have hwf := wf0 (pre_stack hpre) h.body (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g h.body hwf (blk hp b77_in_code (by simp [b77])) e77 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm' hpc hb _ ↦ ?_
  have hv : threeS.eval (envB m0 d [] (fun _ ↦ 0) 0) =
      BitVec.ofNat 64 (64 * alongRow j 3) := by
    rw [threeS_eval _ h.r13]
    change idx3 (reg d .rcx) (reg d .rax) = _
    rw [hc, ha]
    exact (index_values h.lt).2.2.2
  have ha' : reg st.data .rax = BitVec.ofNat 64 (64 * alongRow j 3) :=
    (hm'.regs .rax threeS rfl).trans hv
  have hr : ∀ r ∈ [Reg64.rbp, .rbx, .r15, .r13], reg st.data r = reg d r :=
    keepR_regs hm' (by decide +kernel) fun _ ↦ rfl
  have hk : ∀ r ∈ [Reg64.r14, .r12, .rsi], reg st.data r = reg d r :=
    keepR_regs hm' (by decide +kernel) fun _ ↦ rfl
  have hcond : (SBool.or (.cmp .ult .W64 threeS (.lit 2047))
      (.cmp .eq .W64 threeS (.lit 2047))).eval (envB m0 d [] (fun _ ↦ 0) 0) = true := by
    change (CmpOp.apply .ult .W64 (threeS.eval _) 2047#64 ||
      CmpOp.apply .eq .W64 (threeS.eval _) 2047#64) = true
    rw [hv]
    have hl := alongRow_lt j 3 h.lt
    have hh : (64 * alongRow j 3) % 2 ^ 64 < 2047 := by omega
    simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat,
      show 2047 % 2 ^ 64 = 2047 from rfl, decide_eq_true hh, Bool.true_or]
  simp only [PcOk] at hpc
  change st.pc = if (SBool.or (.cmp .ult .W64 threeS (.lit 2047))
      (.cmp .eq .W64 threeS (.lit 2047))).eval (envB m0 d [] (fun _ ↦ 0) 0) = true
    then Labels.label NativeRustcVmX64.Vm.VerifyLayer.label_40 else Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b77Offset + b77.length) at hpc
  rw [hcond] at hpc
  simp only [↓reduceIte] at hpc
  rw [lbl hp b70_in_code rfl] at hpc
  exact at_pc hpc (cont st.data (h.read hb (hm'.dmem_eq hwf rfl) hr) hk ha')

theorem weights_three (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) (hlp : lp.size = 11)
    {d : MachineData} (h : WHead m0 a c ch b pt lp t s6 j d)
    (ha : reg d .rax = BitVec.ofNat 64 (64 * alongRow j 3))
    (hsi : reg d .rsi = BitVec.ofNat 64 (j % 64)) {R : MachineState → Prop}
    (cont : ∀ d', WHead m0 a c ch b pt lp t s6 j d' →
      reg d' .r14 = reg d .r14 → reg d' .r12 = reg d .r12 →
      ewArg (reg d' .rdx) (reg d' .rcx) = (eqKernel lp).getD (keccakAlong j 3) 0 →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b71Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b70Offset)⟩ := by
  have g := geo_of hpre
  have hi : keccakAlong j 3 < 1600 := by rw [along_eq]; have := alongRow_lt j 3 h.lt; omega
  have hwf := wfScratch hpre h.body (p := 107520 + 16 * keccakAlong j 3) (n := 16)
    (by omega) (by omega) (ret := 0)
  have hw56 := h.mem.fw (56, .ofBitVec (sA m0 + BitVec.ofNat 64 107520))
    (by apply List.mem_append_left; fw_mem)
  have halias : a70.eval (envB m0 d [(sA m0 + BitVec.ofNat 64 (107520 + 16 * keccakAlong j 3), 16)]
      (fun _ ↦ 0) 0) = sA m0 + BitVec.ofNat 64 (107520 + 16 * keccakAlong j 3) + BitVec.ofInt 64 0 := by
    simp only [a70, Sym.eval]
    rw [fload8 hw56]
    change BinOp.apply .add .W64
      (BinOp.apply .shl .W32 (reg d .rsi) 4#64)
      (BinOp.apply .add .W64 (sA m0 + BitVec.ofNat 64 107520)
        (BinOp.apply .shl .W64 (reg d .rax) 4#64)) = _
    rw [ha, hsi, along_eq]
    norm_num [BinOp.apply, low, ext, shiftCount, Width.bits, shiftMask]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Width.bits, Nat.shiftLeft_eq]
    have hl := alongRow_lt j 3 h.lt
    omega
  have hm : Match (envB m0 d [(sA m0 + BitVec.ofNat 64 (107520 + 16 * keccakAlong j 3), 16)]
      (fun _ ↦ 0) 0) (fr 24 [16] [] [] [(a70, 1, 0)]) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial ⟨halias, trivial⟩
  have hl := scratchLoads (ret := 0) h.mem.eq (i := keccakAlong j 3)
    (by rw [NativeVm.Math.Keccak.eqKernel_size, hlp]; omega)
  refine Body.blk (o' := 24) g h.body hwf (blk hp b70_in_code (by simp [b70])) e70 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm' hpc hb _ ↦ ?_
  have hd : st.data.dmem = d.dmem := hm'.dmem_eq hwf rfl
  have hr : ∀ r ∈ [Reg64.rbp, .rbx, .r15, .r13], reg st.data r = reg d r :=
    keepR_regs hm' (by decide +kernel) fun _ ↦ rfl
  have he : ewArg (reg st.data .rdx) (reg st.data .rcx) =
      (eqKernel lp).getD (keccakAlong j 3) 0 := by
    rw [show reg st.data .rdx = _ from hm'.regs .rdx _ rfl,
      show reg st.data .rcx = _ from hm'.regs .rcx _ rfl]
    simp only [Sym.eval]
    rw [hl.1, hl.2, ewArg_ew]
  simp only [PcOk] at hpc
  exact at_pc hpc (cont st.data (h.read hb hd hr) (hm'.regs .r14 _ rfl) (hm'.regs .r12 _ rfl) he)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
