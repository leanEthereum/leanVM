module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.WeightsState
public import NativeRustcVmX64.Code.Vm.VerifyLayer.Names

/-! # The weights loop's column and row arithmetic -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea)

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {c : KeccakClaimW} {ch b : EW}
  {pt lp t : Array EW} {s6 : TState} {j : Nat}

omit [Labels] in
theorem WHead.read {d d' : MachineData} (h : WHead m0 a c ch b pt lp t s6 j d)
    (hb : Body m0 (wFront m0) 24 d') (hd : d'.dmem = d.dmem)
    (hr : ∀ r ∈ [Reg64.rbp, .rbx, .r15, .r13], reg d' r = reg d r) :
    WHead m0 a c ch b pt lp t s6 j d' :=
  ⟨hb, hd ▸ h.mem, h.lt, (hr .rbp (by simp)).trans h.rbp,
    (hr .rbx (by simp)).trans h.rbx, (hr .r15 (by simp)).trans h.r15,
    (hr .r13 (by simp)).trans h.r13⟩

omit [Labels] in
theorem bits32 (x : BitVec 64) :
    (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 x) 63#64).toNat = x.toNat % 64 := by
  simp only [BinOp.apply, UnOp.apply, toNat_ext, BitVec.toNat_and, toNat_low,
    BitVec.toNat_ofNat]
  change ((x.toNat % 2 ^ 32) % 2 ^ 32 &&& (2 ^ 6 - 1)) = x.toNat % 64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

end

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {j k : Nat}

theorem weights_head (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    {d : MachineData} (h : WHead m0 a c ch b pt lp t s6 j d) {R : MachineState → Prop}
    (cont : ∀ d', WHead m0 a c ch b pt lp t s6 j d' →
      reg d' .rcx = BitVec.ofNat 64 (j / 64 % 5) →
      reg d' .rax = BitVec.ofNat 64 (5 * (j / 320)) →
      reg d' .rdi = BitVec.ofNat 64 (64 * alongRow j 4) →
      reg d' .rsi = BitVec.ofNat 64 (j % 64) →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b75Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b74Offset)⟩ := by
  have g := geo_of hpre
  have hwf := wf0 (pre_stack hpre) h.body (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g h.body hwf (blk hp b74_in_code (by simp [b74])) e74 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm' hpc hb _ ↦ ?_
  have hd : st.data.dmem = d.dmem := hm'.dmem_eq hwf rfl
  have hr : ∀ r ∈ [Reg64.rbp, .rbx, .r15, .r13], reg st.data r = reg d r :=
    keepR_regs hm' (by decide +kernel) fun _ ↦ rfl
  have hc : reg st.data .rcx = BitVec.ofNat 64 (j / 64 % 5) := by
    rw [show reg st.data .rcx = colS.eval _ from hm'.regs .rcx colS rfl, colS_eval]
    change idxCol (reg d .rbp) = _
    rw [h.rbp]
    exact (index_values h.lt).1
  have ha : reg st.data .rax = BitVec.ofNat 64 (5 * (j / 320)) := by
    rw [show reg st.data .rax = rowS.eval _ from hm'.regs .rax rowS rfl, rowS_eval]
    change idxRow (reg d .rbp) = _
    rw [h.rbp]
    exact (index_values h.lt).2.1
  have hv : fourS.eval (envB m0 d [] (fun _ ↦ 0) 0) = BitVec.ofNat 64 (64 * alongRow j 4) := by
    rw [fourS_eval _ h.r13]
    change idx4 (reg d .rbp) = _
    rw [h.rbp]
    exact (index_values h.lt).2.2.1
  have hdi : reg st.data .rdi = BitVec.ofNat 64 (64 * alongRow j 4) :=
    (hm'.regs .rdi fourS rfl).trans hv
  have hsi : reg st.data .rsi = BitVec.ofNat 64 (j % 64) := by
    rw [show reg st.data .rsi = _ from hm'.regs .rsi _ rfl]
    simp only [Sym.eval]
    apply BitVec.eq_of_toNat_eq
    rw [bits32]
    change (reg d .rbp).toNat % 64 = _
    rw [h.rbp, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hcond : (SBool.and (.not (.cmp .ult .W64 fourS (.lit 2047)))
      (.not (.cmp .eq .W64 fourS (.lit 2047)))).eval (envB m0 d [] (fun _ ↦ 0) 0) = false := by
    simp only [SBool.eval, Sym.eval, hv, CmpOp.apply, low_W64, BitVec.ult,
      BitVec.toNat_ofNat]
    have hl := alongRow_lt j 4 h.lt
    have hh : (64 * alongRow j 4) % 2 ^ 64 < 2047 := by omega
    simp only [show 2047 % 2 ^ 64 = 2047 from rfl, decide_eq_true hh, Bool.not_true,
      Bool.false_and]
  simp only [PcOk] at hpc
  change st.pc = if (SBool.and (.not (.cmp .ult .W64 fourS (.lit 2047)))
      (.not (.cmp .eq .W64 fourS (.lit 2047)))).eval (envB m0 d [] (fun _ ↦ 0) 0) = true
    then Labels.label NativeRustcVmX64.Vm.VerifyLayer.label_44 else Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b74Offset + b74.length) at hpc
  rw [hcond] at hpc
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc
  exact at_pc hpc (cont st.data (h.read hb hd hr) hc ha hdi hsi)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
