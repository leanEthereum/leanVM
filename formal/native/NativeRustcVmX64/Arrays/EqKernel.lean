module

public import NativeRustcVmX64.Arrays.EqKernel.Loop
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `eq_kernel` on x86-64

**`eqKernel_spec`**: rustc's `eq_kernel(point, out)`, placed anywhere in the program, meets
`EqKernelPre`/`EqKernelPost` given `EW::mul`'s contract. The prologue (`b0`) pushes the six
callee-saved registers, opens its 56-byte frame, stores `point` there and compares `|out|` with
`2^|point|` (`shl` by CL: `|point| < 64`). Below, it returns `None` (`b1`, `b14`). Else `b2`
stores `out[0] = 1`; at `|point| = 0` the epilogue (`b14`) returns `Some(1)`. Else `b3` stores the
size, `point`'s end and `|out|` in the frame (`Loc`) and each round `i` (`OInv`: `out` holds the
kernel `K i` of the first `i` coordinates) loads `r = point[i]` into the frame (`b6`-`b8`) and runs
over the `2^i` pairs (`IInv`, `b9`, `EW::mul`, `b10`): `out[2^i + j] = K[j]·r`,
`out[j] = K[j] + K[j]·r`. After the last round (`RInv`, `b11`, `b5`) the epilogue (`b13`, `b14`)
returns the size.
-/

namespace NativeRustcVmX64.Arrays.EqKernel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EqKernel NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (EWsAt)

public section

theorem shiftCount_of_lt (y : BitVec 64) (h : y.toNat < 64) : shiftCount .W64 y = y.toNat := by
  unfold shiftCount shiftMask
  rw [toNat_low, show Width.W8.bits = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)

/-- `1 << y`, `y < 64`. -/
theorem one_shl (y : BitVec 64) (hy : y.toNat < 64) :
    BinOp.apply .shl .W64 (BitVec.ofNat 64 1) y = BitVec.ofNat 64 (2 ^ y.toNat) := by
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount_of_lt y hy]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ofNat_toNat_lt (by decide), Nat.one_mul,
    ofNat_toNat_lt (Nat.pow_lt_pow_right (by decide) hy)]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hy)

variable [Host] {k : Nat}

/-- **`eq_kernel` meets its contract.** -/
theorem eqKernel_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hpre' := hpre
  obtain ⟨hS, h64, hP, hO, hap⟩ := hpre
  have hL : len m0 = (reg m0 .rcx).toNat := rfl
  have hN : np m0 = (reg m0 .rsi).toNat := rfl
  have hnO : NoWrap (out m0) (16 * len m0) := hO.1.2
  have hlen := lt_of_offStack hO.1.2 hO.2
  have hp64 : 2 ^ np m0 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h64
  have h112 : 112 ≤ eqKernelStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h112)
    fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 112) (frameS 112) m0 := match_frame
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) hm fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hw0, hmem0, hsp0, hw08, hax0, hdx0, hcx0, hr80, hr150⟩ := after_eq run_b0 ▸ b0_facts
  have hdx1 : reg s1.data .rdx = BitVec.ofNat 64 (2 ^ np m0) := by
    rw [show reg s1.data .rdx = _ from hm1.regs .rdx _ hdx0]
    exact one_shl _ h64
  simp only [PcOk, NativeRustcVmX64.Vm.EqKernel.b0_length] at hpc1
  rw [eval_not, eval_cmp_ult, eval_reg,
    show (Sym.bin .shl .W64 (.lit 1) (.reg .rsi)).eval (frameEnv m0 m0 112) =
      BitVec.ofNat 64 (2 ^ np m0) from one_shl _ h64,
    show (frameEnv m0 m0 112).regs .rcx = reg m0 .rcx from rfl, ofNat_toNat_lt hp64] at hpc1
  obtain ⟨hT, hFl⟩ := pc_cond hpc1
  by_cases hle : 2 ^ np m0 ≤ len m0
  swap
  · -- `None`.
    have hpc1 := hFl (by simp; omega)
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf (by intro l h; cases h) hpc1 hm1
      fun s2 hm2 hpc2 ↦ ?_
    obtain ⟨hw1, hmem1, hsp1, hax1⟩ := after_eq run_b1 ▸ b1_facts
    have hb : B m0 s2.data := Body.of_entry hS h112 hm2 hsp1 hw1
      (by rw [freeRegs_slots]; intro r h; cases h) hmem1
    simp only [PcOk] at hpc2
    refine exec_at (hb14 hp) run_b14 (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h112)
      (by intro l h; cases h) (hpc2.trans (lbl_11 hp)) hb.mid_match fun s3 hm3 hpc3 ↦ .done _ ?_
    obtain ⟨hres, hmem, hax, -⟩ := after_eq run_b14 ▸ b14_facts
    obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h112 hm3 hpc3 hres hmem
      (ret_not_in hS hO.1.2 hO.2)
    refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
    split
    · rename_i hn; exact absurd hn hle
    · rw [show reg s3.data .rax = _ from hm3.regs .rax _ hax, eval_reg]
      exact hm2.regs .rax _ hax1
  -- `out[0] = 1`
  have hpc1 := (hT (by simp; omega)).trans (lbl_2 hp)
  have hb1 : B m0 s1.data := Body.of_entry hS h112 hm1 hsp0 hw0
    (by rw [freeRegs_slots]; intro r h; cases h) hmem0
  have h0 : 0 < len m0 := lt_of_lt_of_le (Nat.two_pow_pos _) hle
  obtain ⟨hwf2, hm2⟩ := hb1.at_elem (ret := 0) hS h112 hO.1 hO.2 h0 (x := .reg .r15) (o := 0) (by
    rw [eval_reg]
    show reg s1.data .r15 = _
    rw [show reg s1.data .r15 = _ from hm1.regs .r15 _ hr150, eval_reg]
    simp)
  refine exec_at (hb2 hp) run_b2 hwf2 (by intro l h; cases h) hpc1 hm2 fun s2 hm2' hpc2 ↦ ?_
  obtain ⟨hk2, hw2, hw2a, hw2b⟩ := after_eq run_b2 ▸ b2_facts
  have bd2 : B m0 s2.data := hb1.of_store hwf2 hm2 hm2' (keepsRegs_rsp hk2) hw2
    (fun p h ↦ in_out hnO h0 h) (fun p hp ↦ (slots_ok p hp).2)
  have e2 := regs_eq_of hm2 hm2' hk2
  have ker0 : EWsAt s2.data.dmem (out m0) (K m0 0) := by
    rw [K_zero, NativeRustcVm.ewsAt_singleton]
    have a := ewAt_of_writes hm2' (r := 1) (o := 0) rfl (by decide) hw2a hw2b
    rw [add_ofNat_zero, Nat.mul_zero, add_ofNat_zero] at a
    exact a
  have ptw1 : NativeRustcVm.WordAt s1.data.dmem (fb m0 + BitVec.ofNat 64 8)
      (UInt64.ofBitVec (pt m0)) := by
    have a := fw_write hm1 (by decide) hw08
    rw [eval_reg] at a
    exact a
  have ptw2 : NativeRustcVm.WordAt s2.data.dmem (fb m0 + BitVec.ofNat 64 8)
      (UInt64.ofBitVec (pt m0)) := by
    refine fw_congr ptw1 fun t _ h2 ↦ same01 hm2' hwf2 (k0 := 0) (k1 := 16) (by decide) le_rfl
      (fun w hw ↦ Or.inr (hw2 w hw)) _ (by unfold InRange; omega)
      (fun h ↦ frame_not_out hpre' (show t < 120 by omega) (in_out hnO h0 h))
  have hcx2 : reg s2.data .rcx = reg m0 .rsi :=
    (e2 .rcx (by simp)).trans ((hm1.regs .rcx _ hcx0).trans (eval_reg _))
  simp only [PcOk, NativeRustcVmX64.Vm.EqKernel.b2_length] at hpc2
  rw [eval_test, eval_reg, show (elemEnv m0 s1.data 112 (out m0) 0).regs .rcx = reg s1.data .rcx
    from rfl, ← e2 .rcx (by simp), hcx2, beq_ofNat _ (by decide)] at hpc2
  obtain ⟨hT2, hF2⟩ := pc_cond hpc2
  by_cases hz : np m0 = 0
  · -- `|point| = 0`: `Some(1)`.
    have hpc2 := (hT2 (decide_eq_true hz)).trans (lbl_11 hp)
    refine exec_at (hb14 hp) run_b14 (bd2.wf (vars := fun _ ↦ 0) (ret := 0) hS h112)
      (by intro l h; cases h) hpc2 bd2.mid_match fun s3 hm3 hpc3 ↦ .done _ ?_
    obtain ⟨hres, hmem, hax, hdx⟩ := after_eq run_b14 ▸ b14_facts
    obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := bd2.done hS h112 hm3 hpc3 hres hmem
      (ret_not_in hS hO.1.2 hO.2)
    refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact bd2.same p hp', hsaved⟩
    split
    rotate_left
    · rename_i hn; exact absurd hle hn
    refine ⟨?_, ?_, ?_⟩
    · rw [show reg s3.data .rax = _ from hm3.regs .rax _ hax, eval_reg]
      show reg s2.data .rax = _
      rw [e2 .rax (by simp)]
      exact hm1.regs .rax _ hax0
    · rw [show reg s3.data .rdx = _ from hm3.regs .rdx _ hdx, eval_reg]
      show (reg s2.data .rdx).toNat = _
      rw [e2 .rdx (by simp), hdx1, ofNat_toNat_lt hp64]
    · rw [hdm, ← K_np, hz]; exact ker0
  -- `|point| ≥ 1`: the locals, the rounds
  have hpc2 := hF2 fun h ↦ hz (of_decide_eq_true h)
  have hwf3 := bd2.wf (vars := fun _ ↦ 0) (ret := 0) hS h112
  refine exec_at (hb3 hp) run_b3 hwf3 (by intro l h; cases h) hpc2 bd2.mid_match
    fun s3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hw3, hdx3, hr153, o8, w16, w32, w40⟩ := after_eq run_b3 ▸ b3_facts
  have bd3 := bd2.of_frame (L := 64) hS h112 hwf3 bd2.mid_match hm3 (keepsRegs_rsp hk3) hw3
    (by decide) slots_ok
  have e3 := regs_eq_of bd2.mid_match hm3 hk3
  have hr82 : reg s2.data .r8 = reg m0 .rcx :=
    (e2 .r8 (by simp)).trans ((hm1.regs .r8 _ hr80).trans (eval_reg _))
  have loc3 : Loc m0 s3.data.dmem 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Nat.mul_zero, add_ofNat_zero]
      exact fw_keep hm3 (by decide) o8 ptw2
    · have a := fw_write hm3 (by decide) w16
      rwa [eval_reg, show (frameEnv m0 s2.data 112).regs .rdx = reg s2.data .rdx from rfl,
        e2 .rdx (by simp), hdx1] at a
    · have a := fw_write hm3 (by decide) w32
      rwa [eval_add, eval_load, load_fw ptw2, eval_shl_lit _ (by decide), eval_reg,
        show (frameEnv m0 s2.data 112).regs .rcx = reg s2.data .rcx from rfl, hcx2,
        UInt64.toBitVec_ofBitVec, shl4_toNat _ (by omega)] at a
    · have a := fw_write hm3 (by decide) w40
      rwa [eval_reg, show (frameEnv m0 s2.data 112).regs .r8 = reg s2.data .r8 from rfl,
        hr82] at a
  simp only [PcOk] at hpc3
  have hI0 : OInv m0 0 s3.data := by
    refine ⟨bd3, loc3, Nat.pos_of_ne_zero hz, hm3.regs .rdx _ hdx3, ?_, ?_, ?_⟩
    · exact (e3 .r8 (by simp)).trans hr82
    · rw [show reg s3.data .r15 = _ from hm3.regs .r15 _ hr153, eval_add, eval_lit, eval_reg,
        show (frameEnv m0 s2.data 112).regs .r15 = reg s2.data .r15 from rfl,
        e2 .r15 (by simp), show reg s1.data .r15 = _ from hm1.regs .r15 _ hr150, eval_reg,
        BitVec.add_comm]
      rfl
    · exact ews_kept hpre' hm3 hwf3 hw3 (by rw [K_zero]; simp; omega) ker0
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqKernel.b6Offset) ∧ ∃ i, np m0 - i = n ∧ OInv m0 i s.data)
    (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc3.trans (lbl_4 hp), 0, rfl, hI0⟩
  refine Eventually.bind (start hp hpre' hle hpc hI) fun s1 ⟨hpc1, hI1⟩ ↦
    Eventually.bind (inner hp hmul hpre' hle hpc1 hI1) fun s2 ⟨hpc2, hR⟩ ↦
      Eventually.mono (next hp hpre' hle hpc2 hR) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨np m0 - (i + 1), by have := hI'.lt; have := hI.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.EqKernel
