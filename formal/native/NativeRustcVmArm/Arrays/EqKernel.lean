module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Arrays.EqKernel.Loop

/-!
# `eq_kernel` on AArch64

**`eqKernel_spec`**: rustc's `eq_kernel(point, out)`, placed anywhere in the program, meets
`EqKernelPre`/`EqKernelPost` given `EW::mul`'s contract. When `|out| < 2^|point|` it returns `None`
at once (`b0`, `b1`). Else the prologue (`b2`) saves the callee-saved registers in its 112-byte
frame and stores `out[0] = 1`; at `|point| = 0` the epilogue (`b13`) returns. Else `b3` stores the
size and `point`'s end at `[sp]`, `[sp, #8]` (`Frame`) and each round `i` (`OInv`: `out` holds the
kernel `K i` of the first `i` coordinates) loads `r = point[i]` (`b5`-`b7`) and runs over the
`2^i` pairs (`IInv`, `b8`, `EW::mul`, `b9`): `out[2^i + j] = K[j]·r`, `out[j] = K[j] + K[j]·r`.
After the last round (`RInv`, `b10`, `b4`) `b12` loads the size and the epilogue returns it.
-/

namespace NativeRustcVmArm.Arrays.EqKernel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.EqKernel NativeVm.Model
open NativeRustcVm (EWsAt)

public section

variable [Host] {k : Nat}

/-- **A round's end** (`b10`, `b4`): the next coordinate, or out of the loop and returned. -/
theorem next (hp : Placed code k) {m0 : MachineData} (hpre : EqKernelPre m0)
    (hle : 2 ^ np m0 ≤ len m0) {i : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b10Offset))
    (hR : RInv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b5Offset) ∧ OInv m0 (i + 1) s'.data)) s := by
  obtain ⟨hS, h64, ⟨⟨hmP, hnP⟩, hoP⟩, ⟨⟨hmO, hnO⟩, hoO⟩, hap⟩ := id hpre
  have hnP' : (pt m0).toNat + 16 * np m0 ≤ 2 ^ 64 := hnP
  have hlt := hR.lt
  refine exec_at (hb10 hp) run_b10 (Env.wf_nil _) hpc (match_nil _) fun s1 hm1 hpc1 ↦ ?_
  have bd1 := hR.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b10 ▸ b10_keeps)
  have hdm1 : s1.data.dmem = s.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have e1 : ∀ r, s1.data.regs.getXReg r = s.data.regs.getXReg r := fun r ↦ by
    cases r <;> exact Match.reg_eq (match_nil _) hm1 rfl rfl
  simp only [PcOk] at hpc1
  obtain ⟨hwf, hm⟩ := bd1.exit_match hS (by decide) rfl
  refine exec_at (hb4 hp) run_b4 hwf (hpc1.trans (lbl_4 hp)) hm fun s2 hm2 hpc2 ↦ ?_
  have bd2 := bd1.of_block hm hm2 hwf rfl (after_eq run_b4 ▸ b4_keeps)
  have hdm2 : s2.data.dmem = s.data.dmem := (hm2.dmem_eq hwf rfl).trans hdm1
  have hf1 : Frame m0 s1.data := hR.frame.of_dmem hdm1
  have hend : (frameEnv m0 s1.data 112).load 0 8 8 = pt m0 + BitVec.ofNat 64 (16 * np m0) :=
    load_word hf1.pend
  have e2 : ∀ r ∈ [XReg.X20, .X27], s2.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (Match.reg_eq hm hm2 rfl rfl).trans (e1 _)
  have x22 : (s2.data.regs.getXReg .X22).toBitVec = pt m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
    have h := hm2.regs .X22 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs, BinOp.apply, Sym.low_W64, Sym.ext_W64] at h
    rw [h, e1, show s.data.regs.getXReg .X22 = s.data.regs.X22 from rfl, hR.x22,
      show 16 * (i + 1) = 16 * i + 16 by omega, NativeRustcVm.addr_add]
  have x29 : (s2.data.regs.getXReg .X29).toNat = 2 ^ (i + 1) := by
    have h := hm2.regs .X29 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs, lsl1] at h
    show (s2.data.regs.getXReg .X29).toBitVec.toNat = _
    rw [h, e1, BitVec.toNat_ofNat, show (s.data.regs.getXReg .X29).toBitVec.toNat = 2 ^ i from hR.x29,
      Nat.pow_succ]
    have h64' : np m0 < 64 := h64
    have := Nat.pow_lt_pow_right (a := 2) (by decide) (show i + 1 < 64 by omega)
    rw [Nat.pow_succ] at this
    omega
  simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b4_length, NativeRustcVmArm.Vm.EqKernel.b4Length] at hpc2
  sym_simp at hpc2
  have hpc2' := pc_cond hpc2
  have hc : ((frameEnv m0 s1.data 112).regs .X22 + 16#64 == (frameEnv m0 s1.data 112).load 0 8 8)
      = true ↔ i + 1 = np m0 := by
    rw [hend, beq_iff_eq]
    show (s1.data.regs.getXReg .X22).toBitVec + 16#64 = _ ↔ _
    rw [e1, show s.data.regs.getXReg .X22 = s.data.regs.X22 from rfl, hR.x22]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
      omega
    · intro h
      rw [← h, show 16 * (i + 1) = 16 * i + 16 by omega, NativeRustcVm.addr_add]
  have hdm2' : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf rfl
  by_cases hlast : i + 1 = np m0
  · refine Eventually.mono (finish12 hp hpre hle ((hpc2'.1 (hc.mpr hlast)).trans (lbl_10 hp)) bd2
      (hf1.of_dmem hdm2') ?_) fun _ h ↦ Or.inl h
    rw [hdm2, ← hlast]
    exact hR.ker
  · refine .done _ (Or.inr ⟨hpc2'.2 (fun h ↦ hlast (hc.mp h)), bd2, hf1.of_dmem hdm2', by omega,
      x29, x22, ?_, ?_, by rw [hdm2]; exact hR.ker⟩)
    · show s2.data.regs.getXReg .X20 = _
      rw [e2 .X20 (by simp)]; exact hR.x20
    · show (s2.data.regs.getXReg .X27).toBitVec = _
      rw [e2 .X27 (by simp)]; exact hR.x27

/-- **`eq_kernel` meets its contract.** -/
theorem eqKernel_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hS, h64, ⟨⟨hmP, hnP⟩, hoP⟩, ⟨⟨hmO, hnO⟩, hoO⟩, hap⟩ := id hpre
  have hnO' : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have hc : (m0.regs.getXReg .X3).toBitVec.ult
      (1#64 <<< ((m0.regs.getXReg .X1).toBitVec.toNat % RegWidth.W64.bits)) =
      decide (len m0 < 2 ^ np m0) := by
    simp only [BitVec.ult, one_shl_toNat (m0.regs.getXReg .X1).toBitVec h64]
    rfl
  by_cases hle : 2 ^ np m0 ≤ len m0
  · have h112 : 112 ≤ eqKernelStack := by decide
    obtain ⟨hmF, hnF, heF⟩ := frame_ok hS h112
    have h16 : 16 ≤ 16 * m0.regs.X3.toNat := by
      have := Nat.one_le_two_pow (n := np m0); have : 2 ^ np m0 ≤ m0.regs.X3.toNat := hle; omega
    have hwf : (Env.ofMachine m0 [(fb m0, 112), (out m0, 16)]).WF := by
      refine Env.wf_of ⟨⟨hmF, hnF⟩, ⟨fun j hj ↦ hmO j (by omega), by
        have : 16 ≤ 16 * len m0 := h16
        show (out m0).toNat + 16 ≤ 2 ^ 64; omega⟩, trivial⟩ ?_
      refine List.Pairwise.cons ?_ (List.Pairwise.cons nofun .nil)
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      have hSle : eqKernelStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
      have hoO' : (out m0).toNat + 16 * len m0 ≤ (stackBelow m0 eqKernelStack).toNat ∨
          (stackBelow m0 eqKernelStack).toNat + eqKernelStack ≤ (out m0).toNat := hoO
      unfold stackBelow at hoO'
      rw [toNat_sub_ofNat hSle, eqKernelStack_eq] at hoO'
      rw [eqKernelStack_eq] at hSle
      show (m0.regs.SP.toBitVec - BitVec.ofNat 64 112).toNat + 112 ≤ (out m0).toNat ∨
        (out m0).toNat + 16 ≤ (m0.regs.SP.toBitVec - BitVec.ofNat 64 112).toNat
      rw [heF]
      omega
    have hm : Match (Env.ofMachine m0 [(fb m0, 112), (out m0, 16)]) entryS m0 :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h112 rfl, rfl, nofun, trivial⟩
        (by
          show _ = fb m0 + BitVec.ofInt 64 112
          rw [show BitVec.ofInt 64 112 = BitVec.ofNat 64 112 from rfl, BitVec.sub_add_cancel])
        ⟨(BitVec.add_zero _).symm, trivial⟩ trivial trivial trivial
    refine exec_then (hb0 hp) run_b0e hwf hm fun s1 hm1 hpc1 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b0_length, NativeRustcVmArm.Vm.EqKernel.b0Length] at hpc1
    sym_simp at hpc1
    have hpc1 := (pc_cond hpc1).1 (by simp only [Env.ofMachine_regs, hc]; simpa using hle)
    refine exec_at (hb2 hp) (exec_after run_b0e run_b2) hwf (hpc1.trans (lbl_2 hp)) hm1
      fun s2 hm2 hpc2 ↦ ?_
    obtain ⟨⟨hsp2, hx0_2, hw2, hr2, hmem2, ho0, ho8⟩, hx8_2⟩ := after_eq run_b2 ▸ S2_ok
    have hin : ∀ p, InRange (out m0) 16 p → InRange (out m0) (16 * len m0) p := fun p h ↦
      inRange_mono (c := 0) (by rwa [add_ofNat_zero]) (by omega)
    have bd2 : B m0 s2.data := Body.of_entry2 hS h112 hwf hm2 hsp2 hw2 hr2 hmem2 hin
    have hx8v : (s2.data.regs.getXReg .X8).toNat = 2 ^ np m0 := by
      have h := hm2.regs .X8 _ hx8_2
      show (s2.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [h, size_eval h64, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h64)
    simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b2_length, NativeRustcVmArm.Vm.EqKernel.b2Length] at hpc2
    sym_simp at hpc2
    have hpc2' := pc_cond hpc2
    by_cases hz : np m0 = 0
    · have hpc2 := hpc2'.1 (by
        simp only [Env.ofMachine_regs, beq_iff_eq]; exact BitVec.eq_of_toNat_eq hz)
      refine finish13 hp hpre hle (hpc2.trans (lbl_11 hp)) bd2 hx8v ?_
        (by rw [hz]; exact out0_of hm2 ho0 ho8)
      rw [show s2.data.regs.X0 = s2.data.regs.getXReg .X0 from rfl, reg_of hm2 hx0_2]
      rfl
    · have hpc2 := hpc2'.2 (by
        simp only [Env.ofMachine_regs, beq_iff_eq]; exact fun h ↦ hz (congrArg BitVec.toNat h))
      refine exec_at (hb3 hp) (exec_after run_b2 run_b3) hwf hpc2 hm2 fun s3 hm3 hpc3 ↦ ?_
      obtain ⟨⟨hsp3, hx0_3, hw3, hr3, hmem3, ho0', ho8'⟩, hsz3, hend3, h20, h22, h27, h29⟩ :=
        after_eq run_b3 ▸ S3_ok
      have bd3 : B m0 s3.data := Body.of_entry2 hS h112 hwf hm3 hsp3 hw3 hr3 hmem3 hin
      have hf3 : Frame m0 s3.data := by
        have a0 := BufEW.wordAt_of_writeSym hm3 (r := 0) (o := 0) rfl (by decide) hsz3
        have a1 := BufEW.wordAt_of_writeSym hm3 (r := 0) (o := 8) rfl (by decide) hend3
        rw [add_ofNat_zero, size_eval h64] at a0
        rw [end_eval] at a1
        exact ⟨a0, a1⟩
      have hI0 : OInv m0 0 s3.data := by
        refine ⟨bd3, hf3, Nat.pos_of_ne_zero hz, ?_, ?_, ?_, ?_, out0_of hm3 ho0' ho8'⟩
        · rw [show s3.data.regs.X29 = s3.data.regs.getXReg .X29 from rfl, reg_of hm3 h29]
          rfl
        · have h := hm3.regs .X22 _ h22
          simp only [Sym.eval, Env.ofMachine_regs] at h
          rw [Nat.mul_zero, add_ofNat_zero]
          exact h
        · rw [show s3.data.regs.X20 = s3.data.regs.getXReg .X20 from rfl, reg_of hm3 h20]
          simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec]
          rfl
        · have h := hm3.regs .X27 _ h27
          simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.map_some, Option.getD_some] at h
          exact h
      simp only [PcOk] at hpc3
      refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b5Offset) ∧ ∃ i, np m0 - i = n ∧
        OInv m0 i s.data) (fun _ s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc3.trans (lbl_5 hp), 0, rfl, hI0⟩
      refine Eventually.bind (round hp hpre hle hpc hI) fun s1 ⟨hpc1, hI1⟩ ↦ ?_
      refine Eventually.bind (inner hp hmul hpre hle hpc1 hI1) fun s2 ⟨hpc2, hR⟩ ↦ ?_
      refine Eventually.mono (next hp hpre hle hpc2 hR) fun s' h ↦ ?_
      rcases h with h | ⟨hpc', hI'⟩
      · exact Or.inl h
      · exact Or.inr ⟨np m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩
  · refine exec_then (hb0 hp) run_b0 (Env.wf_nil _) (match_nil _) fun s1 hm1 hpc1 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.EqKernel.b0_length, NativeRustcVmArm.Vm.EqKernel.b0Length] at hpc1
    sym_simp at hpc1
    have hpc1 := (pc_cond hpc1).2 (by simp only [Env.ofMachine_regs, hc]; simpa using hle)
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) (Env.wf_nil _) hpc1 hm1
      fun s2 hm2 hpc2 ↦ .done _ ?_
    obtain ⟨hk, hmem, hx0⟩ := after_eq run_b1 ▸ b1_keeps
    refine ⟨?_, ?_, fun p _ ↦ by rw [hm2.dmem_eq (Env.wf_nil _) hmem]; rfl,
      Match.saved (match_nil _) hm2 (Env.wf_nil _) rfl hk⟩
    · simp only [PcOk] at hpc2
      rw [hpc2]
      simp only [retOf]
      rw [show s2.data.regs.X30 = m0.regs.X30 from Match.reg_eq (r := .X30) (match_nil _) hm2 rfl rfl]
    · simp only [hle, ↓reduceIte]
      rw [show s2.data.regs.X0 = s2.data.regs.getXReg .X0 from rfl, reg_of hm2 hx0]
      rfl

end

end NativeRustcVmArm.Arrays.EqKernel
