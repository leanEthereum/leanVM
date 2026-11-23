module

public import NativeRustcVmArm.Tables.TableWeights.Head

/-!
# `table_weights`: a coordinate of the loop

From the loop head with `c` coordinates done (`It c`, `.LTableWeights_4`): the factor
(`head_step`), the six multiplications (`first_step`, `mid_step` with `b4` to `b8`), then `b9`
back to the loop head with `c + 1` done or, the point done, to the exit (`last_step`); the whole
turn (`turn_step`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Vm.TableWeights
open NativeRustcVm (wordOf ewOf)

public section

variable {m0 : MachineData}

theorem mb4 : MidBlock 1 (after b4 midS) := by
  rw [after_eq run_b4]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩
theorem mb5 : MidBlock 2 (after b5 midS) := by
  rw [after_eq run_b5]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩
theorem mb6 : MidBlock 3 (after b6 midS) := by
  rw [after_eq run_b6]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩
theorem mb7 : MidBlock 4 (after b7 midS) := by
  rw [after_eq run_b7]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩
theorem mb8 : MidBlock 5 (after b8 midS) := by
  rw [after_eq run_b8]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩

theorem cond_lt {c : Nat} (hc : c < 2 ^ 64) (y : BitVec 64) :
    (BitVec.ofNat 64 c).ult y = decide (c < y.toNat) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem toBitVec_one_xor_zero : ((1 : UInt64) ^^^ 0).toBitVec = BitVec.ofNat 64 1 := rfl

variable [Host] {k : Nat}

/-- **The loop head**: the factor of coordinate `c`. -/
theorem head_step (hp : Placed code k) (hc : Ctx m0) {c : Nat} {m : MachineData}
    (hit : It m0 c m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b3Offset) ∧ Pre3 m0 c st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b10Offset)⟩ := by
  have hx := hc.ptc hit.lt
  have hwf := hc.wf_in hit.frm hx
  have hcn : c < 2 ^ 64 := Nat.lt_of_lt_of_le hit.lt (UInt64.toNat_lt _).le
  have hm : Match (Env.ofMachine m [(fb m0, 240), (rg m0 .X4 + BitVec.ofNat 64 (16 * c), 16)])
      headS m :=
    match_frame (rs := [(_, 16)]) (srs := [(16, false)]) (known := [(.X27, .ptr 1 0)])
      (aliases := []) hc.geo hit.frm ⟨rfl, fun h => absurd h (by decide), trivial⟩
      ⟨by simp [Sym.eval]; exact hit.x27, trivial⟩ trivial
  refine exec_then (hb10 hp) run_b10 hwf hm fun st1 hm1 hpc1 => ?_
  have hm1' : Match (Env.ofMachine m [(fb m0, 240), (rg m0 .X4 + BitVec.ofNat 64 (16 * c), 16)])
      (after b10 headS) st1.data := by rw [after_eq run_b10]; exact hm1
  have hd := hd_of hc hit hm1' headB_b10
  have h72 : fw m0 m 72 = rg m0 .X3 := hit.frm.slots (72, rg m0 .X3) (by simp [kslots])
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs, load_fw,
    h72] at hpc1
  rw [show (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 c from hit.x22, cond_lt hcn] at hpc1
  by_cases hlt : c < m0.regs.X3.toNat
  · -- the equality point's coordinate `c`
    simp only [show (rg m0 .X3).toNat = m0.regs.X3.toNat from rfl, hlt, decide_true,
      ↓reduceIte, lbl_2 hp] at hpc1
    have hy := hc.eq.sub (o := 16 * c) (l := 16) (by omega) (by omega)
    have hwfB := hc.wf_in hd.frm hy
    have hmB : Match (Env.ofMachine st1.data [(fb m0, 240), (rg m0 .X2 + BitVec.ofNat 64 (16 * c),
        16)]) eqS st1.data :=
      match_frame (rs := [(_, 16)]) (srs := [(16, false)]) (known := [(.X23, .ptr 1 8)])
        (aliases := []) hc.geo hd.frm ⟨rfl, fun h => absurd h (by decide), trivial⟩
        ⟨by
          simp only [Sym.eval, Env.base_ofMachine_eq]
          rw [show (8 : Int) = ((8 : Nat) : Int) from rfl]
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]
          rw [add_ofNat_ofInt, Nat.add_comm]
          exact hd.x23, trivial⟩ trivial
    refine exec_at (hb2 hp) run_b2 hwfB hpc1 hmB fun st2 hm2 hpc2 => .done _
      ⟨hpc2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableWeights.b2_next])), ?_⟩
    have hm2' : Match (Env.ofMachine st1.data [(fb m0, 240),
        (rg m0 .X2 + BitVec.ofNat 64 (16 * c), 16)]) (after b2 eqS) st2.data := by
      rw [after_eq run_b2]; exact hm2
    obtain ⟨hf2, hw2⟩ := keep_of hc hy hd.frm hd.w hm2' keepB_b2
    refine ⟨hd.lt, hf2, ?_, ?_, ?_, ?_, ?_, ?_, hw2⟩
    · rw [rg_keep hm2 (r := .X22) rfl]; exact hd.x22
    · rw [show rg st2.data .X23 = _ from hm2.regs .X23 _ rfl]
      simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      rw [show (8 : Int) = ((8 : Nat) : Int) from rfl, add_ofNat_ofInt, Nat.add_comm]
    · rw [rg_keep hm2 (r := .X27) rfl]; exact hd.x27
    · rw [rg_keep hm2 (r := .X24) rfl]; exact hd.x24
    · rw [show rg st2.data .X25 = _ from hm2.regs .X25 _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [hc.load_in hd.frm hy (by omega), fac_c0, UInt64.xor_comm, UInt64.toBitVec_xor]
      have := e_c hlt 0 (Or.inl rfl)
      simp only [↓reduceIte] at this
      rw [this]
      rfl
    · rw [show rg st2.data .X26 = _ from hm2.regs .X26 _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [hc.load_in hd.frm hy (by omega), fac_c1, UInt64.toBitVec_xor]
      have := e_c hlt 8 (Or.inr rfl)
      simp only [show (8 = 0) = False by decide, ↓reduceIte] at this
      rw [this, show (st1.data.regs.getXReg .X24).toBitVec = _ from hd.x24]
  · -- no equality coordinate: `b11`
    simp only [show (rg m0 .X3).toNat = m0.regs.X3.toNat from rfl, hlt, decide_false,
      Bool.false_eq_true, ↓reduceIte] at hpc1
    refine exec_at (hb11 hp) run_b11 hwf (hpc1.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableWeights.b10_next]))) hm1'
      fun st2 hm2 hpc2 => .done _ ⟨by rw [hpc2, lbl_3 hp], ?_⟩
    have hm2' : Match (Env.ofMachine m [(fb m0, 240), (rg m0 .X4 + BitVec.ofNat 64 (16 * c), 16)])
        (after b11 (after b10 headS)) st2.data := by
      rw [after_eq run_b11]; exact hm2
    have hd2 := hd_of hc hit hm2' headB_b11
    refine ⟨hd2.lt, hd2.frm, hd2.x22, hd2.x23, hd2.x27, hd2.x24, ?_, ?_, hd2.w⟩
    · rw [show rg st2.data .X25 = _ from hm2.regs .X25 _ rfl, fac_c0, E_getD_none hlt]
      exact toBitVec_one_xor_zero.symm
    · rw [show rg st2.data .X26 = _ from hm2.regs .X26 _ rfl, fac_c1, E_getD_none hlt]
      show (Env.ofMachine m _).load 1 8 8 = ((0 : UInt64) ^^^ (ch m0 c).c1).toBitVec
      rw [UInt64.zero_xor, hc.load_in hit.frm hx (by omega), ch_c1 hit.lt]

end

end NativeRustcVmArm.Tables.TableWeights
