module

public import NativeRustcVmArm.Code.Vm.KeccakPi.Names
public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.KeccakPi
public import NativeRustcVmArm.Spec.KeccakGkr
meta import NativeRustcVmArm.Code.Vm.KeccakPi
import Mathlib.Tactic.IntervalCases

/-!
# `keccak_pi` meets its contract

One straight-line block without memory accesses: `i / 5` by a 32-bit multiplication by `205`
(exact below `25`), `(2 (i % 5) + 3 (i / 5)) % 5` by a multiply-high by `⌈2^66 / 5⌉`. Below `25`
the value is checked at each `i`.
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakPi

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.KeccakPi
open LeanVM.Parameters

set_option Elab.async false

sym_block run0 := exec b0 (init [] .sp)

public section

theorem keccakPi_spec [NativeRustcArm.Host] {k : Nat} (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost := by
  intro m hpre
  have hl : Labels.label NativeRustcVmArm.Vm.KeccakPi.entryLabel = NativeRustcArm.Host.addrOf k := hp.label (j := NativeRustcVmArm.Vm.KeccakPi.entryOffset) NativeRustcVmArm.Vm.KeccakPi.entry_at
  rw [hl]
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run0 (Env.wf_nil m) (match_nil m)
    fun st hm hpc => .done _ ⟨?_, ?_, hm.dmem_eq (Env.wf_nil _) rfl,
      Match.saved (match_nil _) hm (Env.wf_nil _) rfl rfl⟩
  · have h30 : st.data.regs.getXReg .X30 = m.regs.getXReg .X30 :=
      Match.reg_eq (match_nil _) hm rfl rfl
    simp only [PcOk] at hpc
    rw [hpc]
    unfold retOf
    rw [show st.data.regs.X30 = m.regs.X30 from h30]
  · have h := hm.regs .X0 _ rfl
    show (st.data.regs.getXReg .X0).toBitVec.toNat = keccakPi (m.regs.getXReg .X0).toBitVec.toNat
    have hx : (m.regs.getXReg .X0).toBitVec.toNat < 25 := hpre
    rw [h]
    sym_simp
    simp only [Env.ofMachine_regs]
    generalize (m.regs.getXReg .X0).toBitVec = x at hx ⊢
    obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, n < 2 ^ 64 ∧ x = BitVec.ofNat 64 n :=
      ⟨x.toNat, x.isLt, by simp⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hx ⊢
    interval_cases n <;> decide

end

end NativeRustcVmArm.KeccakGkr.KeccakPi
