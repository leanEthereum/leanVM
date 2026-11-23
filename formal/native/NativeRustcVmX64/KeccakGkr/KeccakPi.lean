module

public import NativeRustcVmX64.KeccakGkr.KeccakPi.Exec
public import NativeRustcVmX64.Field.Leaf
public import NativeRustcVmX64.Spec.KeccakGkr
import Mathlib.Tactic.IntervalCases
public import NativeRustcVmX64.Code.Vm.KeccakPi.Names

/-!
# `keccak_pi` on x86-64

`keccakPi_spec`: one straight-line block without memory accesses (`KeccakPi.Exec`); below `25`
the value it leaves in RAX is checked at each `i`.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakPi

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.KeccakPi
open LeanVM.Parameters

public section

/-- **`keccak_pi` meets its contract.** -/
theorem keccakPi_spec [Host] {k : Nat} (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost := by
  intro m hpre
  rw [show Labels.label NativeRustcVmX64.Vm.KeccakPi.entryLabel = Host.addrOf k from hp.label NativeRustcVmX64.Vm.KeccakPi.entry_at]
  have hk : b0.IsInfixAt Host.prog k :=
    (b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _) :)
  have hwf := frame_wf (m := m) (vars := fun _ ↦ 0) (ret := 0) hpre.1 fun _ h ↦ h
  refine exec_then hk r.run hwf (by rw [exit_eq]; nofun) match_frame fun st hm hpc ↦ ?_
  rw [exit_eq] at hpc
  obtain ⟨hpc, hsp, -, hsv⟩ := leaf_done hpre.1 hm hpc rsp_eq keeps_eq
    (by rw [mem_eq]; nofun)
  refine .done _ ⟨hpc, hsp, ?_, hm.dmem_eq hwf mem_eq, hsv⟩
  have hx : (m.regs.get64 .rdi).toNat < 25 := hpre.2
  show (st.data.regs.get64 .rax).toNat = keccakPi (m.regs.get64 .rdi).toNat
  rw [hm.regs .rax _ rax_eq]
  simp only [piS, rS, hS, cS, qS]
  sym_simp
  simp only [Env.ofMachine_regs]
  generalize m.regs.get64 .rdi = x at hx ⊢
  obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, n < 2 ^ 64 ∧ x = BitVec.ofNat 64 n :=
    ⟨x.toNat, x.isLt, by simp⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hx ⊢
  interval_cases n <;> decide

end

end NativeRustcVmX64.KeccakGkr.KeccakPi
