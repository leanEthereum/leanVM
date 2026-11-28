module

public import NativeRustcX64.Code.Common.KeccakF.Names
public import NativeRustcX64.Rodata.Names

public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Common.KeccakF
public meta import NativeRustcX64.Code.Common.KeccakF

/-!
# The executor on `keccak_f`'s round loop

The loop body of rustc's x86-64 `keccak_f` (`NativeRustcX64.Common.KeccakF.b1`) computes two
rounds, with stack traffic below and above RSP and memory operands in `xor`. Region 0 is its
stack frame (RSP at offset 128), region 1 the round-constant table, and stack offset 176 holds
the next round's constant offset.
-/

namespace NativeRustcX64.Sym.Test.Keccak

set_option Elab.async false

open NativeRustcX64.Common.KeccakF


/-- Before rounds `i` and `i + 1`: RSP at offset 128, the saved counter `8 * i + 8`. -/
def atRound (i : Nat) : SState :=
  { init [296, 192] [(.rsp, .ptr 0 128)] [(NativeRustcX64.roundConstantsLabel, 1)] with
    known := [⟨0, 176, 8, .lit (8 * i + 8)⟩] }

sym_block round0_exec := exec b1 (atRound 0)

sym_block round22_exec := exec b1 (atRound 22)

/-- The first pair of rounds loops back, the last falls out. -/
example : (exec b1 (atRound 0)).map (·.2) = some (.cond (.lit true) NativeRustcX64.Common.KeccakF.label_1) := by
  rw [round0_exec]
  rfl

example : (exec b1 (atRound 22)).map (·.2) = some (.cond (.lit false) NativeRustcX64.Common.KeccakF.label_1) := by
  rw [round22_exec]
  rfl

/-- The machine runs a pair of rounds from any state `atRound i` describes, to the state the executor
computed. -/
theorem round0_spec [Host] {k : Nat} (hk : b1.IsInfixAt Host.prog k) {env : Env}
    (hwf : env.WF) {m : MachineData} (hm : Match env (atRound 0) m) :
    Eventually (step1 Host.exe) (fun st =>
      Match env ((exec b1 (atRound 0)).map (·.1) |>.getD (atRound 0)) st.data ∧
      st.pc = Labels.label NativeRustcX64.Common.KeccakF.label_1) ⟨m, Host.addrOf k⟩ := by
  refine NativeRustcX64.Eventually.mono (exec_sound hk round0_exec hwf nofun hm)
    fun st ⟨hm', hpc⟩ => ⟨by rw [round0_exec]; exact hm', ?_⟩
  simp only [PcOk, SBool.eval, ite_true] at hpc
  exact hpc

end NativeRustcX64.Sym.Test.Keccak
