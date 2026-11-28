module

public import NativeRustcArm.Code.Common.KeccakF.Names
public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Common.KeccakF
public meta import NativeRustcArm.Code.Common.KeccakF

/-!
# The executor on `keccak_f`'s round loop

The loop body of rustc's `keccak_f`, ingested from its assembly, runs from a state with its
stack frame as region 0, the round-constant table as region 1, and the round counter X17 a
literal or a variable with a bound.
-/

namespace NativeRustcArm.Sym.Test.Keccak

set_option Elab.async false

open NativeRustcArm.Common.KeccakF


/-- The state at the loop head of round `i`: SP the stack frame's base (region 0), X17 `8 * i`. -/
def start (i : Nat) : SState :=
  init [(192, true), (192, false)] (.ptr 0 0) [(.X17, .lit (8 * i))] [(NativeRustcArm.roundConstantsLabel, 1)]

sym_block round0 := exec b1 (start 0)

sym_block round23 := exec b1 (start 23)

/-- The state at the loop head of any round: X17 the variable 0, below 185. -/
def startAny : SState :=
  init [(192, true), (192, false)] (.ptr 0 0) [(.X17, .var 0)] [(NativeRustcArm.roundConstantsLabel, 1)] [(.var 0, 185)]

sym_block roundAny := exec b1 startAny

/-- The round constant: the table's word at X17. -/
example : (exec b1 startAny).map (·.1.mem.length) = some 11 := by
  rw [roundAny]
  rfl

open NativeRustcArm in
/-- After round 0 the loop branches back, X17 is 8, and X12 (lane `A[2][1]`'s new value, before
the next round's `θ`) is the plain BitVec expression of `χ ∘ π ∘ ρ ∘ θ` over the registers and
stack slots at the loop head. -/
theorem round0_spec [Host] {k : Nat} (hk : b1.IsInfixAt Host.prog k) {env : Env}
    (hwf : env.WF) {m : MachineData} (hm : Match env (start 0) m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Labels.label NativeRustcArm.Common.KeccakF.label_1 ∧
      (st.data.regs.getXReg .X17).toBitVec = 8#64 ∧
      (st.data.regs.getXReg .X12).toBitVec =
        ((env.load 0 56 8 ^^^ (env.regs .X8 ^^^ (env.regs .X0).rotateRight 63)).rotateRight 36 &&&
            ~~~(env.regs .X16 ^^^ (env.regs .X30 ^^^ (env.regs .X15).rotateRight 63)).rotateRight 3) ^^^
          (env.regs .X19 ^^^ (env.regs .X28 ^^^ (env.regs .X8).rotateRight 63)).rotateRight 19)
      ⟨m, Host.addrOf k⟩ := by
  refine NativeRustcArm.Eventually.mono (exec_sound hk round0 hwf hm) fun st ⟨hm', hpc⟩ =>
    ⟨?_, ?_, ?_⟩
  · simpa [PcOk, SBool.eval] using hpc
  · rw [hm'.regs .X17 _ rfl]
    rfl
  · rw [hm'.regs .X12 _ rfl]
    sym_simp

end NativeRustcArm.Sym.Test.Keccak
