module

public import NativeRustcVmArm.Whir.FoldRound.Reads

/-!
# `fold_round`: the blocks between the calls before the squeezes

`check8` (`b1`: the first scalar's tag, `None` to `.LFoldRound_8`), `check4` (`b3`, `b5`, `b7`: a
scalar's tag, `None` to `.LFoldRound_7`), `load_rs` (`b2`, `b4`, `b6`: the scalar into two
registers, `read_scalar` again).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

/-- A block of the frame without writes, keeping SP and the registers but `rs`. -/
theorem frame_block (h : FoldRoundPre a s0 w m0) {ds : List Directive} {j : Nat}
    (hk : ds.IsInfixAt code j) (hne : ds ≠ []) {S' : SState} {x : Exit}
    (hx : exec ds midS = some (S', x)) (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hp : Placed code k)
    (hb : Base w m0 st.data) {R : MachineState → Prop}
    (cont : ∀ st', Match (frameEnv m0 st.data) S' st'.data →
      PcOk (frameEnv m0 st.data) x (Host.addrOf (k + j + ds.length)) st' →
      FFr m0 st'.data → st'.data.dmem = st.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := frame_wf h hb.fr
  have hm := frame_match h hb.fr
  exact exec_at (inf hp hk hne) hx hwf hpc hm fun st' hm' hpc' ↦
    cont st' hm' hpc' (Fr.ofBlock hb.fr hm hm' hwf rfl hmem (by rw [hsp]; rfl)
      (fun _ h ↦ by cases h)) (hm'.dmem_eq hwf hmem)

/-- The registers a block keeps but `r₀`. -/
theorem keeps_but {env : Env} {S S' : SState} {m m' : MachineData} (hm : Match env S m)
    (hm' : Match env S' m') {r : XReg} (hS : S.reg r = some (.reg r))
    (hS' : S'.reg r = some (.reg r)) : m'.regs.getXReg r = m.regs.getXReg r :=
  Match.reg_eq hm hm' hS hS'

end

end NativeRustcVmArm.Whir.FoldRound
