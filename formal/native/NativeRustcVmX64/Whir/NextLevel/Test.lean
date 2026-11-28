module

public import NativeRustcVmX64.Whir.NextLevel.Inv

/-!
# `next_level`: a callee's `bool` tested (x86-64)

`test_spec`: a two-instruction block `testb %al, %al; je l` (`b1`, `b4`, `b6`, `b12`, `b14`) from
a state of the body leaves registers and memory as they were and goes to `l` when AL is `0`, else
to the next block. `K.congr`: `K` in a state with the same registers and memory.
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

public section

theorem retS_some (r : Reg64) : (retS.reg r).isSome = true := by cases r <;> decide

/-- A block whose registers are its start's leaves the machine's registers. -/
theorem regs_same [Labels] {env : Env} {S : SState} {d d' : MachineData} (hm0 : Match env retS d)
    (hm : Match env S d') (hS : S.regs = retS.regs) : ∀ r, reg d' r = reg d r := fun r ↦ by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (retS_some r)
  exact Match.reg_eq hm0 hm hv (by unfold SState.reg at hv ⊢; rw [hS]; exact hv)

/-- `Frame` in a state with the same registers and memory. -/
theorem Frame.congr' {m0 d d' : MachineData} {F o : Nat} {sl : Slots} (hf : Frame m0 F sl o d)
    (hr : ∀ r, reg d' r = reg d r) (hd : d'.dmem = d.dmem) : Frame m0 F sl o d' :=
  ⟨by show reg d' .rsp = _; rw [hr]; exact hf.sp, fun p hp ↦ by rw [hd]; exact hf.slot p hp,
    fun j hj ↦ by rw [hd]; exact hf.ret j hj, by rw [hd]; exact hf.kept,
    fun r hr' hs ↦ by rw [hr]; exact hf.regs r hr' hs⟩

theorem K.congr [Labels] {level : Whir.Level} {w : WhirStateW} {rounds : Array FoldRoundW}
    {m0 d d' : MachineData} {o : Nat} (hK : K level w rounds m0 o d) (hr : ∀ r, reg d' r = reg d r)
    (hd : d'.dmem = d.dmem) : K level w rounds m0 o d' :=
  ⟨⟨Frame.congr' hK.fr.frame hr hd, by rw [Sm, hd]; exact hK.fr.same⟩, by rw [hd]; exact hK.w80,
    by rw [hd]; exact hK.lv, by rw [hd]; exact hK.wa⟩

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **A `bool` tested**: AL `0` goes to `l`, else to the next block; nothing else changes. -/
theorem test_spec (hp : Placed code k) (c : Ctx a s level w rounds m0) {b : List Directive}
    {j : Nat} (hb : b.IsInfixAt code j) (hlen : b.length = 2) {l : Label}
    (hx : exec b retS = some (after b retS, .cond cAl l))
    (hok : (after b retS).mem = [] ∧ (after b retS).regs = retS.regs) {st : MachineState}
    (hK : K level w rounds m0 72 st.data) (hpc : st.pc = Host.addrOf (k + j)) {x : Bool}
    (hal : (reg st.data .rax).toNat % 256 = (okWord x).toNat) :
    Eventually (step1 Host.exe) (fun st' ↦ (∀ r, reg st'.data r = reg st.data r) ∧
      st'.data.dmem = st.data.dmem ∧
      st'.pc = if x then Host.addrOf (k + j + 2) else Labels.label l) st := by
  have hwf := c.wf0 hK.fr.frame.kept (ret := 0)
  have hm : Match (argEnv m0 st.data 8176 8 []) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hK.fr.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hb (by intro h; rw [h] at hlen; cases hlen) hp) hx hwf nofun hpc hm
    fun st' hm' hpc' ↦ .done _ ⟨regs_same hm hm' hok.2, hm'.dmem_eq hwf hok.1, ?_⟩
  simp only [PcOk, cAl_eval] at hpc'
  have h' : ((argEnv m0 st.data 8176 8 []).regs .rax).toNat % 256 = (okWord x).toNat := hal
  rw [hpc', hlen, h']
  cases x <;> rfl

/-- **A block without writes or register changes** ending in a conditional branch. -/
theorem cond_spec (hp : Placed code k) (c : Ctx a s level w rounds m0) {b : List Directive}
    {j : Nat} (hb : b.IsInfixAt code j) (hne : b ≠ []) {l : Label} {cnd : SBool}
    (hx : exec b retS = some (after b retS, .cond cnd l))
    (hok : (after b retS).mem = [] ∧ (after b retS).regs = retS.regs) {st : MachineState}
    (hK : K level w rounds m0 72 st.data) (hpc : st.pc = Host.addrOf (k + j)) :
    Eventually (step1 Host.exe) (fun st' ↦ (∀ r, reg st'.data r = reg st.data r) ∧
      st'.data.dmem = st.data.dmem ∧
      st'.pc = if cnd.eval (argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) 0) then Labels.label l
        else Host.addrOf (k + j + b.length)) st := by
  have hwf := c.wf0 hK.fr.frame.kept (ret := 0)
  have hm : Match (argEnv m0 st.data 8176 8 []) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hK.fr.frame, trivial⟩ trivial trivial trivial
  exact exec_at (infix_of hb hne hp) hx hwf nofun hpc hm
    fun st' hm' hpc' ↦ .done _ ⟨regs_same hm hm' hok.2, hm'.dmem_eq hwf hok.1, hpc'⟩

end

end NativeRustcVmX64.Whir.Levels.NL
