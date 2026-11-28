module

public import NativeRustcVmX64.Top.VerifyExecution.Basic
public import NativeRustcVmX64.Code.Vm.VerifyExecution.Names

/-!
# `verify_execution`: the blocks between the calls (x86-64)

The blocks' places and labels; between the calls the blocks run from `bodyS` (`At.env`). Bytes of
the working area outside a call's changes stay the same (`Geo.same`). The failure path at
`NativeRustcVmX64.Vm.VerifyExecution.label_10` (`fail`: `0`, the epilogue), the test after a call (`branch`: to `fail`
when the callee returned `None`), and the return after `verify_stacked_opening` (`exitVso`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)

public section

section
variable [Labels] {a : DecArea} {m0 d : MachineData}

/-- **The blocks' start** between the calls. -/
theorem At.env (h : At m0 d) (g : Geo a m0) {ret : BitVec 64} :
    (frameEnv m0 d 96 [] (fun _ ↦ 0) ret).WF ∧ Match (frameEnv m0 d 96 [] (fun _ ↦ 0) ret) bodyS d :=
  ⟨frame_wf ⟨Mapped.keeps g.fmapped h.frame.kept, g.fnw⟩ (by simp) (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.frame.rsp_eval, trivial⟩ trivial trivial trivial⟩

/-- A block between the calls without writes keeps `At`. -/
theorem At.block (h : At m0 d) (g : Geo a m0) {d' : MachineData} {S : SState} {ret : BitVec 64}
    (hm : Match (frameEnv m0 d 96 [] (fun _ ↦ 0) ret) S d') (hmid : MidOk 96 40 slots S = true)
    (hmem : S.mem = [])
    (hk : [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].all (fun r ↦ S.reg r == some (.reg r)) = true) :
    At m0 d' ∧ d'.dmem = d.dmem ∧
      ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp], reg d' r = reg d r := by
  have hwf := (h.env g (ret := ret)).1
  have hd := hm.dmem_eq hwf hmem
  have kr : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp], reg d' r = reg d r :=
    fun r hr ↦ hm.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  exact ⟨⟨Frame.of_block h.frame hwf hm hmid slots_le, by rw [hd]; exact h.same,
    (kr .rbx (by simp)).trans h.rbx, (kr .r14 (by simp)).trans h.r14⟩, hd, kr⟩

/-- Bytes of the working area a change misses stay the same. -/
theorem Geo.same (g : Geo a m0) {d d' : DataMem} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552)
    (hR : ∀ q, R q → q.toNat < (reg m0 .r8).toNat + o ∨ (reg m0 .r8).toNat + o + n ≤ q.toNat) :
    NativeRustcVm.Layout.Same d d' (off (reg m0 .r8) o) n :=
  NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ by
    have := hR _ hq
    rw [off_add, g.wo (by omega)] at this
    omega

end

variable [Host] {k : Nat}

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.VerifyExecution.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.VerifyExecution.entry_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.VerifyExecution.label_10 = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b20Offset) :=
  hp.label NativeRustcVmX64.Vm.VerifyExecution.label_10_at
theorem lbl_11 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.VerifyExecution.label_11 = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b21Offset) :=
  hp.label NativeRustcVmX64.Vm.VerifyExecution.label_11_at

/-- **The epilogue** (`b21`), RSP at offset `48`, RAX kept. -/
theorem exit21 (hp : Placed code k) {a : DecArea} {m0 : MachineData} (g : Geo a m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b21Offset)) (hf : Frame m0 96 slots 48 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ reg st'.data .rax = reg st.data .rax ∧
      st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 96) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps g.fmapped hf.kept, g.fnw⟩ (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b21_in_code (by simp [b21]) hp) run_b21 hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st' hm hpc' ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := after_eq run_b21 ▸ ok_b21
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm hepi
  simp only [PcOk] at hpc'
  exact .done _ ⟨by rw [hpc']; exact hf.load_ret g.stackOk (by decide), hrsp, hm.regs .rax _ hrax,
    hm.dmem_eq hwf hmem, hsv⟩

/-- **The failure path** at `NativeRustcVmX64.Vm.VerifyExecution.label_10`: `0`, returned. -/
theorem fail (hp : Placed code k) {a : DecArea} {m0 : MachineData} (g : Geo a m0)
    {st : MachineState} (h : At m0 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b20Offset)) :
    Eventually (step1 Host.exe) (Done a m0 none) st := by
  obtain ⟨hwf, hm⟩ := h.env g (ret := 0)
  refine exec_at (infix_of b20_in_code (by simp [b20]) hp) run_b20 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hmid, hmem, hrax⟩ := after_eq run_b20 ▸ ok_b20
  have hf' : Frame m0 96 slots 48 st'.data := Frame.of_block h.frame hwf hm' hmid slots_le
  have hd := hm'.dmem_eq hwf hmem
  simp only [PcOk] at hpc'
  refine Eventually.mono (exit21 hp g (hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyExecution.b20_next)) hf')
    fun s ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, by
      unfold OkAl boolRet
      rw [h3, show reg st'.data .rax = BitVec.ofNat 64 0 from hm'.regs .rax _ hrax]
      rfl, fun _ _ h ↦ absurd h (by simp), by rw [h4, hd]; exact h.same, h5⟩

/-- **The test after a call** (`test %al, %al; je .LVerifyExecution_10`): to `fail` when the call
returned `None`, else on, `At` kept, the memory and the callee-saved registers unchanged. -/
theorem branch (hp : Placed code k) {a : DecArea} {m0 : MachineData} (g : Geo a m0)
    {b : List Directive} {j : Nat} (hin : b.IsInfixAt code j) (hne : b ≠ [])
    (hx : exec b bodyS = some (after b bodyS, .cond (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax)
      (.reg .rax)) (.lit 0)) NativeRustcVmX64.Vm.VerifyExecution.label_10))
    (hk : MidOk 96 40 slots (after b bodyS) = true ∧ (after b bodyS).mem = [] ∧
      [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].all
        (fun r ↦ (after b bodyS).reg r == some (.reg r)) = true)
    {st : MachineState} (h : At m0 st.data) (hpc : st.pc = Host.addrOf (k + j)) {ok : Bool}
    (hok : OkAl st.data ok) {R : Option (Unit × TState)} (hnone : ok = false → R = none)
    (cont : ∀ st', ok = true → At m0 st'.data → st'.data.dmem = st.data.dmem →
      (∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp], reg st'.data r = reg st.data r) →
      st'.pc = Host.addrOf (k + j + b.length) → Eventually (step1 Host.exe) (Done a m0 R) st') :
    Eventually (step1 Host.exe) (Done a m0 R) st := by
  obtain ⟨hwf, hm⟩ := h.env g (ret := 0)
  refine exec_at (infix_of hin hne hp) hx hwf nofun hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨h', hd, hkr⟩ := h.block g hm' hk.1 hk.2.1 hk.2.2
  simp only [PcOk] at hpc'
  have hc : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (frameEnv m0 st.data 96 [] (fun _ ↦ 0) 0) = !ok := by
    simp only [SBool.eval, Sym.eval]
    exact testAl_okAl hok
  rw [hc] at hpc'
  cases ok with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at hpc'
    rw [hnone rfl]
    exact fail hp g h' (hpc'.trans (lbl_10 hp))
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc'
    exact cont st' rfl h' hd hkr hpc'

end

end NativeRustcVmX64.Top.VerifyExecution
