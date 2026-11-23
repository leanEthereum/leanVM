module

public import NativeRustcVmArm.Bus.BytecodeShare.Exec
public import NativeRustcVmArm.Bus.GkrCommon
public import NativeRustcVmArm.Bus.GkrModel
public import NativeRustcVmArm.Bus.Frame

/-!
# `bytecode_share`: the frame, the model, the exits

The 432-byte frame saves X19 to X30 at offsets 336 to 432 (`slots`); the locals are the slot
point (four elements at 16) and the kernel (sixteen at 80), whose first 24 bytes are also the
`Option<EW>` the transcript's calls return. The outputs grow as the proof goes: the `TState`
(`outsT`) until the copy, then the point (`outsP`), then the output (`outs`).

- `bytecodeShare_run`: the model step by step.
- `exit16`: the epilogue `.LBytecodeShare_10`; `none15`: the tag `0` (`.LBytecodeShare_9`).
- `match_frame3`, `wf_frame3`: the frame and two regions at registers.
-/

namespace NativeRustcVmArm.Bus.BytecodeShare

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BytecodeShare
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open LeanVM.Protocol.Verifier (busBits)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(336, .X29), (344, .X30), (352, .X28), (360, .X27), (368, .X26), (376, .X25), (384, .X24),
    (392, .X23), (400, .X22), (408, .X21), (416, .X20), (424, .X19)]

/-- Every callee-saved register is saved. -/
abbrev keep : List XReg := []

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 432 := by decide

/-- The point's bytes. -/
abbrev ptBytes : Nat := 16 * sharePointSlots

theorem ptBytes_eq : ptBytes = 1072 := rfl

/-- The outputs before the copy: the `TState`. -/
@[expose] def outsT (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X1.toBitVec tstateBytes q

/-- The outputs during the copy: the `TState` and the point. -/
@[expose] def outsP (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X1.toBitVec tstateBytes q ∨ InRange m0.regs.X5.toBitVec ptBytes q

/-- All the outputs. -/
@[expose] def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec 48 q ∨ outsP m0 q

theorem outsT_P {m0 : MachineData} : ∀ q, outsT m0 q → outsP m0 q := fun _ h ↦ .inl h
theorem outsP_all {m0 : MachineData} : ∀ q, outsP m0 q → outs m0 q := fun _ h ↦ .inr h

theorem N_ge : 432 ≤ bytecodeShareStack := by unfold bytecodeShareStack; omega
theorem le_rs : 432 + readScalarStack ≤ bytecodeShareStack := by
  unfold bytecodeShareStack maxOf; simp only [List.foldr]; omega
theorem le_sc : 432 + sumcheckPlainStack ≤ bytecodeShareStack := by
  unfold bytecodeShareStack maxOf; simp only [List.foldr]; omega
theorem le_ek : 432 + eqKernelStack ≤ bytecodeShareStack := by
  unfold bytecodeShareStack maxOf; simp only [List.foldr]; omega
theorem le_dot : 432 + dotStack ≤ bytecodeShareStack := by
  unfold bytecodeShareStack maxOf; simp only [List.foldr]; omega
theorem le_mul : 432 + ewMulStack ≤ bytecodeShareStack := by
  unfold bytecodeShareStack maxOf; simp only [List.foldr]; omega

/-- **`bytecodeShare` step by step.** -/
theorem bytecodeShare_run (w bl : Array EW) (s : TState) :
    (bytecodeShare w bl).run s =
      (readScalar.run s).bind fun x ↦ ((sumcheckPlain x.1 3 busBits).run x.2).bind fun y ↦
        (readScalar.run y.2).bind fun z ↦
          if (y.1.2 == dot (eqKernel y.1.1) w * z.1) = true then
            some ((x.1, bl ++ y.1.1, z.1), z.2)
          else none := by
  simp only [bytecodeShare, StateT.run, bind, StateT.bind, pure, StateT.pure, require]
  cases readScalar s with
  | none => rfl
  | some x =>
    simp only [Option.bind_some]
    cases sumcheckPlain x.1 3 busBits x.2 with
    | none => rfl
    | some y =>
      simp only [Option.bind_some]
      cases readScalar y.2 with
      | none => rfl
      | some z =>
        simp only [Option.bind_some]
        by_cases hc : (y.1.2 == dot (eqKernel y.1.1) w * z.1) = true <;>
          simp [hc, StateT.pure, reject]

/-- The precondition's parts. -/
theorem pre_parts [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}
    (h : BytecodeSharePre a s0 m0) :
    StackOk m0 bytecodeShareStack ∧ RcAt m0 bytecodeShareStack ∧
      TStateAt m0.dmem m0.regs.X1.toBitVec a s0 ∧
      TStateOk m0 m0.regs.X1.toBitVec a bytecodeShareStack ∧
      EWsOk m0 m0.regs.X2.toBitVec 16 bytecodeShareStack ∧ m0.regs.X4.toNat ≤ busPointCap ∧
      SliceOk m0 m0.regs.X3 m0.regs.X4 bytecodeShareStack ∧
      OutOk m0 m0.regs.X1.toBitVec a m0.regs.X0.toBitVec 48 bytecodeShareStack ∧
      OutOk m0 m0.regs.X1.toBitVec a m0.regs.X5.toBitVec ptBytes bytecodeShareStack ∧
      Apart m0.regs.X0.toBitVec 48 m0.regs.X5.toBitVec ptBytes ∧
      Apart m0.regs.X5.toBitVec ptBytes m0.regs.X3.toBitVec (16 * m0.regs.X4.toNat) ∧
      Apart m0.regs.X2.toBitVec (16 * 16) m0.regs.X1.toBitVec tstateBytes ∧
      Apart m0.regs.X3.toBitVec (16 * m0.regs.X4.toNat) m0.regs.X1.toBitVec tstateBytes := h

/-- A state in the frame with two more regions at the addresses in registers `r1`, `r2`, less
`c1`, `c2`. -/
theorem match_frame3 [Labels] {m0 m : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (h16 : F % 16 = 0) (hsp : m.regs.SP.toBitVec = base m0 F) {r1 r2 : XReg} {n1 n2 c1 c2 : Nat}
    {x1 x2 : BitVec 64} (h1 : (m.regs.getXReg r1).toBitVec = x1 + BitVec.ofNat 64 c1)
    (h2 : (m.regs.getXReg r2).toBitVec = x2 + BitVec.ofNat 64 c2) :
    Match (Env.ofMachine m [(base m0 F, F), (x1, n1), (x2, n2)])
      (init [(F, true), (n1, false), (n2, false)] (.ptr 0 0)
        [(r1, .ptr 1 (c1 : Int)), (r2, .ptr 2 (c2 : Int))]) m :=
  match_ofMachine (sregions := [(F, true), (n1, false), (n2, false)])
    (regions := [(base m0 F, F), (x1, n1), (x2, n2)])
    ⟨rfl, fun _ ↦ base_aligned hS hF h16, rfl, nofun, rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hsp]; simp)
    ⟨show (m.regs.getXReg r1).toBitVec = _ by rw [h1]; simp [Sym.eval, Env.base_ofMachine_eq],
      ⟨show (m.regs.getXReg r2).toBitVec = _ by rw [h2]; simp [Sym.eval, Env.base_ofMachine_eq],
        trivial⟩⟩
    trivial trivial trivial

/-- A three-region environment of the frame and two readable regions, apart from the stack and
each other, is well formed. -/
theorem wf_frame3 {m0 m : MachineData} {F N : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    (hk : Kept m0.dmem m.dmem) {a1 a2 : BitVec 64} {n1 n2 : Nat}
    (hm1 : NativeRustcVm.Mapped m.dmem a1 n1) (hn1 : NoWrap a1 n1)
    (hm2 : NativeRustcVm.Mapped m.dmem a2 n2) (hn2 : NoWrap a2 n2)
    (ha1 : Apart a1 n1 (stackBelow m0 N) N) (ha2 : Apart a2 n2 (stackBelow m0 N) N)
    (h12 : Apart a1 n1 a2 n2) :
    (Env.ofMachine m [(base m0 F, F), (a1, n1), (a2, n2)]).WF := by
  have hN := hS.2.1
  have hb := base_toNat (m0 := m0) (F := F) (by omega)
  have hsb : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  refine Env.wf_of ⟨⟨fun i hi ↦ hk _ ((frame_mapped hS hF).1 i hi), (frame_mapped hS hF).2⟩,
    ⟨hm1, hn1⟩, ⟨hm2, hn2⟩, trivial⟩ ?_
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    unfold Apart at ha1 ha2 ⊢
    constructor <;> omega
  · simp only [List.mem_singleton, forall_eq]
    exact h12

variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData} {k : Nat}

/-- What `bytecode_share` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ BytecodeSharePost a s0 m0 st.data

/-- The model's result. -/
abbrev res (s0 : TState) (m0 : MachineData) : Option ((EW × Array EW × EW) × TState) :=
  (bytecodeShare (NativeRustcVm.ewsOf m0.dmem m0.regs.X2.toBitVec 16).toArray
    (slice m0 m0.regs.X3 m0.regs.X4)).run s0

/-- **The epilogue** `.LBytecodeShare_10` (`b16`): the result as the memory has it. -/
theorem exit16 (hp : Placed code k) (h : BytecodeSharePre a s0 m0) {m : MachineData}
    (hfr : Fr m0 432 bytecodeShareStack slots keep (outs m0) m)
    (hpost : OptShareAt m.dmem m0.regs.X0.toBitVec ((res s0 m0).map (·.1)) ∧
      (∀ x s', res s0 m0 = some (x, s') →
        NativeRustcVm.EWsAt m.dmem m0.regs.X5.toBitVec x.2.1.toList ∧
          TStateAt m.dmem m0.regs.X1.toBitVec a s')) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b16Offset)⟩ := by
  have hS := (pre_parts h).1
  have hwf := Bus.wf_frame (F := 432) hS N_ge hfr.kept
  have hm := Bus.match_frame (m := m) hS N_ge rfl hfr.sp
  refine exec_then (b16_in_code.trans hp.1 (by simp [b16])) run_b16 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit hm' hwf (by decide)
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], ?_, ?_, ?_, hsv⟩
  · rw [hd]; exact hpost.1
  · intro x s' hx; rw [hd]; exact hpost.2 x s' hx
  · intro q hq
    rw [hd]
    refine hfr.same q fun h' ↦ hq ?_
    rcases h' with h' | h' | h' | h'
    · exact .inr (.inr (.inr h'))
    · exact .inl h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inl h')

/-- **The tag `0`** (`.LBytecodeShare_9`, `b15`): the model failed. -/
theorem none15 (hp : Placed code k) (h : BytecodeSharePre a s0 m0) {m : MachineData}
    (hfr : Fr m0 432 bytecodeShareStack slots keep (outs m0) m)
    (h19 : m.regs.getXReg .X19 = m0.regs.X0) (hr : res s0 m0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b15Offset)⟩ := by
  obtain ⟨hS, -, -, -, -, -, -, hoo, -⟩ := pre_parts h
  have hwf : (Env.ofMachine m [(base m0 432, 432), (m0.regs.X0.toBitVec, 48)]).WF :=
    Bus.wf_frame2 hS N_ge hfr.kept ⟨hoo.1, hoo.2.1⟩ hoo.2.2.2.2.1
  have hm := match_frameW (n := 48) hS N_ge rfl hfr.sp (r := .X19) (by rw [h19])
  refine exec_then (b15_in_code.trans hp.1 (by simp [b15])) run_b15 hwf hm fun st hm' hpc ↦ ?_
  have hfr' : Fr m0 432 bytecodeShareStack slots keep (outs m0) st.data :=
    Fr.ofBlockW hfr hm hm' hwf rfl rfl (fun r hr ↦ absurd hr List.not_mem_nil) rfl N_ge hS.2.1
      slots_le fun w hw ↦ writeOk_two' (fun i hi ↦ .inl (NativeRustcVm.inRange_add hi
        (by have := hoo.2.1; unfold NoWrap at this; omega))) (by revert w; decide)
  have hw0 : NativeRustcVm.WordAt st.data.dmem m0.regs.X0.toBitVec 0 := by
    have := Bus.wordAt_write hm' (r := 1) (o := 0) rfl (by omega) (v := .lit 0) (by decide)
    simpa [Sym.eval, NativeRustcVm.addr_add_zero] using this
  simp only [PcOk] at hpc
  refine at_pc hpc (exit16 hp h hfr' ⟨?_, fun _ _ he ↦ ?_⟩)
  · rw [hr]; exact hw0
  · rw [hr] at he; cases he

end

end NativeRustcVmArm.Bus.BytecodeShare
