module

public import NativeRustcVmArm.Whir.FoldRound.Basic

/-!
# `fold_round`: the environments, the `None` exits

The frame's environment (`frameEnv`, `frame_wf`, `frame_match`), with the output (`outEnv`).
`none_exit`: from `.LFoldRound_7` (`b20`, a scalar or the grind failed), tag word `0` and the
epilogue; `none0_exit`: from `b1` (the first scalar failed) straight to `.LFoldRound_8`.
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

section
variable [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

/-- The frame. -/
abbrev frameEnv (m0 st : MachineData) : Env := Env.ofMachine st [(base m0 208, 208)]

/-- The frame and the output. -/
abbrev outEnv (m0 st : MachineData) : Env :=
  Env.ofMachine st [(base m0 208, 208), (oA m0, 40)]

theorem frame_mapped' (h : FoldRoundPre a s w m0) {st : MachineData} (hf : FFr m0 st) :
    NativeRustcVm.Mapped st.dmem (base m0 208) 208 :=
  fun i hi ↦ hf.kept _ (frame_mapped h.1.1 (by rw [stack_eq]; decide) i hi)

theorem frame_wf (h : FoldRoundPre a s w m0) {st : MachineData} (hf : FFr m0 st) :
    (frameEnv m0 st).WF :=
  Env.wf_of ⟨⟨frame_mapped' h hf, base_noWrap (by have := pre_hN h; rw [stack_eq] at this; omega)⟩,
    trivial⟩ (List.pairwise_singleton _ _)

theorem frame_match (h : FoldRoundPre a s w m0) {st : MachineData} (hf : FFr m0 st) :
    Match (frameEnv m0 st) midS st :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1.1 (by rw [stack_eq]; decide) rfl, trivial⟩
    (by rw [hf.sp]; simp [Sym.eval]) trivial trivial trivial trivial

theorem out_wf (h : FoldRoundPre a s w m0) {st : MachineData} (hf : FFr m0 st) :
    (outEnv m0 st).WF := by
  have hoo : OutOk m0 (tA m0) a (oA m0) 40 foldRoundStack := h.2.2.2.2.2.1.1
  have hN := pre_hN h
  rw [stack_eq] at hN
  refine Env.wf_of ⟨⟨frame_mapped' h hf, base_noWrap (by omega)⟩,
    ⟨fun i hi ↦ hf.kept _ (hoo.1 i hi), hoo.2.1⟩, trivial⟩
    (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm (NativeRustcVmArm.Ring.apart_frame
      (pre_hN h) (by rw [stack_eq]; decide) hoo.2.2.2.2.1)))

end

section
variable [Host] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

/-- `fold_round`'s postcondition, reached. -/
abbrev Goal (a : DecArea) (s : TState) (w : WhirStateW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ FoldRoundPost a s w m0 st.data

theorem inf (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- The epilogue's changes are the contract's, the tag word `0`. -/
theorem none_post (h : FoldRoundPre a s w m0) (hnone : (foldRound w).run s = none)
    {st : MachineData} (hf : FFr m0 st) {S : SState} {st2 : MachineState}
    (hm : Match (outEnv m0 st) S st2.data) (hwf : (outEnv m0 st).WF)
    (hok : exitOk S 208 slots [] = true) (hpc : st2.pc = retOf st2.data)
    (hS : ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ 208) ∨ (w.r = 1 ∧ w.off + w.n ≤ 40))
    (h0 : NativeRustcVm.WordAt st2.data.dmem (oA m0) 0) : Goal a s w m0 st2 := by
  obtain ⟨hret, hsv⟩ := hf.exit hm hwf hok
  have hN := pre_hN h
  rw [stack_eq] at hN
  have hs : SameOutside st.dmem st2.data.dmem
      (fun q ↦ InRange (base m0 208) 208 q ∨ InRange (oA m0) 40 q) :=
    NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun q hq ↦ by
      obtain ⟨w', hw, b, sz, hb, hin⟩ := written_inRange hwf (fun w hw b sz hb ↦ by
        rcases hS w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩ <;> rw [hr] at hb <;> simp at hb <;> omega) hq
      rcases hS w' hw with ⟨hr, -⟩ | ⟨hr, -⟩ <;> rw [hr] at hb <;> simp at hb <;>
        obtain ⟨rfl, rfl⟩ := hb
      · exact Or.inl hin
      · exact Or.inr hin
  refine ⟨hpc.trans hret, ?_, ?_, hsv⟩
  · rw [hnone]; exact h0
  · refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hf.same hs) ?_
    intro q hq
    rcases hq with (hq | hq | hq | hq) | hq | hq
    · exact Or.inr hq
    · exact Or.inl ⟨_, List.mem_cons_self, hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hq⟩
    · exact Or.inr (frame_sub (pre_hN h) (by rw [stack_eq]; decide) hq)
    · exact Or.inl ⟨_, List.mem_cons_self, hq⟩

/-- **`None` from `.LFoldRound_7`.** -/
theorem none_exit (hp : Placed code k) (h : FoldRoundPre a s w m0)
    (hnone : (foldRound w).run s = none) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b20Offset)) (hb : Base w m0 st.data) :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  have hwf := out_wf h hb.fr
  have hm : Match (outEnv m0 st.data) noneS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1.1 (by rw [stack_eq]; decide) rfl, rfl,
      fun h ↦ absurd h (by decide), trivial⟩ (by rw [hb.fr.sp]; simp [Sym.eval])
      ⟨by show (st.data.regs.getXReg .X19).toBitVec = _; simp [Sym.eval]
          exact congrArg UInt64.toBitVec hb.x19,
        trivial⟩ trivial trivial trivial
  refine exec_at (inf hp b20_in_code (by simp [b20])) run_b20 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show k + NativeRustcVmArm.Vm.FoldRound.b20Offset + b20.length = k + NativeRustcVmArm.Vm.FoldRound.b21Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRound.b20_next]] at hpc1
  refine exec_at (inf hp b21_in_code (by simp [b21])) (exec_after run_b20 run_b21n) hwf hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hS : ∀ w ∈ (after b21 (after b20 noneS)).mem,
      (w.r = 0 ∧ w.off + w.n ≤ 208) ∨ (w.r = 1 ∧ w.off + w.n ≤ 40) := by
    rw [after_eq run_b21n]; decide
  rw [after_eq run_b21n] at hS
  refine .done _ (none_post h hnone hb.fr hm2 hwf (by decide) hpc2 hS ?_)
  have hw := hm2.bytesAt_write (r := 1) (o := 0) (n := 8) (b := oA m0) (sz := 40) rfl
    (by decide) (v := .lit 0) (by decide)
  rw [wordBytes_reg, NativeRustcVm.addr_add_zero] at hw
  exact hw

/-- **`None` from `b1`**: the first scalar failed, X8 `0`. -/
theorem none0_exit (hp : Placed code k) (h : FoldRoundPre a s w m0)
    (hnone : (foldRound w).run s = none) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b21Offset)) (hb : Base w m0 st.data) (h8 : st.data.regs.X8 = 0) :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  have hwf := out_wf h hb.fr
  have hm : Match (outEnv m0 st.data) none0S st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1.1 (by rw [stack_eq]; decide) rfl, rfl,
      fun h ↦ absurd h (by decide), trivial⟩ (by rw [hb.fr.sp]; simp [Sym.eval])
      ⟨by show (st.data.regs.getXReg .X19).toBitVec = _; simp [Sym.eval]
          exact congrArg UInt64.toBitVec hb.x19,
        by show (st.data.regs.getXReg .X8).toBitVec = _; simp [Sym.eval]
           exact congrArg UInt64.toBitVec h8,
        trivial⟩ trivial trivial trivial
  refine exec_at (inf hp b21_in_code (by simp [b21])) run_b21z hwf hpc hm fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hS : ∀ w ∈ (after b21 none0S).mem,
      (w.r = 0 ∧ w.off + w.n ≤ 208) ∨ (w.r = 1 ∧ w.off + w.n ≤ 40) := by
    rw [after_eq run_b21z]; decide
  rw [after_eq run_b21z] at hS
  refine .done _ (none_post h hnone hb.fr hm2 hwf (by decide) hpc2 hS ?_)
  have hw := hm2.bytesAt_write (r := 1) (o := 0) (n := 8) (b := oA m0) (sz := 40) rfl
    (by decide) (v := .lit 0) (by decide)
  rw [wordBytes_reg, NativeRustcVm.addr_add_zero] at hw
  exact hw

end

end

end NativeRustcVmArm.Whir.FoldRound
