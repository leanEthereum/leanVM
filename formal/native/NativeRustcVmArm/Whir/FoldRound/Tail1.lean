module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Whir.FoldRound.Words

/-!
# `fold_round`: the two squeezes

`squeezes`: from `b10` (`AtB10`), `α` (`b10`), then `c0`'s low word and `c1` saved in the frame,
`α` into X25, X22, and `β` (`b11`), to `b12` (`AtB12`).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

section
variable [Labels]

/-- **At `b12`**: `α` in X25, X22, `β` in X0, X1, `c0`'s low word and `c1` in the frame. -/
structure AtB12 (a : DecArea) (s0 : TState) (w : WhirStateW) (m0 : MachineData) (s5 : TState)
    (u0 v c0 c1 : EW) (st : MachineData) : Prop where
  base : Base w m0 st
  x29 : st.regs.X29 = u0.c0
  x24 : st.regs.X24 = u0.c1
  x27 : st.regs.X27 = v.c0
  x28 : st.regs.X28 = v.c1
  x26 : st.regs.X26 = c0.c1
  x25 : st.regs.X25 = (sq s5).1.c0
  x22 : st.regs.X22 = (sq s5).1.c1
  x0 : st.regs.X0 = (sq (sq s5).2).1.c0
  x1 : st.regs.X1 = (sq (sq s5).2).1.c1
  ts : TStateAt st.dmem (tA m0) a (sq (sq s5).2).2
  fw : FW st.dmem m0 [(48, c0.c0), (72, c1.c1), (80, c1.c0)]
  model : (foldRound w).run s0 = some ((foldW w u0 v c0 c1 (sq s5).1 (sq (sq s5).2).1,
    ⟨(sq s5).1, (sq (sq s5).2).1⟩), (sq (sq s5).2).2)

end

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

omit [Host] in
theorem sq_le : 208 + squeezeStack ≤ foldRoundStack := by decide

/-- After a squeeze: the base kept. -/
theorem base_sq (h : FoldRoundPre a s0 w m0) {st m2 : MachineData} (hb : Base w m0 st)
    (hf2 : FFr m0 m2) (hcs : ∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r)
    (hs : SameOutside st.dmem m2.dmem fun q ↦ InRange (tA m0) spongeBytes q ∨
      InRange (stackBelow st squeezeStack) squeezeStack q) : Base w m0 m2 := by
  have hnt : NoWrap (tA m0) tstateBytes := h.2.1.footprint.1.2
  exact ⟨hf2, (hcs .X19 rfl).trans hb.x19, (hcs .X20 rfl).trans hb.x20,
    (hcs .X23 rfl).trans hb.x23, ws_keep h hb.ws hs fun q hq ↦ by
      rcases hq with hq | hq
      · exact Or.inr (Or.inr (NativeRustcVm.InRange.mono hq
          (NativeRustcVm.NoWrap.mono hnt sponge_le') hnt
          (Nat.le_refl _) (Nat.add_le_add_left sponge_le' _)))
      · exact Or.inl (stack_sub h hb.fr sq_le hq)⟩

/-- **The two squeezes.** -/
theorem squeezes (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} {s5 : TState} {u0 v c0 c1 : EW} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b10Offset))
    (hb : AtB10 a s0 w m0 s5 u0 v c0 c1 st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b12Offset) → AtB12 a s0 w m0 s5 u0 v c0 c1 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx h
  have hnt : NoWrap (tA m0) tstateBytes := h.2.1.footprint.1.2
  -- `b10`: `α`
  refine frame_block h b10_in_code (by simp [b10]) run_b10 rfl rfl hpc hp hb.base
    fun st1 hm1 hpc1 hf1 hd1 ↦ ?_
  simp only [PcOk] at hpc1
  have hk1 : ∀ r, calleeSaved r = true → st1.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ reg_of hm1 (v := .reg r) (by cases r <;> first | rfl | simp [calleeSaved] at hr)
      rfl
  have hb1 : Base w m0 st1.data :=
    ⟨hf1, (hk1 .X19 rfl).trans hb.base.x19, (hk1 .X20 rfl).trans hb.base.x20,
      (hk1 .X23 rfl).trans hb.base.x23, by rw [hd1]; exact hb.base.ws⟩
  have hx0 : st1.data.regs.X0.toBitVec = tA m0 := by
    rw [show st1.data.regs.X0 = st.data.regs.X23 from
      reg_of hm1 (r := .X0) (v := .reg .X23) rfl rfl, hb.base.x23]
  refine tsqueeze c hsq hf1 sq_le (fun _ h ↦ by cases h) slots_le hpc1 hx0
    (by rw [hd1]; exact hb.ts) fun m2 hf2 hts2 ha0 ha1 hcs2 hs2 ↦ ?_
  have hb2 := base_sq h hb1 hf2 hcs2 hs2
  have hk2 : ∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ (hcs2 r hr).trans (hk1 r hr)
  -- `b11`: the frame's words, `β`
  have hwf3 := frame_wf h hf2
  have hm3 := frame_match h hf2
  refine exec_at (st := ⟨m2, _⟩) (k := k + NativeRustcVmArm.Vm.FoldRound.b11Offset) (inf hp b11_in_code (by simp [b11])) run_b11 hwf3
    rfl hm3 fun st3 hm3' hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have hmem3 : ∀ w ∈ (after b11 midS).mem, w.r = 0 ∧ w.off + w.n ≤ 208 := by
    rw [after_eq run_b11]; decide
  rw [after_eq run_b11] at hmem3
  have hs3 : SameOutside m2.dmem st3.data.dmem (InRange (base m0 208) 208) :=
    NativeRustcVm.SameOutside.mono (hm3'.sameOutside hwf3) fun q hq ↦ written_r0 hwf3 rfl hmem3 hq
  have hf3 : FFr m0 st3.data := Fr.ofBlockW hf2 hm3 hm3' hwf3 rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by decide) (pre_hN h) slots_le
    (writeOk_of (F := 208) (slots := slots) (wr := []) hm3' (by decide) (fun _ h ↦ by cases h))
  have hk3 : ∀ r, calleeSaved r = true → r ≠ .X22 → r ≠ .X25 →
      st3.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr h22 h25 ↦
    (reg_of hm3' (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl).trans
      (hk2 r hr)
  have hb3 : Base w m0 st3.data :=
    ⟨hf3, (hk3 .X19 rfl (by decide) (by decide)).trans hb.base.x19,
      (hk3 .X20 rfl (by decide) (by decide)).trans hb.base.x20,
      (hk3 .X23 rfl (by decide) (by decide)).trans hb.base.x23,
      ws_keep h hb2.ws hs3 fun q hq ↦ frame_away h hq⟩
  have hfw3 : FW st3.data.dmem m0 [(48, c0.c0), (72, c1.c1), (80, c1.c0)] := by
    refine FW.cons ?_ (FW.cons ?_ (FW.cons ?_ (FW.nil _ _)))
    · have := fw_write (m0 := m0) hm3' rfl (o := 48) (by decide) (v := .reg .X25) (by decide)
      rwa [show UInt64.ofBitVec ((Sym.reg XReg.X25).eval (frameEnv m0 m2)) = c0.c0 from
        (hk2 .X25 rfl).trans hb.x25] at this
    · have := fw_write (m0 := m0) hm3' rfl (o := 72) (by decide) (v := .reg .X22) (by decide)
      rwa [show UInt64.ofBitVec ((Sym.reg XReg.X22).eval (frameEnv m0 m2)) = c1.c1 from
        (hk2 .X22 rfl).trans hb.x22] at this
    · have := fw_write (m0 := m0) hm3' rfl (o := 80) (by decide) (v := .reg .X21) (by decide)
      rwa [show UInt64.ofBitVec ((Sym.reg XReg.X21).eval (frameEnv m0 m2)) = c1.c0 from
        (hk2 .X21 rfl).trans hb.x21] at this
  have hts3 : TStateAt st3.data.dmem (tA m0) a (sq s5).2 :=
    hts2.frame (hm3'.kept hwf3) (fun q hq ↦ frame_not_t h hq) hs3
  have hx0' : st3.data.regs.X0.toBitVec = tA m0 := by
    rw [show st3.data.regs.X0 = st.data.regs.X23 from
      (reg_of hm3' (r := .X0) (v := .reg .X23) rfl rfl).trans (hk2 .X23 rfl), hb.base.x23]
  have h25 : st3.data.regs.X25 = (sq s5).1.c0 := (reg_of hm3' (r := .X25) (v := .reg .X0) rfl rfl).trans ha0
  have h22 : st3.data.regs.X22 = (sq s5).1.c1 := (reg_of hm3' (r := .X22) (v := .reg .X1) rfl rfl).trans ha1
  refine tsqueeze c hsq hf3 sq_le (fun _ h ↦ by cases h) slots_le hpc3 hx0' hts3
    fun m4 hf4 hts4 hb0 hb1' hcs4 hs4 ↦ cont ⟨m4, _⟩ rfl ?_
  have hk4 : ∀ r, calleeSaved r = true → r ≠ .X22 → r ≠ .X25 →
      m4.regs.getXReg r = st.data.regs.getXReg r := fun r hr h1 h2 ↦
    (hcs4 r hr).trans (hk3 r hr h1 h2)
  exact {
    base := base_sq h hb3 hf4 hcs4 hs4
    x29 := (hk4 .X29 rfl (by decide) (by decide)).trans hb.x29
    x24 := (hk4 .X24 rfl (by decide) (by decide)).trans hb.x24
    x27 := (hk4 .X27 rfl (by decide) (by decide)).trans hb.x27
    x28 := (hk4 .X28 rfl (by decide) (by decide)).trans hb.x28
    x26 := (hk4 .X26 rfl (by decide) (by decide)).trans hb.x26
    x25 := (hcs4 .X25 rfl).trans h25
    x22 := (hcs4 .X22 rfl).trans h22
    x0 := hb0
    x1 := hb1'
    ts := hts4
    fw := fw_call h hf3 sq_le (NativeRustcVm.SameOutside.mono hs4 fun q hq ↦ by
      rcases hq with hq | hq
      · exact .inr (.inr (.inr (NativeRustcVm.InRange.mono hq
          (NativeRustcVm.NoWrap.mono hnt sponge_le') hnt
          (Nat.le_refl _) (Nat.add_le_add_left sponge_le' _))))
      · exact .inl hq) (by simp) hfw3
    model := hb.model }

end

end NativeRustcVmArm.Whir.FoldRound
