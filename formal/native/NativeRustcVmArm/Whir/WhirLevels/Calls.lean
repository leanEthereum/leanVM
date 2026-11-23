module

public import NativeRustcVmArm.Code.Vm.FoldRounds.Names
public import NativeRustcVmArm.Whir.WhirLevels.Blocks

/-!
# `whir_levels`: what a callee gets, and the fold rounds' call

From a state of a frame of `F` bytes (`Fr m0 F …`, the 96-byte frame or, at the tail call, none),
a callee using `N'` bytes below it gets the transcript's context (`Ctx.whirT`), the outputs
(`Ctx.whirOut`), the inputs (`Ctx.whirIn`, `Ctx.basisIn`) and their sub-ranges (`apart_sub`,
`OutOk.sub`). `fold_call`: `fold_rounds` from `Head k`, to `None` (the run rejected) or `Mid k`.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder

public section

theorem apart_sub {a b : BitVec 64} {n m o k : Nat} (h : Apart a n b m) (hnw : NoWrap a n)
    (hk : o + k ≤ n) : Apart (a + BitVec.ofNat 64 o) k b m := by
  have := NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by unfold NoWrap at hnw; omega)
  unfold NoWrap at hnw
  unfold Apart at h ⊢
  omega

theorem rodataApart_sub [Labels] {a : BitVec 64} {n o k : Nat}
    (h : NativeRustcVm.RodataApart rodataAddr a n) (hnw : NoWrap a n) (hk : o + k ≤ n) :
    NativeRustcVm.RodataApart rodataAddr (a + BitVec.ofNat 64 o) k := fun t ↦
  apart_sub (h t) hnw hk

theorem outOk_sub [Labels] {m : MachineData} {t : BitVec 64} {a : DecArea} {x : BitVec 64}
    {n N o k : Nat} (h : OutOk m t a x n N) (hk : o + k ≤ n) :
    OutOk m t a (x + BitVec.ofNat 64 o) k N :=
  ⟨NativeRustcVm.Mapped.sub h.1 hk, NativeRustcVm.NoWrap.sub h.2.1 hk, apart_sub h.2.2.1 h.2.1 hk,
    apart_sub h.2.2.2.1 h.2.1 hk, apart_sub h.2.2.2.2.1 h.2.1 hk,
    apart_sub h.2.2.2.2.2 h.2.1 hk⟩

theorem whirOut_sub [Labels] {m : MachineData} {t : BitVec 64} {a : DecArea} {x : BitVec 64}
    {n N o k : Nat} (h : WhirOut m t a x n N) (hk : o + k ≤ n) :
    WhirOut m t a (x + BitVec.ofNat 64 o) k N :=
  ⟨outOk_sub h.1 hk, rodataApart_sub h.2 h.1.2.1 hk⟩

theorem whirIn_sub {m : MachineData} {x : BitVec 64} {n N o k : Nat} (h : WhirIn m x n N)
    (hk : o + k ≤ n) : WhirIn m (x + BitVec.ofNat 64 o) k N :=
  ⟨⟨NativeRustcVm.Mapped.sub h.1.1 hk, NativeRustcVm.NoWrap.sub h.1.2 hk⟩,
    apart_sub h.2 h.1.2 hk⟩

section
variable [Labels] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat}
  {F : Nat} {sl : List (Nat × XReg)} {kp : List XReg} {st : MachineData} {N' : Nat}

namespace Ctx

variable (c : Ctx a s0 levels ba b claim m0 rate)
  (hf : Fr m0 F whirLevelsStack sl kp (outs m0) st) (hF : F ≤ whirLevelsStack) (h16 : F % 16 = 0)
  (hle : F + N' ≤ whirLevelsStack)
include c hf hF h16 hle

/-- The read-only data for a callee. -/
theorem rodataAt : RodataAt st N' := by
  refine rodataAt_callee c.ro hf.same (fun q hq t ↦ ?_) hf.sp c.hN hF (by omega)
  rcases hq with hq | hq | hq
  · exact rodata_not_stack c.ro c.hN t hq
  · exact rodata_not_out c.pout.2 c.pout.1.2.1 t hq (c.ro t).2.1
  · exact rodata_not_out c.tro c.ts0.footprint.1.2 t hq (c.ro t).2.1

/-- **The transcript's context** for a callee. -/
theorem whirT : WhirT st (tA m0) a N' :=
  ⟨(c.tctx hF h16).stackOk hf hle, (c.tctx hF h16).rcAt hf hle, c.rodataAt hf hF h16 hle,
    (c.tctx hF h16).tstateOk hf hle, c.tro⟩

/-- An output for a callee. -/
theorem whirOut {o : BitVec 64} {n : Nat} (h : WhirOut m0 (tA m0) a o n whirLevelsStack) :
    WhirOut st (tA m0) a o n N' :=
  ⟨(c.tctx hF h16).outOk hf hle h.1, h.2⟩

omit hF h16 in
/-- An input for a callee. -/
theorem whirIn {x : BitVec 64} {n : Nat} (h : WhirIn m0 x n whirLevelsStack) :
    WhirIn st x n N' :=
  ⟨⟨fun i hi ↦ hf.kept _ (h.1.1 i hi), h.1.2⟩, hf.apart c.hN h.2 hle⟩

omit hF h16 in
/-- The basis's areas for a callee. -/
theorem basisIn {x o : BitVec 64} {n : Nat} (h : BasisIn m0 x ba whirLevelsStack o n) :
    BasisIn st x ba N' o n :=
  ⟨c.whirIn hf hle h.1, h.2.1, fun r hr ↦ ⟨c.whirIn hf hle (h.2.2 r hr).1,
    (h.2.2 r hr).2⟩⟩

end Ctx

omit [Labels] in
/-- The callee-saved registers kept keep `Regs`. -/
theorem Regs.saved {len : Nat} {st st' : MachineData} (h : Regs m0 len st)
    (hcs : ∀ r, calleeSaved r = true → st'.regs.getXReg r = st.regs.getXReg r) :
    Regs m0 len st' where
  x19 := (hcs .X19 rfl).trans h.x19
  x20 := (hcs .X20 rfl).trans h.x20
  x21 := (hcs .X21 rfl).trans h.x21
  x22 := (hcs .X22 rfl).trans h.x22
  x23 := (hcs .X23 rfl).trans h.x23
  x24 := by rw [hcs .X24 rfl]; exact h.x24
  x25 := (hcs .X25 rfl).trans h.x25
  x27 := by rw [hcs .X27 rfl]; exact h.x27
  x28 := by rw [hcs .X28 rfl]; exact h.x28

omit [Labels] in
/-- Registers and memory kept keep `Regs`. -/
theorem Regs.congr {len : Nat} {st st' : MachineData} (h : Regs m0 len st)
    (he : ∀ r, st'.regs.getXReg r = st.regs.getXReg r) : Regs m0 len st' :=
  h.saved fun r _ ↦ he r

omit [Labels] in
/-- Registers and memory kept keep the frame. -/
theorem WFr.congr {st st' : MachineData} (h : WFr m0 st) (hsp : st'.regs.SP = st.regs.SP)
    (he : ∀ r, st'.regs.getXReg r = st.regs.getXReg r) (hd : st'.dmem = st.dmem) : WFr m0 st' :=
  h.step hsp (fun r _ ↦ he r) (fun p hp ↦ by rw [hd]; exact hp)
    (NativeRustcVm.SameOutside.of_eq hd (fun _ ↦ False)) (fun _ h ↦ h.elim) fun _ _ _ _ h ↦ h

end

/-! ## `fold_rounds` -/

theorem roundsOff_le : roundsOff + (8 + roundBytes * roundCap) ≤ whirBytes := by decide

section
variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat}

/-- **`fold_rounds`** at level `k`: the run rejected (`0`), or `Mid k` (`1`). -/
theorem fold_call
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmArm.Vm.FoldRounds.entryLabel) (FoldRoundsPre a s w)
      (FoldRoundsPost a s w))
    (c : Ctx a s0 levels ba b claim m0 rate) {k : Nat} {s : TState} {w : WhirStateW}
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hh : Head a s0 levels b claim m0 k s w st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.FoldRounds.entryLabel ∧ retOf st.data = next)
    (hx0 : st.data.regs.X0 = m0.regs.X0) (hx1 : st.data.regs.X1.toNat = foldAt k)
    (hx2 : st.data.regs.X2 = m0.regs.X6)
    (hx3 : st.data.regs.X3.toBitVec = pA m0 + BitVec.ofNat 64 roundsOff)
    (hx26 : X26Ok m0 levels.length k st.data)
    (cont : ∀ m2, WFr m0 m2 → Regs m0 levels.length m2 →
      (m2.regs.X0 = 0 ∧ runAll s0 levels b claim m0 = none) ∨
        (m2.regs.X0 = 1 ∧ ∃ s' w' rs, Mid a s0 levels b claim m0 rate k s' w' rs m2) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨hv, hv1, -, -⟩ := stack_val
  have hle : 96 + foldRoundsStack ≤ whirLevelsStack := by omega
  have hf := hh.fr
  have hk := hh.lt
  have hl6 := c.len_le.2
  have ht : st.data.regs.X0.toBitVec = tA m0 := by rw [hx0]
  have hp : st.data.regs.X2.toBitVec = pA m0 := by rw [hx2]
  have hro := roundsOff_le
  have hpre : FoldRoundsPre a s w st.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht]; exact c.whirT hf (by omega) rfl hle
    · rw [ht]; exact hh.ts
    · rw [hp]; exact hh.ws
    · rw [hx1]; unfold foldAt roundCap; split_ifs <;> omega
    · rw [hx1, hh.alphas]; unfold alphasAt foldAt stackCap; split_ifs <;> omega
    · rw [ht, hp]
      have := whirOut_sub (o := 0) (k := stateBytes) c.pout (by decide)
      rw [NativeRustcVm.addr_add_zero] at this
      exact c.whirOut hf (by omega) rfl hle this
    · rw [ht, hx3]
      exact c.whirOut hf (by omega) rfl hle (whirOut_sub c.pout hro)
    · rw [hx3, hp]
      have hnw := c.pout.1.2.1
      have := NativeRustcVm.toNat_add_ofNat (a := pA m0) (i := roundsOff)
        (by unfold NoWrap at hnw; unfold whirBytes at hnw; unfold roundsOff; omega)
      unfold Apart
      rw [this]
      unfold roundsOff stateBytes
      omega
  refine Fr.leafAt hf c.hN hle keep_saved slots_le (fun q hq ↦ c.outs_not_frame (by omega) hq)
    (hfr a s w) hpc hpre (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq ↦ ?_,
      hq.2.2.2⟩) fun m2 hf2 hq hcs ↦ cont m2 hf2 (hh.regs.saved hcs) ?_
  · rcases hq with ⟨r, hr, hq⟩ | hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · right; left
        have hq' : InRange (pA m0 + BitVec.ofNat 64 roundsOff) (8 + roundBytes * roundCap) q := by
          rw [← hx3]; exact hq
        exact NativeRustcVm.InRange.of_sub hq' c.pout.1.2.1 hro
      · right; left
        have hq' : InRange (pA m0) stateBytes q := by rw [← hp]; exact hq
        exact NativeRustcVm.InRange.mono hq' (NativeRustcVm.NoWrap.mono c.pout.1.2.1 (by decide))
          c.pout.1.2.1 le_rfl (by unfold stateBytes whirBytes; omega)
      · right; right; rw [← ht]; exact hq
    · left; exact hq
  · obtain ⟨h0, hsome, -, -⟩ := hq
    rw [hx1] at h0 hsome
    have hrun := hh.run
    rw [c.drop_eq hk] at hrun
    rcases hres : (foldRounds (foldAt k) w).run s with _ | ⟨⟨w', rs⟩, s'⟩
    · rw [hres] at h0
      exact .inl ⟨h0, hrun.trans (run_none (level := lvl (logN m0) rate k) hres)⟩
    · rw [hres] at h0
      obtain ⟨hws', hrs', hts'⟩ := hsome w' rs s' hres
      obtain ⟨ha', hg', hr'⟩ := foldRounds_facts hres
      have hx26' : X26Ok m0 levels.length k m2 := by
        unfold X26Ok at hx26 ⊢; rw [hcs .X26 rfl]; exact hx26
      refine .inr ⟨h0, s', w', rs, hf2, hh.regs.saved hcs, hx26', ?_, ⟨?_, ?_⟩, hk, ?_, ?_, ?_,
        fun hk1 ↦ ?_, fun hk1 ↦ ?_⟩
      · rw [← ht]; exact hts'
      · rw [← hp]; exact hws'
      · show BufRoundsAt m2.dmem (pA m0 + BitVec.ofNat 64 roundsOff) _
        rw [← hx3]; exact hrs'
      · rw [ha', hh.alphas, alphasAt_succ]
      · rw [hg', hh.glued]
      · rw [hr']; exact hh.roots
      · rw [List.drop_eq_nil_of_le (by omega)] at hrun
        exact hrun.trans (run_final (level := lvl (logN m0) rate k) hres)
      · rw [c.drop_eq hk1] at hrun ⊢
        exact hrun.trans (run_next (level := lvl (logN m0) rate k) hres)

end

end

end NativeRustcVmArm.Whir.WhirLevels
