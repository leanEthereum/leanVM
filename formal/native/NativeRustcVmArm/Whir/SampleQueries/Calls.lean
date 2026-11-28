module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Whir.SampleQueries.Defs
public import NativeRustcVmArm.Sumcheck.Common

/-!
# `sample_queries`: what its frame keeps, its calls

From the precondition at `m1` and the frame (`SFr m1 st`): the round constants, the read-only data,
the stack and the `TState`'s footprint where a callee needs them (`rc_at`, `rodata_at`,
`stackOk_at`), and the two calls: `SpongeW::squeeze` on the `TState`'s sponge (`squeeze_call`: the
challenge `(sq s).1` in X0, X1, the `TState` then `(sq s).2`) and `query_bits` (`queryBits_call`).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

theorem sponge_le : spongeBytes ≤ tstateBytes := by decide

theorem N_eq : sampleQueriesStack = 112 + squeezeStack := rfl
theorem squeezeStack_eq : squeezeStack = 432 := rfl

/-- The SP of a frame's state is the frame's base. -/
theorem sp_of {m1 st : MachineData} (hf : SFr m1 st) :
    st.regs.SP.toBitVec = m1.regs.SP.toBitVec - BitVec.ofNat 64 112 := hf.sp

variable {a : DecArea} {s0 : TState} {m1 : MachineData}


variable [Labels] in
/-- The precondition's pieces at `m1`. -/
theorem pre_stack (h : SampleQueriesPre a s0 m1) : StackOk m1 sampleQueriesStack := h.1.1
variable [Labels] in
theorem pre_N (h : SampleQueriesPre a s0 m1) : sampleQueriesStack ≤ m1.regs.SP.toNat := h.1.1.2.1

/-- A range apart from the entry's stack and the outputs keeps its bytes in the frame's states. -/
theorem keep_bytes {st : MachineData} (hf : SFr m1 st) {x : BitVec 64} {bs : List UInt8}
    (hb : NativeRustcVm.BytesAt m1.dmem x bs) (hx : NoWrap x bs.length)
    (hs : Apart x bs.length (stackBelow m1 sampleQueriesStack) sampleQueriesStack)
    (ho : Apart x bs.length (oA m1) queryBufBytes) (ht : Apart x bs.length (tA m1) tstateBytes)
    (hno : NoWrap (oA m1) queryBufBytes) (hnt : NoWrap (tA m1) tstateBytes)
    (hN : sampleQueriesStack ≤ m1.regs.SP.toNat) :
    NativeRustcVm.BytesAt st.dmem x bs :=
  hb.of_sameOutside hf.same fun i hi hq ↦ by
    rcases hq with hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange_add hs hx (base_noWrap hN) hi hq
    · exact NativeRustcVm.Apart.not_inRange_add ho hx hno hi hq
    · exact NativeRustcVm.Apart.not_inRange_add ht hx hnt hi hq

variable [Labels]

/-- **The round constants** for a callee of `N'` bytes of stack. -/
theorem rc_at (h : SampleQueriesPre a s0 m1) {st : MachineData} (hf : SFr m1 st) {N' : Nat}
    (hle : 112 + N' ≤ sampleQueriesStack) : RcAt st N' := by
  have hrc := h.1.2.1
  have hN := pre_N h
  obtain ⟨hto, hda, htr⟩ := h.1.2.2.2.1
  obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, -⟩ := h.2.2.2
  have hfp := h.2.1.footprint
  refine Sumcheck.RcAt.sub hrc (sp_of hf) hle hN fun p hp ↦ hf.same p fun hq ↦ ?_
  have hnrc : NoWrap rcAddr 192 := hrc.2.1
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange hrc.2.2 hnrc (base_noWrap hN) hp hq
  · exact NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm hor) hnrc hno hp hq
  · exact NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm htr) hnrc hfp.1.2 hp hq

omit [Labels] in
/-- The callee's stack below a frame's state is inside the entry's. -/
theorem stack_in {st : MachineData} (hf : SFr m1 st) {N' : Nat} (hle : 112 + N' ≤ sampleQueriesStack)
    (hN : sampleQueriesStack ≤ m1.regs.SP.toNat) {q : BitVec 64}
    (hq : InRange (stackBelow st N') N' q) : InRange (stackBelow m1 sampleQueriesStack)
      sampleQueriesStack q := by
  rw [stackBelow_eq hf.sp (by omega)] at hq
  have e1 := base_toNat (m0 := m1) (F := 112 + N') (by omega)
  have e2 := base_toNat (m0 := m1) (F := sampleQueriesStack) hN
  have := m1.regs.SP.toNat_lt
  rw [Sym.inRange_iff (by omega)] at hq
  rw [show stackBelow m1 sampleQueriesStack = base m1 sampleQueriesStack from rfl,
    Sym.inRange_iff (by omega)]
  omega

end

public section

/-- A contract with a condition on the entry carried to the exit. -/
theorem spec_and [NativeRustcArm.Host] {e : Int64} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (h : Spec e P Q) (C : MachineData → Prop) :
    Spec e (fun m ↦ P m ∧ C m) (fun m m' ↦ Q m m' ∧ C m) := by
  intro m hpc
  exact Eventually.mono (h m hpc.1) fun _ hh ↦ ⟨hh.1, hh.2, hpc.2⟩

section
variable [Host] {a : DecArea} {s0 : TState} {m1 : MachineData}

/-- **`SpongeW::squeeze` on the `TState`'s sponge**: the challenge `(sq s).1` in X0, X1, the
`TState` then `(sq s).2`, nothing else changed but the sponge and the callee's stack. -/
theorem squeeze_call (h : SampleQueriesPre a s0 m1)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (hf : SFr m1 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel ∧ retOf st.data = next)
    (hx0 : st.data.regs.X0 = m1.regs.X0) {s : TState} (hts : TStateAt st.data.dmem (tA m1) a s)
    (cont : ∀ m2 : MachineData, SFr m1 m2 → TStateAt m2.dmem (tA m1) a (sq s).2 →
      m2.regs.X0 = (sq s).1.c0 → m2.regs.X1 = (sq s).1.c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange (tA m1) spongeBytes q ∨
        InRange (stackBelow st.data squeezeStack) squeezeStack q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hN := pre_N h
  have hS := pre_stack h
  obtain ⟨hto, hda, htr⟩ := h.1.2.2.2.1
  have hfp := hts.footprint
  have hle : 112 + squeezeStack ≤ sampleQueriesStack := by rw [N_eq]
  have hspst := hf.stackOk hS (by decide) hle
  have hts' := hf.apart hN hto hle
  have hda' := hf.apart hN hda hle
  have hnwt : NoWrap (tA m1) spongeBytes := NativeRustcVm.NoWrap.mono hfp.1.2 sponge_le
  have hnws : NoWrap (stackBelow st.data squeezeStack) squeezeStack := by
    rw [stackBelow_eq hf.sp (by omega)]
    exact NativeRustcVm.NoWrap.mono (base_noWrap (m0 := m1) (F := 112 + squeezeStack) (by omega))
      (by omega)
  have hpre : SqueezePre s.sponge st.data := by
    have sl := sponge_le
    refine ⟨hspst, rc_at h hf hle, ⟨?_, by rw [hx0]; exact hnwt, ?_, ?_⟩, ?_⟩
    · rw [hx0]; exact NativeRustcVm.Mapped.mono hfp.1.1 sl
    · rw [hx0]
      exact NativeRustcVm.Apart.mono hts' (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)
    · rw [hx0]
      exact NativeRustcVm.Apart.mono htr (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)
    · rw [hx0]; exact hts.sponge
  refine Fr.leaf hf hN hle (by simp) (by decide) ?_
    (spec_and (hsq s.sponge) fun m ↦ m.regs.X0 = m1.regs.X0) (fun m m' hq ↦ ?_) hpc ⟨hpre, hx0⟩
    fun m2 hf2 hq hcs ↦ ?_
  · intro q hq hin
    have hnf := base_noWrap (m0 := m1) (F := 112) (by omega)
    have hnN := base_noWrap hN
    have e1 := base_toNat (m0 := m1) (F := 112) (by omega)
    have e2 := base_toNat (m0 := m1) (F := sampleQueriesStack) hN
    have hsub : InRange (base m1 sampleQueriesStack) sampleQueriesStack q :=
      NativeRustcVm.InRange.mono hin hnf hnN (by omega) (by omega)
    obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, -⟩ := h.2.2.2
    rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange hos hno hnN hq hsub
    · exact NativeRustcVm.Apart.not_inRange hto hfp.1.2 hnN hq hsub
  · obtain ⟨⟨-, -, -, hs, hsv⟩, hx⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · right; right
      rw [hx] at hq
      exact NativeRustcVm.InRange.mono hq hnwt hfp.1.2 (Nat.le_refl _)
        (by have := sponge_le; omega)
    · exact Or.inl hq
  · obtain ⟨⟨h0, h1, hsp, hs, hsv⟩, -⟩ := hq
    rw [hx0] at hsp hs
    refine cont m2 hf2 ?_ h0 h1 hcs hs
    refine hts.with_sponge (R := fun q ↦ InRange (stackBelow st.data squeezeStack) squeezeStack q)
      hsv.2.2 (fun q hq ↦ ⟨?_, ?_⟩) (NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_) hsp
    · exact NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm hts') hnws hfp.1.2 hq
    · exact NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm hda') hnws
        hfp.2.1.2 hq
    · rcases hq with hq | hq
      · left
        obtain ⟨i, hi, rfl⟩ := NativeRustcVm.InRange.exists hq
        exact ⟨i, by have := sponge_le; omega, hi, rfl⟩
      · exact Or.inr hq

end

end

end NativeRustcVmArm.Whir.SampleQueries
