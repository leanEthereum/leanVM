module

public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.Absorb.Exec

/-!
# `SpongeW::absorb`'s push and epilogue

**`tail`**: from `.LSpongeWAbsorb_2` with a queue of `n < 4` scalars at the sponge (X20, X8 = `n`)
and the scalar and tag in X22, X21, X19, `b3` stores them in slot `n` and the count `n + 1`; `b4`
restores the registers and returns.
-/

namespace NativeRustcVmArm.Transcript.Absorb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWAbsorb
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm LeanVM.Parameters LeanVM.Protocol.Compile

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

/-- The absorb's outputs: the sponge and the stack. -/
abbrev Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange m0.regs.X0.toBitVec 328 q ∨
    NativeRustcVm.InRange (stackBelow m0 absorbStack) absorbStack q

variable [Host] {k : Nat}

/-- **The push and the epilogue.** -/
theorem tail (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 absorbStack)
    (hmap : Mapped m0.dmem m0.regs.X0.toBitVec 328) (hnw : m0.regs.X0.toBitVec.toNat + 328 ≤ 2 ^ 64)
    (hapF : NativeRustcVm.Apart m0.regs.X0.toBitVec 328 (frameBase m0 48) 48) {sp0 : SpongeW}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWAbsorb.b3Offset)) (hf : Frame m0 48 slots st.data)
    (hlt : sp0.pending.size < 4) (hx8 : st.data.regs.X8.toNat = sp0.pending.size)
    (hx19 : st.data.regs.X19 = m0.regs.X3) (hx20 : st.data.regs.X20.toBitVec = m0.regs.X0.toBitVec)
    (hx21 : st.data.regs.X21 = m0.regs.X2) (hx22 : st.data.regs.X22 = m0.regs.X1)
    (hsp : SpongeAt st.data.dmem m0.regs.X0.toBitVec sp0)
    (hso : SameOutside m0.dmem st.data.dmem (Out m0)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      SpongeAt st'.data.dmem m0.regs.X0.toBitVec
        { sp0 with pending := sp0.pending.push (⟨m0.regs.X1, m0.regs.X2⟩, m0.regs.X3) } ∧
      SameOutside m0.dmem st'.data.dmem (Out m0) ∧ Saved m0 st'.data) st := by
  set p := m0.regs.X0.toBitVec with hpdef
  set n := sp0.pending.size with hndef
  have hfnw := frame_noWrap (m := m0) (F := 48) (by
    have := hst.2.1; have e : absorbStack = 464 := rfl; omega)
  have hwf : (frameEnv m0 st.data 48 [(p, 328)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 48) hst (by decide)) hf.kept, hfnw⟩,
      ⟨Mapped.keeps hmap hf.kept, hnw⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm : Match (frameEnv m0 st.data 48 [(p, 328)]) (pushS n) st.data := by
    refine match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun,
      trivial⟩ (by rw [hf.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl hx20, ?_, trivial⟩ trivial trivial trivial
    show st.data.regs.X8.toBitVec = BitVec.ofNat 64 n
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, UInt64.toNat_toBitVec, hx8]
    omega
  obtain ⟨hrun, hok, hwc, hw0, hw1, hw2, hws⟩ := run_b3 n hlt
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) hrun hwf hpc hm fun st4 hm4 hpc4 => ?_
  have hf4 : Frame m0 48 slots st4.data := Frame.of_block hf hwf hm4 hok slots_le
  have hs4 := sameOutside_W hwf hm4 (r := 1) (W := fun j ↦ (200 + 24 * n ≤ j ∧ j < 224 + 24 * n) ∨
    (296 ≤ j ∧ j < 304)) rfl (fun w hw ↦ by
      obtain ⟨hr, h⟩ := hws w hw
      exact ⟨hr, by omega, fun j h1 h2 ↦ by omega⟩)
  have hA : Agree st.data.dmem st4.data.dmem p spongeBytes
      (fun j ↦ (200 + 24 * n ≤ j ∧ j < 224 + 24 * n) ∨ (296 ≤ j ∧ j < 304)) :=
    agree_of_sameOutside hnw (fun _ h ↦ h.elim) hs4
  have hsp4 : SpongeAt st4.data.dmem p
      { sp0 with pending := sp0.pending.push (⟨m0.regs.X1, m0.regs.X2⟩, m0.regs.X3) } := by
    refine hsp.push (by unfold rateScalars; omega) hA ?_ ⟨ewAt_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · have h := wordAt_write hm4 (r := 1) (o := 296) (b := p) (sz := 328) rfl (by omega) hwc
      have e : UInt64.ofBitVec ((Sym.lit (n + 1)).eval (frameEnv m0 st.data 48 [(p, 328)])) =
          (n + 1).toUInt64 := rfl
      rw [e] at h; exact h
    · have h := wordAt_write hm4 (r := 1) (o := 200 + 24 * n) (b := p) (sz := 328) rfl (by omega) hw0
      have e : UInt64.ofBitVec ((Sym.reg .X22).eval (frameEnv m0 st.data 48 [(p, 328)])) =
          m0.regs.X1 := hx22
      rw [e] at h; exact h
    · have h := wordAt_write hm4 (r := 1) (o := 208 + 24 * n) (b := p) (sz := 328) rfl (by omega) hw1
      have e : UInt64.ofBitVec ((Sym.reg .X21).eval (frameEnv m0 st.data 48 [(p, 328)])) =
          m0.regs.X2 := hx21
      rw [e] at h
      rw [off_off, show 200 + 24 * n + 8 = 208 + 24 * n by omega]; exact h
    · have h := wordAt_write hm4 (r := 1) (o := 216 + 24 * n) (b := p) (sz := 328) rfl (by omega) hw2
      have e : UInt64.ofBitVec ((Sym.reg .X19).eval (frameEnv m0 st.data 48 [(p, 328)])) =
          m0.regs.X3 := hx19
      rw [e] at h
      rw [off_off, show 200 + 24 * n + 16 = 216 + 24 * n by omega]; exact h
  -- `b4`: the epilogue.
  have hwf4 : (frameEnv m0 st4.data 48 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 48) hst (by decide)) hf4.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm4' : Match (frameEnv m0 st4.data 48 []) exitS st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf4
    (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWAbsorb.b3_next])) hm4' fun st5 hm5 hpc5 => ?_
  obtain ⟨hepi, hmem5⟩ := after_eq run_b4 ▸ ok_b4
  obtain ⟨hsv5, hsl5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
  have hx30 : st5.data.regs.X30 = m0.regs.X30 := hsl5 (0, .X30) (List.mem_cons_self ..)
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
  refine .done _ ⟨by simp only [PcOk] at hpc5; rw [hpc5]; simp only [retOf, hx30], hd5 ▸ hsp4,
    fun q hq ↦ ?_, hsv5⟩
  rw [hd5, hs4 q fun h ↦ by
      rcases h with h | h
      · exact hq (Or.inl (inRange_of_touch hnw h))
      · exact h]
  exact hso q hq

end

end NativeRustcVmArm.Transcript.Absorb
