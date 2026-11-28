module

public import NativeRustcVmX64.Transcript.Absorb.Exec

/-!
# `SpongeW::absorb`'s push and epilogue (x86-64)

**`tail`**: from `NativeRustcVmX64.Vm.SpongeWAbsorb.label_2` with a queue of `n < 4` scalars at the sponge (RBX, RAX =
`n`) and the scalar and tag in R12, R15, R14, `b3` stores them in slot `n` and the count `n + 1`;
`b4` pops the registers and returns.
-/

namespace NativeRustcVmX64.Transcript.Absorb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWAbsorb
open NativeRustcVm.Transcript NativeVm.Model

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

/-- The absorb's outputs: the sponge and the stack. -/
abbrev Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) 328 q ∨
    NativeRustcVm.InRange (stackBelow m0 absorbStack) absorbStack q

variable [Host] {k : Nat}

/-- **The push and the epilogue.** -/
theorem tail (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 absorbStack)
    (hmap : NativeRustcVm.Mapped m0.dmem (reg m0 .rdi) 328)
    (hnw : NativeRustcVm.NoWrap (reg m0 .rdi) 328)
    (hapF : NativeRustcVm.Apart (reg m0 .rdi) 328 (stackBelow m0 48) (48 + 8)) {sp0 : SpongeW}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SpongeWAbsorb.b3Offset)) (hf : Frame m0 48 slots 8 st.data)
    (hlt : sp0.pending.size < 4) (hrax : reg st.data .rax = BitVec.ofNat 64 sp0.pending.size)
    (hr14 : reg st.data .r14 = reg m0 .rcx) (hrbx : reg st.data .rbx = reg m0 .rdi)
    (hr15 : reg st.data .r15 = reg m0 .rdx) (hr12 : reg st.data .r12 = reg m0 .rsi)
    (hsp : SpongeAt st.data.dmem (reg m0 .rdi) sp0)
    (hso : NativeRustcVm.SameOutside m0.dmem st.data.dmem (Out m0)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧
      SpongeAt st'.data.dmem (reg m0 .rdi)
        { sp0 with pending := (sp0.pending.push
          (⟨.ofBitVec (reg m0 .rsi), .ofBitVec (reg m0 .rdx)⟩, .ofBitVec (reg m0 .rcx))) } ∧
      NativeRustcVm.SameOutside m0.dmem st'.data.dmem (Out m0) ∧ Saved m0 st'.data) st := by
  set p := reg m0 .rdi with hpdef
  set n := sp0.pending.size with hndef
  have hfnw := frame_noWrap (F := 48) hst (by decide)
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 48) (rest := [(p, 328)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hmap hf.kept, hnw⟩)
    (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm : Match (frameEnv m0 st.data 48 [(p, 328)]) (pushS n) st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, known_ptr rfl hrbx, hrax, trivial⟩ trivial
      trivial trivial
  obtain ⟨hrun, hok, hwc, hw0, hw1, hw2, hws⟩ := run_b3 n hlt
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) hrun hwf nofun hpc hm
    fun st4 hm4 hpc4 => ?_
  have hf4 : Frame m0 48 slots 8 st4.data := Frame.of_block hf hwf hm4 hok slots_le
  have hs4 := sameOutside_W hwf hm4 (r := 1) (W := fun j ↦ (200 + 24 * n ≤ j ∧ j < 224 + 24 * n) ∨
    (296 ≤ j ∧ j < 304)) rfl (fun w hw ↦ by
      obtain ⟨hr, h⟩ := hws w hw
      exact ⟨hr, by omega, fun j h1 h2 ↦ by omega⟩)
  have hA : Agree st.data.dmem st4.data.dmem p spongeBytes
      (fun j ↦ (200 + 24 * n ≤ j ∧ j < 224 + 24 * n) ∨ (296 ≤ j ∧ j < 304)) :=
    agree_of_sameOutside (R := fun _ ↦ False) hnw (fun _ h ↦ h.elim)
      (SameOutside.mono hs4 fun _ h ↦ Or.inl h)
  have hsp4 : SpongeAt st4.data.dmem p
      { sp0 with pending := (sp0.pending.push
        (⟨.ofBitVec (reg m0 .rsi), .ofBitVec (reg m0 .rdx)⟩, .ofBitVec (reg m0 .rcx))) } := by
    refine hsp.push (by unfold LeanVM.Protocol.Compile.rateScalars; omega) hA ?_
      ⟨ewAt_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · have h := wordAt_write hm4 (r := 1) (o := 296) (b := p) (sz := 328) rfl (by omega) hwc
      have e : UInt64.ofBitVec ((Sym.lit (n + 1)).eval (frameEnv m0 st.data 48 [(p, 328)])) =
          (n + 1).toUInt64 := rfl
      rw [e] at h; exact h
    · have h := wordAt_write hm4 (r := 1) (o := 200 + 24 * n) (b := p) (sz := 328) rfl
        (by omega) hw0
      have e : UInt64.ofBitVec ((Sym.reg .r12).eval (frameEnv m0 st.data 48 [(p, 328)])) =
          .ofBitVec (reg m0 .rsi) := by rw [← hr12]; rfl
      rw [e] at h; exact h
    · have h := wordAt_write hm4 (r := 1) (o := 208 + 24 * n) (b := p) (sz := 328) rfl
        (by omega) hw1
      have e : UInt64.ofBitVec ((Sym.reg .r15).eval (frameEnv m0 st.data 48 [(p, 328)])) =
          .ofBitVec (reg m0 .rdx) := by rw [← hr15]; rfl
      rw [e] at h
      rw [off_off, show 200 + 24 * n + 8 = 208 + 24 * n by omega]; exact h
    · have h := wordAt_write hm4 (r := 1) (o := 216 + 24 * n) (b := p) (sz := 328) rfl
        (by omega) hw2
      have e : UInt64.ofBitVec ((Sym.reg .r14).eval (frameEnv m0 st.data 48 [(p, 328)])) =
          .ofBitVec (reg m0 .rcx) := by rw [← hr14]; rfl
      rw [e] at h
      rw [off_off, show 200 + 24 * n + 16 = 216 + 24 * n by omega]; exact h
  -- `b4`: the epilogue.
  have hwf4 := frame_wf (m0 := m0) (d := st4.data) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf4.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf4 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWAbsorb.b3_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf4.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st5 hm5 hpc5 => ?_
  obtain ⟨hepi, hmem5⟩ := after_eq run_b4 ▸ ok_b4
  obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
  simp only [PcOk] at hpc5
  refine .done _ ⟨by rw [hpc5]; exact hf4.load_ret hst (by decide), hrsp5, hd5 ▸ hsp4,
    fun q hq ↦ ?_, hsv5⟩
  rw [hd5, hs4 q fun h ↦ hq (Or.inl (inRange_of_touch hnw h))]
  exact hso q hq

end

end NativeRustcVmX64.Transcript.Absorb
