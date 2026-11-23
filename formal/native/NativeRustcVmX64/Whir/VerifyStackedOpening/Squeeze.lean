module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Step
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `verify_stacked_opening`: the batching challenge's squeeze (x86-64)

`Parts.squeeze`: `squeeze` on the `TState`'s sponge from a state of the frame at its call: the
challenge in RAX, RDX, the `TState` after it, `Ok` and the frame's bytes kept.
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir

public section

variable [Host] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **`squeeze`** on the `TState`'s sponge from a state of the frame at its call. -/
theorem Parts.squeeze (h : Parts a s layout target coefficients point slices cs z value m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {env : Env} {st : MachineState} (hok : Ok m0 st.data 0) {s' : TState}
    (hts : TStateAt st.data.dmem (tA m0) a s') (hdi : reg st.data .rdi = tA m0) {next : Int64}
    (hpc : PcOk env (.call NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) next st) {R : MachineState → Prop}
    (cont : ∀ st2 : MachineState, st2.pc = next → Ok m0 st2.data 8 →
      FrameSame m0 st.data.dmem st2.data.dmem →
      TStateAt st2.data.dmem (tA m0) a (sq s').2 →
      reg st2.data .rax = (sq s').1.c0.toBitVec → reg st2.data .rdx = (sq s').1.c1.toBitVec →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st.data r) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st := by
  have hN : 512 + squeezeStack ≤ verifyStackedOpeningStack := by rw [stack_eq]; decide
  have hsp := hok.sp
  have htok := h.wt.2.2.2.1
  have hfp := hts.footprint
  have hTn : (tA m0).toNat + 760 ≤ 2 ^ 64 := hfp.1.2
  have hpre : SqueezePre s'.sponge st.data := by
    unfold SqueezePre
    rw [hdi]
    have h1 := apart_callee htok.1 hsp h.wt.1.1 hN
    have h2 : (tA m0).toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (tA m0).toNat := htok.2.2
    refine ⟨hok.stackOk h hN, hok.rcAt h hN,
      ⟨fun j hj ↦ hfp.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_, ?_, ?_⟩,
      hts.sponge, ?_⟩
    · show (tA m0).toNat + 328 ≤ 2 ^ 64; omega
    · unfold NativeRustcVm.Apart at h1
      have : tstateBytes = 760 := rfl
      show (tA m0).toNat + 328 ≤ _ ∨ _ ≤ (tA m0).toNat
      omega
    · show (tA m0).toNat + 328 ≤ _ ∨ _ ≤ (tA m0).toNat; omega
    · apply hok.got_callee h hN (by simp)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, by
          dsimp only [Prod.fst, Prod.snd, spongeBytes, tstateBytes]; omega⟩
      · have hrc : (rcAddr, 192) ∈ rodataAreas := by
          change (rodataAddr .keccakRC, NativeRustcVm.Data.Item.bytes .keccakRC |>.length) ∈ rodataAreas
          exact List.mem_map.mpr ⟨.keccakRC, by decide, rfl⟩
        exact ⟨(rcAddr, 192), by simp [hrc], le_rfl, le_rfl⟩
  refine call_then (P := SqueezePre s'.sponge) (Q := SqueezePost s'.sponge) hpc (hsq s'.sponge) hpre
    fun st2 hpc2 hrsp2 ⟨hc0, hc1, hsp2, hs2, hsv2⟩ ↦ ?_
  rw [hdi] at hsp2 hs2
  have hT328 : ∀ q, NativeRustcVm.InRange (tA m0) spongeBytes q →
      NativeRustcVm.InRange (tA m0) tstateBytes q :=
    fun q hq ↦ inRange_mono hq (by simp only [spongeBytes]; show 328 ≤ 760; omega)
  obtain ⟨hok2, hfs⟩ := hok.call h hsv2 hrsp2 (N' := squeezeStack) hN
    (Rw := NativeRustcVm.InRange (tA m0) spongeBytes)
    (fun q hq ↦ .inr (.inr (hT328 q hq))) hs2
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st.data squeezeStack) squeezeStack q →
      ¬ NativeRustcVm.InRange (tA m0) tstateBytes q ∧
        ¬ NativeRustcVm.InRange a.words (8 * a.len) q := fun q hq ↦ by
    have hs := (h.callee_stack hsp hN hq).1
    have hsnw := noWrap_stackBelow h.wt.1
    exact ⟨fun ht ↦ not_inRange_of_apart htok.1 hTn hsnw ht (inRange_mono hs (by omega)),
      fun hd ↦ not_inRange_of_apart htok.2.1 hfp.2.1.2 hsnw hd (inRange_mono hs (by omega))⟩
  have hts2 : TStateAt st2.data.dmem (tA m0) a (sq s').2 := by
    refine hts.with_sponge hsv2.2 hcal (fun q hq ↦ hs2 q ?_) hsp2
    rintro (h' | h')
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn : NativeRustcVm.NoWrap (tA m0) 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
    · exact hq (Or.inr h')
  exact cont st2 hpc2 hok2 hfs hts2 hc0 hc1 hsv2.1

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
