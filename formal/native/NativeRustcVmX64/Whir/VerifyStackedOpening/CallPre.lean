module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Copy
public import NativeRustcVm.Top.Same

/-!
# `verify_stacked_opening`: `whir_levels`' precondition (x86-64)

At the call of `whir_levels` (`AtCall`): the frame (RSP at its base), the outputs, the `BasisW`'s
words at the frame's `104`, the levels at `320`, WHIR's fresh state at the `WhirW`, the `WhirW`'s
address the stack argument, the arguments. `pre_of`: `whir_levels`' precondition with the basis
`basisOf` over the areas `baOf` and the batched target `claimOf`. `run_eq`: the model's run is
`whirLevels`'.
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening
open LeanVM.Parameters

@[expose] public section

/-- The basis' areas. -/
def baOf (layout : LayoutW) (cs : Array ColumnClaimW) (m0 : MachineData) : BasisAddrs :=
  ⟨off (scA m0) 8, cntOf layout cs, layA m0, reg m0 .rcx, reg m0 .r8, clA m0, oA m0⟩

/-- The basis. -/
def basisOf (s : TState) (layout : LayoutW) (target : EW) (point coefficients : Array EW)
    (cs : Array ColumnClaimW) (z : Array EW) (value : EW) : BasisW :=
  ⟨scalesOf s layout cs, stackClaims layout target point coefficients cs z value⟩

/-- **At the call of `whir_levels`.** -/
structure AtCall [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (ls : List Whir.Level) (m0 st : MachineData) :
    Prop where
  ok : Ok m0 st 0
  out : Outs a s layout cs m0 st.dmem
  fw : FW st.dmem m0 (fwL m0 ++ basisW m0 layout cs)
  lad : Whir.ladder layout.stackLog (reg m0 .rdx).toNat = some ls
  len : ls.length ≤ 6
  lv : LevelsAt st.dmem (win m0 320) ls
  ws : WhirStateAt st.dmem (pA m0) ⟨claimOf s layout target cs value, #[], #[]⟩
  arg : NativeRustcVm.WordAt st.dmem (win m0 8) (UInt64.ofBitVec (pA m0))
  rdi : reg st .rdi = tA m0
  rsi : reg st .rsi = layout.stackLog.toUInt64.toBitVec
  rdx : (reg st .rdx).toNat = (ls.head?.map (·.fold)).getD 0
  rcx : reg st .rcx = win m0 104
  r8 : reg st .r8 = win m0 320
  r9 : (reg st .r9).toNat = ls.length

end

public section

theorem regions_baOf {layout : LayoutW} {cs : Array ColumnClaimW} {m0 : MachineData} :
    (baOf layout cs m0).regions = ⟨off (scA m0) 8, 16 * cntOf layout cs⟩ :: vsoInputs m0 := rfl

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **The model's run** from the call of `whir_levels`. -/
theorem run_eq (h : Parts a s layout target coefficients point slices cs z value m0)
    {ls : List Whir.Level} (hlad : Whir.ladder layout.stackLog (reg m0 .rdx).toNat = some ls) :
    runOf s layout target coefficients point cs z value m0 =
      (whirLevels layout.stackLog ((ls.head?.map (·.fold)).getD 0)
        (basisOf s layout target point coefficients cs z value) 0 ls
        ⟨claimOf s layout target cs value, #[], #[]⟩).run (sq s).2 := by
  unfold runOf
  rw [vso_run _ _ _ (size_claims_le h.n_le target point coefficients z value), hlad,
    claimOf_eq, size_stackClaims]
  rfl

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

/-- An area apart from the stack and readable at the entry, for a callee. -/
theorem Ok.whirIn {st : MachineData} (hok : Ok m0 st 0) {N' : Nat}
    (hN' : 512 + N' ≤ verifyStackedOpeningStack) {x : BitVec 64} {n : Nat}
    (hin : WhirIn m0 x n verifyStackedOpeningStack) : WhirIn st x n N' :=
  ⟨⟨Mapped.keeps hin.1.1 hok.fr.kept, hin.1.2⟩, apart_callee hin.2 (Ok.sp hok) h.wt.1.1 hN'⟩

theorem Parts.sc8_apart {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Apart (scA m0) scalesBytes x n) :
    NativeRustcVm.Apart (off (scA m0) 8) (16 * cntOf layout cs) x n := by
  have hsc8 := h.sc8_le (layout := layout)
  have hscn : (scA m0).toNat + scalesBytes ≤ 2 ^ 64 := h.sc_nw
  unfold NativeRustcVm.Apart at hx ⊢
  rw [toNat_off (by unfold scalesBytes stackClaimCap at *; omega)]
  omega

/-- A frame window, including the return-address slot, lies in the entry's stack area. -/
theorem Parts.win_stack_cover {lo n : Nat} (hlo : lo + n ≤ 520) :
    (stackBelow m0 verifyStackedOpeningStack).toNat ≤ (win m0 lo).toNat ∧
      (win m0 lo).toNat + n ≤
        (stackBelow m0 verifyStackedOpeningStack).toNat + (verifyStackedOpeningStack + 8) := by
  have hr : 11936 ≤ (rspOf m0).toNat := h.rsp.1
  rw [h.sb, h.win_toNat (lo := lo) (by omega), stack_eq]
  omega

/-- **`whir_levels`' precondition.** -/
theorem pre_of {ls : List Whir.Level} {st : MachineData}
    (hc : AtCall a s layout target cs value ls m0 st) :
    WhirLevelsPre a (sq s).2 ls (baOf layout cs m0)
      (basisOf s layout target point coefficients cs z value) (claimOf s layout target cs value)
      st := by
  have hok := hc.ok
  have hR := h.rsp
  have hfb : (stackBelow m0 512).toNat = (rspOf m0).toNat - 512 := h.fbn
  have hN : 512 + whirLevelsStack ≤ verifyStackedOpeningStack := by rw [stack_eq]; decide
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans h.n_le
  have hsc8 := h.sc8_le (layout := layout)
  have hscn := h.sc_nw
  have hlen := hc.len
  have hlog : layout.stackLog < 2 ^ 64 := h.lay.stack_log_lt
  have hadm : Whir.Admissible layout.stackLog (reg m0 .rdx).toNat := by
    by_contra hn
    have := hc.lad
    simp [Whir.ladder, hn] at this
  have htok := h.wt.2.2.2.1
  have hpo := h.po
  have hso := h.so
  have hsp := Ok.sp hok
  -- the stack argument
  have hrsp8 : rspOf st + 8#64 = win m0 8 := by
    rw [hsp]
  have harg : stackArg st 0 = pA m0 := by
    unfold stackArg
    rw [show rspOf st + BitVec.ofNat 64 (8 + 8 * 0) = win m0 8 by rw [hsp],
      NativeRustcVm.wordOf_of_wordAt hc.arg]
  -- the basis' areas
  have hscIn : WhirIn st (off (scA m0) 8) (16 * cntOf layout cs) whirLevelsStack :=
    hok.whirIn h hN ⟨⟨mapped_off hso.1.1 hsc8, noWrap_off' hscn (by unfold cntOf; omega) hsc8⟩,
      h.sc8_apart hso.1.2.2.2.2.1⟩
  have hregs : ∀ r ∈ (baOf layout cs m0).regions, WhirIn st r.addr r.size whirLevelsStack ∧
      NativeRustcVm.Apart r.addr r.size (pA m0) whirBytes ∧
      NativeRustcVm.Apart r.addr r.size (tA m0) tstateBytes ∧
      NativeRustcVm.Apart r.addr r.size (stackBelow m0 verifyStackedOpeningStack)
        (verifyStackedOpeningStack + 8) := by
    intro r hr
    rw [regions_baOf] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨hscIn, h.sc8_apart (Apart.symm' h.psc), h.sc8_apart hso.1.2.2.1,
        h.sc8_apart hso.1.2.2.2.2.1⟩
    · have hi := h.ins r hr
      exact ⟨hok.whirIn h hN hi.1, hi.2.2.1, hi.2.1, hi.1.2⟩
  have hbin : ∀ (o : BitVec 64) (n : Nat),
      NativeRustcVm.Apart (win m0 104) 56 o n →
      (∀ r ∈ (baOf layout cs m0).regions, NativeRustcVm.Apart r.addr r.size o n) →
      BasisIn st (win m0 104) (baOf layout cs m0) whirLevelsStack o n := fun o n ho hr ↦
    ⟨hok.win_in h (lo := 104) (n := 56) (by omega) (by omega) hN, ho, fun r hr' ↦ ⟨(hregs r hr').1, hr r hr'⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ⟨(reg m0 .rdx).toNat, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hc.rdi]
    exact ⟨hok.stackOk h hN, hok.rcAt h hN, hok.rodataAt h hN,
      ⟨apart_callee htok.1 hsp h.wt.1.1 hN, apart_callee htok.2.1 hsp h.wt.1.1 hN, htok.2.2⟩,
      h.wt.2.2.2.2⟩
  · refine ⟨?_, by rw [hsp, hfb]; omega⟩
    rw [hrsp8]
    exact mapped_off (hok.frame_ok h).1 (by omega)
  · rw [hc.rdi]; exact hc.out.ts
  · show s.roots.size + ls.length ≤ 8
    have := h.roots; omega
  · rw [hc.rsi, u64n hlog]; exact hc.lad
  · rw [hc.r9]
  · rw [hc.r8]; exact hc.lv
  · rw [hc.rcx]
    refine ⟨by show cntOf layout cs < 2 ^ 64; unfold cntOf; omega, ?_,
      by simp [basisOf, baOf, size_scalesOf], hc.out.scs, ?_⟩
    · rw [NativeRustcVm.wordsAt_iff]
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      rw [off_add]
      have hw := hc.fw.right
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hw.get (by simp [basisW, baOf])
    · refine ⟨⟨layout, target, coefficients, point, slices, cs, z, value, hadm.2.1, ?_, ?_, ?_,
        ?_, ?_, rfl⟩⟩
      · exact hok.lay h
      · exact NativeRustcVm.Top.RingWAt.of_same h.ring (hok.same_in h mem_ring)
      · exact NativeRustcVm.Top.KeccakOutAt.of_same h.kec (hok.same_in h mem_kec)
      · exact hok.cl h
      · exact NativeRustcVm.Top.EqClaimAt.of_same h.ood (hok.same_in h mem_ood)
  · rw [harg]; exact hc.ws
  · rw [hc.rdi, harg]
    exact ⟨⟨Mapped.keeps hpo.1.1 hok.fr.kept, hpo.1.2.1, hpo.1.2.2.1, hpo.1.2.2.2.1,
      apart_callee hpo.1.2.2.2.2.1 hsp h.wt.1.1 hN, hpo.1.2.2.2.2.2⟩, hpo.2⟩
  · rw [hc.r8]
    exact hok.win_in h (by omega) (by show 320 + 24 * ls.length ≤ 520; omega) hN
  · rw [hc.r8, harg]; exact h.win_p (by show 320 + 24 * ls.length ≤ 520; omega)
  · rw [hc.r8, hc.rdi]; exact h.win_t (by show 320 + 24 * ls.length ≤ 520; omega)
  · rw [hc.rcx, harg]
    exact hbin _ _ (h.win_p (lo := 104) (n := 56) (by omega)) fun r hr ↦ (hregs r hr).2.1
  · rw [hc.rcx, hc.rdi]
    exact hbin _ _ (h.win_t (lo := 104) (n := 56) (by omega)) fun r hr ↦ (hregs r hr).2.2.1
  · rw [hc.rcx]
    refine List.pairwise_cons.mpr ⟨fun r hr ↦ h.win_apart (lo := 104) (n := 56) (by omega) (hregs r hr).2.2.2, ?_⟩
    rw [regions_baOf]
    refine List.pairwise_cons.mpr ⟨fun r hr ↦ ?_, h.pw⟩
    exact h.sc8_apart (Apart.symm' (h.ins r hr).2.2.2)
  · rw [hrsp8, hc.rdi]
    exact h.win_t (lo := 8) (n := 8) (by omega)
  · rw [hrsp8, harg]
    exact h.win_p (lo := 8) (n := 8) (by omega)
  · rw [hc.rdi, harg, hc.r8, hrsp8]
    apply hok.got_callee h hN (.refl _)
    intro ar har
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with (rfl | rfl | rfl | rfl | rfl) | har
    · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · exact ⟨(pA m0, whirBytes), by simp, le_rfl, le_rfl⟩
    · have hbytes : 320 + levelBytes * ls.length ≤ 520 :=
        (Nat.add_le_add_left (Nat.mul_le_mul_left 24 hlen) 320).trans (by decide)
      exact ⟨(stackBelow m0 verifyStackedOpeningStack, verifyStackedOpeningStack + 8),
        List.mem_cons_self, h.win_stack_cover (lo := 320) hbytes⟩
    · exact ⟨(stackBelow m0 verifyStackedOpeningStack, verifyStackedOpeningStack + 8),
        List.mem_cons_self, h.win_stack_cover (lo := 8) (n := 8) (by decide)⟩
    · exact ⟨ar, by simp [har], le_rfl, le_rfl⟩

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
