module

public import NativeRustcVmArm.Whir.VerifyStackedOpening.LadStep
public import NativeRustcVmArm.Whir.WhirLevels.Calls

/-!
# `verify_stacked_opening`: `whir_levels`' precondition

At the call of `whir_levels` (`AtCall`): the frame with all the outputs, the `TState` after the
squeeze, the scales, the `BasisW`'s words at the frame's byte 56, the levels copied to byte 112,
WHIR's fresh state at the `WhirW`, the arguments. `pre_of`: `whir_levels`' precondition with the
basis `basisOf` over the areas `baOf` and the batched target `claimOf`.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open LeanVM.Parameters

@[expose] public section

/-- The basis' areas. -/
def baOf (layout : LayoutW) (cs : Array ColumnClaimW) (m0 : MachineData) : BasisAddrs :=
  ⟨scA m0 + BitVec.ofNat 64 8, cntOf layout cs, m0.regs.X1.toBitVec, m0.regs.X3.toBitVec,
    m0.regs.X4.toBitVec, m0.regs.X5.toBitVec, m0.regs.X6.toBitVec⟩

/-- The basis. -/
def basisOf (s : TState) (layout : LayoutW) (target : EW) (point coefficients : Array EW)
    (cs : Array ColumnClaimW) (z : Array EW) (value : EW) : BasisW :=
  ⟨scalesOf s layout cs, stackClaims layout target point coefficients cs z value⟩

/-- **At the call of `whir_levels`.** -/
structure AtCall [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (ls : List Whir.Level) (m0 st : MachineData) :
    Prop where
  fr : OFr m0 (outsF m0) st
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  scs : NativeRustcVm.EWsAt st.dmem (scA m0 + BitVec.ofNat 64 8) (scalesOf s layout cs).toList
  fwb : FW st.dmem m0 (basisWords layout cs m0)
  lad : Whir.ladder layout.stackLog m0.regs.X2.toNat = some ls
  len : ls.length ≤ 6
  lv : LevelsAt st.dmem (loc m0 112) ls
  ws : WhirStateAt st.dmem (pA m0) ⟨claimOf s layout target cs value, #[], #[]⟩
  x0 : st.regs.X0 = m0.regs.X0
  x1 : st.regs.X1 = layout.stackLog.toUInt64
  x2 : st.regs.X2.toNat = (ls.head?.map (·.fold)).getD 0
  x3 : st.regs.X3.toBitVec = loc m0 56
  x4 : st.regs.X4.toBitVec = loc m0 112
  x5 : st.regs.X5 = ls.length.toUInt64
  x6 : st.regs.X6.toBitVec = pA m0

end

public section

variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

omit [Labels] in
theorem regions_baOf : (baOf layout cs m0).regions =
    ⟨scA m0 + BitVec.ofNat 64 8, 16 * cntOf layout cs⟩ :: vsoInputs m0 := rfl

omit [Labels] in
/-- The frame's words from byte `o`, as words. -/
theorem wordsAt_of_fw {d : Mem 64} :
    ∀ (ws : List UInt64) (o : Nat), (∀ i (hi : i < ws.length),
      NativeRustcVm.WordAt d (loc m0 (o + 8 * i)) ws[i]) →
      NativeRustcVm.WordsAt d (loc m0 o) ws
  | [], _, _ => NativeRustcVm.wordsAt_nil _ _
  | w :: ws, o, h => by
    have h0 := h 0 (by simp)
    rw [Nat.mul_zero, Nat.add_zero] at h0
    refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h0, ?_⟩
    rw [NativeRustcVm.addr_add_add]
    exact wordsAt_of_fw ws (o + 8) fun i hi ↦ by
      have := h (i + 1) (by simp; omega)
      rw [show o + 8 * (i + 1) = o + 8 + 8 * i by omega] at this
      simpa using this

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

theorem Parts.base_toNat' : (base m0 512).toNat = m0.regs.SP.toNat - 512 :=
  base_toNat (by have := h.hS; omega)

/-- A window of the frame apart from what the frame is apart from. -/
theorem Parts.loc_apart {x : BitVec 64} {n o k : Nat} (hx : Apart (base m0 512) 512 x n)
    (hk : o + k ≤ 512) : Apart (loc m0 o) k x n := by
  have := h.loc_toNat (o := o) (by omega)
  have := h.base_toNat'
  unfold Apart at *
  omega

/-- An area apart from the entry's stack is apart from the frame. -/
theorem Parts.frame_apart {x : BitVec 64} {n : Nat}
    (hx : Apart x n (stackBelow m0 verifyStackedOpeningStack) verifyStackedOpeningStack) :
    Apart (base m0 512) 512 x n :=
  NativeRustcVm.Apart.symm (Ring.apart_frame h.hN (by rw [stack_eq]; decide) hx)

/-- A window of the frame, off a callee's stack. -/
theorem Parts.loc_off {O : BitVec 64 → Prop} {st : MachineData} (hf : OFr m0 O st) {N' o k : Nat}
    (hle : 512 + N' ≤ verifyStackedOpeningStack) (hk : o + k ≤ 512) :
    OffStack st (loc m0 o) k N' := by
  have hS := h.hS
  rw [stack_eq] at hle
  show Apart _ _ _ _
  rw [stackBelow_eq hf.sp (by omega)]
  have := h.loc_toNat (o := o) (by omega)
  have := base_toNat (m0 := m0) (F := 512 + N') (by omega)
  unfold Apart
  omega

/-- An input of the entry, for a callee. -/
theorem Parts.whirIn {O : BitVec 64 → Prop} {st : MachineData} (hf : OFr m0 O st) {N' : Nat}
    (hle : 512 + N' ≤ verifyStackedOpeningStack) {x : BitVec 64} {n : Nat}
    (hin : WhirIn m0 x n verifyStackedOpeningStack) : WhirIn st x n N' :=
  ⟨⟨fun i hi ↦ hf.kept _ (hin.1.1 i hi), hin.1.2⟩, hf.apart h.hN hin.2 hle⟩

theorem Parts.sc8_nw : NoWrap (scA m0 + BitVec.ofNat 64 8) (16 * cntOf layout cs) := by
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans h.cl.len_le
  have : NativeRustcVm.Layout.claimCap = 160 := rfl
  exact NativeRustcVm.NoWrap.sub h.sc_nw (by unfold cntOf; show _ ≤ 2600; omega)

theorem Parts.sc8_le : 8 + 16 * cntOf layout cs ≤ scalesBytes := by
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans h.cl.len_le
  have : NativeRustcVm.Layout.claimCap = 160 := rfl
  unfold cntOf; show _ ≤ 2600; omega

/-- **An input area** unchanged in a state of a frame with outputs among `outsF`. -/
theorem Parts.same_inF {O : BitVec 64 → Prop} (hO : ∀ q, O q → outsF m0 q) {st : MachineData}
    (hf : OFr m0 O st) {r : NativeRustcVm.Region} (hr : r ∈ vsoInputs m0) :
    NativeRustcVm.Layout.Same m0.dmem st.dmem r.addr r.size := by
  have hi := h.ins r hr
  have hnx : NoWrap r.addr r.size := hi.1.1.2
  have hnN := base_noWrap (m0 := m0) (F := verifyStackedOpeningStack) h.hN
  refine fun j hj ↦ hf.same _ fun hq ↦ ?_
  have hxj := NativeRustcVm.inRange_add (a := r.addr) hj (by unfold NoWrap at hnx; omega)
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange hi.1.2 hnx hnN hxj hq
  rcases hO _ hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange hi.2.2.1 hnx h.po.1.2.1 hxj hq
  · exact NativeRustcVm.Apart.not_inRange hi.2.2.2 hnx h.so.1.2.1 hxj hq
  · exact NativeRustcVm.Apart.not_inRange hi.2.1 hnx h.ts.footprint.1.2 hxj hq

/-- The scales' elements apart from what the scales are apart from. -/
theorem Parts.sc8_apart {x : BitVec 64} {n : Nat} (hx : Apart (scA m0) scalesBytes x n) :
    Apart (scA m0 + BitVec.ofNat 64 8) (16 * cntOf layout cs) x n :=
  WhirLevels.apart_sub hx h.sc_nw h.sc8_le

/-- **`whir_levels`' precondition.** -/
theorem pre_of {ls : List Whir.Level} {st : MachineData}
    (hc : AtCall a s layout target cs value ls m0 st) :
    WhirLevelsPre a (sq s).2 ls (baOf layout cs m0)
      (basisOf s layout target point coefficients cs z value) (claimOf s layout target cs value)
      st := by
  have hS := h.hS
  have hle : 512 + whirLevelsStack ≤ verifyStackedOpeningStack := by rw [stack_eq]; decide
  have hF : ∀ q, outsF m0 q → outsF m0 q := fun _ hq ↦ hq
  have cF : TCtx m0 512 verifyStackedOpeningStack (tA m0) a (outsF m0) :=
    h.ctxOf hF fun _ hq ↦ .inr (.inr hq)
  have hf := hc.fr
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans h.cl.len_le
  have hcap : NativeRustcVm.Layout.claimCap = 160 := rfl
  have hadm : Whir.Admissible layout.stackLog m0.regs.X2.toNat := by
    by_contra hn
    have := hc.lad
    simp [Whir.ladder, hn] at this
  have hlog : layout.stackLog < 2 ^ 64 := h.lay.stack_log_lt
  have e0 : st.regs.X0.toBitVec = tA m0 := by rw [hc.x0]
  have e1 : st.regs.X1.toNat = layout.stackLog := by
    rw [hc.x1]; exact natCast_toUInt64_toNat hlog
  have hpo := h.po
  have hso := h.so
  have htok := h.wt.2.2.2.1
  have hfp := h.ts.footprint
  -- the frame's windows
  have hfrP : Apart (base m0 512) 512 (pA m0) whirBytes := h.frame_apart hpo.1.2.2.2.2.1
  have hfrT : Apart (base m0 512) 512 (tA m0) tstateBytes := h.frame_apart htok.1
  have hfrS : Apart (base m0 512) 512 (scA m0 + BitVec.ofNat 64 8) (16 * cntOf layout cs) :=
    NativeRustcVm.Apart.symm (h.sc_frame h.sc8_le (by unfold cntOf; omega))
  have hlvn : levelBytes * ls.length + 112 ≤ 512 := by
    have := hc.len; show 24 * _ + 112 ≤ 512; omega
  -- the basis' areas
  have hscIn : WhirIn st (scA m0 + BitVec.ofNat 64 8) (16 * cntOf layout cs)
      whirLevelsStack :=
    h.whirIn hf hle ⟨⟨NativeRustcVm.Mapped.sub hso.1.1 h.sc8_le, h.sc8_nw⟩,
      h.sc8_apart hso.1.2.2.2.2.1⟩
  have hregs : ∀ r ∈ (baOf layout cs m0).regions, WhirIn st r.addr r.size whirLevelsStack ∧
      Apart r.addr r.size (pA m0) whirBytes ∧ Apart r.addr r.size (tA m0) tstateBytes ∧
      Apart (base m0 512) 512 r.addr r.size := by
    intro r hr
    rw [regions_baOf] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨hscIn, h.sc8_apart (NativeRustcVm.Apart.symm h.psc), h.sc8_apart hso.1.2.2.1, hfrS⟩
    · have hi := h.ins r hr
      exact ⟨h.whirIn hf hle hi.1, hi.2.2.1, hi.2.1, h.frame_apart hi.1.2⟩
  have hbin : ∀ (o : BitVec 64) (n : Nat), Apart (base m0 512) 512 o n →
      (∀ r ∈ (baOf layout cs m0).regions, Apart r.addr r.size o n) →
      BasisIn st (loc m0 56) (baOf layout cs m0) whirLevelsStack o n := fun o n ho hr ↦
    ⟨⟨h.loc_readable hf (by decide), h.loc_off hf hle (by decide)⟩, h.loc_apart ho (by decide),
      fun r hr' ↦ ⟨(hregs r hr').1, hr r hr'⟩⟩
  refine ⟨?_, ?_, ?_, ⟨m0.regs.X2.toNat, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]
    exact ⟨cF.stackOk hf hle, cF.rcAt hf hle, h.rodataAt hF hf hle, cF.tstateOk hf hle,
      h.wt.2.2.2.2⟩
  · rw [e0]; exact hc.ts
  · show s.roots.size + ls.length ≤ 8
    have := h.roots; have := hc.len; omega
  · rw [e1]; exact hc.lad
  · rw [hc.x5]; exact (natCast_toUInt64_toNat (by have := hc.len; omega)).symm
  · rw [hc.x4]; exact hc.lv
  · rw [hc.x3]
    refine ⟨by show cntOf layout cs < 2 ^ 64; unfold cntOf; omega, ?_,
      by simp [basisOf, baOf, size_scalesOf], hc.scs, ?_⟩
    · refine wordsAt_of_fw _ 56 fun i hi ↦ ?_
      simp only [List.length_cons, List.length_nil] at hi
      have hw := hc.fwb
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [baOf] using hw.get (by simp [basisWords])
    · refine ⟨⟨layout, target, coefficients, point, slices, cs, z, value, hadm.2.1, ?_, ?_, ?_,
        ?_, ?_, rfl⟩⟩
      · exact NativeRustcVm.Tables.LayoutWAt.of_same h.lay (h.same_inF hF hf mem_lay)
      · exact NativeRustcVm.Top.RingWAt.of_same h.ring (h.same_inF hF hf mem_ring)
      · exact NativeRustcVm.Top.KeccakOutAt.of_same h.kec (h.same_inF hF hf mem_kec)
      · exact NativeRustcVm.Tables.ClaimsWAt.of_same h.cl (h.same_inF hF hf mem_cl)
      · exact NativeRustcVm.Top.EqClaimAt.of_same h.ood (h.same_inF hF hf mem_ood)
  · rw [hc.x6]; exact hc.ws
  · rw [e0, hc.x6]; exact ⟨cF.outOk hf hle hpo.1, hpo.2⟩
  · rw [hc.x4]
    exact ⟨h.loc_readable hf (by omega), h.loc_off hf hle (by omega)⟩
  · rw [hc.x4, hc.x6]; exact h.loc_apart hfrP (by omega)
  · rw [hc.x4, e0]; exact h.loc_apart hfrT (by omega)
  · rw [hc.x3, hc.x6]
    exact hbin _ _ hfrP fun r hr ↦ (hregs r hr).2.1
  · rw [hc.x3, e0]
    exact hbin _ _ hfrT fun r hr ↦ (hregs r hr).2.2.1
  · rw [hc.x3]
    refine List.pairwise_cons.mpr ⟨fun r hr ↦ h.loc_apart (hregs r hr).2.2.2
      (by show 56 + 56 ≤ 512; omega), ?_⟩
    rw [regions_baOf]
    refine List.pairwise_cons.mpr ⟨fun r hr ↦ ?_, h.pw⟩
    exact h.sc8_apart (NativeRustcVm.Apart.symm (h.ins r hr).2.2.2)

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
