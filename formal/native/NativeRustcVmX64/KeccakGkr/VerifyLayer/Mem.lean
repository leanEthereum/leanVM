module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Defs
public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Got

/-!
# `verify_layer` on x86-64: memory in the body

- A block's environment is well formed (`wf0`, `wf1`: the frame and at most one region beside).
- The frame's bytes `[o, o + n)` kept (`FrSame`) by a block whose writes miss them (`frSame_blk`,
  checked on the block's result by `missB`), by a call writing elsewhere (`frSame_call`); words
  and elements there kept (`FrSame.bytes`).
- What the precondition keeps everywhere: the bytes outside the changes (`Body.keep`): the read-only
  data, the round constants for a callee (`Body.at_`), the claim and its bit weights before the
  tail.
- The transcript's context for a call from offset `oc` (`ctx`, `Body.at_`: `Sumcheck.Ctx`,
  `Sumcheck.At` with the frame `2016 - oc`), the frame's addresses in it (`off_fr`).
- A word of the frame as a block loads it (`fw_load`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck (Ctx At)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)

@[expose] public section

/-- The frame's bytes `[o, o + n)` are the same in `d` and `d'`. -/
def FrSame (m0 : MachineData) (d d' : DataMem) (o n : Nat) : Prop :=
  ∀ i < n, d'.get? (off (stackBelow m0 2016) (o + i)) = d.get? (off (stackBelow m0 2016) (o + i))

/-- A block's writes miss the frame's bytes `[o, o + n)`. -/
def missB (o n : Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r != 0 || decide (w.off + w.n ≤ o) || decide (o + n ≤ w.off)

end

public section

variable {m0 : MachineData}

theorem off_fr (o : Nat) : off (stackBelow m0 2000) o = off (stackBelow m0 2016) (o + 16) := by
  unfold stackBelow off
  bv_omega

theorem FrSame.refl (d : DataMem) (o n : Nat) : FrSame m0 d d o n := fun _ _ ↦ rfl

theorem FrSame.trans {d d' d'' : DataMem} {o n : Nat} (h : FrSame m0 d d' o n)
    (h' : FrSame m0 d' d'' o n) : FrSame m0 d d'' o n := fun i hi ↦ (h' i hi).trans (h i hi)

theorem FrSame.sub {d d' : DataMem} {o n o' n' : Nat} (h : FrSame m0 d d' o n) (h1 : o ≤ o')
    (h2 : o' + n' ≤ o + n) : FrSame m0 d d' o' n' := fun i hi ↦ by
  have := h (o' - o + i) (by omega)
  rwa [show o + (o' - o + i) = o' + i by omega] at this

/-- **Bytes in a kept range** are kept. -/
theorem FrSame.bytes {d d' : DataMem} {o n : Nat} (h : FrSame m0 d d' o n) {bs : List UInt8}
    (hb : NativeRustcVm.BytesAt d (off (stackBelow m0 2016) o) bs) (hl : bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (off (stackBelow m0 2016) o) bs := fun i hi ↦ by
  rw [NativeRustcVm.Transcript.off_add, h i (by omega), ← NativeRustcVm.Transcript.off_add]
  exact hb i hi

theorem FrSame.word {d d' : DataMem} {o n : Nat} (h : FrSame m0 d d' o n) {w : UInt64}
    (hb : NativeRustcVm.WordAt d (off (stackBelow m0 2016) o) w) (hl : 8 ≤ n) :
    NativeRustcVm.WordAt d' (off (stackBelow m0 2016) o) w :=
  h.bytes hb (by rw [NativeRustcVm.length_wordBytes]; exact hl)

theorem FrSame.ews {d d' : DataMem} {o n : Nat} (h : FrSame m0 d d' o n) {xs : List EW}
    (hb : NativeRustcVm.EWsAt d (off (stackBelow m0 2016) o) xs) (hl : 16 * xs.length ≤ n) :
    NativeRustcVm.EWsAt d' (off (stackBelow m0 2016) o) xs :=
  h.bytes hb (by rw [NativeRustcVm.length_ewsBytes]; exact hl)

end

public section

variable {m0 : MachineData}

/-- The frame of a body is mapped and does not wrap. -/
theorem frame_ok (hS : StackOk m0 3232) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) :
    NativeRustcVm.Mapped d.dmem (stackBelow m0 2016) (2016 + 8) ∧
      NativeRustcVm.NoWrap (stackBelow m0 2016) (2016 + 8) :=
  ⟨NativeRustcVm.Transcript.Mapped.keeps (frame_mapped hS (by decide)) hk, frame_noWrap hS (by decide)⟩

/-- A body's block environment with the frame alone. -/
theorem wf0 (hS : StackOk m0 3232) {W : BitVec 64 → Prop} {o : Nat} {d : MachineData}
    (hb : Body m0 W o d) {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (envB m0 d [] vars ret).WF :=
  frame_wf (frame_ok hS hb.fr.kept) (fun _ h ↦ by cases h) (List.pairwise_singleton _ _)

/-- A body's block environment with one region beside the frame. -/
theorem wf1 (hS : StackOk m0 3232) {W : BitVec 64 → Prop} {o : Nat} {d : MachineData}
    (hb : Body m0 W o d) {x : BitVec 64 × Nat} (hm : NativeRustcVm.Mapped d.dmem x.1 x.2)
    (hnw : NativeRustcVm.NoWrap x.1 x.2)
    (hap : NativeRustcVm.Apart (stackBelow m0 2016) (2016 + 8) x.1 x.2)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (envB m0 d [x] vars ret).WF :=
  frame_wf (frame_ok hS hb.fr.kept) (fun y hy ↦ by
      simp only [List.mem_singleton] at hy; subst hy; exact ⟨hm, hnw⟩)
    (List.pairwise_pair.mpr hap)

/-- **A block keeps the frame's bytes** its writes miss. -/
theorem frSame_blk [Labels] {d d' : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (envB m0 d ex vars ret).WF)
    (hm : Match (envB m0 d ex vars ret) S d') (hin : writesIn S = true) {o n : Nat}
    (hon : o + n ≤ 2024) (hmiss : missB o n S = true) : FrSame m0 d.dmem d'.dmem o n := by
  intro i hi
  rw [hm.get?_mem0 hwf fun hW ↦ ?_]
  · rfl
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hW
  have hnw0 := hwf.noWrap 0 (stackBelow m0 2016) (2016 + 8) rfl
  have hq : (off (stackBelow m0 2016) (o + i)).toNat = (stackBelow m0 2016).toNat + (o + i) :=
    NativeRustcVm.Transcript.toNat_off (by omega)
  rw [hq] at h1 h2
  have hmw := List.all_eq_true.mp hmiss w hw
  by_cases hr : w.r = 0
  · rw [hr] at hb
    cases hb
    simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hmw
    omega
  · have hw' := List.all_eq_true.mp hin w hw
    obtain ⟨sz', hS'⟩ : ∃ sz', S.regions[w.r]? = some sz' := by
      revert hw'
      cases S.regions[w.r]? with
      | none => simp
      | some x => exact fun _ ↦ ⟨x, rfl⟩
    rw [hS'] at hw'
    simp only [decide_eq_true_eq] at hw'
    obtain ⟨b', hb'⟩ := hm.regions _ _ hS'
    rw [hb] at hb'
    cases hb'
    have := hwf.disjoint 0 w.r _ _ _ _ (Ne.symm hr) rfl hb
    omega

/-- The frame's base `16` higher. -/
theorem fr16 : stackBelow m0 2000 = off (stackBelow m0 2016) 16 := by
  unfold stackBelow off
  bv_omega

/-- **A callee keeps the frame's bytes** above its return address it does not write. -/
theorem frSame_call (g : Geo m0) {W : BitVec 64 → Prop} {oc : Nat} {mc : MachineData}
    {d' : DataMem} (hb : Body m0 W oc mc) {Sk : Nat} (hSk : 2016 - oc + Sk ≤ 3232)
    {Wc : BitVec 64 → Prop}
    (hso : SameOutside mc.dmem d' (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ Wc q))
    {o n : Nat} (hoc : oc + 8 ≤ o) (hon : o + n ≤ 2024)
    (hWc : ∀ q, Wc q → ¬InRange (off (stackBelow m0 2016) o) n q) : FrSame m0 mc.dmem d' o n := by
  intro i hi
  have hN := g.hN; have htop := g.top
  have hfo := g.fa (o := o) (by omega)
  have hnw : n ≤ 2 ^ 64 := by omega
  refine hso _ fun h ↦ h.elim (fun h ↦ ?_) fun h ↦ hWc _ h ?_
  · have hmsp : (rspOf mc).toNat = (rspOf m0).toNat - 2016 + oc := by
      rw [hb.fr.sp]; exact g.fa (by omega)
    have hcs : (stackBelow mc Sk).toNat = (rspOf m0).toNat - 2016 + oc - Sk := by
      rw [stackBelow_toNat (by omega), hmsp]
    have hq : (off (stackBelow m0 2016) (o + i)).toNat = (rspOf m0).toNat - 2016 + (o + i) :=
      g.fa (by omega)
    rw [Sym.inRange_iff (by omega), hcs, hq] at h
    omega
  · rw [← NativeRustcVm.Transcript.off_add]
    exact NativeRustcVm.Transcript.inRange_off_self hi hnw

end

/-! ## The precondition everywhere -/

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem pre_stack (h : VerifyLayerPre a s c m0) : StackOk m0 3232 := stack_eq ▸ h.1
theorem pre_rc (h : VerifyLayerPre a s c m0) : RcAt m0 3232 := stack_eq ▸ h.2.1
theorem pre_proj (h : VerifyLayerPre a s c m0) : ProjectAt m0 := h.2.2.1
theorem pre_rho (h : VerifyLayerPre a s c m0) : RhoAt m0 := h.2.2.2.1
theorem pre_ts (h : VerifyLayerPre a s c m0) : TStateAt m0.dmem (tA m0) a s := h.2.2.2.2.1
theorem pre_claim (h : VerifyLayerPre a s c m0) : NativeRustcVm.KeccakGkr.ClaimAt m0.dmem (cA m0) c :=
  h.2.2.2.2.2.1
theorem pre_w (h : VerifyLayerPre a s c m0) :
    NativeRustcVm.KeccakGkr.WeightsAt m0.dmem (lA m0) c := h.2.2.2.2.2.2.1
theorem pre_step (h : VerifyLayerPre a s c m0) : (reg m0 .rdx).toNat < 12 := h.2.2.2.2.2.2.2.1
theorem pre_seg (h : VerifyLayerPre a s c m0) : SegmentsFit (reg m0 .rsi).toNat c :=
  h.2.2.2.2.2.2.2.2.1
theorem pre_areas (h : VerifyLayerPre a s c m0) :
    Areas m0 3232 [⟨tA m0, tstateBytes⟩, ⟨cA m0, 768⟩, ⟨sA m0, 205824⟩]
      [a.region, rcRegion, projectRegion, rhoRegion] := stack_eq ▸ h.2.2.2.2.2.2.2.2.2.1

/-- Exactly the loader slot reached by this function and its callees. -/
theorem pre_got (h : VerifyLayerPre a s c m0) :
    GotAt m0 verifyLayerStack
      [(tA m0, tstateBytes), (cA m0, 768), (sA m0, 205824),
        (a.region.addr, a.region.size), (rcAddr, 192), (projectAddr, 128), (rhoAddr, 100)]
      ["memcpy"] := h.2.2.2.2.2.2.2.2.2.2

/-- Every body write misses the ordinary-memory loader slot. -/
theorem Body.got_bytes (hpre : VerifyLayerPre a s c m0)
    {W : BitVec 64 → Prop} {o : Nat} {d : MachineData}
    (hb : Body m0 W o d) (hW : ∀ q, W q → outs m0 q) :
    ∀ l ∈ ["memcpy"], ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  intro l hl i hi
  have hg := (pre_got hpre).1 l hl
  have g := geo_of hpre
  have hst : NoWrap (stackBelow m0 3232) (3232 + 8) :=
    noWrap_stackBelow (pre_stack hpre)
  have hgs : Apart (gotAddr l) 8 (stackBelow m0 3232) (3232 + 8) := by
    simpa only [stack_eq, stackBelow, apart_eq] using hg.2.2.1
  apply hb.same
  rintro (h | h)
  · exact hgs.not_inRange hg.2.1 hst hi (inRange_mono h (by omega))
  rcases hW _ h with ht | hc | hs
  · exact (hg.2.2.2 (tA m0, tstateBytes) (by simp)).not_inRange hg.2.1 g.ht hi ht
  · exact (hg.2.2.2 (cA m0, 768) (by simp)).not_inRange hg.2.1 g.hc hi hc
  · have hsc : InRange (sA m0) 205824 (gotAddr l + BitVec.ofNat 64 i) := by
      exact inRange_of_off g.hs (show 25600 + 114688 ≤ 205824 by decide) hs
    exact (hg.2.2.2 (sA m0, 205824) (by simp)).not_inRange hg.2.1 g.hs hi hsc

/-- A callee's protected subregions inherit the body's preserved loader slot. -/
theorem Body.got (hpre : VerifyLayerPre a s c m0)
    {W : BitVec 64 → Prop} {o n : Nat} {d : MachineData}
    (hb : Body m0 W o d) (hW : ∀ q, W q → outs m0 q)
    (ho : o ≤ 2016) (hn : 2016 - o + n ≤ 3232)
    {areas : List (BitVec 64 × Nat)}
    (hcover : ∀ p ∈ areas,
      ∃ b ∈ (stackBelow m0 verifyLayerStack, verifyLayerStack + 8) ::
        [(tA m0, tstateBytes), (cA m0, 768), (sA m0, 205824),
          (a.region.addr, a.region.size), (rcAddr, 192), (projectAddr, 128), (rhoAddr, 100)],
        b.1.toNat ≤ p.1.toNat ∧ p.1.toNat + p.2 ≤ b.1.toNat + b.2) :
    GotAt d n areas ["memcpy"] := by
  have g := geo_of hpre
  have hN := g.hN
  have ht := g.top
  have hrsp : (rspOf d).toNat = (rspOf m0).toNat - 2016 + o := by
    rw [hb.fr.sp]
    exact g.fa (by omega)
  have hbase : (stackBelow d n).toNat = (rspOf m0).toNat - 2016 + o - n := by
    rw [stackBelow_toNat (by omega), hrsp]
  apply NativeRustcVmX64.GotAt.callee (pre_got hpre) (hb.got_bytes hpre hW) _ _ hcover
  · rw [stack_eq, g.sbN, hbase]; omega
  · rw [stack_eq, g.sbN, hbase]; omega

/-- A written region and a read one of the precondition apart, as numbers. -/
theorem pre_apart (h : VerifyLayerPre a s c m0) {w r : NativeRustcVm.Region}
    (hw : w ∈ stackRegion m0 3232 :: [⟨tA m0, tstateBytes⟩, ⟨cA m0, 768⟩, ⟨sA m0, 205824⟩])
    (hr : r ∈ [a.region, rcRegion, projectRegion, rhoRegion]) :
    w.addr.toNat + w.size ≤ r.addr.toNat ∨ r.addr.toNat + r.size ≤ w.addr.toNat :=
  areas_rs (pre_areas h) hw hr

theorem pre_rok (h : VerifyLayerPre a s c m0) {r : NativeRustcVm.Region}
    (hr : r ∈ [a.region, rcRegion, projectRegion, rhoRegion]) :
    NativeRustcVm.Region.Ok m0.dmem r :=
  areas_ok (pre_areas h) (.inr hr)

/-- **A read-only region** is apart from every change. -/
theorem chg_not_ro (h : VerifyLayerPre a s c m0) {r : NativeRustcVm.Region}
    (hr : r ∈ [a.region, rcRegion, projectRegion, rhoRegion]) {q : BitVec 64}
    (hq : Chg m0 (outs m0) q) : ¬InRange r.addr r.size q := by
  have g := geo_of h
  have hnw := (pre_rok h hr).2
  unfold NativeRustcVm.NoWrap at hnw
  have h0 := pre_apart h (w := stackRegion m0 3232) (by simp) hr
  have h1 := pre_apart h (w := ⟨tA m0, tstateBytes⟩) (by simp) hr
  have h2 := pre_apart h (w := ⟨cA m0, 768⟩) (by simp) hr
  have h3 := pre_apart h (w := ⟨sA m0, 205824⟩) (by simp) hr
  simp only [stackRegion, tstateBytes] at h0 h1 h2 h3
  have hsb := g.sbN; have := g.hN; have := g.top; have := g.ht; have := g.hc; have := g.hs
  have hl := g.lN
  rw [Sym.inRange_iff hnw]
  rcases hq with hq | hq | hq | hq
  · rw [Sym.inRange_iff (by omega), hsb] at hq; rw [hsb] at h0; omega
  · rw [Sym.inRange_iff (by omega)] at hq; omega
  · rw [Sym.inRange_iff (by omega)] at hq; omega
  · rw [Sym.inRange_iff (by omega), hl] at hq; omega

/-- **Bytes the precondition places in a read-only region** are kept. -/
theorem Body.keep_ro (h : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {o : Nat} {d : MachineData} (hb : Body m0 W o d)
    {r : NativeRustcVm.Region} (hr : r ∈ [a.region, rcRegion, projectRegion, rhoRegion])
    {bs : List UInt8} (hbs : NativeRustcVm.BytesAt m0.dmem r.addr bs) (hl : bs.length ≤ r.size) :
    NativeRustcVm.BytesAt d.dmem r.addr bs := fun i hi ↦ by
  rw [hb.same _ fun hq ↦ chg_not_ro h hr (hq.elim .inl fun hq ↦ .inr (hWo _ hq))
    (NativeRustcVm.Transcript.inRange_off_self (by omega) (by have := (pre_rok h hr).2; unfold NativeRustcVm.NoWrap at this; omega))]
  exact hbs i hi

/-- The transcript's context for calls from the frame `F`. -/
theorem ctx (h : VerifyLayerPre a s c m0) {F : Nat} (hF : F ≤ 3232) : Ctx m0 (tA m0) a 3232 F := by
  have hA := pre_areas h
  refine ⟨pre_stack h, pre_rc h, ⟨?_, ?_, ?_⟩, (pre_ts h).footprint, hF⟩
  · have := areas_stack hA (w := ⟨tA m0, tstateBytes⟩) (by simp)
    exact this
  · have := pre_apart h (w := stackRegion m0 3232) (by simp) (r := a.region) (by simp)
    unfold NativeRustcX64.Apart
    simp only [stackRegion, NativeRustcVm.Transcript.DecArea.region] at this
    omega
  · have := pre_apart h (w := ⟨tA m0, tstateBytes⟩) (by simp) (r := rcRegion) (by simp)
    unfold NativeRustcX64.Apart
    simp only [rcRegion] at this
    omega

/-- **A call from the body**: the state at the call is at the frame `2016 - oc`, the round
constants' bytes kept. -/
theorem Body.at_ (h : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {oc : Nat} (hoc : oc ≤ 2016) {d : MachineData}
    (hb : Body m0 W oc d) : At m0 (2016 - oc) d := by
  have g := geo_of h
  refine ⟨?_, hb.fr.kept, fun i hi ↦ hb.same _ fun hq ↦ chg_not_ro h (r := rcRegion) (by simp)
    (hq.elim .inl fun hq ↦ .inr (hWo _ hq))
    (NativeRustcVm.Transcript.inRange_off_self (N := 192) hi (by omega))⟩
  rw [hb.fr.sp]
  unfold stackBelow off
  bv_omega

/-- A range of the claim, readable by a callee from the frame `2000` using `Sk` bytes of stack. -/
theorem claimSlice (h : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {mc : MachineData} (hb : Body m0 W 16 mc) {Sk : Nat}
    (hSk : 2000 + Sk ≤ 3232) {o n : Nat} (ho' : o < 768) (hon : o + n ≤ 768) :
    NativeRustcVm.Mapped mc.dmem (cA m0 + BitVec.ofNat 64 o) n ∧
      NativeRustcVm.NoWrap (cA m0 + BitVec.ofNat 64 o) n ∧
      NativeRustcVm.Apart (cA m0 + BitVec.ofNat 64 o) n (stackBelow mc Sk) (Sk + 8) := by
  have g := geo_of h
  have hok := areas_ok (pre_areas h) (r := ⟨cA m0, 768⟩) (.inl (by simp))
  have hap := areas_stack (pre_areas h) (w := ⟨cA m0, 768⟩) (by simp)
  have hc := g.hc
  have ho : (cA m0 + BitVec.ofNat 64 o).toNat = (cA m0).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  refine ⟨fun i hi ↦ ?_, by unfold NativeRustcVm.NoWrap; omega, ?_⟩
  · rw [NativeRustcVm.Transcript.off_add]
    exact hb.fr.kept _ (hok.1 _ (by dsimp only; omega))
  · refine (ctx h (F := 2000) (by decide)).apart (hb.at_ h hWo (by decide)) hSk ?_
    unfold NativeRustcVm.Apart at hap ⊢
    dsimp only at hap
    omega

/-- **A leaf call** from the frame's offset `16`, the callee changing its stack only: the body at
`24`, the frame's bytes from `24` and the `TState` kept. -/
theorem Body.leaf (h : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {mc d' : MachineData} (hb : Body m0 W 16 mc) {Sk : Nat}
    (hSk : 2000 + Sk ≤ 3232) (hsv : Saved mc d') (hrsp : rspOf d' = rspOf mc + 8#64)
    (hso : SameOutside mc.dmem d'.dmem (InRange (stackBelow mc Sk) Sk)) :
    Body m0 W 24 d' ∧ FrSame m0 mc.dmem d'.dmem 24 2000 ∧
      ∀ s', TStateAt mc.dmem (tA m0) a s' → TStateAt d'.dmem (tA m0) a s' := by
  have g := geo_of h
  have hso' : SameOutside mc.dmem d'.dmem (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ False) :=
    NativeRustcVm.SameOutside.mono hso fun q hq ↦ .inl hq
  refine ⟨Body.call g hWo hb (by decide) hsv hrsp hSk hso' fun q hq ↦ hq.elim,
    frSame_call g hb hSk hso' (by decide) (by decide) fun _ h ↦ h.elim, fun s' hts ↦ ?_⟩
  exact hts.frame hsv.2 (fun q hq ↦ (ctx h (F := 2000) (by decide)).stack_not_t
    ((ctx h (F := 2000) (by decide)).inRange_callee (hb.at_ h hWo (by decide)) hSk hq).1) hso

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
