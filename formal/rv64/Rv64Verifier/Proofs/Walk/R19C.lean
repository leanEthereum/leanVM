import Rv64Verifier.Proofs.Walk.R19B

/-!
# `walk` R19, the public input's claims: `r19a`, from `ExitR18` to the loop's head
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section Entry
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word}

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- From `ExitR18` to the claims loop's head, no claim pushed, or the run dies. -/
theorem r19a (hD : DuplexSpec) (hFE : MultilinearContracts.FromElemSpec) (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus)
    (Ex : ExitR18 OI s u₀ w t u layout rows lir bus evs P C L) :
    ∃ v, Reaches Image.code u v ∧ ((∃ c pt, HeadR19 OI s u₀ w t v layout rows lir bus evs P C L 0
      c pt) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have C₀ := Ex.toCoreR18.toT
  have sp := C₀.rest.inv.sp
  -- `0x80003a48`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003a48_spec Ex.pc (by rv_eval [])
  have m₁ := b80003a48_mem_same h₁
  have k₁ := b80003a48_keeps h₁
  have C₁ := C₀.same hpre m₁ (k₁ .x2 (by decide))
  have st₁ : StepW s u u₁ (fun _ ↦ False) False := StepW.same C₀.rest.inv.heap m₁ (k₁ .x2 (by decide)) _ _
  -- `duplex`, `sample`
  obtain ⟨v₁, hrv₁, ⟨hpcv₁, hp₁, st₂, tr₂⟩ | hd⟩ := duplexW hD hpre C₁.rest.inv C₁.proofPtr hr₁
    (b80003a48_pc h₁) (by rw [b80003a48_x10 h₁, sp, tp]; bv_omega)
  swap
  · exact ⟨v₁, hrv₁, Or.inr hd⟩
  obtain ⟨c, hc⟩ : ∃ c, eAt v₁ (tp s + 136) = c := ⟨_, rfl⟩
  have C₂ : CoreT OI s u₀ w t v₁ layout lir evs P C L.toNat (bus.claims ++ tableClaimsRust evs)
      (pubRest layout (bytesAt s (s.getReg .x12) 32) c >>=
        afterPublic layout rows lir bus evs (bus.claims ++ tableClaimsRust evs)) := by
    have tr := C₁.tracks
    rw [afterTables_sample] at tr
    refine C₁.step hpre st₂ (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) ?_
    refine tr.bind (x := c) Rv64Verifier.Model.Pcs.Keeps.sample fun T hT ↦ ⟨_, ?_, tr₂ T hT⟩
    rw [← hc]; exact sample_lanes (tr₂ T hT).sponge
  have I₂ := C₂.rest.inv
  have sp₂ := I₂.sp
  have pc₂ : v₁.pc = 0x80003a54 := by rw [hpcv₁, returnAddress, b80003a48_x1 h₁]; decide
  -- `0x80003a54`
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003a54_spec pc₂ (by
    rv_eval [sp₂]; and_intros <;> valid_access hval [hb1, hb3])
  have m₂ := b80003a54_mem_same h₂
  have k₂ := b80003a54_keeps h₂
  have C₃ := C₂.same hpre m₂ (k₂ .x2 (by decide))
  have I₃ := C₃.rest.inv
  have st₂₂ : StepW s v₁ u₂ (fun _ ↦ False) False := StepW.same I₂.heap m₂ (k₂ .x2 (by decide)) _ _
  have lc : Model.limbs c = (v₁.getMem (s.getReg .x2 - 2312), v₁.getMem (s.getReg .x2 - 2304),
      v₁.getMem (s.getReg .x2 - 2296)) := by
    rw [← hc, limbs_eAt, show tp s + 136 = s.getReg .x2 - 2312 by rw [tp]; bv_omega,
      show s.getReg .x2 - 2312 + 8 = s.getReg .x2 - 2304 by bv_omega,
      show s.getReg .x2 - 2312 + 16 = s.getReg .x2 - 2296 by bv_omega]
  have x20₂ : u₂.getReg .x20 = (Model.limbs c).1 := by
    rw [b80003a54_x20 h₂, spAdd hpre sp₂ 344 2312 rfl, lc]
  have x21₂ : u₂.getReg .x21 = (Model.limbs c).2.1 := by
    rw [b80003a54_x21 h₂, spAdd hpre sp₂ 352 2304 rfl, lc]
  have x27₂ : u₂.getReg .x27 = (Model.limbs c).2.2 := by
    rw [b80003a54_x27 h₂, spAdd hpre sp₂ 360 2296 rfl, lc]
  have x12₂ : u₂.getReg .x12 = u₀.getMem (s.getReg .x2 - 1928) := by
    rw [b80003a54_x12 h₂, spAdd hpre sp₂ 728 1928 rfl,
      show (1928 : Word) = BitVec.ofNat 64 1928 from rfl,
      C₂.rest.get (keep_slot hpre (by omega))]
  have hnW : (u₀.getMem (s.getReg .x2 - 1928)).toNat = layout.logMemory := h.layoutIn.logMemory
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 1560 := by
    rw [b80003a54_x10 h₂, spAdd hpre sp₂ 1096 1560 rfl]
  have x11₂ : u₂.getReg .x11 = 0xa0000068 := b80003a54_x11 h₂
  -- `from_elem`
  have hfs : MultilinearContracts.fromElemStack ≤ 8736 := by decide
  have pre : MultilinearContracts.FromElemPre u₂ := {
    heap := I₃.heap
    out := by rw [x10₂]; valid_sub hval [hb1, hb3]
    elem := by rw [x11₂]; intro i hi; interval_cases i <;> decide
    stack := hpre.stack.sub 2656 I₃.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by
      rw [x10₂]
      exact (fr_ok hpre I₃ (c := 1560) (k := 1560) (n := 24) (m := 0) rfl (by omega) (by omega)
        (by omega)).1
    outStack := by
      rw [x10₂]
      exact (fr_ok hpre I₃ (c := 1560) (k := 1560) (n := 24) rfl (by omega) (by omega) hfs).2.1
    elemFree := by
      rw [x11₂]; simp only [Outside, Apart, heapEnd, nextAddr]
      exact ⟨Or.inr (by decide), by decide⟩
    elemStack := by
      rw [x11₂, stackLo_callee I₃]; simp only [Apart]; right; right; left; addr_omega [hb1, hfs]
    elemOut := by rw [x11₂, x10₂]; simp only [Apart]; right; right; left; addr_omega [hb1] }
  obtain ⟨v₂, hrv₂, ⟨hpcv₂, hp₂, post⟩ | hd⟩ := hFE.call (hrv₁.trans hr₂) (b80003a54_pc h₂) pre
  swap
  · exact ⟨v₂, hrv₂, Or.inr hd⟩
  have fr := post.frame
  rw [x10₂] at fr
  have st₃ : StepW s u₂ v₂ (Within · (s.getReg .x2 - 1560) 24) False :=
    StepW.ofCall hpre I₃ hfs (DFrame.of_byteFrame fr) post.heap post.mono (hp₂ .x2 (by decide))
  have ln := post.len
  have el := post.elems
  have fs := post.fresh
  rw [x10₂, x12₂] at ln fs
  rw [x10₂, x12₂, x11₂] at el
  rw [hnW] at fs
  have ro := I₃.rodata hpre
  have r0 : u₂.getMem 0xa0000068 = 0 := ro.word
  have r8 : u₂.getMem (0xa0000068 + 8) = 0 := ro.word
  have r16 : u₂.getMem (0xa0000068 + 16) = 0 := ro.word
  have z0 : eAt u₂ 0xa0000068 = 0 := eAt_eq_of_limbs (by rw [r0, r8, r16, limbs_zeroE])
  rw [z0, hnW] at el
  have W3ok : ∀ a, Within a (s.getReg .x2 - 1560) 24 → InF s a ∧ ¬ KeepR s u₀ a ∧
      ¬ Within a (tp s) 368 ∧ ¬ Within a (s.getReg .x2 - 1632) 16 ∧
      ¬ Within a (s.getReg .x2 - 2616) 16 := fun a ha ↦
    range_okT hpre C₃.rest (c := 1560) (k := 1560) (n := 24) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha
  have C₄ := C₃.stepW hpre st₃ (fun a ha ↦ ⟨(W3ok a ha).1, (W3ok a ha).2.1, (W3ok a ha).2.2.1⟩)
    (fun a ha ↦ (W3ok a ha).2.2.2)
  have I₄ := C₄.rest.inv
  have sp₄ := I₄.sp
  have pc₄ : v₂.pc = 0x80003a78 := by rw [hpcv₂, returnAddress, b80003a54_x1 h₂]; decide
  -- `0x80003a78`: the length check
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003a78_spec pc₄ (by
    rv_eval [sp₄]; and_intros <;> valid_access hval [hb1, hb3])
  have e1112 : v₂.getMem (v₂.getReg .x2 + 1112) = u₀.getMem (s.getReg .x2 - 1928) := by
    rw [spAdd hpre sp₄ 1112 1544 rfl, show s.getReg .x2 - 1544 = s.getReg .x2 - 1560 + 16 by
      bv_omega]
    exact ln
  rcases Nat.eq_zero_or_pos layout.logMemory with hn0 | hn
  · refine ⟨u₃, hrv₂.trans hr₃, Or.inr (trapAt (b80003a78_pc_taken h₃ ?_))⟩
    rw [e1112]; apply BitVec.eq_of_toNat_eq; rw [hnW, hn0]; rfl
  have pc₅ := b80003a78_pc_not_taken h₃ (by
    rw [e1112]; intro h0; rw [h0] at hnW; simp at hnW; omega)
  have k₃ := b80003a78_keeps h₃
  have fr₄ : DFrame v₂ u₃ (Within · (s.getReg .x2 - 2512) 8) := by
    have := DFrame.of_memFrame (b80003a78_frame h₃ (by rw [sp₄]; addr_omega [hb1, hb2]))
    rwa [spAdd hpre sp₄ 144 2512 rfl] at this
  have W4ok : ∀ a, Within a (s.getReg .x2 - 2512) 8 → InF s a ∧ ¬ KeepR s u₀ a ∧
      ¬ Within a (tp s) 368 ∧ ¬ Within a (s.getReg .x2 - 1632) 16 ∧
      ¬ Within a (s.getReg .x2 - 2616) 16 := fun a ha ↦
    range_okT hpre C₄.rest (c := 2512) (k := 2512) (n := 8) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha
  have st₄ : StepW s v₂ u₃ (Within · (s.getReg .x2 - 2512) 8) False :=
    StepW.ofFrame hpre I₄.heap fr₄ (fun a ha ↦ (W4ok a ha).1) (k₃ .x2 (by decide))
  have m144 : u₃.getMem (s.getReg .x2 - 2512) = u₀.getMem (s.getReg .x2 - 1928) := by
    rw [← spAdd hpre sp₄ 144 2512 rfl, b80003a78_m_x2_144 h₃, spAdd hpre sp₄ 1112 1544 rfl,
      show s.getReg .x2 - 1544 = s.getReg .x2 - 1560 + 16 by bv_omega]
    exact ln
  have C₅ := C₄.stepW hpre st₄ (fun a ha ↦ ⟨(W4ok a ha).1, (W4ok a ha).2.1, (W4ok a ha).2.2.1⟩)
    (fun a ha ↦ (W4ok a ha).2.2.2)
  have sp₃ := C₅.rest.inv.sp
  -- the point's buffer
  obtain ⟨pt, hpt⟩ : ∃ pt, vecPtr v₂ (s.getReg .x2 - 1560) = pt := ⟨_, rfl⟩
  rw [hpt] at fs
  rcases fs with ⟨fa, f0 | ⟨f1, f2⟩⟩
  · omega
  have hh := post.heap.hi
  have hl := I₃.heap.lo
  simp only [heapEnd, heapStart] at hh hl
  have ept : u₃.getMem (s.getReg .x2 - 1552) = pt := by
    rw [← hpt, vecPtr, show s.getReg .x2 - 1560 + 8 = s.getReg .x2 - 1552 by bv_omega]
    exact fr₄ _ fun i hi hw ↦ by simp only [Within] at hw; addr_omega [hw, hi, hb1]
  have hn₃ : heapNext u₃ = heapNext v₂ := le_antisymm (by
    simp only [heapNext]
    rw [fr₄ nextAddr fun i hi hw ↦ by simp only [Within] at hw; addr_omega [hw, hi, hb1]]) st₄.mono
  -- `0x80003a84`
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80003a84_spec pc₅ (by
    rv_eval [sp₃, ept]
    and_intros <;> first
      | valid_access hval [hb1, hb3]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [f1, f2, hh, hl, fa, hn])
      | addr_omega [f1, f2, hh, hl, hb1, hn])
  have k₄ := b80003a84_keeps h₄
  have fr₅ : DFrame u₃ u₄ fun a ↦ W84 s a ∨ Within a pt 24 := h₄.dframe (by
    rv_eval [sp₃, ept]
    and_intros <;> first
      | (left; simp only [W84, true_or, or_true]; done)
      | (right; simp only [Within]; constructor <;> addr_omega [f2, hh, hn]))
  have st₅ : StepW s u₂ u₄ (fun a ↦ (Within a (s.getReg .x2 - 1560) 24 ∨
      Within a (s.getReg .x2 - 2512) 8) ∨ W84 s a) False :=
    ((st₃.trans st₄).weaken (T' := False) (fun _ h ↦ h) (fun h ↦ h.elim id id)).thenW hpre I₃.heap
      (fun a ha ↦ (W84_ok hpre C₅.rest ha).1) fr₅ (by omega) (by rw [hn₃]; omega)
      (k₄ .x2 (by decide))
  have C₆ := C₃.stepW hpre st₅ (fun a ha ↦ by
      rcases ha with (ha | ha) | ha
      · exact ⟨(W3ok a ha).1, (W3ok a ha).2.1, (W3ok a ha).2.2.1⟩
      · exact ⟨(W4ok a ha).1, (W4ok a ha).2.1, (W4ok a ha).2.2.1⟩
      · exact ⟨(W84_ok hpre C₅.rest ha).1, (W84_ok hpre C₅.rest ha).2.1,
          (W84_ok hpre C₅.rest ha).2.2.1⟩)
    (fun a ha ↦ by
      rcases ha with (ha | ha) | ha
      · exact (W3ok a ha).2.2.2
      · exact (W4ok a ha).2.2.2
      · exact (W84_ok hpre C₅.rest ha).2.2.2)
  have C₇ := C₆.congr (cl' := bus.claims ++ tableClaimsRust evs ++
      (pubClaims layout (bytesAt s (s.getReg .x12) 32) c).take 0) (by simp) (pubRest_pos hn)
  have R₃ := C₅.rest
  -- every step from `u` on
  have all := ((st₁.trans st₂).trans st₂₂).trans st₅
  have gA (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648)
      (hk1 : k ≤ 808 ∨ (936 ≤ k ∧ k ≤ 1536) ∨ (1568 ≤ k ∧ k ≤ 2088) ∨ (2448 ≤ k ∧ k ≤ 2504) ∨
        2552 ≤ k) :
      u₄.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    all.getF hpre (by addr_omega [hb1, hk]) (fun i hi hw ↦ by
      rcases hw with ((hw | hw) | hw) | hw
      · exact False.elim hw
      · exact False.elim hw
      · exact False.elim hw
      · rcases hw with (hw | hw) | hw
        · simp only [Within] at hw; rcases hk1 with q | q | q | q | q <;> addr_omega [hw, hi, hb1, q, hk]
        · simp only [Within] at hw; rcases hk1 with q | q | q | q | q <;> addr_omega [hw, hi, hb1, q, hk]
        · rcases W84_within hpre hw with hw | hw <;> simp only [Within] at hw <;>
            rcases hk1 with q | q | q | q | q <;> addr_omega [hw, hi, hb1, q, hk])
      (fun _ ↦ by rw [tp]; simp only [Apart]; rcases hk1 with q | q | q | q | q <;>
        addr_omega [hb1, q, hk])
  have x20₃ : u₃.getReg .x20 = (Model.limbs c).1 := by
    rw [k₃ .x20 (by decide), hp₂ .x20 (by decide), x20₂]
  have x21₃ : u₃.getReg .x21 = (Model.limbs c).2.1 := by
    rw [k₃ .x21 (by decide), hp₂ .x21 (by decide), x21₂]
  have x27₃ : u₃.getReg .x27 = (Model.limbs c).2.2 := by
    rw [k₃ .x27 (by decide), hp₂ .x27 (by decide), x27₂]
  have back (r : Reg) (hr : r ∈ calleeSaved) (h4 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15,
      .x16, .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] :
      List Reg))
      (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x13, .x14, .x15, .x16, .x17, .x18,
        .x19, .x22, .x23, .x24, .x25, .x26, .x28, .x29, .x30, .x31] : List Reg))
      (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
        .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] :
        List Reg)) :
      u₄.getReg r = u.getReg r := by
    rw [k₄ r h4, k₃ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp), hp₂ r hr, k₂ r h2, hp₁ r hr, k₁ r h1]
  have hn₄ : heapNext u₄ = heapNext u₃ := by
    simp only [heapNext]
    rw [fr₅ nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw
      · rcases W84_within hpre hw with hw | hw <;> simp only [Within] at hw <;> addr_omega [hw, hi, hb1]
      · simp only [Within] at hw; addr_omega [hw, hi, f2, hh, hn]]
  have m5 (x : Word) (h1 : x.toNat + 8 ≤ (s.getReg .x2 - 2544).toNat ∨
      ((s.getReg .x2 - 2512).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 928).toNat) ∨
      (s.getReg .x2 - 808).toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : x.toNat + 8 ≤ pt.toNat ∨ pt.toNat + 24 ≤ x.toNat) :
      u₄.getMem x = u₃.getMem x :=
    fr₅ x fun i hi hw ↦ by
      rcases hw with hw | hw
      · rcases W84_within hpre hw with hw | hw <;> simp only [Within] at hw <;>
          rcases h1 with q | q | q <;> addr_omega [hw, hi, hb1, q, h2]
      · simp only [Within] at hw; rcases h3 with q | q <;> addr_omega [hw, hi, q, f2, hh, hn, h2, hb2]
  have el' : eListAt v₂ pt layout.logMemory = List.replicate layout.logMemory 0 := by
    rw [vecEs, ln, hnW, hpt] at el; exact el
  have zv (i : Nat) (hi : i < layout.logMemory) : eAt v₂ (pt + BitVec.ofNat 64 (24 * i)) = 0 := by
    have := congrArg (fun l : List E ↦ l[i]?) el'
    simpa [eListAt, hi] using this
  have g (x : Word) (h1 : pt.toNat + 24 ≤ x.toNat) (h2 : x.toNat + 8 ≤ heapNext v₂) :
      u₄.getMem x = v₂.getMem x := by
    rw [m5 x (Or.inl (by addr_omega [h2, hh, hb1])) (by addr_omega [h2, hh, hb1]) (Or.inr h1)]
    exact fr₄ x fun i hi hw ↦ by simp only [Within] at hw; addr_omega [hw, hi, h2, hh, hb1]
  have m21 := b80003a84_m21 h₄
  have m20 := b80003a84_m20 h₄
  have m18 := b80003a84_m18 h₄
  rw [spAdd hpre sp₃ 1104 1552 rfl, ept] at m21 m20 m18
  have hsm := C₃.smono
  have hum := C₃.rest.mono
  have htm := C₃.tmono
  have hbuf := C₃.buf.2.1
  have spu := C₀.rest.inv.sp
  refine ⟨u₄, hrv₂.trans (hr₃.trans hr₄), Or.inl ⟨c, pt, {
    toCoreT := C₇
    pc := b80003a84_pc h₄
    hi := by decide
    x12 := b80003a84_x12 h₄
    x20 := by rw [k₄ .x20 (by decide), x20₃]
    x21 := by rw [k₄ .x21 (by decide), x21₃]
    x27 := by rw [k₄ .x27 (by decide), x27₃]
    x24 := by rw [back .x24 (by decide) (by decide) (by decide) (by decide), Ex.x24]
    x25 := by rw [back .x25 (by decide) (by decide) (by decide) (by decide), Ex.x25]; simp
    lenSlot := by
      rw [show (1616 : Word) = BitVec.ofNat 64 1616 from rfl, gA 1616 (by omega) (by omega)]
      rw [show L + BitVec.ofNat 64 0 = L by simp]; exact Ex.lenSlot
    ptr184 := by
      rw [show (2472 : Word) = BitVec.ofNat 64 2472 from rfl, gA 2472 (by omega) (by omega)]
      exact Ex.ptr184
    c0 := by rw [← spAdd hpre sp₃ 128 2528 rfl, b80003a84_m_x2_128 h₄, x20₃]
    c1 := by rw [← spAdd hpre sp₃ 120 2536 rfl, b80003a84_m_x2_120 h₄, x21₃]
    c2 := by rw [← spAdd hpre sp₃ 112 2544 rfl, b80003a84_m_x2_112 h₄, x27₃]
    ptSlot := by
      rw [← spAdd hpre sp₃ 136 2520 rfl, b80003a84_m_x2_136 h₄, spAdd hpre sp₃ 1104 1552 rfl, ept]
    nSlot := by
      rw [m5 _ (Or.inr (Or.inl ⟨le_refl _, by addr_omega [hb1]⟩)) (by addr_omega [hb1])
        (Or.inr (by addr_omega [hb1, f2, hh])), m144, hnW]
    hn := hn
    ptOld := ⟨⟨fa, by rw [hn₄, hn₃]; omega, Or.inr (by omega)⟩, by omega⟩
    ptVal := eList_point hn (eAt_eq_of_limbs (by rw [m21, m20, m18, x20₃, x21₃, x27₃]))
      fun i hi0 hi ↦ by
        rw [← zv i hi]
        exact eAt_congr (g _ (by addr_omega [f2, hh, hi0, hi]) (by addr_omega [f2, hh, hi0, hi]))
          (g _ (by addr_omega [f2, hh, hi0, hi]) (by addr_omega [f2, hh, hi0, hi]))
          (g _ (by addr_omega [f2, hh, hi0, hi]) (by addr_omega [f2, hh, hi0, hi]))
    ptApart := Or.inr (Or.inr (Or.inr (by omega)))
    pairs := fun j hj ↦ by
      have kk (k : Nat) (hk : 2552 ≤ k ∧ k ≤ 2576) (a : Word) (ha : a.toNat + k = 2656) :
          u₃.getMem (u₃.getReg .x2 + a) = u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
        rw [spAdd hpre sp₃ a (BitVec.ofNat 64 k) (by rw [BitVec.toNat_ofNat]; omega)]
        exact R₃.get (keep_slot hpre (by omega))
      interval_cases j
      · rw [show s.getReg .x2 - 912 + BitVec.ofNat 64 (16 * 0) = u₃.getReg .x2 + 1744 by
            rw [sp₃]; bv_omega,
          show s.getReg .x2 - 904 + BitVec.ofNat 64 (16 * 0) = u₃.getReg .x2 + 1752 by
            rw [sp₃]; bv_omega,
          b80003a84_m_x2_1744 h₄, b80003a84_m_x2_1752 h₄, kk 2568 (by omega) 88 rfl,
          kk 2576 (by omega) 80 rfl]
        exact ⟨h.pi0, h.pi2⟩
      · rw [show s.getReg .x2 - 912 + BitVec.ofNat 64 (16 * 1) = u₃.getReg .x2 + 1760 by
            rw [sp₃]; bv_omega,
          show s.getReg .x2 - 904 + BitVec.ofNat 64 (16 * 1) = u₃.getReg .x2 + 1768 by
            rw [sp₃]; bv_omega,
          b80003a84_m_x2_1760 h₄, b80003a84_m_x2_1768 h₄, kk 2552 (by omega) 104 rfl,
          kk 2560 (by omega) 96 rfl]
        exact ⟨h.pi1, h.pi3⟩
      · rw [show s.getReg .x2 - 912 + BitVec.ofNat 64 (16 * 2) = u₃.getReg .x2 + 1776 by
            rw [sp₃]; bv_omega,
          show s.getReg .x2 - 904 + BitVec.ofNat 64 (16 * 2) = u₃.getReg .x2 + 1784 by
            rw [sp₃]; bv_omega,
          b80003a84_m_x2_1776 h₄, b80003a84_m_x2_1784 h₄]
        exact ⟨rfl, rfl⟩
    cols := fun j hj ↦ by
      interval_cases j
      · rw [show s.getReg .x2 - 848 + BitVec.ofNat 64 (8 * 0) = u₃.getReg .x2 + 1808 by
          rw [sp₃]; bv_omega, b80003a84_m_x2_1808 h₄]; rfl
      · rw [show s.getReg .x2 - 848 + BitVec.ofNat 64 (8 * 1) = u₃.getReg .x2 + 1816 by
          rw [sp₃]; bv_omega, b80003a84_m_x2_1816 h₄]; rfl
      · rw [show s.getReg .x2 - 848 + BitVec.ofNat 64 (8 * 2) = u₃.getReg .x2 + 1824 by
          rw [sp₃]; bv_omega, b80003a84_m_x2_1824 h₄]; rfl }⟩⟩

end Entry

end Rv64Verifier.Proofs.Walk
