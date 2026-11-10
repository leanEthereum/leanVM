import Rv64Verifier.Proofs.Walk.R20C

/-!
# `walk` R20, `verify_keccak`'s result

`r20ret`: from `KcRet`, an `Err` is copied to the result (`0x80003fe4`) and leaves by `errTail₁`;
an `Ok` (`0x80003f14`) copies the inputs' point `Vec` to `S - 1728` and the outputs to
`S - 1768`, then branches on the outputs being `None` (`AtOut`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.Gkr Rv64Verifier.Model.Gkr Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Past `0x80003f14`, the openings `o` in memory, the code running `afterKeccak` on them. -/
structure AtOut (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t c x : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (cl : List ColumnClaim) (o : KeccakOpenings) (ks ke : Nat) : Prop where
  core : CoreT OI s u₀ w t x layout lir evs P C L.toNat cl
    (afterKeccak layout rows lir bus cl (o, ks, ke))
  pcs : (o.outputs = none ∧ x.pc = 0x80003ff4) ∨ (o.outputs ≠ none ∧ x.pc = 0x80003f5c)
  x12 : x.getReg .x12 = vecPtr x (s.getReg .x2 - 904)
  x13 : x.getReg .x13 = vecLen x (s.getReg .x2 - 904)
  x19 : x.getReg .x19 = x.getMem (s.getReg .x2 - 880)
  x22 : x.getReg .x22 = lir
  x23 : x.getReg .x23 = s.getReg .x10
  x24 : x.getReg .x24 = s.getReg .x2 - 512
  x25 : x.getReg .x25 = L
  x26 : x.getReg .x26 + 1 = L
  before : heapNext t ≤ heapNext c ∧ P.toNat + 56 * C.toNat ≤ heapNext c
  in1 : NewVecE c x (s.getReg .x2 - 1728) o.inputs.1
  in2 : NewVecE c x (s.getReg .x2 - 904) o.inputs.2
  outs : OutputsAt c x (s.getReg .x2 - 880) o.outputs
  /-- The outputs' pointer, length and word copied to `S - 1768`. -/
  copy : x.getMem (s.getReg .x2 - 1768) = x.getMem (s.getReg .x2 - 872) ∧
    x.getMem (s.getReg .x2 - 1760) = x.getMem (s.getReg .x2 - 864) ∧
    x.getMem (s.getReg .x2 - 1752) = x.getMem (s.getReg .x2 - 856) ∧
    x.getMem (s.getReg .x2 - 1744) = x.getMem (s.getReg .x2 - 848) ∧
    x.getMem (s.getReg .x2 - 1736) = x.getMem (s.getReg .x2 - 840)
  olen : 4 ≤ o.inputs.1.length ∧ o.inputs.2.length = Verifier.kBits

theorem NewVecE.keep {s t t' : MachineState} {a : Word} {xs : List E} (h : NewVecE s t a xs)
    (hm : ∀ y, t'.getMem y = t.getMem y) : NewVecE s t' a xs := by
  have hn : heapNext t' = heapNext t := by simp only [heapNext, hm]
  have e1 : vecCap t' a = vecCap t a := hm _
  have e2 : vecPtr t' a = vecPtr t a := hm _
  have e3 : vecLen t' a = vecLen t a := hm _
  obtain ⟨⟨⟨r1, r2⟩, vl⟩, b, el⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [e2]; exact r1
  · rw [e1, e2, hn]; exact r2
  · rw [e1, e3]; exact vl
  · simp only [NewBuf] at b ⊢; rw [e1, e2, hn]; exact b
  · rw [← el]; simp only [vecEs, e2, e3]
    exact Bus.eListAt_congr fun i _ ↦ eAt_congr (hm _) (hm _) (hm _)

/-- A `Vec<E>` whose header was copied from `a` to `b` and whose buffer is kept. -/
theorem NewVecE.move {s t x : MachineState} {a b : Word} {xs : List E} (h : NewVecE s t a xs)
    (h0 : x.getMem b = t.getMem a) (h8 : x.getMem (b + 8) = t.getMem (a + 8))
    (h16 : x.getMem (b + 16) = t.getMem (a + 16)) (hn : heapNext t ≤ heapNext x)
    (hbuf : ∀ y : Word, (vecPtr t a).toNat ≤ y.toNat →
      y.toNat + 8 ≤ (vecPtr t a).toNat + 24 * xs.length → x.getMem y = t.getMem y) :
    NewVecE s x b xs := by
  obtain ⟨Ia, Il, If⟩ := newVecE_facts h
  have e1 : vecCap x b = vecCap t a := h0
  have e2 : vecPtr x b = vecPtr t a := h8
  have e3 : vecLen x b = vecLen t a := h16
  obtain ⟨⟨⟨r1, r2⟩, vl⟩, bf, el⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [e2]; exact r1
  · rw [e1, e2]; rcases r2 with r | ⟨r, r'⟩
    · exact Or.inl r
    · exact Or.inr ⟨r, by omega⟩
  · rw [e1, e3]; exact vl
  · simp only [NewBuf] at bf ⊢; rw [e1, e2]; rcases bf.2 with r | ⟨r, r'⟩
    · exact ⟨bf.1, Or.inl r⟩
    · exact ⟨bf.1, Or.inr ⟨r, by omega⟩⟩
  · rw [← el]; simp only [vecEs, e2, e3]
    refine Bus.eListAt_congr fun i hi ↦ ?_
    rw [Il] at hi If
    rcases If with h0' | ⟨q1, q2⟩
    · omega
    have hN : heapNext t < 2 ^ 64 := (t.getMem nextAddr).isLt
    exact eAt_congr (hbuf _ (by addr_omega [q1, q2, hi, hN]) (by addr_omega [q1, q2, hi, hN]))
      (hbuf _ (by addr_omega [q1, q2, hi, hN]) (by addr_omega [q1, q2, hi, hN]))
      (hbuf _ (by addr_omega [q1, q2, hi, hN]) (by addr_omega [q1, q2, hi, hN]))

section Ret
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t c v : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {cl : List ColumnClaim}

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- `verify_keccak`'s result: the `Err` return, or `AtOut`. -/
theorem r20ret (hDN : DropNopSpec) (hDL : DropLayoutSpec) (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus)
    (Kr : KcRet OI s u₀ w t c v layout rows lir bus evs P C L cl) :
    ∃ x, Reaches Image.code v x ∧ ((∃ o ks ke,
      AtOut OI s u₀ w t c x layout rows lir bus evs P C L cl o ks ke) ∨
      Done OI s x ∨ Dead Image.code x) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have R := Kr.rest
  have sp := R.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003f00_spec Kr.pc (by
    rv_eval [sp]; and_intros <;> valid_access hval [hb1])
  have m₁ := b80003f00_mem_same h₁
  have k₁ := b80003f00_keeps h₁
  have e1728 : v.getReg .x2 + 1728 = s.getReg .x2 - 928 := by rw [sp]; bv_omega
  by_cases he : v.getMem (s.getReg .x2 - 928) = 0xffffffffffffffff
  · -- `Err`: copied to the result, then `errTail₁`
    have R₁ := R.same m₁ (k₁ .x2 (by decide))
    have hR := hpre.out
    have x23 : u₁.getReg .x23 = s.getReg .x10 := by rw [k₁ .x23 (by decide), Kr.x23]
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003fe4_spec
      (b80003f00_pc_taken h₁ (by rw [e1728]; exact he)) (by
        rv_eval [x23]
        and_intros <;> exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR])
          (by addr_omega [hR]))
    have fr₀ := b80003fe4_frame h₂ (by rw [x23]; addr_omega [hR])
    rw [x23] at fr₀
    have R₂ := R₁.result hpre (n := 24) (by omega) (DFrame.of_memFrame fr₀)
      (b80003fe4_keeps h₂ .x2 (by decide))
    obtain ⟨t', hr₃, hd⟩ := errTail₁ hDN hDL hpre h R₂ (b80003fe4_pc h₂) (by
      rw [← x23, b80003fe4_m_x23_0 h₂, b80003f00_x14 h₁]; rfl)
    exact ⟨t', hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  -- `Ok`
  obtain ⟨H, n1, n2, n3, l1, l2⟩ := Kr.ok he
  have pc₁ := b80003f00_pc_not_taken h₁ (by rw [e1728]; exact he)
  have H₁ := H.same hpre m₁ (k₁ .x2 (by decide))
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide), sp]
  obtain ⟨x, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003f14_spec pc₁ (by
    rv_eval [sp₁]; and_intros <;> valid_access hval [hb1])
  have k₂ := b80003f14_keeps h₂
  have fr : DFrame u₁ x (Within · (s.getReg .x2 - 1768) 64) := by
    have := DFrame.of_memFrame (b80003f14_frame h₂ (by rw [sp₁]; addr_omega [hb1, hb2]))
    rwa [show u₁.getReg .x2 + 888 = s.getReg .x2 - 1768 by rw [sp₁]; bv_omega] at this
  have Wok : ∀ a, Within a (s.getReg .x2 - 1768) 64 → InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦
    range_ok hpre H₁.rest (c := 1768) (k := 1768) (n := 64) rfl (by omega) (by omega) ha
  have st : StepW s u₁ x (Within · (s.getReg .x2 - 1768) 64) False :=
    StepW.ofFrame hpre H₁.rest.inv.heap fr (fun a ha ↦ (Wok a ha).1) (k₂ .x2 (by decide))
  have H₂ := H₁.stepW hpre st (fun a ha ↦ ⟨(Wok a ha).1, (Wok a ha).2, by
      rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩)
    (fun a ha ↦ by simp only [Within] at ha ⊢; constructor <;> addr_omega [ha, hb1])
  -- what the copy left alone
  have gx (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648) (hw : k ≤ 1704 ∨ 1776 ≤ k) :
      x.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
    rw [st.getF hpre (by addr_omega [hb1, hk]) (fun i hi hw' ↦ by
      simp only [Within] at hw'; rcases hw with hw | hw <;> addr_omega [hw', hw, hi, hb1, hk])
      (fun hf ↦ hf.elim), m₁]
  have gH : ∀ y : Word, y.toNat + 8 ≤ heapNext v → x.getMem y = v.getMem y := fun y hy ↦ by
    rw [st.getH hpre (fun a ha ↦ (Wok a ha).1) (by simp only [heapNext, m₁] at hy ⊢; exact hy), m₁]
  have hxm : heapNext v ≤ heapNext x := by
    have := st.mono; simp only [heapNext, m₁] at this ⊢; exact this
  have gxa (a : Word) (k : Nat) (ha : a = s.getReg .x2 - BitVec.ofNat 64 k)
      (hk : 112 ≤ k ∧ k ≤ 2648) (hw : k ≤ 1704 ∨ 1776 ≤ k) : x.getMem a = v.getMem a := by
    subst ha; exact gx k hk hw
  have eu (c' d : Word) (hc : c'.toNat + d.toNat = 2656) :
      u₁.getReg .x2 + c' = s.getReg .x2 - d := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have ev (c' d : Word) (hc : c'.toNat + d.toNat = 2656) :
      v.getReg .x2 + c' = s.getReg .x2 - d := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have mu (c' d : Word) (hc : c'.toNat + d.toNat = 2656) :
      u₁.getMem (u₁.getReg .x2 + c') = v.getMem (s.getReg .x2 - d) := by
    rw [eu c' d hc, m₁]
  have eo : (kOpOf v (s.getReg .x2 - 928)).outputs =
      if vecCap v (s.getReg .x2 - 880) = errNiche then none
      else some (vecEs v (s.getReg .x2 - 880), eAt v (s.getReg .x2 - 856)) := by
    simp only [kOpOf, show s.getReg .x2 - 928 + 48 = s.getReg .x2 - 880 by bv_omega,
      show s.getReg .x2 - 928 + 72 = s.getReg .x2 - 856 by bv_omega]
  have cap₁ : u₁.getMem (u₁.getReg .x2 + 1776) = vecCap v (s.getReg .x2 - 880) := mu 1776 880 rfl
  have x14₁ : u₁.getReg .x14 = errNiche := b80003f00_x14 h₁
  have bufv (a : Word) {xs : List E} (hv : NewVecE c v a xs) : ∀ y : Word,
      (vecPtr v a).toNat ≤ y.toNat → y.toNat + 8 ≤ (vecPtr v a).toNat + 24 * xs.length →
      x.getMem y = v.getMem y := by
    intro y h1 h2
    obtain ⟨-, Il, If⟩ := newVecE_facts hv
    rw [Il] at If
    rcases If with h0 | ⟨-, q2⟩
    · omega
    exact gH y (by omega)
  have R1 (r : Reg) (h2 : r ∈ ([.x1, .x2, .x3, .x4, .x8, .x10, .x11, .x14, .x15, .x18, .x20, .x21,
      .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h1 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x16, .x17, .x18, .x19,
        .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      x.getReg r = v.getReg r := by rw [k₂ r h2, k₁ r h1]
  refine ⟨x, hr₁.trans hr₂, Or.inl ⟨_, _, _, {
    core := H₂
    pcs := by
      by_cases hO : vecCap v (s.getReg .x2 - 880) = errNiche
      · exact Or.inl ⟨by rw [eo, ite_eq_left_of_eq_true _ _ (eq_true hO)],
          b80003f14_pc_taken h₂ (by rw [cap₁, x14₁, hO])⟩
      · exact Or.inr ⟨by rw [eo, ite_eq_right_of_eq_false _ _ (eq_false hO)]; simp,
          b80003f14_pc_not_taken h₂ (by rw [cap₁, x14₁]; exact hO)⟩
    x12 := by
      rw [b80003f14_x12 h₂, mu 1760 896 rfl]
      simp only [vecPtr]; rw [gxa _ 896 (by bv_omega) (by omega) (by omega)]; congr 1; bv_omega
    x13 := by
      rw [b80003f14_x13 h₂, mu 1768 888 rfl]
      simp only [vecLen]; rw [gxa _ 888 (by bv_omega) (by omega) (by omega)]; congr 1; bv_omega
    x19 := by
      rw [b80003f14_x19 h₂, mu 1776 880 rfl]
      exact (gxa (s.getReg .x2 - 880) 880 rfl (by omega) (by omega)).symm
    x22 := by rw [R1 .x22 (by decide) (by decide), Kr.x22]
    x23 := by rw [R1 .x23 (by decide) (by decide), Kr.x23]
    x24 := by rw [R1 .x24 (by decide) (by decide), Kr.x24]
    x25 := by rw [R1 .x25 (by decide) (by decide), Kr.x25]
    x26 := by rw [R1 .x26 (by decide) (by decide), Kr.x26]
    before := Kr.before
    in1 := by
      refine NewVecE.move n1 ?_ ?_ ?_ hxm (bufv _ n1)
      · rw [← eu 928 1728 rfl, b80003f14_m_x2_928 h₂, b80003f00_x15 h₁, e1728]
      · rw [show s.getReg .x2 - 1728 + 8 = u₁.getReg .x2 + 936 by rw [sp₁]; bv_omega,
          b80003f14_m_x2_936 h₂, b80003f00_x11 h₁, ev 1736 920 rfl]
        congr 1; bv_omega
      · rw [show s.getReg .x2 - 1728 + 16 = u₁.getReg .x2 + 944 by rw [sp₁]; bv_omega,
          b80003f14_m_x2_944 h₂, b80003f00_x10 h₁, ev 1744 912 rfl]
        congr 1; bv_omega
    in2 := by
      refine NewVecE.move n2 (gxa (s.getReg .x2 - 904) 904 rfl (by omega) (by omega))
        (gxa _ 896 (by bv_omega) (by omega) (by omega)) (gxa _ 888 (by bv_omega) (by omega) (by omega))
        hxm (bufv _ n2)
    outs := by
      generalize (kOpOf v (s.getReg .x2 - 928)).outputs = oo at n3 ⊢
      rcases oo with _ | ⟨p, wd⟩
      · simp only [OutputsAt] at n3 ⊢
        simp only [vecCap]; rw [gxa (s.getReg .x2 - 880) 880 rfl (by omega) (by omega)]; exact n3
      · simp only [OutputsAt] at n3 ⊢
        obtain ⟨hc, hv, hw⟩ := n3
        refine ⟨by simp only [vecCap]; rw [gxa (s.getReg .x2 - 880) 880 rfl (by omega) (by omega)]; exact hc,
          NewVecE.move hv (gxa (s.getReg .x2 - 880) 880 rfl (by omega) (by omega))
            (gxa _ 872 (by bv_omega) (by omega) (by omega))
            (gxa _ 864 (by bv_omega) (by omega) (by omega)) hxm (bufv _ hv), ?_⟩
        rw [← hw]
        exact eAt_congr (gxa _ 856 (by bv_omega) (by omega) (by omega))
          (gxa _ 848 (by bv_omega) (by omega) (by omega))
          (gxa _ 840 (by bv_omega) (by omega) (by omega))
    copy := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [← eu 888 1768 rfl, b80003f14_m_x2_888 h₂, mu 1784 872 rfl,
          gxa (s.getReg .x2 - 872) 872 rfl (by omega) (by omega)]
      · rw [← eu 896 1760 rfl, b80003f14_m_x2_896 h₂, mu 1792 864 rfl,
          gxa (s.getReg .x2 - 864) 864 rfl (by omega) (by omega)]
      · rw [← eu 904 1752 rfl, b80003f14_m_x2_904 h₂, mu 1800 856 rfl,
          gxa (s.getReg .x2 - 856) 856 rfl (by omega) (by omega)]
      · rw [← eu 912 1744 rfl, b80003f14_m_x2_912 h₂, mu 1808 848 rfl,
          gxa (s.getReg .x2 - 848) 848 rfl (by omega) (by omega)]
      · rw [← eu 920 1736 rfl, b80003f14_m_x2_920 h₂, mu 1816 840 rfl,
          gxa (s.getReg .x2 - 840) 840 rfl (by omega) (by omega)]
    olen := ⟨l1, l2⟩ }⟩⟩

end Ret

end Rv64Verifier.Proofs.Walk
