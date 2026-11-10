import Rv64Verifier.Proofs.Pcs.VsoFinalClaims

/-!
# `verify_stacked_opening`'s final level: the basis at the terminal point

`0x8000ba98` calls `StackBasis::evaluate(S - 184, S - 728, rotated point)`, which returns at
`0x8000bab0` (`TB`): the batched basis at the point rotated by the first fold count, the claims and
the scales those of the configured state.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A weight whose regions a callee reads. -/
theorem weightSrc_of {t : MachineState} {k : ℕ} {e : Word} {P : Word → ℕ → Prop}
    (hP : ∀ a n, P a n → Src t k a n) (h88 : Src t k e 88) (he8 : e.toNat % 8 = 0)
    (hcr : Extend.ClaimRegions P t e) : WeightSrc t k e := by
  have hb := h88.bound
  refine ⟨h88.prefix (by omega), ?_⟩
  simp only [Extend.ClaimRegions] at hcr
  by_cases h1 : t.getMem e = eqTag
  · simp only [h1, ↓reduceIte] at hcr ⊢; exact hP _ _ hcr.2
  · by_cases h2 : t.getMem e = ringTag
    · simp only [h2, ↓reduceIte] at hcr ⊢
      have e32 : e + 8 + 24 = e + 32 := Extend.add_lit _ _ _ _ rfl
      refine ⟨h88.sub ?_ ?_ ?_, hP _ _ hcr.2.1, by rw [e32]; exact hP _ _ hcr.2.2⟩ <;>
        rcases hb with h0 | h0
      all_goals first | omega | addr_omega [h0, he8]
    · simp only [h1, h2, ↓reduceIte] at hcr ⊢
      exact ⟨h88.prefix (by omega), hP _ _ hcr.2.1, hP _ _ hcr.2.2⟩

/-- The configured state's words below the mark, between the entry's `NEXT` and the mark, kept. -/
theorem LM.eList {s c u : MachineState} {L : ℕ} {hi p : Word} {n : ℕ} (hpre : VsoPre s)
    (hfr : DFrame c u (LM s L hi)) (hp1 : heapNext s ≤ p.toNat) (hp2 : p.toNat + 24 * n ≤ L)
    (hL : L ≤ heapEnd) : eListAt u p n = eListAt c p n := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIf := hI.free
  have hrf := hpre.root.free
  simp only [Outside] at hIf hrf
  obtain ⟨hnx, -⟩ := sfacts hpre
  simp only [heapEnd] at hL
  refine DFrame.eList hfr (fun a ha hw ↦ ?_) (Or.inr (by omega))
  simp only [Within] at ha
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw
  · addr_omega [ha.1, ha.2, hw, hb, hp2, hL]
  · addr_omega [ha.1, ha.2, hw, hb, hp2, hL]
  · addr_omega [ha.1, ha.2, hw, hb, hp2, hL]
  · addr_omega [ha.1, ha.2, hw, hb, hp2, hL]
  · addr_omega [ha.1, ha.2, hw, hb, hp2, hL]
  · addr_omega [ha.1, ha.2, hw, hb, hp2, hL]
  · addr_omega [ha.1, ha.2, hw, hnx, hp2, hL]
  · omega
  · rcases hw with hw | hw
    · simp only [W] at hw
      rcases hIf.1 with h1 | h1
      · addr_omega [ha.1, ha.2, hw, h1, hp1, hS]
      · addr_omega [ha.1, ha.2, hw, h1, hS, hp2, hL]
    · rcases hrf.1 with h1 | h1
      · addr_omega [ha.1, ha.2, hw, h1, hp1]
      · addr_omega [ha.1, ha.2, hw, h1, hp2, hL]

/-- `log_n ≤ 28`, the configuration's. -/
theorem logN_le {s b c : MachineState} {nxb QP QL FP RP : Word}
    (hc : Configured s b c nxb QP QL FP RP) : (s.getReg .x12).toNat ≤ 28 := by
  have h := hc.config
  by_contra hn
  rw [Model.Pcs.deriveConfigRust, Model.Pcs.whirQueriesRust_none (fun ha ↦ hn (by
    unfold Whir.Admissible Whir.maxLogStack at ha; omega))] at h
  cases h

/-- At `0x8000bab0`: the batched basis `w0` at the rotated point in `S - 184`. -/
structure TB (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) (tf : List E) (rt : E)
    (w0 : E) : Prop extends TI OA s x u v Wl residual where
  pc : v.pc = 0x8000bab0
  tfl : tf.length = mlF s Wl
  x8 : v.getReg .x8 = vecPtr v (s.getReg .x2 - 304)
  x19 : v.getReg .x19 = BitVec.ofNat 64 (mlF s Wl)
  tail : TailV s u v tf
  trg : E.ofLimbs (BF64.ofBitVec (v.getMem (s.getReg .x2 - 904)))
    (BF64.ofBitVec (v.getMem (s.getReg .x2 - 920))) (BF64.ofBitVec (v.getMem (s.getReg .x2 - 864))) = rt
  six : 6 ≤ (Wl.folds ++ tf).length
  point : VecOk v (s.getReg .x2 - 280) 24 8 ∧ vecEs v (s.getReg .x2 - 280) = Wl.folds ++ tf ∧
    NewBuf u v (vecPtr v (s.getReg .x2 - 280)) ((vecCap v (s.getReg .x2 - 280)).toNat * 24) 8
  basis : basisOf s x ((Wl.folds ++ tf).drop 6 ++ (Wl.folds ++ tf).take 6) = some w0
  wt : eAt v (s.getReg .x2 - 184) = w0
  value : RunsF OA s v (afterTail (cfgOf s) (basisOf s x) residual Wl tf rt)

/-- **The basis at the terminal point**: `0x8000ba98` to `0x8000bab0`, or a dead end. -/
theorem tBasis (hB : BasisSpec) {OA : MachineState → Word → Model.TState → Prop}
    {s : MachineState} {x : LCtx} {u v : MachineState} {Wl : Model.Pcs.WhirLocals}
    {residual : List E} {tf : List E} {rt : E} (hpre : VsoPre s) (hv : TV OA s x u v Wl residual tf rt) :
    ∃ w, Reaches Image.code v w ∧ (Dead Image.code w ∨ ∃ w0, TB OA s x u w Wl residual tf rt w0) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hst.above
  rw [stackLo_vso] at hab
  have hsp := hv.sp
  have hfin := hv.toTI.fin
  have hsu := hfin.su
  have hhs := hpre.heap.lo
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000ba98_spec hv.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000ba98_keeps h₁
  have hm₁ := b8000ba98_mem_same h₁
  obtain ⟨T₁, n₁⟩ := hv.toTI.stepS hpre (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₁ .x2 (by decide))
  have inv₁ := T₁.inv hpre
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₁.sp
  have hsl : stackLo t₁ basisStack = s.getReg .x2 - 2432 := by
    simp only [stackLo, basisStack, ringEvalStack, mulStack, sp₁]; addr_omega [hb]
  -- the configured state's `StackBasis`, kept
  have hc := hfin.cfg
  have hmark := hfin.mark
  have hcm := hfin.mono
  have hhu := hfin.heap.hi
  have hL : x.L ≤ heapEnd := by omega
  have kc (y : Word) (hy : (s.getReg .x2 - 776).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 688).toNat) : t₁.getMem y = x.c.getMem y := by
    rw [hm₁, hv.toTI.keepStk hpre (Or.inr ⟨hy.1, by addr_omega [hy.2, hb]⟩)]
    exact LM.keep hpre hfin.fr hhu (Or.inr (Or.inr (Or.inr hy)))
  have hK := hc.kept
  have hsc := hc.scales
  have hnc := hc.nxs
  have hSp : vecPtr t₁ (s.getReg .x2 - 728) = vecPtr x.c (s.getReg .x2 - 728) := by
    simp only [vecPtr]; exact kc _ (by addr_omega [hb])
  have hSl : vecLen t₁ (s.getReg .x2 - 728) = vecLen x.c (s.getReg .x2 - 728) := by
    simp only [vecLen]; exact kc _ (by addr_omega [hb])
  have hSb : ncl s = 0 ∨ heapNext s ≤ (vecPtr x.c (s.getReg .x2 - 728)).toNat ∧
      (vecPtr x.c (s.getReg .x2 - 728)).toNat + 24 * ncl s ≤ x.nxb.toNat := hsc.2.2
  have hSe : vecEs t₁ (s.getReg .x2 - 728) = vecEs x.c (s.getReg .x2 - 728) := by
    simp only [vecEs, hSp, hSl, hsc.1]
    rcases hSb with h0 | h0
    · rw [h0]; rfl
    · rw [T₁.eList hpre (Or.inr ⟨h0.1, by omega⟩),
        LM.eList hpre hfin.fr h0.1 (by omega) hL]
  have hcp : basisClaimsPtr t₁ (s.getReg .x2 - 728) = s.getReg .x14 := by
    simp only [basisClaimsPtr]
    rw [kc _ (by addr_omega [hb]), show s.getReg .x2 - 728 + 24 = s.getReg .x2 - 704 by addr_omega [hb]]
    exact hK.b3
  have hcl : basisClaimsLen t₁ (s.getReg .x2 - 728) = (s.getReg .x15).toNat := by
    simp only [basisClaimsLen]
    rw [kc _ (by addr_omega [hb]), show s.getReg .x2 - 728 + 32 = s.getReg .x2 - 696 by addr_omega [hb]]
    rw [hK.b4]
  -- the rotated point
  obtain ⟨hRv, hRe, hRn⟩ := hv.rot
  have hRl := hRv.len
  have hR8 := hRv.raw.1
  have hRlen : (vecLen v (s.getReg .x2 - 464)).toNat = (Wl.folds ++ tf).length := by
    have := congrArg List.length hRe
    simp only [vecEs, eListAt_length, List.length_append, List.length_drop, List.length_take] at this
    have h6 := hv.six
    rw [List.length_append] at h6 ⊢; omega
  have hhv := hv.heap.hi
  simp only [heapEnd] at hhv hab
  have hn1 : heapNext t₁ = heapNext v := by simp only [heapNext, n₁]
  have hvm := hv.mono
  have hRb : (vecLen v (s.getReg .x2 - 464)).toNat = 0 ∨
      heapNext s ≤ (vecPtr v (s.getReg .x2 - 464)).toNat ∧
      (vecPtr v (s.getReg .x2 - 464)).toNat + 24 * (vecLen v (s.getReg .x2 - 464)).toNat ≤
        heapNext t₁ := by
    rcases hRn.2 with h0 | h0
    · left; omega
    · right; exact ⟨by omega, by omega⟩
  have hx10 : t₁.getReg .x10 = s.getReg .x2 - 184 := by rw [b8000ba98_x10 h₁, hsp]; addr_omega [hb]
  have hx11 : t₁.getReg .x11 = s.getReg .x2 - 728 := by rw [b8000ba98_x11 h₁, hsp]; addr_omega [hb]
  have hx12 : t₁.getReg .x12 = vecPtr v (s.getReg .x2 - 464) := by
    rw [b8000ba98_x12 h₁, hsp, show s.getReg .x2 - BitVec.ofNat 64 1040 + 584 =
      s.getReg .x2 - 464 + 8 by addr_omega [hb]]; rfl
  have hx13 : t₁.getReg .x13 = vecLen v (s.getReg .x2 - 464) := by
    rw [b8000ba98_x13 h₁, hsp, show s.getReg .x2 - BitVec.ofNat 64 1040 + 592 =
      s.getReg .x2 - 464 + 16 by addr_omega [hb]]; rfl
  have heapSrc (p : Word) (n : ℕ)
      (hp : n = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + n ≤ heapNext t₁) (h8 : p.toNat % 8 = 0)
      (hp0 : n = 0 → p.toNat ≤ heapNext t₁) : Src t₁ basisStack p n := by
    rcases hp with h0 | h0
    · subst h0
      refine ⟨Or.inl rfl, Or.inl rfl, ⟨Or.inl (by have := hp0 rfl; omega), Or.inl rfl⟩⟩
    · by_cases hn0 : n = 0
      · subst hn0; exact ⟨Or.inl rfl, Or.inl rfl, ⟨Or.inl (by omega), Or.inl rfl⟩⟩
      refine ⟨Or.inr (heap_region (by simp only [heapStart, heapNext] at hhs h0 ⊢; omega)
        (by simp only [heapEnd]; omega) h8), ?_, ⟨Or.inl h0.2, ?_⟩⟩
      · rw [hsl]; simp only [basisStack, ringEvalStack, mulStack]; addr_omega [h0.2, hhv, hab, hb, hn1]
      · addr_omega [h0.2, hhv, hnx, hab, hb, hn1]
  have hsu₁ : heapNext s ≤ heapNext t₁ := T₁.su
  have hcu : heapNext x.c ≤ heapNext t₁ := by omega
  have hcalle {a : Word} {n : ℕ} (h : Src s vsoStack a n) : Src t₁ basisStack a n :=
    h.callee (by rw [stackLo_vso, hsl]; addr_omega [hb])
      (by rw [stackLo_vso, hsl]; simp only [basisStack, ringEvalStack, mulStack, vsoStack,
        roundPolyStack, nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack,
        keccakFStack, memStack]; addr_omega [hb])
      (by rw [stackLo_vso]; simp only [vso_stack]; addr_omega [hb]) hsu₁
  have hc14 := hpre.claims
  have hcb := hc14.bound
  have hpreB : BasisPre t₁ := {
    heap := T₁.heap
    stack := hst.sub 1040 sp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    rodata := inv₁.rodata' hpre
    out := by
      rw [hx10]
      have := hst.rodata
      rw [stackLo_vso, vso_stack] at this
      exact ⟨stack_region hpre (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]),
        by rw [hsl]; simp only [basisStack, ringEvalStack, mulStack]; addr_omega [hb],
        stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb]), by addr_omega [this, hb]⟩
    self := by
      rw [hx11]
      exact ⟨Or.inr (stack_region hpre (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])),
        by rw [hsl]; simp only [basisStack, ringEvalStack, mulStack]; addr_omega [hb],
        stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])⟩
    scales := by
      rw [hx11, hSp, hSl, hsc.1]
      rcases hSb with h0 | h0
      · exact Or.inl h0
      · have := hmark.2.2.1
        have := hmark.2.2.2
        exact Or.inr (heapSrc _ _ (Or.inr ⟨h0.1, by omega⟩) hsc.2.1 fun _ ↦ by omega)
    claims := by rw [hx11, hcp, hcl]; exact hcalle hc14
    weights := by
      intro i hi
      rw [hx11, hcl] at hi
      rw [hx11, hcp]
      have hcr := (claim_keep hpre inv₁ hi).2
      have h88 := (claimRegions_ro hpre hi).1
      exact weightSrc_of (P := Ro s) (fun a n h ↦ hcalle h.1) (hcalle h88.1) (by
        rcases hc14.region with h0 | h0
        · omega
        · have := Region.bounds h0; addr_omega [this, hi]) hcr
    point := by
      rw [hx12, hx13]
      exact heapSrc _ _ (by
        rcases hRb with h0 | h0
        · left; omega
        · right; exact h0) hR8 (fun h0 ↦ by have := hv.six; omega)
    outScales := by
      rw [hx10, hx11, hSp, hSl, hsc.1]
      rcases hSb with h0 | h0
      · rw [h0]; exact Or.inr (Or.inl rfl)
      · have := hmark.2.2.1; have hL' := hL; simp only [heapEnd] at hL'
        addr_omega [h0.2, hb, hab, hL', this] }
  obtain ⟨t₂, r₂, ⟨hpc₂, hpres₂, hpost⟩ | hdead⟩ := hB.call (Reaches.refl t₁) (b8000ba98_pc h₁) hpreB
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inl hdead⟩
  have X₂ := hpost.frame
  rw [hx10, hsl] at X₂
  have hhi₂ := hpost.heap.hi
  simp only [heapEnd] at hhi₂
  have T₂ : TI OA s x u t₂ Wl residual := T₁.trans X₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl (by
          simp only [basisStack, ringEvalStack, mulStack] at ha; addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_trans T₁.mono ha.1, ha.2⟩)))))
    hpost.heap hpost.mono (hpres₂ .x2 (by decide))
  have hX₂ (a : Word) (ha : Within a (s.getReg .x2 - 184) 24 ∨
      Within a (s.getReg .x2 - 2432) basisStack ∨ Within a nextAddr 8 ∨ Fresh t₁ t₂ a) :
      ¬ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext t₁) := by
    rcases ha with ha | ha | ha | ha
    · exact SS.heap hpre (Or.inr (Or.inl (by addr_omega [ha, hb]))) T₁.heap.hi
    · exact SS.heap hpre (Or.inr (Or.inr (Or.inl (by
        simp only [basisStack, ringEvalStack, mulStack] at ha; addr_omega [ha, hb])))) T₁.heap.hi
    · intro ⟨_, h2⟩; addr_omega [ha, h2, hhv, hn1, hnx, hab, hb]
    · intro ⟨_, h2⟩; simp only [Fresh] at ha; omega
  have kw (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 184).toNat) : t₂.getMem y = v.getMem y := by
    rw [X₂.word (fun a ha hx ↦ by
      rcases hx with hx | hx | hx | hx
      · addr_omega [ha, hx, hy, hb]
      · simp only [basisStack, ringEvalStack, mulStack] at hx; addr_omega [ha, hx, hy, hb]
      · addr_omega [ha, hx, hy, hb, hnx]
      · simp only [Fresh] at hx; addr_omega [ha, hx.2, hy, hb, hhi₂, hab]) (by addr_omega [hy, hb]), hm₁]
  have hval := hpost.value
  rw [hx11, hx12, hx13, hx10, hcp, hcl, claims_keep hpre inv₁, hSe,
    show eListAt t₁ (vecPtr v (s.getReg .x2 - 464)) (vecLen v (s.getReg .x2 - 464)).toNat =
      vecEs v (s.getReg .x2 - 464) by simp only [vecEs, eListAt, eAt, hm₁], hRe] at hval
  obtain ⟨hPv, hPe, hPn⟩ := hv.point
  have hPk := vecE_keep ((DFrame.of_same hm₁ _).trans X₂ fun _ h ↦ h) hPv (fun a ha ↦ ⟨fun hw ↦ by
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hw, hb]
      · simp only [basisStack, ringEvalStack, mulStack] at ha; addr_omega [ha, hw, hb]
      · addr_omega [ha, hw, hb, hnx]
      · simp only [Fresh] at ha; addr_omega [ha.2, hw, hb, hhi₂, hab], fun hw ↦ by
      rcases hPn.2 with h0 | h0
      · simp only [Within] at hw; omega
      · exact hX₂ a ha ⟨by simp only [Within] at hw; omega, by simp only [Within] at hw; omega⟩⟩)
    (by addr_omega [hb]) (by have := hpost.mono; omega) hv.heap
  refine ⟨t₂, r₁.trans r₂, Or.inr ⟨eAt t₂ (s.getReg .x2 - 184), {
    toTI := T₂
    pc := by rw [hpc₂, returnAddress_eq, b8000ba98_x1 h₁]; decide
    tfl := hv.tfl
    x8 := by
      rw [hpres₂ .x8 (by decide), k₁ .x8 (by decide), hv.x8]; simp only [vecPtr]
      rw [kw _ (by addr_omega [hb])]
    x19 := by rw [hpres₂ .x19 (by decide), k₁ .x19 (by decide), hv.x19]
    tail := hv.tail.keep hv.heap hv.toTI.fin.su ((DFrame.of_same hm₁ _).trans X₂ fun _ h ↦ h)
      (fun a ha hw ↦ by
        rcases ha with ha | ha | ha | ha
        · addr_omega [ha, hw, hb]
        · simp only [basisStack, ringEvalStack, mulStack] at ha; addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb, hnx]
        · simp only [Fresh] at ha; addr_omega [ha.2, hw, hb, hhi₂, hab])
      (fun a ha ↦ by rw [← hn1]; exact hX₂ a ha) (by addr_omega [hb]) (by have := hpost.mono; omega)
    trg := by
      rw [kw _ (by addr_omega [hb]), kw _ (by addr_omega [hb]), kw _ (by addr_omega [hb])]
      exact hv.trg
    six := hv.six
    point := ⟨hPk.1, by rw [hPk.2.1]; exact hPe, by
      rw [hPk.2.2.1, hPk.2.2.2.1]; exact NewBuf.grow hPn (by have := hpost.mono; omega)⟩
    basis := hval
    wt := rfl
    value := hv.value.keep hpre (hv.toTI.inv hpre) ((DFrame.of_same hm₁ _).trans X₂ fun _ h ↦ h)
      fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inl (by simp only [basisStack, ringEvalStack, mulStack] at ha; addr_omega [ha, hb])
        · exact Or.inr (Or.inl ha)
        · simp only [Fresh] at ha
          exact Or.inr (Or.inr (Or.inl ⟨by omega, by simp only [heapEnd]; omega⟩)) }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
