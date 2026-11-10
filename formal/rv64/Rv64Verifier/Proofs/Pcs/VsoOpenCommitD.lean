import Rv64Verifier.Proofs.Pcs.VsoOpenCommitC

/-!
# `verify_stacked_opening`'s level loop: the out-of-domain value

`0x8000a630` calls `next_scalar` into `S - 384`; `0x8000a640` returns its `Err`; `0x8000a654`
copies the value to `S - 584` and calls `sumcheck_round_poly(S - 464, 3, S - 584, None)`, whose
`Err` `0x8000a684` returns: then the intro message is at `S - 464` (`OodV`, at `0x8000a654`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000a654`, from `CommitS` at `v`: the value read at `S - 376`. -/
structure OodV (s : MachineState) (x : LCtx) (h t u v w : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q : List E) (d : Digest) : Prop where
  cs : CommitS s x h t u v ℓ Wl lf q d
  pc : w.pc = 0x8000a654
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s w (w.getMem nextAddr)
  fr : DFrame v w fun a ↦ Within a (s.getReg .x2 - 384) 32 ∨
    Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424
  regs : ∀ r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x27],
    w.getReg r = v.getReg r
  x1 : w.getReg .x1 = w.getMem (s.getReg .x2 - 376)
  x26 : w.getReg .x26 = w.getMem (s.getReg .x2 - 368)
  dig : digestAt w (s.getReg .x11) = digestAt v (s.getReg .x11)
  value : RunsC s w ℓ
    (Model.TM.sumcheckRoundPoly 3 (eAt w (s.getReg .x2 - 376)) none >>= fun i ↦
      Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (fcOf s ℓ)
        (rtOf s ℓ) (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf
        ([], [(i, Model.Pcs.GluedWeightRust.ood (vecEs v (s.getReg .x2 - 560)))]))
    [(d, rootShape s (ℓ + 1))]

/-- **`0x8000a630`**: the out-of-domain value read, or an `Err`. -/
theorem oodValue (hN : NextScalarSpec) {s : MachineState} {x : LCtx} {h t u v : MachineState}
    {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q : List E} {d : Digest} (hpre : VsoPre s)
    (hv : CommitS s x h t u v ℓ Wl lf q d) :
    ∃ w, Reaches Image.code v w ∧ (FailR s w ∨ OodV s x h t u v w ℓ Wl lf q d) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrs := hpre.rootSponge
  have hsp := hv.sp
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a630_spec hv.pc trivial
  have k₁ := b8000a630_keeps h₁
  have hm₁ := b8000a630_mem_same h₁
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [hm₁]; exact Inv.same' hv.inv hm₁ (k₁ .x2 (by decide))
  obtain ⟨t₂, hr₂, hv₂⟩ := callNextScalar (o := s.getReg .x2 - 384) hN hpre inv₁
    (b8000a630_pc h₁) (by rw [b8000a630_x10 h₁, hsp]; addr_omega [hb])
    (by rw [b8000a630_x11 h₁, hv.x27]) (by addr_omega [hb])
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, X₂, herr₂, hval₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (Or.inl hd)⟩
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [hpres₂ .x2 (by decide), k₁ .x2 (by decide), hsp]
  have hX₂ (a : Word) (ha : Within a (s.getReg .x2 - 384) 32 ∨ Within a (s.getReg .x10 + 8) 344 ∨
      Within a (s.getReg .x2 - 2464) 1424) : Wr s vsoStack (WR s) (t₁.getMem nextAddr) a ∧
      ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 104) 104 := by
    rcases ha with ha | ha | ha
    · exact ⟨Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb]))), by addr_omega [ha, hb]⟩
    · exact ⟨Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS])), by addr_omega [ha, hS, hIs, hb]⟩
    · exact ⟨Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb]))), by addr_omega [ha, hb]⟩
  have nx₂ : t₂.getMem nextAddr = t₁.getMem nextAddr := X₂ _ fun i hi hw ↦ by
    obtain ⟨hnx, -⟩ := sfacts hpre
    rcases hw with hw | hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hS, hI.free.2]
    · addr_omega [hw, hi, hb, hnx]
  have inv₂ : InvR s t₂ (t₂.getMem nextAddr) := by
    rw [nx₂]
    exact Inv.step' hpre inv₁ X₂ (fun a ha ↦ (hX₂ a ha).1) (fun a ha ↦ (hX₂ a ha).2) nx₂
      (le_refl _) inv₁.fits (hpres₂ .x2 (by decide))
  have e656 : t₂.getReg .x2 + 656 = s.getReg .x2 - 384 := by addr_omega [hb, sp₂]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a640_spec
    (by rw [hpc₂, returnAddress_eq, b8000a630_x1 h₁]; decide) (by
      rv_eval [sp₂]
      and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000a640_keeps h₃
  have hm₃ := b8000a640_mem_same h₃
  have inv₃ : InvR s t₃ (t₃.getMem nextAddr) := by
    rw [hm₃]; exact Inv.same' inv₂ hm₃ (k₃ .x2 (by decide))
  have e664 : t₂.getReg .x2 + 664 = s.getReg .x2 - 376 := by addr_omega [hb, sp₂]
  have e672 : t₂.getReg .x2 + 672 = s.getReg .x2 - 368 := by addr_omega [hb, sp₂]
  by_cases htag : t₂.getMem (s.getReg .x2 - 384) = 0
  swap
  · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a650_spec
      (b8000a640_pc_not_taken h₃ (by rw [e656]; exact htag)) trivial
    have inv₄ : InvR s t₄ (t₃.getMem nextAddr) :=
      Inv.same' inv₃ (b8000a650_mem_same h₄) (b8000a650_keeps h₄ .x2 (by decide))
    obtain ⟨w, hw, hfw⟩ := fail844 inv₄ (b8000a650_pc h₄) (by
      rw [b8000a650_keeps h₄ .x1 (by decide), b8000a640_x1 h₃, e664,
        show s.getReg .x2 - 376 = s.getReg .x2 - 384 + 8 by addr_omega [hb], herr₂ htag]
      decide)
    exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hw))), Or.inl hfw⟩
  have X : DFrame v t₃ fun a ↦ Within a (s.getReg .x2 - 384) 32 ∨
      Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 :=
    (((DFrame.of_same hm₁ _).trans X₂ fun _ h ↦ h).trans (DFrame.of_same hm₃ _)) fun _ h ↦ h
  have hd₃ : digestAt t₃ (s.getReg .x11) = digestAt v (s.getReg .x11) :=
    digest_keep X (root_bound hpre) fun y hy hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrs]
      · addr_omega [hy, hw, hrst, hb]
  have e376 : s.getReg .x2 - 376 = s.getReg .x2 - 384 + 8 := by addr_omega [hb]
  have V₁ := hv.value.same (v := t₁) (by simp only [digestAt, hm₁]) fun T hT ↦
    tr_keep hpre hv.inv hT (DFrame.of_same hm₁ fun _ ↦ False) fun _ h ↦ h.elim
  have V₂ := V₁.bind (v := t₃) (nx' := []) (eAt t₃ (s.getReg .x2 - 376))
    (by rw [hd₃]; simp only [digestAt, hm₁]) fun T hT ↦ by
      have hval := hval₂ T hT
      cases hrun : Model.TM.nextScalar.run T with
      | none => rw [hrun] at hval; rw [hval.1] at htag; exact absurd htag (by decide)
      | some r =>
        obtain ⟨xv, T'⟩ := r
        rw [hrun] at hval
        obtain ⟨-, hx, hT'⟩ := hval
        have hk := Model.Pcs.Keeps.nextScalar T xv T' hrun
        refine ⟨T', ?_, tr_keep hpre inv₂ hT' (DFrame.of_same hm₃ fun _ ↦ False) fun _ h ↦ h.elim,
          hk.1, hk.2.2, by rw [hk.2.1, List.append_nil]⟩
        rw [← hx, e376]
        simp only [eAt, hm₃]
  rw [List.append_nil] at V₂
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr {
    cs := hv
    pc := b8000a640_pc_taken h₃ (by rw [e656]; exact htag)
    sp := by rw [k₃ .x2 (by decide), sp₂]
    inv := inv₃
    fr := X
    regs := fun r hr' ↦ by
      rw [k₃ r (mem_of_mem hr' _), hpres₂ r (by simp only [calleeSaved]; exact mem_of_mem hr' _),
        k₁ r (mem_of_mem hr' _)]
    x1 := by rw [b8000a640_x1 h₃, e664, hm₃]
    x26 := by rw [b8000a640_x26 h₃, e672, hm₃]
    dig := hd₃
    value := V₂ }⟩

/-- At `0x8000a698`, from `OodV` at `w`: the intro message at `S - 464`. -/
structure IntroR (s : MachineState) (x : LCtx) (h t u v w r : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q : List E) (d : Digest) : Prop where
  ov : OodV s x h t u v w ℓ Wl lf q d
  pc : r.pc = 0x8000a698
  sp : r.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s r (r.getMem nextAddr)
  heap : HeapOk r
  mono : heapNext w ≤ heapNext r
  fr : DFrame w r fun a ↦ Within a (s.getReg .x2 - 584) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
    Within a (s.getReg .x2 - 384) 8 ∨ Within a (s.getReg .x10 + 8) 344 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh w r a
  regs : ∀ r' ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25],
    r.getReg r' = w.getReg r'
  x1 : r.getReg .x1 = vecPtr r (s.getReg .x2 - 464)
  x26 : r.getReg .x26 = vecLen r (s.getReg .x2 - 464)
  x27 : r.getReg .x27 = vecCap r (s.getReg .x2 - 464)
  intro : VecOk r (s.getReg .x2 - 464) 24 8 ∧
    NewBuf w r (vecPtr r (s.getReg .x2 - 464)) ((vecCap r (s.getReg .x2 - 464)).toNat * 24) 8
  dig : digestAt r (s.getReg .x11) = digestAt w (s.getReg .x11)
  value : RunsC s r ℓ
    (Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (fcOf s ℓ)
      (rtOf s ℓ) (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf
      ([], [(vecEs r (s.getReg .x2 - 464),
        Model.Pcs.GluedWeightRust.ood (vecEs v (s.getReg .x2 - 560)))]))
    [(d, rootShape s (ℓ + 1))]

/-- **`0x8000a654`**: the intro message read, or an `Err`. -/
theorem oodIntro (hRP : RoundPolyErrSpec) {s : MachineState} {x : LCtx}
    {h t u v w : MachineState} {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q : List E} {d : Digest}
    (hpre : VsoPre s) (hw : OodV s x h t u v w ℓ Wl lf q d) :
    ∃ r, Reaches Image.code w r ∧ (FailR s r ∨ IntroR s x h t u v w r ℓ Wl lf q d) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hrs := hpre.rootSponge
  have hsp := hw.sp
  have nxw : w.getMem nextAddr = v.getMem nextAddr := hw.fr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx
    · addr_omega [hx, hi, hb, hnx]
    · addr_omega [hx, hi, hS, hI.free.2]
    · addr_omega [hx, hi, hb, hnx]
  have hnw : heapNext w = heapNext v := by simp only [heapNext, nxw]
  have hheapw : HeapOk w := ⟨by have := hw.cs.heap.lo; omega, by have := hw.cs.heap.hi; omega⟩
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a654_spec hw.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000a654_keeps h₁
  have st (o : ℕ) (val : Word) (e : t₁.getMem (w.getReg .x2 + BitVec.ofNat 64 o) = val) (a : Word)
      (ha : a = w.getReg .x2 + BitVec.ofNat 64 o) : t₁.getMem a = val := by rw [ha]; exact e
  have X₁ : DFrame w t₁ fun a ↦ Within a (s.getReg .x2 - 584) 24 ∨
      Within a (s.getReg .x2 - 384) 8 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw'⟩ ↦ by
      simp only [b8000a654, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rv_eval [hsp] at hw' <;> first
        | exact Or.inl (by addr_omega [hw', hb])
        | exact Or.inr (by addr_omega [hw', hb])
  obtain ⟨nx₁, inv₁⟩ := InvR.stk hpre hw.inv X₁ (fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb]) (k₁ .x2 (by decide))
  have hn₁ : heapNext t₁ = heapNext w := by simp only [heapNext, nx₁]
  have hheap₁ : HeapOk t₁ := ⟨by have := hheapw.lo; omega, by have := hheapw.hi; omega⟩
  have m0 : t₁.getMem (s.getReg .x2 - 384) = 0 :=
    st 656 _ (b8000a654_m_x2_656 h₁) _ (by addr_omega [hb, hsp])
  have hcl : eAt t₁ (s.getReg .x2 - 584) = eAt w (s.getReg .x2 - 376) := by
    have a0 : s.getReg .x2 - 584 = w.getReg .x2 + 456 := by addr_omega [hb, hsp]
    have a1 : s.getReg .x2 - 584 + 8 = w.getReg .x2 + 464 := by addr_omega [hb, hsp]
    have a2 : s.getReg .x2 - 584 + 16 = w.getReg .x2 + 472 := by addr_omega [hb, hsp]
    have b1 : s.getReg .x2 - 376 + 8 = s.getReg .x2 - 368 := by addr_omega [hb]
    have b2 : s.getReg .x2 - 376 + 16 = w.getReg .x2 + 680 := by addr_omega [hb, hsp]
    refine eAt_congr ?_ ?_ ?_
    · rw [a0, b8000a654_m_x2_456 h₁, hw.x1]
    · rw [a1, b8000a654_m_x2_464 h₁, hw.x26, b1]
    · rw [a2, b8000a654_m_x2_472 h₁, b2]
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans hsp
  obtain ⟨t₂, hr₂, hv₂⟩ := callRoundPoly (o := s.getReg .x2 - 464) (cl := s.getReg .x2 - 584) hRP
    hpre inv₁ hheap₁ (b8000a654_pc h₁) (by rw [b8000a654_x10 h₁, hsp]; addr_omega [hb])
    (by rw [b8000a654_x11 h₁, hw.regs .x27 (by decide), hw.cs.x27]) (b8000a654_x12 h₁)
    (by rw [b8000a654_x13 h₁, hsp]; addr_omega [hb]) (by rw [b8000a654_x14 h₁, hsp]; addr_omega [hb])
    m0 (by addr_omega [hb]) (by addr_omega [hb])
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, herr₂, hok₂, hval₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (Or.inl hd)⟩
  have inv₂ := InvR.callT hpre inv₁ X₂ (by simp only [Slot24]; addr_omega [hb]) hheap₂ hmono₂
    (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := (hpres₂ .x2 (by decide)).trans sp₁
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a684_spec
    (by rw [hpc₂, returnAddress_eq, b8000a654_x1 h₁]; decide) (by
      rv_eval [sp₂]
      and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000a684_keeps h₃
  have hm₃ := b8000a684_mem_same h₃
  have inv₃ : InvR s t₃ (t₃.getMem nextAddr) := by
    rw [hm₃]; exact Inv.same' inv₂ hm₃ (k₃ .x2 (by decide))
  have e576 : t₂.getReg .x2 + 576 = s.getReg .x2 - 464 := by addr_omega [hb, sp₂]
  have e584 : t₂.getReg .x2 + 584 = s.getReg .x2 - 464 + 8 := by addr_omega [hb, sp₂]
  have e592 : t₂.getReg .x2 + 592 = s.getReg .x2 - 464 + 16 := by addr_omega [hb, sp₂]
  have x8₂ : t₂.getReg .x8 = 0xffffffffffffffff := by
    rw [hpres₂ .x8 (by decide), k₁ .x8 (by decide), hw.regs .x8 (by decide), hw.cs.x8]
  by_cases herr : vecCap t₂ (s.getReg .x2 - 464) = errNiche
  · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a694_spec
      (b8000a684_pc_not_taken h₃ (by rw [e576, x8₂]; exact herr)) trivial
    have inv₄ : InvR s t₄ (t₃.getMem nextAddr) :=
      Inv.same' inv₃ (b8000a694_mem_same h₄) (b8000a694_keeps h₄ .x2 (by decide))
    obtain ⟨r, hr, hfr⟩ := fail844 inv₄ (b8000a694_pc h₄) (by
      rw [b8000a694_keeps h₄ .x1 (by decide), b8000a684_x1 h₃, e584]; exact herr₂ herr)
    exact ⟨r, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr))), Or.inl hfr⟩
  obtain ⟨hvo, hnb⟩ := hok₂ herr
  have hn₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, hm₃]
  have hhi₂ := hheap₂.hi
  have X : DFrame w t₃ fun a ↦ Within a (s.getReg .x2 - 584) 24 ∨
      Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x2 - 384) 8 ∨
      Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
      Within a nextAddr 8 ∨ Fresh w t₃ a :=
    ((X₁.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl ha))).trans X₂ fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))).trans
      (DFrame.of_same hm₃ _) fun _ h ↦ h
  have hdig : digestAt t₃ (s.getReg .x11) = digestAt w (s.getReg .x11) :=
    digest_keep X (root_bound hpre) fun y hy hx ↦ by
      rcases hx with hx | hx | hx | hx | hx | hx | hx
      · addr_omega [hy, hx, hrst, hb]
      · addr_omega [hy, hx, hrst, hb]
      · addr_omega [hy, hx, hrst, hb]
      · addr_omega [hy, hx, hrs]
      · addr_omega [hy, hx, hrst, hb]
      · addr_omega [hy, hx, hrf.2]
      · simp only [Fresh] at hx
        have hsw : heapNext s ≤ heapNext w := hw.inv.mono
        rcases hrf.1 with h1 | h1
        · addr_omega [hy, hx.1, h1, hsw]
        · addr_omega [hy, hx.2, h1, hhi₂, hn₃]
  have V₁ := hw.value.keep hpre hw.inv X₁ (fun a ha ↦ Or.inl (by
      rcases ha with ha | ha <;> addr_omega [ha, hb]))
    fun y hy hx ↦ by rcases hx with hx | hx <;> addr_omega [hy, hx, hrst, hb]
  rw [← hcl] at V₁
  have V₂ := V₁.bind (v := t₃) (nx' := []) (vecEs t₃ (s.getReg .x2 - 464))
    (hdig.trans (digest_keep X₁ (root_bound hpre) fun y hy hx ↦ by
      rcases hx with hx | hx <;> addr_omega [hy, hx, hrst, hb]).symm) fun T hT ↦ by
      have hval := hval₂ T hT
      cases hrun : (Model.TM.sumcheckRoundPoly 3 (eAt t₁ (s.getReg .x2 - 584)) none).run T with
      | none => rw [hrun] at hval; exact absurd hval herr
      | some p =>
        obtain ⟨qv, T'⟩ := p
        rw [hrun] at hval
        obtain ⟨-, hnew, hT'⟩ := hval
        have hk := Model.Pcs.Keeps.roundPoly _ _ _ T qv T' hrun
        refine ⟨T', ?_, tr_keep hpre inv₂ hT' (DFrame.of_same hm₃ fun _ ↦ False) fun _ h ↦ h.elim,
          hk.1, hk.2.2, by rw [hk.2.1, List.append_nil]⟩
        have e : qv = vecEs t₃ (s.getReg .x2 - 464) := by
          rw [← hnew.elems]
          simp only [vecEs, vecPtr, vecLen, hm₃]
          exact ((DFrame.of_same hm₃ fun _ ↦ False).eListAt fun _ _ h ↦ h).symm
        exact congrArg (fun z ↦ some (z, T')) e
  rw [List.append_nil] at V₂
  simp only [NewBuf] at hnb
  have hraw₃ : RawVecOk t₃ (s.getReg .x2 - 464) 24 8 := by
    have := hvo.raw
    simp only [RawVecOk, Buf, vecPtr, vecCap, heapNext, hm₃] at this ⊢
    exact this
  have hlen₃ : (vecLen t₃ (s.getReg .x2 - 464)).toNat ≤ (vecCap t₃ (s.getReg .x2 - 464)).toNat := by
    simp only [vecLen, vecCap, hm₃]; exact hvo.len
  have hnb₃ : NewBuf w t₃ (vecPtr t₃ (s.getReg .x2 - 464))
      ((vecCap t₃ (s.getReg .x2 - 464)).toNat * 24) 8 := by
    have ep : vecPtr t₃ (s.getReg .x2 - 464) = vecPtr t₂ (s.getReg .x2 - 464) := by
      simp only [vecPtr, hm₃]
    have ec : vecCap t₃ (s.getReg .x2 - 464) = vecCap t₂ (s.getReg .x2 - 464) := by
      simp only [vecCap, hm₃]
    rw [ep, ec]
    simp only [NewBuf]
    refine ⟨hnb.1, ?_⟩
    rcases hnb.2 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, by omega⟩
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr {
    ov := hw
    pc := b8000a684_pc_taken h₃ (by rw [e576, x8₂]; exact herr)
    sp := by rw [k₃ .x2 (by decide), sp₂]
    inv := inv₃
    heap := ⟨by have := hheap₂.lo; omega, by omega⟩
    mono := by omega
    fr := X
    regs := fun r' hr' ↦ by
      rw [k₃ r' (mem_of_mem hr' _), hpres₂ r' (by simp only [calleeSaved]; exact mem_of_mem hr' _),
        k₁ r' (mem_of_mem hr' _)]
    x1 := by rw [b8000a684_x1 h₃, e584]; simp only [vecPtr, hm₃]
    x26 := by rw [b8000a684_x26 h₃, e592]; simp only [vecLen, hm₃]
    x27 := by rw [b8000a684_x27 h₃, e576]; simp only [vecCap, hm₃]
    intro := ⟨⟨hraw₃, hlen₃⟩, hnb₃⟩
    dig := hdig
    value := V₂ }⟩

end Rv64Verifier.Proofs.Pcs.Vso
