import Rv64Verifier.Proofs.Pcs.VsoOpenCommitB

/-!
# `verify_stacked_opening`'s level loop: the out-of-domain point

`0x8000a588` copies the halves to `S - 384` and the root's bytes to the frame (`B58`, the first
seven to `S - 592`), then `samples(S - 560, ml)` draws the out-of-domain point (`CommitS`, at
`0x8000a630`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A transcript the machine's stands for. -/
theorem exists_TA (s : MachineState) (p : Word) : ∃ T, TranscriptAt s p T :=
  ⟨⟨⟨eListAt s (streamPtr s p) (streamLen s p), []⟩, spongeAt s (p + 8),
    (s.getMem (p + 344)).toNat, (s.getMem (p + 352)).toNat, []⟩, rfl, rfl, rfl, rfl⟩

/-- At `0x8000a630`, from `u` at `0x8000a534`: the next root `d` in the frame, the
out-of-domain point at `S - 560`. -/
structure CommitS (s : MachineState) (x : LCtx) (h t u v : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q : List E) (d : Digest) : Prop where
  at304 : At304 s x h t u ℓ Wl lf q
  pc : v.pc = 0x8000a630
  sp : v.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s v (v.getMem nextAddr)
  heap : HeapOk v
  mono : heapNext t ≤ heapNext v
  fr : DFrame u v fun a ↦ (Within a (s.getReg .x2 - 1008) 72 ∨ Within a (s.getReg .x2 - 920) 8) ∨
    Within a (s.getReg .x2 - 592) 8 ∨
    Within a (s.getReg .x2 - 560) 24 ∨ Within a (s.getReg .x2 - 384) 24 ∨
    Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a nextAddr 8 ∨ (heapNext t ≤ a.toNat ∧ a.toNat < heapNext v)
  bytes : B58 v (s.getReg .x2 - 1040) d[0].toBitVec d[1].toBitVec d[2].toBitVec d[3].toBitVec
  low : v.getMem (s.getReg .x2 - 592) &&& 0x00ffffffffffffff = d[0].toBitVec &&& 0x00ffffffffffffff
  x8 : v.getReg .x8 = 0xffffffffffffffff
  x9 : v.getReg .x9 = x.FP
  x27 : v.getReg .x27 = s.getReg .x10
  pt : VecOk v (s.getReg .x2 - 560) 24 8 ∧
    NewBuf t v (vecPtr v (s.getReg .x2 - 560)) ((vecCap v (s.getReg .x2 - 560)).toNat * 24) 8
  dig : digestAt v (s.getReg .x11) = digestAt u (s.getReg .x11)
  value : RunsC s v ℓ
    (Model.TM.nextScalar >>= fun val ↦ Model.TM.sumcheckRoundPoly 3 val none >>= fun i ↦
      Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (fcOf s ℓ)
        (rtOf s ℓ) (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf
        ([], [(i, Model.Pcs.GluedWeightRust.ood (vecEs v (s.getReg .x2 - 560)))]))
    [(d, rootShape s (ℓ + 1))]

/-- **`0x8000a588`**: the root's bytes kept, `samples(ml)` drawn. -/
theorem oodPoint (hSm : SamplesSpec) {s : MachineState} {x : LCtx} {h t u w : MachineState}
    {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q : List E} {p : Word} (hpre : VsoPre s)
    (hw : CommitH s x h t u w ℓ Wl lf q p) :
    ∃ v, Reaches Image.code w v ∧ (Dead Image.code v ∨ CommitS s x h t u v ℓ Wl lf q (dOf w p)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hsm := stack_mapped hpre
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hrs := hpre.rootSponge
  have hsp := hw.sp
  have hbuf := hw.buf
  have hhi := hw.heap.hi
  have hRP : Region p 48 := heap_region (by have := hw.at304.fo.heap.lo; simp only [heapStart] at this; omega)
    (le_trans hbuf.2.2 hhi) hbuf.1
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a588_spec hw.pc (by
    rv_eval [hsp, hw.x1]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRP (by addr_omega [hbuf]) (by addr_omega [hbuf]) (by addr_omega [hbuf])
      | (refine validAccess_one ?_; addr_omega [hsm, hb])
      | exact stack_valid hpre (Or.inl rfl) (by addr_omega [hb]) (by addr_omega [hb])
          (by addr_omega [hb])
      | exact stack_valid hpre (Or.inr rfl) (by addr_omega [hb]) (by addr_omega [hb])
          (by addr_omega [hb])
      | addr_omega [hbuf, hb, hhi])
  have k₁ := b8000a588_keeps h₁
  have X₁ : DFrame w t₁ fun a ↦ (Within a (s.getReg .x2 - 1008) 72 ∨
      Within a (s.getReg .x2 - 920) 8) ∨ Within a (s.getReg .x2 - 592) 8 ∨
      Within a (s.getReg .x2 - 384) 24 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw'⟩ ↦ by
      simp only [b8000a588, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> rv_eval [hsp] at hw' <;> first
        | exact Or.inl (Or.inl (by addr_omega [hw', hb]))
        | exact Or.inl (Or.inr (by addr_omega [hw', hb]))
        | exact Or.inr (Or.inl (by addr_omega [hw', hb]))
        | exact Or.inr (Or.inr (by addr_omega [hw', hb]))
  have hsp₁ : t₁.getReg .x2 = w.getReg .x2 := k₁ .x2 (by decide)
  obtain ⟨nx₁, inv₁⟩ := InvR.stk hpre hw.inv X₁ (fun a ha ↦ by
    rcases ha with (ha | ha) | ha | ha <;> addr_omega [ha, hb]) hsp₁
  -- the root's words
  have B₁ := b58_of h₁
  have hd := dOf_get w p
  have e8 : w.getMem (p + 8#64) = (dOf w p)[1].toBitVec := hd.2.1.symm
  have e24 : w.getMem (p + 24#64) = (dOf w p)[2].toBitVec := hd.2.2.1.symm
  have e32 : w.getMem (p + 32#64) = (dOf w p)[3].toBitVec := by
    rw [hd.2.2.2]; congr 1; addr_omega [hbuf]
  rw [hw.x1, hsp, ← hd.1, e8, e24, e32] at B₁
  have hlow : t₁.getMem (s.getReg .x2 - 592) &&& 0x00ffffffffffffff =
      (dOf w p)[0].toBitVec &&& 0x00ffffffffffffff := by
    have e : t₁.getMem (w.getReg .x2 + 448) = _ := h₁.mem_eq 0 (by decide) (by rv_eval []) rfl
    simp only [reduceMem, List.getElem_cons_zero, Sym.E.eval, Sym.BinOp.eval, Sym.UnOp.eval,
      Sym.LoadKind.fromWord] at e
    rw [show s.getReg .x2 - 592 = w.getReg .x2 + 448 by addr_omega [hb, hsp], e, hw.x1, hd.1]
    exact low7b _ _
  -- `samples(ml)`
  have hn₁ : heapNext t₁ = heapNext w := by simp only [heapNext, nx₁]
  have hheap₁ : HeapOk t₁ := ⟨by have := hw.heap.lo; omega, by omega⟩
  have hml : (s.getReg .x12).toNat - (Wl.folds ++ lf).length < 2 ^ 64 := by
    have := (s.getReg .x12).isLt; omega
  have x12₁ : (t₁.getReg .x12).toNat = (s.getReg .x12).toNat - (Wl.folds ++ lf).length := by
    rw [k₁ .x12 (by decide), hw.x12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hml]
  obtain ⟨v, hr₂, hv₂⟩ := callSamples (o := s.getReg .x2 - 560) hSm hpre inv₁ hheap₁
    (b8000a588_pc h₁) (by rw [b8000a588_x10 h₁, hsp]; addr_omega [hb])
    (by rw [b8000a588_x11 h₁, hw.x27]) (by simp only [Slot24]; addr_omega [hb])
  rcases hv₂ with hdd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, hval₂⟩
  · exact ⟨v, hr₁.trans hr₂, Or.inl hdd⟩
  have inv₂ := InvR.callT hpre inv₁ X₂ (by simp only [Slot24]; addr_omega [hb]) hheap₂ hmono₂
    (hpres₂ .x2 (by decide))
  have hhi₂ := hheap₂.hi
  have hmiss (a : Word) (ha : Within a (s.getReg .x2 - 560) 24 ∨
      Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
      Within a nextAddr 8 ∨ Fresh t₁ v a) : ¬ Within a (s.getReg .x2 - 1040 + 32) 96 := by
    rcases ha with ha | ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hIs, hS]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · simp only [Fresh] at ha; addr_omega [ha.2, hb, hhi₂]
  -- the point
  obtain ⟨T₀, hT₀⟩ := exists_TA t₁ (s.getReg .x10)
  obtain ⟨xs₀, T₀', -, hnew₀, -⟩ := hval₂ T₀ hT₀
  have hd₁ : digestAt t₁ (s.getReg .x11) = digestAt w (s.getReg .x11) :=
    digest_keep X₁ (root_bound hpre) fun y hy hw' ↦ by
      rcases hw' with (hw' | hw') | hw' | hw' <;> addr_omega [hy, hw', hrst, hb]
  have hd₂ : digestAt v (s.getReg .x11) = digestAt t₁ (s.getReg .x11) := by
    exact digest_keep X₂ (root_bound hpre) fun y hy hw' ↦ by
      rcases hw' with hw' | hw' | hw' | hw' | hw'
      · addr_omega [hy, hw', hrst, hb]
      · addr_omega [hy, hw', hrs]
      · addr_omega [hy, hw', hrst, hb]
      · addr_omega [hy, hw', hrf.2]
      · simp only [Fresh] at hw'
        have hs₁ : heapNext s ≤ heapNext t₁ := inv₁.mono
        rcases hrf.1 with h1 | h1
        · addr_omega [hy, hw'.1, h1, hs₁]
        · addr_omega [hy, hw'.2, h1, hhi₂]
  have V₁ := hw.value.keep hpre hw.inv X₁ (fun a ha ↦ Or.inl (by
      rcases ha with (ha | ha) | ha | ha <;> addr_omega [ha, hb]))
    fun y hy hw' ↦ by rcases hw' with (hw' | hw') | hw' | hw' <;> addr_omega [hy, hw', hrst, hb]
  have V₂ := V₁.bind (v := v) (nx' := []) (vecEs v (s.getReg .x2 - 560)) hd₂
    fun T hT ↦ by
      obtain ⟨xs, T', hrun, hnew, hT'⟩ := hval₂ T hT
      rw [x12₁] at hrun
      have hk := Model.Pcs.Keeps.samples _ T xs T' hrun
      exact ⟨T', by rw [hrun, hnew.elems], hT', hk.1, hk.2.2, by rw [hk.2.1, List.append_nil]⟩
  rw [List.append_nil] at V₂
  have hmo := hw.mono
  have hnb₀ := hnew₀.buf
  simp only [NewBuf] at hnb₀
  refine ⟨v, hr₁.trans hr₂, Or.inr {
    at304 := hw.at304
    pc := by rw [hpc₂, returnAddress_eq, b8000a588_x1 h₁]; decide
    sp := by rw [hpres₂ .x2 (by decide), hsp₁, hsp]
    inv := inv₂
    heap := hheap₂
    mono := by omega
    fr := ((hw.fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha.1, by omega⟩))))))).trans
      X₁ fun a ha ↦ by
        rcases ha with ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))).trans X₂ fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))))))
    bytes := B₁.keep (fun r hr' ↦ hpres₂ r (by simp only [calleeSaved]; exact mem_of_mem hr' _))
      X₂ hmiss (by addr_omega [hb])
    low := by
      rw [X₂ _ fun i hi hw' ↦ by
        rcases hw' with hw' | hw' | hw' | hw' | hw'
        · addr_omega [hw', hi, hb]
        · addr_omega [hw', hi, hb, hIs, hS]
        · addr_omega [hw', hi, hb]
        · addr_omega [hw', hi, hb, hnx]
        · simp only [Fresh] at hw'; addr_omega [hw'.2, hi, hb, hhi₂]]
      exact hlow
    x8 := by rw [hpres₂ .x8 (by decide), k₁ .x8 (by decide), hw.x8]
    x9 := by rw [hpres₂ .x9 (by decide), k₁ .x9 (by decide), hw.x9]
    x27 := by rw [hpres₂ .x27 (by decide), k₁ .x27 (by decide), hw.x27]
    pt := ⟨hnew₀.vec, by
      simp only [NewBuf]
      refine ⟨hnb₀.1, ?_⟩
      rcases hnb₀.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, h0.2⟩⟩
    dig := hd₂.trans (hd₁.trans hw.dig)
    value := V₂ }⟩

end Rv64Verifier.Proofs.Pcs.Vso
