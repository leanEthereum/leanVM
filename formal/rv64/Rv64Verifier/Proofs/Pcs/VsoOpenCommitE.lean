import Rv64Verifier.Proofs.Pcs.VsoOpenCommitD

/-!
# `verify_stacked_opening`'s level loop: the pending claim pushed

`0x8000a698` reassembles the next root's doublewords in the frame and calls `grow_one` on the
pending claims' empty `Vec` at `S - 616` (`growPend`); `0x8000a754` pushes the intro message and the
out-of-domain weight and goes on at `0x8000a790` (`pushPend`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000a754`, from `IntroR` at `r`: the pending claims' `Vec` grown, still empty. -/
structure Grown (s : MachineState) (x : LCtx) (h t u v w r g : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q : List E) (d : Digest) : Prop where
  ir : IntroR s x h t u v w r ℓ Wl lf q d
  pc : g.pc = 0x8000a754
  sp : g.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s g (g.getMem nextAddr)
  heap : HeapOk g
  mono : heapNext r ≤ heapNext g
  fr : DFrame r g fun a ↦ Within a (s.getReg .x2 - 952) 24 ∨ Within a (s.getReg .x2 - 920) 8 ∨
    Within a (s.getReg .x2 - 616) 16 ∨ Within a (s.getReg .x2 - 1200) 160 ∨
    Within a nextAddr 8 ∨ Fresh r g a
  x8 : g.getReg .x8 = 0xffffffffffffffff
  x9 : g.getReg .x9 = x.FP
  x20 : g.getReg .x20 = vecPtr r (s.getReg .x2 - 464)
  x26 : g.getReg .x26 = vecLen r (s.getReg .x2 - 464)
  x27 : g.getReg .x27 = vecCap r (s.getReg .x2 - 464)
  root : NR g (s.getReg .x2) d
  len : vecLen g (s.getReg .x2 - 616) = 0
  cap : 1 ≤ (vecCap g (s.getReg .x2 - 616)).toNat
  buf : NewBuf r g (vecPtr g (s.getReg .x2 - 616)) ((vecCap g (s.getReg .x2 - 616)).toNat * 80) 8
  value : RunsC s g ℓ
    (Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (fcOf s ℓ)
      (rtOf s ℓ) (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf
      ([], [(vecEs r (s.getReg .x2 - 464),
        Model.Pcs.GluedWeightRust.ood (vecEs v (s.getReg .x2 - 560)))]))
    [(d, rootShape s (ℓ + 1))]

/-- What `IntroR` keeps since `u` and `v`: the slots `At304` set, the root's bytes, the low
doubleword of the next root. -/
theorem IntroR.keeps {s : MachineState} {x : LCtx} {h t u v w r : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} {d : Digest} (hpre : VsoPre s)
    (hr : IntroR s x h t u v w r ℓ Wl lf q d) :
    (∀ y : Word, (s.getReg .x2 - 928).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 920).toNat ∨ (s.getReg .x2 - 912).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 592).toNat → r.getMem y = u.getMem y) ∧
    B58 r (s.getReg .x2 - 1040) d[0].toBitVec d[1].toBitVec d[2].toBitVec d[3].toBitVec ∧
    r.getMem (s.getReg .x2 - 592) = v.getMem (s.getReg .x2 - 592) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hw := hr.ov
  have hv := hw.cs
  have hhir := hr.heap.hi
  have hhv := hv.heap.hi
  have hP : (s.getReg .x2 - 1040).toNat + 128 ≤ 2 ^ 64 := by addr_omega [hb]
  have Bw := hv.bytes.keep (fun r' hr' ↦ hw.regs r' (mem_of_mem hr' _)) hw.fr (fun a ha ↦ by
      rcases ha with ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hS, hIs]
      · addr_omega [ha, hb]) hP
  refine ⟨fun y hy ↦ ?_, Bw.keep (fun r' hr' ↦ hr.regs r' (mem_of_mem hr' _)) hr.fr (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hS, hIs]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx]
      · simp only [Fresh] at ha; addr_omega [ha.2, hb, hhir]) hP, ?_⟩
  · exact (hr.fr y fun i hi hx ↦ by
        rcases hx with hx | hx | hx | hx | hx | hx | hx
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb, hS, hIs]
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb, hnx]
        · simp only [Fresh] at hx; addr_omega [hx.2, hi, hy, hb, hhir]).trans
      ((hw.fr y fun i hi hx ↦ by
        rcases hx with hx | hx | hx
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb, hS, hIs]
        · addr_omega [hx, hi, hy, hb]).trans
      (hv.fr y fun i hi hx ↦ by
        rcases hx with (hx | hx) | hx | hx | hx | hx | hx | hx | hx
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb, hS, hIs]
        · addr_omega [hx, hi, hy, hb]
        · addr_omega [hx, hi, hy, hb, hnx]
        · addr_omega [hx.2, hi, hy, hb, hhv]))
  · exact (hr.fr _ fun i hi hx ↦ by
        rcases hx with hx | hx | hx | hx | hx | hx | hx
        · addr_omega [hx, hi, hb]
        · addr_omega [hx, hi, hb]
        · addr_omega [hx, hi, hb]
        · addr_omega [hx, hi, hb, hS, hIs]
        · addr_omega [hx, hi, hb]
        · addr_omega [hx, hi, hb, hnx]
        · simp only [Fresh] at hx; addr_omega [hx.2, hi, hb, hhir]).trans
      (hw.fr _ fun i hi hx ↦ by
        rcases hx with hx | hx | hx
        · addr_omega [hx, hi, hb]
        · addr_omega [hx, hi, hb, hS, hIs]
        · addr_omega [hx, hi, hb])

/-- **`0x8000a698`**: the next root's doublewords, the pending claims' `Vec` grown. -/
theorem growPend (hG : GrowOneFreshSpec 0x8000c7d0 80 8) {s : MachineState} {x : LCtx}
    {h t u v w r : MachineState} {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q : List E} {d : Digest}
    (hpre : VsoPre s) (hr : IntroR s x h t u v w r ℓ Wl lf q d) :
    ∃ g, Reaches Image.code r g ∧ (Dead Image.code g ∨ Grown s x h t u v w r g ℓ Wl lf q d) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hw := hr.ov
  have hv := hw.cs
  have ha := hv.at304
  have hsp := hr.sp
  have hhir := hr.heap.hi
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a698_spec hr.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000a698_keeps h₁
  have X₁ : DFrame r t₁ fun a ↦ Within a (s.getReg .x2 - 952) 24 ∨
      Within a (s.getReg .x2 - 920) 8 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw'⟩ ↦ by
      simp only [b8000a698, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rv_eval [hsp] at hw' <;> first
        | exact Or.inl (by addr_omega [hw', hb])
        | exact Or.inr (by addr_omega [hw', hb])
  obtain ⟨nx₁, inv₁⟩ := InvR.stk hpre hr.inv X₁ (fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb]) (k₁ .x2 (by decide))
  have hn₁ : heapNext t₁ = heapNext r := by simp only [heapNext, nx₁]
  have hheap₁ : HeapOk t₁ := ⟨by have := hr.heap.lo; omega, by omega⟩
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans hsp
  have hsr : heapNext s ≤ heapNext r := hr.inv.mono
  obtain ⟨hq₀, Br, lowr⟩ := hr.keeps hpre
  rw [← hsp] at Br
  obtain ⟨w96, w88, w120, w104⟩ := a698_words h₁ Br
  have hq (y : Word) (hy : (s.getReg .x2 - 928).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 920).toNat ∨ (s.getReg .x2 - 912).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 592).toNat) : t₁.getMem y = u.getMem y :=
    (X₁ y fun i hi hx ↦ by rcases hx with hx | hx <;> addr_omega [hx, hi, hy, hb]).trans (hq₀ y hy)
  have c0 : vecCap t₁ (s.getReg .x2 - 616) = 0 := by
    simp only [vecCap]; rw [hq _ (by addr_omega [hb]), ha.m424]
  have p8 : vecPtr t₁ (s.getReg .x2 - 616) = 8 := by
    have e : s.getReg .x2 - 616 + 8 = s.getReg .x2 - 608 := by addr_omega [hb]
    simp only [vecPtr]; rw [e, hq _ (by addr_omega [hb]), ha.m432]
  have l0 : vecLen t₁ (s.getReg .x2 - 616) = 0 := by
    have e : s.getReg .x2 - 616 + 16 = s.getReg .x2 - 600 := by addr_omega [hb]
    simp only [vecLen]; rw [e, hq _ (by addr_omega [hb]), ha.m440]
  -- `grow_one`
  obtain ⟨t₂, hr₂, hv₂⟩ := callGrow80 (A := s.getReg .x2 - 616) hG hpre inv₁ hheap₁ (b8000a698_pc h₁)
    (by rw [b8000a698_x10 h₁, hsp]; addr_omega [hb]) (by addr_omega [hb])
    ⟨by simp only [RawVecOk, Buf, p8, c0]; exact ⟨rfl, Or.inl rfl⟩, by rw [l0, c0]⟩
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, hl₂, hc₂, -, hnb₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have inv₂ := InvR.callT (o := s.getReg .x2 - 616) hpre inv₁ (X₂.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha))))
    (by simp only [Slot24]; addr_omega [hb]) hheap₂ hmono₂ (hpres₂ .x2 (by decide))
  have hhi₂ := hheap₂.hi
  have k₂ (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 616).toNat ∨ (s.getReg .x2 - 600).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2).toNat) : t₂.getMem y = t₁.getMem y :=
    X₂ y fun i hi hx ↦ by
      rcases hx with hx | hx | hx | hx
      · addr_omega [hx, hi, hy, hb]
      · addr_omega [hx, hi, hy, hb]
      · addr_omega [hx, hi, hy, hb, hnx]
      · simp only [Fresh] at hx; addr_omega [hx.2, hi, hy, hb, hhi₂]
  have e96 : s.getReg .x2 - 944 = r.getReg .x2 + 96 := by rw [hsp]; addr_omega [hb]
  have e88 : s.getReg .x2 - 952 = r.getReg .x2 + 88 := by rw [hsp]; addr_omega [hb]
  have e104 : s.getReg .x2 - 936 = r.getReg .x2 + 104 := by rw [hsp]; addr_omega [hb]
  have e120 : s.getReg .x2 - 920 = r.getReg .x2 + 120 := by rw [hsp]; addr_omega [hb]
  have V₁ := hr.value.keep hpre hr.inv X₁ (fun a ha ↦ Or.inl (by
      rcases ha with ha | ha <;> addr_omega [ha, hb]))
    fun y hy hx ↦ by rcases hx with hx | hx <;> addr_omega [hy, hx, hrst, hb]
  have V₂ := V₁.keep hpre inv₁ X₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    fun y hy hx ↦ by
      rcases hx with hx | hx | hx | hx
      · addr_omega [hy, hx, hrst, hb]
      · addr_omega [hy, hx, hrst, hb]
      · addr_omega [hy, hx, hrf.2]
      · simp only [Fresh] at hx
        rcases hrf.1 with h1 | h1
        · addr_omega [hy, hx.1, h1, hsr, hn₁]
        · addr_omega [hy, hx.2, h1, hhi₂]
  have hroot : NR t₂ (s.getReg .x2) d := ⟨by
        rw [k₂ _ (by addr_omega [hb]), X₁ _ fun i hi hx ↦ by
          rcases hx with hx | hx <;> addr_omega [hx, hi, hb], lowr]
        exact hv.low,
      by rw [k₂ _ (by addr_omega [hb]), e96, w96],
      by rw [k₂ _ (by addr_omega [hb]), e88, w88],
      by rw [k₂ _ (by addr_omega [hb]), e120, w120],
      by rw [k₂ _ (by addr_omega [hb]), e104, w104]⟩
  have hc0 : (vecCap t₁ (s.getReg .x2 - 616)).toNat = 0 := by rw [c0]; rfl
  refine ⟨t₂, hr₁.trans hr₂, Or.inr {
    ir := hr
    pc := by rw [hpc₂, returnAddress_eq, b8000a698_x1 h₁]; decide
    sp := (hpres₂ .x2 (by decide)).trans sp₁
    inv := inv₂
    heap := hheap₂
    mono := by omega
    fr := (X₁.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)).trans X₂ fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))))
    x8 := by
      rw [hpres₂ .x8 (by decide), k₁ .x8 (by decide), hr.regs .x8 (by decide),
        hw.regs .x8 (by decide), hv.x8]
    x9 := by
      rw [hpres₂ .x9 (by decide), k₁ .x9 (by decide), hr.regs .x9 (by decide),
        hw.regs .x9 (by decide), hv.x9]
    x20 := by rw [hpres₂ .x20 (by decide), b8000a698_x20 h₁, hr.x1]
    x26 := by rw [hpres₂ .x26 (by decide), k₁ .x26 (by decide), hr.x26]
    x27 := by rw [hpres₂ .x27 (by decide), k₁ .x27 (by decide), hr.x27]
    root := hroot
    len := by rw [hl₂, l0]
    cap := by omega
    buf := by simp only [NewBuf] at hnb₂ ⊢; rw [hn₁] at hnb₂; exact hnb₂
    value := V₂ }⟩

/-! ## What the opening writes, below the last level -/

theorem OW.i1 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 1032) 128) :
    OW s t u a := Or.inl h
theorem OW.i2 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 896) 8) :
    OW s t u a := Or.inr (Or.inl h)
theorem OW.i3 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 872) 8) :
    OW s t u a := Or.inr (Or.inr (Or.inl h))
theorem OW.i4 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 808) 8) :
    OW s t u a := Or.inr (Or.inr (Or.inr (Or.inl h)))
theorem OW.i5 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 792) 8) :
    OW s t u a := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem OW.i6 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 616) 88) :
    OW s t u a := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem OW.i7 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 464) 24) :
    OW s t u a := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
theorem OW.i8 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 384) 32) :
    OW s t u a := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
theorem OW.i9 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x2 - 2464) 1424) :
    OW s t u a := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
theorem OW.i10 {s t u : MachineState} {a : Word} (h : Within a nextAddr 8) : OW s t u a :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
theorem OW.i11 {s t u : MachineState} {a : Word} (h : Within a (s.getReg .x10 + 8) 344) :
    OW s t u a := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ?_))))))))))
  simp only [W, Within] at h ⊢; omega
theorem OW.i12 {s t u : MachineState} {a : Word} (h : Fresh t u a) : OW s t u a :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    h))))))))))

/-- The writes from the fold rounds' end `t` to the push's end `z`. -/
theorem owClose {s : MachineState} {x : LCtx} {h t u v w r g z : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} {d : Digest} {p : Word} (hpre : VsoPre s)
    (hg : Grown s x h t u v w r g ℓ Wl lf q d)
    (X₃ : DFrame g z fun a ↦ Within a (s.getReg .x2 - 600) 8 ∨ Within a p 56)
    (hp : heapNext r ≤ p.toNat ∧ p.toNat + 56 ≤ heapNext z) (hz : heapNext g ≤ heapNext z) :
    DFrame t z (OW s t z) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hr := hg.ir
  have hw := hr.ov
  have hv := hw.cs
  have ha := hv.at304
  have nxw : w.getMem nextAddr = v.getMem nextAddr := hw.fr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx
    · addr_omega [hx, hi, hb, hnx]
    · addr_omega [hx, hi, hS, hI.free.2]
    · addr_omega [hx, hi, hb, hnx]
  have hnw : heapNext w = heapNext v := by simp only [heapNext, nxw]
  have m1 := hv.mono
  have m2 := hr.mono
  have m3 := hg.mono
  refine (((((ha.fr.mono fun a ha ↦ ?_).trans hv.fr fun a ha ↦ ?_).trans hw.fr fun a ha ↦ ?_).trans
    hr.fr fun a ha ↦ ?_).trans hg.fr fun a ha ↦ ?_).trans X₃ fun a ha ↦ ?_
  · rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact OW.i1 (by addr_omega [ha, hb])
    · exact OW.i1 (by addr_omega [ha, hb])
    · exact OW.i2 ha
    · exact OW.i3 ha
    · exact OW.i4 ha
    · exact OW.i5 ha
    · exact OW.i6 (by addr_omega [ha, hb])
  · rcases ha with (ha | ha) | ha | ha | ha | ha | ha | ha | ha
    · exact OW.i1 (by addr_omega [ha, hb])
    · exact OW.i1 (by addr_omega [ha, hb])
    · exact OW.i6 (by addr_omega [ha, hb])
    · exact OW.i6 (by addr_omega [ha, hb])
    · exact OW.i8 (by addr_omega [ha, hb])
    · exact OW.i11 ha
    · exact OW.i9 ha
    · exact OW.i10 ha
    · exact OW.i12 ⟨ha.1, by omega⟩
  · rcases ha with ha | ha | ha
    · exact OW.i8 ha
    · exact OW.i11 ha
    · exact OW.i9 ha
  · rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact OW.i6 (by addr_omega [ha, hb])
    · exact OW.i7 ha
    · exact OW.i8 (by addr_omega [ha, hb])
    · exact OW.i11 ha
    · exact OW.i9 ha
    · exact OW.i10 ha
    · simp only [Fresh] at ha; exact OW.i12 ⟨by omega, by omega⟩
  · rcases ha with ha | ha | ha | ha | ha | ha
    · exact OW.i1 (by addr_omega [ha, hb])
    · exact OW.i1 (by addr_omega [ha, hb])
    · exact OW.i6 (by addr_omega [ha, hb])
    · exact OW.i9 (by addr_omega [ha, hb])
    · exact OW.i10 ha
    · simp only [Fresh] at ha; exact OW.i12 ⟨by omega, by omega⟩
  · rcases ha with ha | ha
    · exact OW.i6 (by addr_omega [ha, hb])
    · exact OW.i12 (by simp only [Fresh, Within] at ha ⊢; omega)

/-- `a`'s doublewords below `S - 600` or above `S - 592` in the stack, or the `n` bytes of a
buffer below `NEXT`, miss the push's writes. -/
theorem push_miss {s g : MachineState} {p a : Word} (hpre : VsoPre s) (hhi : heapNext g ≤ heapEnd)
    (hp : p.toNat + 56 ≤ heapNext g)
    (ha : (s.getReg .x2 - 2464).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2 - 600).toNat ∨
      (s.getReg .x2 - 592).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat ∨
      a.toNat + 8 ≤ p.toNat) :
    ∀ i < 8, ¬ (Within (a + BitVec.ofNat 64 i) (s.getReg .x2 - 600) 8 ∨
      Within (a + BitVec.ofNat 64 i) p 56) := by
  have hb := bounds hpre
  intro i hi hx
  rcases hx with hx | hx <;> addr_omega [hx, hi, ha, hb, hp, hhi]

/-- What `Grown` keeps: the slots `At304` set since `u`, the out-of-domain point's header since
`v`, and frames on the buffers allocated before `r` and `v`. -/
theorem Grown.keeps {s : MachineState} {x : LCtx} {h t u v w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} {d : Digest} (hpre : VsoPre s)
    (hg : Grown s x h t u v w r g ℓ Wl lf q d) :
    (∀ y : Word, (s.getReg .x2 - 928).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 920).toNat ∨ (s.getReg .x2 - 912).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 616).toNat → g.getMem y = u.getMem y) ∧
    (∀ y : Word, (s.getReg .x2 - 560).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 536).toNat →
      g.getMem y = v.getMem y) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hr := hg.ir
  have hw := hr.ov
  have hhi₂ := hg.heap.hi
  have hrhi := hr.heap.hi
  refine ⟨fun y hy ↦ (hg.fr y fun i hi hx ↦ ?_).trans ((hr.keeps hpre).1 y (by addr_omega [hy, hb])),
    fun y hy ↦ (hg.fr y fun i hi hx ↦ ?_).trans ((hr.fr y fun i hi hx ↦ ?_).trans
      (hw.fr y fun i hi hx ↦ ?_))⟩
  · rcases hx with hx | hx | hx | hx | hx | hx
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb, hnx]
    · simp only [Fresh] at hx; addr_omega [hx.2, hi, hy, hb, hhi₂]
  · rcases hx with hx | hx | hx | hx | hx | hx
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb, hnx]
    · simp only [Fresh] at hx; addr_omega [hx.2, hi, hy, hb, hhi₂]
  · rcases hx with hx | hx | hx | hx | hx | hx | hx
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb, hS, hIs]
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb, hnx]
    · simp only [Fresh] at hx; addr_omega [hx.2, hi, hy, hb, hrhi]
  · rcases hx with hx | hx | hx
    · addr_omega [hx, hi, hy, hb]
    · addr_omega [hx, hi, hy, hb, hS, hIs]
    · addr_omega [hx, hi, hy, hb]

/-- `Grown`'s writes since `r` and since `v`, coarsely. -/
theorem Grown.frames {s : MachineState} {x : LCtx} {h t u v w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} {d : Digest} (hpre : VsoPre s)
    (hg : Grown s x h t u v w r g ℓ Wl lf q d) :
    DFrame r g (fun a ↦ Within a (s.getReg .x2 - 2464) 2464 ∨ Within a nextAddr 8 ∨
      heapNext r ≤ a.toNat) ∧
    DFrame v g (fun a ↦ Within a (s.getReg .x2 - 2464) 2464 ∨
      Within a (s.getReg .x10 + 8) 344 ∨ Within a nextAddr 8 ∨ heapNext v ≤ a.toNat) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hr := hg.ir
  have hw := hr.ov
  have hv := hw.cs
  have nxw : w.getMem nextAddr = v.getMem nextAddr := hw.fr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx
    · addr_omega [hx, hi, hb, hnx]
    · addr_omega [hx, hi, hS, hI.free.2]
    · addr_omega [hx, hi, hb, hnx]
  have hnw : heapNext w = heapNext v := by simp only [heapNext, nxw]
  have m2 := hr.mono
  have Yr : DFrame r g fun a ↦ Within a (s.getReg .x2 - 2464) 2464 ∨ Within a nextAddr 8 ∨
      heapNext r ≤ a.toNat :=
    hg.fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh] at ha; exact Or.inr (Or.inr ha.1)
  refine ⟨Yr, ((hw.fr.mono fun a ha ↦ ?_).trans hr.fr fun a ha ↦ ?_).trans Yr fun a ha ↦ ?_⟩
  · rcases ha with ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl ha)
    · exact Or.inl (by addr_omega [ha, hb])
  · rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl ha)
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inr (Or.inl ha))
    · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inr (by omega)))
  · rcases ha with ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- **`0x8000a754`**: the pending claim pushed, at `0x8000a790`. -/
theorem pushPend {s : MachineState} {x : LCtx} {h t u v w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} {d : Digest} (hpre : VsoPre s)
    (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (hl : ℓ ≠ K0 s + 1) (hg : Grown s x h t u v w r g ℓ Wl lf q d) :
    ∃ z, Reaches Image.code g z ∧ Opened s x h t z ℓ Wl lf q []
      [(vecEs r (s.getReg .x2 - 464),
        Model.Pcs.GluedWeightRust.ood (vecEs v (s.getReg .x2 - 560)))] d := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hr := hg.ir
  have hw := hr.ov
  have hv := hw.cs
  have ha := hv.at304
  have hf := ha.fo
  have sp₂ := hg.sp
  have hhi₂ := hg.heap.hi
  have hc1 := hg.cap
  have hsr : heapNext s ≤ heapNext r := hr.inv.mono
  have hlo := hr.heap.lo
  have hrhi := hr.heap.hi
  have hhv := hv.heap.hi
  have m1 := hv.mono
  have m2 := hr.mono
  have m3 := hg.mono
  have nxw : w.getMem nextAddr = v.getMem nextAddr := hw.fr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx
    · addr_omega [hx, hi, hb, hnx]
    · addr_omega [hx, hi, hS, hI.free.2]
    · addr_omega [hx, hi, hb, hnx]
  have hnw : heapNext w = heapNext v := by simp only [heapNext, nxw]
  have hst₀ : heapNext s ≤ heapNext t := by
    have := hf.head.facts.hs; have := hf.head.facts.hL; have := hf.mono; omega
  obtain ⟨p, hp⟩ : ∃ p, vecPtr g (s.getReg .x2 - 616) = p := ⟨_, rfl⟩
  have hbuf := hg.buf
  rw [hp] at hbuf
  simp only [NewBuf] at hbuf
  obtain ⟨hp8, hpl, hph⟩ : p.toNat % 8 = 0 ∧ heapNext r ≤ p.toNat ∧
      p.toNat + (vecCap g (s.getReg .x2 - 616)).toNat * 80 ≤ heapNext g := by
    refine ⟨hbuf.1, ?_⟩
    rcases hbuf.2 with h0 | h0
    · omega
    · exact h0
  have hph' : p.toNat + 56 ≤ heapNext g := by omega
  have hRp : Region p 80 := heap_region (by simp only [heapStart] at hlo; omega) (by omega) hp8
  have hPP : g.getMem (s.getReg .x2 - 608) = p := by
    rw [← hp]; simp only [vecPtr]; rv_eval []
  obtain ⟨z, hrz, h₃⟩ := Sym.BlockSpec.reaches b8000a754_spec hg.pc (by
    rv_eval [sp₂, hPP]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRp (by addr_omega [hp8, hph, hhi₂, hc1])
          (by addr_omega [hp8, hph, hhi₂, hc1]) (by addr_omega [hp8, hph, hhi₂, hc1])
      | addr_omega [hb, hp8, hph, hhi₂, hc1])
  have k₃ := b8000a754_keeps h₃
  have X₃ : DFrame g z fun a ↦ Within a (s.getReg .x2 - 600) 8 ∨ Within a p 56 :=
    (holds_dframe h₃).mono fun a ⟨k, hk, hw'⟩ ↦ by
      simp only [b8000a754, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rv_eval [sp₂, hPP] at hw' <;> first
        | exact Or.inl (by addr_omega [hw', hb])
        | exact Or.inr (by addr_omega [hw', hp8, hph, hhi₂, hc1])
  have kz (a : Word) (ha' : (s.getReg .x2 - 2464).toNat ≤ a.toNat ∧
      a.toNat + 8 ≤ (s.getReg .x2 - 600).toNat ∨
      (s.getReg .x2 - 592).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat ∨
      a.toNat + 8 ≤ p.toNat) : z.getMem a = g.getMem a :=
    X₃ a (push_miss hpre hhi₂ hph' ha')
  have nx₃ : z.getMem nextAddr = g.getMem nextAddr := X₃ _ fun i hi hx ↦ by
    rcases hx with hx | hx
    · addr_omega [hx, hi, hb, hnx]
    · addr_omega [hx, hi, hph', hhi₂]
  have hnz : heapNext z = heapNext g := by simp only [heapNext, nx₃]
  have inv₃ : InvR s z (z.getMem nextAddr) := by
    rw [nx₃]
    exact Inv.step' hpre hg.inv X₃ (fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
        · refine Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hpl, hsr], ?_⟩))
          simp only [heapNext] at hph'
          addr_omega [ha, hph'])
      (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb, hph', hhi₂]) nx₃ (le_refl _)
      hg.inv.fits (k₃ .x2 (by decide))
  -- the element's words
  have e432 : g.getReg .x2 + 432 = s.getReg .x2 - 608 := by rw [sp₂]; addr_omega [hb]
  have e480 : g.getReg .x2 + 480 = s.getReg .x2 - 560 := by rw [sp₂]; addr_omega [hb]
  have e488 : g.getReg .x2 + 488 = s.getReg .x2 - 560 + 8 := by rw [sp₂]; addr_omega [hb]
  have e496 : g.getReg .x2 + 496 = s.getReg .x2 - 560 + 16 := by rw [sp₂]; addr_omega [hb]
  have e440 : g.getReg .x2 + 440 = s.getReg .x2 - 616 + 16 := by rw [sp₂]; addr_omega [hb]
  have n0 := b8000a754_m6 h₃
  have n8 := b8000a754_m5 h₃
  have n16 := b8000a754_m4 h₃
  have n24 := b8000a754_m3 h₃
  have n32 := b8000a754_m2 h₃
  have n40 := b8000a754_m1 h₃
  have n48 := b8000a754_m0 h₃
  have nl := b8000a754_m_x2_440 h₃
  rw [e432, hPP] at n0 n8 n16 n24 n32 n40 n48
  rw [e480] at n32
  rw [e488] at n40
  rw [e496] at n48
  rw [e440] at nl
  have hcz : vecCap z (s.getReg .x2 - 616) = vecCap g (s.getReg .x2 - 616) :=
    kz _ (Or.inl (by addr_omega [hb]))
  have hpz : vecPtr z (s.getReg .x2 - 616) = p := by
    rw [← hp]; exact kz _ (Or.inl (by addr_omega [hb]))
  have hlz : (vecLen z (s.getReg .x2 - 616)).toNat = 1 := by
    simp only [vecLen]; rw [nl]; rfl
  have hm24 : z.getMem (p + 24) = 0xffffffffffffffff := n24.trans hg.x8
  have a32 : p + 24 + 8 = p + 32 := by addr_omega [hp8, hph, hhi₂, hc1]
  have a40 : p + 32 + 8 = p + 40 := by addr_omega [hp8, hph, hhi₂, hc1]
  have a48 : p + 32 + 16 = p + 48 := by addr_omega [hp8, hph, hhi₂, hc1]
  have e0 : p + BitVec.ofNat 64 (80 * 0) = p := add_ofNat_zero p
  have iP : vecPtr z p = vecPtr r (s.getReg .x2 - 464) := n8.trans hg.x20
  have iL : vecLen z p = vecLen r (s.getReg .x2 - 464) := n16.trans hg.x26
  have iC : vecCap z p = vecCap r (s.getReg .x2 - 464) := n0.trans hg.x27
  obtain ⟨kU₀, hv560⟩ := hg.keeps hpre
  obtain ⟨Yr₀, Yv₀⟩ := hg.frames hpre
  have oC : vecCap z (p + 32) = vecCap v (s.getReg .x2 - 560) :=
    n32.trans (hv560 _ (by addr_omega [hb]))
  have oP : vecPtr z (p + 32) = vecPtr v (s.getReg .x2 - 560) := by
    simp only [vecPtr]; rw [a40, n40]; exact hv560 _ (by addr_omega [hb])
  have oL : vecLen z (p + 32) = vecLen v (s.getReg .x2 - 560) := by
    simp only [vecLen]; rw [a48, n48]; exact hv560 _ (by addr_omega [hb])
  have Yr : DFrame r z fun a ↦ Within a (s.getReg .x2 - 2464) 2464 ∨ Within a nextAddr 8 ∨
      heapNext r ≤ a.toNat := Yr₀.trans X₃ fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inr (by simp only [Within] at ha; omega))
  have Yv : DFrame v z fun a ↦ Within a (s.getReg .x2 - 2464) 2464 ∨
      Within a (s.getReg .x10 + 8) 344 ∨ Within a nextAddr 8 ∨ heapNext v ≤ a.toNat :=
    Yv₀.trans X₃ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inr (Or.inr (by simp only [Within] at ha; omega)))
  have hiv := hr.intro
  have hnbI := hiv.2
  simp only [NewBuf] at hnbI
  have hlI := hiv.1.len
  have hvE : vecEs z p = vecEs r (s.getReg .x2 - 464) := by
    simp only [vecEs]
    rw [iP, iL]
    exact Yr.eListAt fun i hi hx ↦ by
      rcases hnbI.2 with h0 | h0
      · omega
      · rcases hx with hx | hx | hx
        · addr_omega [hx, hi, h0, hlI, hb, hrhi]
        · addr_omega [hx, hi, h0, hlI, hrhi]
        · addr_omega [hx, hi, h0, hlI, hrhi]
  have hpv := hv.pt
  have hnbP := hpv.2
  simp only [NewBuf] at hnbP
  have hlP := hpv.1.len
  have hpE : vecEs z (p + 24 + 8) = vecEs v (s.getReg .x2 - 560) := by
    rw [a32]
    simp only [vecEs]
    rw [oP, oL]
    exact Yv.eListAt fun i hi hx ↦ by
      rcases hnbP.2 with h0 | h0
      · omega
      · rcases hx with hx | hx | hx | hx
        · addr_omega [hx, hi, h0, hlP, hb, hhv]
        · rcases hI.free.1 with h1 | h1
          · addr_omega [hx, hi, h0, hlP, h1, hst₀, hS]
          · addr_omega [hx, hi, h0, hlP, h1, hhv, hS]
        · addr_omega [hx, hi, h0, hlP, hhv]
        · addr_omega [hx, hi, h0, hlP, hhv]
  have kU (y : Word) (hy : (s.getReg .x2 - 928).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 920).toNat ∨ (s.getReg .x2 - 912).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 616).toNat) : z.getMem y = u.getMem y :=
    (kz y (Or.inl (by addr_omega [hy, hb]))).trans (kU₀ y hy)
  have hlen : (Wl.folds ++ lf).length = ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum := by
    rw [List.length_append, hnf, hf.lfl, take_succ_sum]; rfl
  have hle := folds_le hc hf.head.lvl
  rw [← hlen] at hle
  have V₃ := hg.value.keep hpre hg.inv X₃ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inr (Or.inl ⟨by addr_omega [ha, hpl, hsr],
          by addr_omega [ha, hph', hhi₂]⟩)))
    fun y hy hx ↦ by
      rcases hx with hx | hx
      · addr_omega [hy, hx, hrst, hb]
      · rcases hrf.1 with h1 | h1
        · addr_omega [hy, hx, h1, hpl, hsr]
        · addr_omega [hy, hx, h1, hph', hhi₂]
  have hnr : nextRoots s ℓ d = [(d, rootShape s (ℓ + 1))] := by
    rw [nextRoots, ite_eq_right_of_eq_false _ _ (eq_false hl)]
  rw [← hnr] at V₃
  have hR := hg.root
  refine ⟨z, hrz, {
    fo := hf
    fr := owClose hpre hg X₃ ⟨hpl, by omega⟩ (by omega)
    inv := inv₃
    heap := ⟨by have := hg.heap.lo; omega, by omega⟩
    mono := by omega
    pc := b8000a754_pc h₃
    sp := (k₃ .x2 (by decide)).trans sp₂
    x9 := (k₃ .x9 (by decide)).trans hg.x9
    m144 := by rw [kU _ (by addr_omega [hb]), ha.m144]
    m232 := by rw [kU _ (by addr_omega [hb]), ha.m232]
    m112 := by rw [kU _ (by addr_omega [hb]), ha.m112]
    m128 := by rw [kU _ (by addr_omega [hb]), ha.m128]
    m168 := by rw [kU _ (by addr_omega [hb]), ha.m168]; addr_omega [hle]
    m248 := by rw [kU _ (by addr_omega [hb]), ha.m248]
    rsd := by rw [b8000a754_x1 h₃, b8000a754_x31 h₃]; exact ⟨rfl, rfl, Or.inl rfl⟩
    rsdp := Or.inl (by rw [b8000a754_x31 h₃]; rfl)
    pnd := {
      vec := ⟨by
          simp only [RawVecOk, Buf]; rw [hpz, hcz]
          exact ⟨hp8, Or.inr ⟨by omega, by omega⟩⟩,
        by rw [hlz, hcz]; omega⟩
      elems := by
        rw [hpz, hlz]
        show [(vecEs z (p + BitVec.ofNat 64 (80 * 0)),
          weightAt z (p + BitVec.ofNat 64 (80 * 0) + 24))] = _
        rw [e0, hvE, weightAt, ite_eq_left_of_eq_true _ _ (eq_true hm24), hpE]
      intro := fun i hi ↦ by
        rw [hlz] at hi
        obtain rfl : i = 0 := by omega
        rw [hpz, e0]
        have hraw := hiv.1.raw
        simp only [RawVecOk, Buf] at hraw
        refine ⟨?_, by rw [iL, iC]; exact hlI⟩
        simp only [RawVecOk, Buf]
        rw [iP, iC]
        exact ⟨hraw.1, hraw.2.imp id fun h0 ↦ ⟨h0.1, by omega⟩⟩
      ood := fun i hi ↦ by
        rw [hlz] at hi
        obtain rfl : i = 0 := by omega
        rw [hpz, e0, a32]
        have hraw := hpv.1.raw
        simp only [RawVecOk, Buf] at hraw
        refine ⟨hm24, ?_, by rw [oL, oC]; exact hlP⟩
        simp only [RawVecOk, Buf]
        rw [oP, oC]
        exact ⟨hraw.1, hraw.2.imp id fun h0 ↦ ⟨h0.1, by omega⟩⟩
      fresh := fun y hy ↦ by
        rcases hy with hy | ⟨i, hi, hy⟩
        · rw [hpz, hcz] at hy
          simp only [Within] at hy
          omega
        · rw [hlz] at hi
          obtain rfl : i = 0 := by omega
          rw [hpz, e0] at hy
          rcases hy with hy | hy
          · rw [iP, iC] at hy
            simp only [Within] at hy
            rcases hnbI.2 with h0 | h0 <;> omega
          · rw [InBufs, ite_eq_left_of_eq_true _ _ (eq_true hm24), a32, oP, oL] at hy
            simp only [Within] at hy
            rcases hnbP.2 with h0 | h0 <;> omega
      self := fun i hi y hy ↦ by
        rw [hlz] at hi
        obtain rfl : i = 0 := by omega
        rw [hpz, e0] at hy
        rw [hpz, hcz]
        rcases hy with hy | hy
        · rw [iP, iC] at hy
          simp only [Within] at hy ⊢
          rcases hnbI.2 with h0 | h0 <;> omega
        · rw [InBufs, ite_eq_left_of_eq_true _ _ (eq_true hm24), a32, oP, oL] at hy
          simp only [Within] at hy ⊢
          rcases hnbP.2 with h0 | h0 <;> omega }
    root := ⟨by rw [kz _ (Or.inr (Or.inl (by addr_omega [hb])))]; exact hR.1,
      by rw [kz _ (Or.inl (by addr_omega [hb]))]; exact hR.2.1,
      by rw [kz _ (Or.inl (by addr_omega [hb]))]; exact hR.2.2.1,
      by rw [kz _ (Or.inl (by addr_omega [hb]))]; exact hR.2.2.2.1,
      by rw [kz _ (Or.inl (by addr_omega [hb]))]; exact hR.2.2.2.2⟩
    last := fun h' ↦ absurd h' hl
    rlen := fun h' ↦ absurd h' hl
    value := V₃ }⟩

/-- **A level's opening**, from the fold rounds' end `t` (`0x8000a304`) to `0x8000a790`, or an
`Err`, or a trap. -/
theorem openLevel (hNS : NextScalarsSpec) (hSm : SamplesSpec) (hN : NextScalarSpec)
    (hRP : RoundPolyErrSpec) (hG : GrowOneFreshSpec 0x8000c7d0 80 8) {s : MachineState} {x : LCtx}
    {h t : MachineState} {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hpre : VsoPre s)
    (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (hf : Folded s x h t ℓ Wl lf q) :
    ∃ v, Reaches Image.code t v ∧
      (FailR s v ∨ ∃ res pend d, Opened s x h t v ℓ Wl lf q res pend d) := by
  obtain ⟨u, hr₀, ha, hlast, hnl⟩ := open304 hpre hf
  by_cases hl : ℓ = K0 s + 1
  · obtain ⟨v, hr, hv⟩ := openLast hNS hpre hc hnf ha hl (hlast hl)
    rcases hv with hv | ⟨res, d, hv⟩
    · exact ⟨v, hr₀.trans hr, Or.inl hv⟩
    · exact ⟨v, hr₀.trans hr, Or.inr ⟨res, [], d, hv⟩⟩
  obtain ⟨w, hr₁, hw⟩ := commitRead hNS hpre hc hnf ha hl (hnl hl)
  rcases hw with hw | ⟨p, hw⟩
  · exact ⟨w, hr₀.trans hr₁, Or.inl hw⟩
  obtain ⟨v, hr₂, hv⟩ := oodPoint hSm hpre hw
  rcases hv with hv | hv
  · exact ⟨v, hr₀.trans (hr₁.trans hr₂), Or.inl (Or.inl hv)⟩
  obtain ⟨w', hr₃, hw'⟩ := oodValue hN hpre hv
  rcases hw' with hw' | hw'
  · exact ⟨w', hr₀.trans (hr₁.trans (hr₂.trans hr₃)), Or.inl hw'⟩
  obtain ⟨r, hr₄, hr⟩ := oodIntro hRP hpre hw'
  rcases hr with hr | hr
  · exact ⟨r, hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans hr₄))), Or.inl hr⟩
  obtain ⟨g, hr₅, hg⟩ := growPend hG hpre hr
  rcases hg with hg | hg
  · exact ⟨g, hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅)))), Or.inl (Or.inl hg)⟩
  obtain ⟨z, hr₆, hz⟩ := pushPend hpre hc hnf hl hg
  exact ⟨z, hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))),
    Or.inr ⟨[], _, _, hz⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
