import Rv64Verifier.Proofs.Pcs.VsoTailGrow

/-!
# `verify_stacked_opening`'s level tail: from the rows to the glue

From `0x8000b42c` (`Rowed`): `dot(rows, powers)` into `S - 512`, `sumcheck_round_poly(3, _, None)`
into `S - 464` (an `Err` returned at `0x8000b8e0`), `grow_one` of the pending claims if they are
full, and the push (`push498`), to the glue at `0x8000b650` (`Fronted`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the tail writes from the rows' end `r` to the glue. -/
def FrW (s r g : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 904) 8 ∨ Within a (s.getReg .x2 - 616) 24 ∨
    Within a (s.getReg .x2 - 512) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
    Within a (s.getReg .x2 - 408) 24 ∨ Within a (s.getReg .x2 - 384) 8 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ Within a (s.getReg .x10 + 8) 344 ∨
    Within a nextAddr 8 ∨
    Within a (vecPtr r (s.getReg .x2 - 616)) ((vecCap r (s.getReg .x2 - 616)).toNat * 80) ∨
    Fresh r g a

/-- At `0x8000b650`, from the rows' end `r`: the intro message `q` pushed as the pending claim
`n`, `n` the count at `r`, with its `Queries` weight. -/
structure Fronted (s r g : MachineState) (q : List E) : Prop where
  pc : g.pc = 0x8000b650
  sp : g.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s g (g.getMem nextAddr)
  heap : HeapOk g
  mono : heapNext r ≤ heapNext g
  fr : DFrame r g (FrW s r g)
  regs : ∀ q ∈ [Reg.x9, .x23], g.getReg q = r.getReg q
  x18 : g.getReg .x18 = vecPtr g (s.getReg .x2 - 616)
  x22 : g.getReg .x22 = vecLen g (s.getReg .x2 - 616)
  x25 : g.getReg .x25 = r.getMem (s.getReg .x2 - 792)
  x26 : g.getReg .x26 = r.getMem (s.getReg .x2 - 912)
  len : vecLen g (s.getReg .x2 - 616) = vecLen r (s.getReg .x2 - 616) + 1
  vec : VecOk g (s.getReg .x2 - 616) 80 8 ∧
    HS s g (vecPtr g (s.getReg .x2 - 616)) ((vecCap g (s.getReg .x2 - 616)).toNat * 80)
  pnew : (vecPtr g (s.getReg .x2 - 616) = vecPtr r (s.getReg .x2 - 616) ∧
      vecCap g (s.getReg .x2 - 616) = vecCap r (s.getReg .x2 - 616)) ∨
    NewBuf r g (vecPtr g (s.getReg .x2 - 616)) ((vecCap g (s.getReg .x2 - 616)).toNat * 80) 8
  /-- The claims before `n` copied. -/
  old : ∀ o, o % 8 = 0 → o + 8 ≤ 80 * (vecLen r (s.getReg .x2 - 616)).toNat →
    g.getMem (vecPtr g (s.getReg .x2 - 616) + BitVec.ofNat 64 o) =
      r.getMem (vecPtr r (s.getReg .x2 - 616) + BitVec.ofNat 64 o)
  /-- Claim `n`: the intro message, new since `r`. -/
  intro : VecOk g (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat) 24 8 ∧
    vecEs g (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat) = q ∧
    NewBuf r g (vecPtr g (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat))
      ((vecCap g (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat)).toNat * 24) 8
  /-- Claim `n`'s weight. -/
  w24 : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 24) =
    r.getMem (s.getReg .x2 - 1000)
  w32 : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 32) =
    r.getMem (s.getReg .x2 - 824)
  w40 : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 40) = r.getReg .x26
  w48 : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 48) =
    r.getMem (s.getReg .x2 - 488)
  w56 : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 56) =
    r.getMem (s.getReg .x2 - 480)
  w64 : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 64) =
    r.getMem (s.getReg .x2 - 472)
  w72 : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 72) =
    r.getMem (s.getReg .x2 - 872)
  one : eAt g (s.getReg .x2 - 408) = 1
  /-- `dot`'s lengths agree. -/
  hlen : r.getReg .x27 = vecLen r (s.getReg .x2 - 488)
  dig : digestAt g (s.getReg .x11) = digestAt r (s.getReg .x11)
  value : ∀ T, TranscriptAt r (s.getReg .x10) T → ∃ T',
    (Model.TM.sumcheckRoundPoly 3 (Model.dotRust (eListAt r (r.getReg .x25) (r.getReg .x27).toNat)
      (eListAt r (vecPtr r (s.getReg .x2 - 488)) (r.getReg .x27).toNat)) none).run T =
      some (q, T') ∧ TranscriptAt g (s.getReg .x10) T' ∧ T'.proof = T.proof ∧
      T'.roots = T.roots ∧ T'.openingOffset = T.openingOffset

/-- At `0x8000b47c`, from the rows' end `r`: the intro message `q` read, its `Vec` in
`x21`/`x8`/`x19`. -/
structure RPOut (s r t : MachineState) (q : List E) : Prop where
  pc : t.pc = 0x8000b47c
  sp : t.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s t (t.getMem nextAddr)
  heap : HeapOk t
  mono : heapNext r ≤ heapNext t
  fr : DFrame r t fun a ↦ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a (s.getReg .x2 - 512) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
    Within a (s.getReg .x2 - 384) 8 ∨ Within a (s.getReg .x10 + 8) 344 ∨
    Within a nextAddr 8 ∨ Fresh r t a
  regs : ∀ q ∈ [Reg.x9, .x23, .x26], t.getReg q = r.getReg q
  ilen : (t.getReg .x19).toNat ≤ (t.getReg .x21).toNat
  ibuf : (t.getReg .x8).toNat % 8 = 0 ∧ ((t.getReg .x21).toNat * 24 = 0 ∨
    heapNext r ≤ (t.getReg .x8).toNat ∧ (t.getReg .x8).toNat + (t.getReg .x21).toNat * 24 ≤
      heapNext t)
  intro : eListAt t (t.getReg .x8) (t.getReg .x19).toNat = q
  hlen : r.getReg .x27 = vecLen r (s.getReg .x2 - 488)
  value : ∀ T, TranscriptAt r (s.getReg .x10) T → ∃ T',
    (Model.TM.sumcheckRoundPoly 3 (Model.dotRust (eListAt r (r.getReg .x25) (r.getReg .x27).toNat)
      (eListAt r (vecPtr r (s.getReg .x2 - 488)) (r.getReg .x27).toNat)) none).run T =
      some (q, T') ∧ TranscriptAt t (s.getReg .x10) T' ∧ T'.proof = T.proof ∧
      T'.roots = T.roots ∧ T'.openingOffset = T.openingOffset

/-- **From the rows to the intro message**: `dot`, `sumcheck_round_poly`, its `Err` returned. -/
theorem tailRP (hDt : MultilinearContracts.DotSpec) (hRP : RoundPolyErrSpec)
    {s r : MachineState} (hpre : VsoPre s)
    (hpc : r.pc = 0x8000b42c) (hsp : r.getReg .x2 = s.getReg .x2 - 1040)
    (hinv : InvR s r (r.getMem nextAddr)) (hheap : HeapOk r)
    (hrows : HS s r (r.getReg .x25) (24 * (r.getReg .x27).toNat))
    (hpw : HS s r (vecPtr r (s.getReg .x2 - 488)) (24 * (vecLen r (s.getReg .x2 - 488)).toNat))
    (h816 : r.getMem (s.getReg .x2 - 816) = s.getReg .x10) :
    ∃ t, Reaches Image.code r t ∧ (FailR s t ∨ ∃ q, RPOut s r t q) := by
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
  have hsr : heapNext s ≤ heapNext r := hinv.mono
  -- `dot`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b42c_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000b42c_keeps h₁
  have m₁ := b8000b42c_mem_same h₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans hsp
  have hn₁ : heapNext t₁ = heapNext r := by simp only [heapNext, m₁]
  have hheap₁ : HeapOk t₁ := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [m₁]; exact Inv.same' hinv m₁ (k₁ .x2 (by decide))
  have x13₁ : t₁.getReg .x13 = vecPtr r (s.getReg .x2 - 488) := by
    rw [b8000b42c_x13 h₁, hsp]; simp only [vecPtr]; rv_eval []
  have x14₁ : t₁.getReg .x14 = vecLen r (s.getReg .x2 - 488) := by
    rw [b8000b42c_x14 h₁, hsp]; simp only [vecLen]; rv_eval []
  obtain ⟨t₂, hr₂, hv₂⟩ := callDotV hDt hpre inv₁ hheap₁ (b8000b42c_pc h₁)
    (by rw [b8000b42c_x10 h₁, hsp]; rv_eval [])
    (by rw [b8000b42c_x11 h₁, b8000b42c_x12 h₁]; simpa only [HS, hn₁] using hrows)
    (by rw [x13₁, x14₁]; simpa only [HS, hn₁] using hpw)
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, X₂, hlen₂, hval₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (Or.inl hd)⟩
  rw [b8000b42c_x12 h₁, x14₁] at hlen₂
  rw [b8000b42c_x11 h₁, b8000b42c_x12 h₁, x13₁] at hval₂
  have eL : ∀ p n, eListAt t₁ p n = eListAt r p n := fun p n ↦ by
    simp only [Rv64Verifier.eListAt, Rv64Verifier.eAt, m₁]
  rw [eL, eL] at hval₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := (hpres₂ .x2 (by decide)).trans sp₁
  have nx₂ : t₂.getMem nextAddr = t₁.getMem nextAddr := X₂ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hnx]
  have hn₂ : heapNext t₂ = heapNext r := by simp only [heapNext, nx₂]; exact hn₁
  have inv₂ : InvR s t₂ (t₂.getMem nextAddr) := by
    rw [nx₂]
    exact Inv.step' hpre inv₁ X₂ (fun a ha ↦ Or.inr (Or.inl (in_stack hpre (by
        rcases ha with ha | ha <;> addr_omega [ha, hb]))))
      (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb]) nx₂ (le_refl _) inv₁.fits
      (hpres₂ .x2 (by decide))
  have hheap₂ : HeapOk t₂ := ⟨hn₂ ▸ hheap.lo, hn₂ ▸ hheap.hi⟩
  have k₂ (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat ∨ (s.getReg .x2 - 488).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2).toNat) : t₂.getMem y = r.getMem y :=
    (X₂ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hy]).trans (m₁ y)
  -- `sumcheck_round_poly`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000b448_spec
    (by rw [hpc₂, returnAddress_eq, b8000b42c_x1 h₁]; decide) (by
      rv_eval [sp₂]; and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000b448_keeps h₃
  have f₃ := DFrame.of_memFrame (b8000b448_frame h₃ (by rw [sp₂]; addr_omega [hb]))
  rw [sp₂, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at f₃
  obtain ⟨nx₃, inv₃⟩ := InvR.stk hpre inv₂ f₃ (fun a ha ↦ by addr_omega [ha, hb])
    (k₃ .x2 (by decide))
  have hn₃ : heapNext t₃ = heapNext r := by simp only [heapNext, nx₃]; exact hn₂
  have hheap₃ : HeapOk t₃ := ⟨hn₃ ▸ hheap.lo, hn₃ ▸ hheap.hi⟩
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := (k₃ .x2 (by decide)).trans sp₂
  have m0 : t₃.getMem (s.getReg .x2 - 384) = 0 := by
    have := b8000b448_m_x2_656 h₃
    rw [sp₂, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at this
    exact this
  have hcl : eAt t₃ (s.getReg .x2 - 512) = eAt t₂ (s.getReg .x2 - 512) :=
    f₃.eAt fun i hi hw ↦ by addr_omega [hw, hi, hb]
  obtain ⟨t₄, hr₄, hv₄⟩ := callRoundPoly (o := s.getReg .x2 - 464) (cl := s.getReg .x2 - 512) hRP
    hpre inv₃ hheap₃ (b8000b448_pc h₃) (by rw [b8000b448_x10 h₃, sp₂]; rv_eval [])
    (by
      rw [b8000b448_x11 h₃, sp₂, show s.getReg .x2 - 1040 + 224 = s.getReg .x2 - 816 by rv_eval [],
        k₂ _ (by addr_omega [hb]), h816])
    (b8000b448_x12 h₃) (by rw [b8000b448_x13 h₃, sp₂]; rv_eval [])
    (by rw [b8000b448_x14 h₃, sp₂]; rv_eval []) m0 (by addr_omega [hb]) (by addr_omega [hb])
  rcases hv₄ with hd | ⟨hpc₄, hpres₄, hheap₄, hmono₄, X₄, herr₄, hok₄, hval₄⟩
  · exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl (Or.inl hd)⟩
  have inv₄ := InvR.callT hpre inv₃ X₄ (by simp only [Slot24]; addr_omega [hb]) hheap₄ hmono₄
    (hpres₄ .x2 (by decide))
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := (hpres₄ .x2 (by decide)).trans sp₃
  have hhi₄ := hheap₄.hi
  have hn₄ : heapNext r ≤ heapNext t₄ := hn₃ ▸ hmono₄
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000b468_spec
    (by rw [hpc₄, returnAddress_eq, b8000b448_x1 h₃]; decide) (by
      rv_eval [sp₄]; and_intros <;> valid_access hst.valid [hb])
  have k₅ := b8000b468_keeps h₅
  have m₅ := b8000b468_mem_same h₅
  have e576 : t₄.getReg .x2 + 576 = s.getReg .x2 - 464 := by rw [sp₄]; rv_eval []
  have e584 : t₄.getReg .x2 + 584 = s.getReg .x2 - 464 + 8 := by rw [sp₄]; rv_eval []
  have e592 : t₄.getReg .x2 + 592 = s.getReg .x2 - 464 + 16 := by rw [sp₄]; rv_eval []
  have hr15 := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅)))
  by_cases herr : vecCap t₄ (s.getReg .x2 - 464) = errNiche
  · obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000b8e0_spec
      (b8000b468_pc_taken h₅ (by rw [e576]; exact herr)) trivial
    have inv₆ : InvR s t₆ (t₄.getMem nextAddr) :=
      Inv.same' inv₄ (fun a ↦ by rw [b8000b8e0_mem_same h₆, m₅])
        (by rw [b8000b8e0_keeps h₆ .x2 (by decide), k₅ .x2 (by decide)])
    obtain ⟨z, hrz, hfz⟩ := fail844 inv₆ (b8000b8e0_pc h₆) (by
      rw [b8000b8e0_x1 h₆, b8000b468_x8 h₅, e584]; exact herr₄ herr)
    exact ⟨z, hr15.trans (hr₆.trans hrz), Or.inl hfz⟩
  obtain ⟨hvo, hnb⟩ := hok₄ herr
  have inv₅ : InvR s t₅ (t₅.getMem nextAddr) := by
    rw [m₅]; exact Inv.same' inv₄ m₅ (k₅ .x2 (by decide))
  have hn₅ : heapNext t₅ = heapNext t₄ := by simp only [heapNext, m₅]
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 1040 := (k₅ .x2 (by decide)).trans sp₄
  -- what `r` had, at `t₅`
  have Y₅ : DFrame r t₅ fun a ↦ Within a (s.getReg .x2 - 2464) 1424 ∨
      Within a (s.getReg .x2 - 512) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
      Within a (s.getReg .x2 - 384) 8 ∨ Within a (s.getReg .x10 + 8) 344 ∨
      Within a nextAddr 8 ∨ Fresh r t₅ a := by
    refine ((((DFrame.of_same m₁ _).trans (X₂.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
      (f₃.mono fun a ha ↦ ?_) fun _ h ↦ h).trans (X₄.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
      (DFrame.of_same m₅ _) fun _ h ↦ h
    · rcases ha with ha | ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · rcases ha with ha | ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      · simp only [Fresh] at ha ⊢
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩)))))
        simp only [heapNext] at hn₅ ⊢; rw [m₅]; exact ha.2
  have kreg (q : Reg) (hq : q ∈ [Reg.x9, .x23, .x26]) : t₅.getReg q = r.getReg q := by
    have hc : q ∈ calleeSaved := (by decide : ∀ q ∈ [Reg.x9, .x23, .x26], q ∈ calleeSaved) q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;>
      rw [k₅ _ (by decide), hpres₄ _ hc, k₃ _ (by decide), hpres₂ _ hc, k₁ _ (by decide)]
  have hT₁ (T : Model.TState) (hT : TranscriptAt r (s.getReg .x10) T) :
      TranscriptAt t₃ (s.getReg .x10) T := by
    have h1 : TranscriptAt t₁ (s.getReg .x10) T :=
      tr_keep hpre hinv hT (DFrame.of_same m₁ fun _ ↦ False) fun _ h ↦ h.elim
    have h2 : TranscriptAt t₂ (s.getReg .x10) T := tr_keep hpre inv₁ h1 X₂ fun a ha ↦ Or.inl (by
      rcases ha with ha | ha <;> addr_omega [ha, hb])
    exact tr_keep hpre inv₂ h2 f₃ fun a ha ↦ Or.inl (by addr_omega [ha, hb])
  have hraw := hvo.raw
  simp only [RawVecOk, Buf] at hraw
  simp only [NewBuf] at hnb
  have e21 : t₅.getReg .x21 = vecCap t₄ (s.getReg .x2 - 464) := by
    rw [b8000b468_x21 h₅, e576]; rfl
  have e8 : t₅.getReg .x8 = vecPtr t₄ (s.getReg .x2 - 464) := by
    rw [b8000b468_x8 h₅, e584]; rfl
  have e19 : t₅.getReg .x19 = vecLen t₄ (s.getReg .x2 - 464) := by
    rw [b8000b468_x19 h₅, e592]; rfl
  have hq : eListAt t₅ (t₅.getReg .x8) (t₅.getReg .x19).toNat = vecEs t₄ (s.getReg .x2 - 464) := by
    rw [e8, e19]; simp only [vecEs, Rv64Verifier.eListAt, Rv64Verifier.eAt, m₅]
  refine ⟨t₅, hr15, Or.inr ⟨vecEs t₄ (s.getReg .x2 - 464), {
    pc := b8000b468_pc_not_taken h₅ (by rw [e576]; exact herr)
    sp := sp₅
    inv := inv₅
    heap := ⟨hn₅ ▸ hheap₄.lo, hn₅ ▸ hhi₄⟩
    mono := by rw [hn₅]; exact hn₄
    fr := Y₅
    regs := kreg
    ilen := by rw [e19, e21]; exact hvo.len
    ibuf := by
      rw [e8, e21, hn₅]
      refine ⟨hraw.1, ?_⟩
      rcases hnb.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by rw [← hn₃]; exact h0.1, h0.2⟩
    intro := hq
    hlen := hlen₂
    value := fun T hT ↦ by
      have hv := hval₄ T (hT₁ T hT)
      rw [hcl, hval₂] at hv
      cases hrun : (Model.TM.sumcheckRoundPoly 3 (Model.dotRust
          (eListAt r (r.getReg .x25) (r.getReg .x27).toNat)
          (eListAt r (vecPtr r (s.getReg .x2 - 488)) (r.getReg .x27).toNat)) none).run T with
      | none => rw [hrun] at hv; exact absurd hv herr
      | some p =>
        obtain ⟨qv, T'⟩ := p
        rw [hrun] at hv
        obtain ⟨-, hnew, hT'⟩ := hv
        have hk := Model.Pcs.Keeps.roundPoly _ _ _ T qv T' hrun
        refine ⟨T', ?_, tr_keep hpre inv₄ hT' (DFrame.of_same m₅ fun _ ↦ False) (fun _ h ↦ h.elim),
          hk.1, hk.2.1, hk.2.2⟩
        rw [← hnew.elems] }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
