import Rv64Verifier.Proofs.Pcs.VsoGlueRootsRound

/-!
# `verify_stacked_opening`'s final level: a round's root pushed

`0x8000bd94` compares the roots' length with their capacity; when full, `grow_one(S - 128)` at
`0x8000bda0` and `0x8000bdac` reloads the buffer (`RQ`, `rootsRoom`). `0x8000bcf8` pushes the
round's root and counts the round, back to `0x8000bd1c` or, after the `n`-th, on to `0x8000bdb4`
(`rootsPush`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000bcf8`: room for one more root in the `Vec` at `S - 128`. -/
structure RQ (s v w t p : MachineState) (a : Word) (n k : ℕ) (st : List K × List K) (L : Word) :
    Prop where
  h : RH s v w t a n k st L
  pf : RPF s v w p
  sl : RSL s w p a n L
  pc : p.pc = 0x8000bcf8
  x9 : p.getReg .x9 = BitVec.ofNat 64 (n - k)
  x19 : p.getReg .x19 = BitVec.ofNat 64 (8 * (n - k))
  x20 : p.getReg .x20 = BitVec.ofNat 64 (k + 1)
  x23 : kOf (p.getReg .x23) = (layM st).headD 0
  x27 : p.getReg .x27 = BitVec.ofNat 64 (k + 1) * 8
  x21 : p.getReg .x21 = p.getMem (s.getReg .x2 - 120)
  m792 : p.getMem (s.getReg .x2 - 792) = BitVec.ofNat 64 (k + 1)
  m112 : p.getMem (s.getReg .x2 - 112) = BitVec.ofNat 64 (k + 1)
  rcap : k + 2 ≤ (p.getMem (s.getReg .x2 - 128)).toNat
  Rb : (p.getMem (s.getReg .x2 - 120)).toNat % 8 = 0 ∧
    heapNext w ≤ (p.getMem (s.getReg .x2 - 120)).toNat ∧
    (p.getMem (s.getReg .x2 - 120)).toNat + 8 * (p.getMem (s.getReg .x2 - 128)).toNat ≤ heapNext p
  RL : (p.getMem (s.getReg .x2 - 120)).toNat + 8 * (p.getMem (s.getReg .x2 - 128)).toNat ≤ L.toNat ∨
    L.toNat + 8 * n ≤ (p.getMem (s.getReg .x2 - 120)).toNat
  ht : heapNext t ≤ heapNext p
  rts : kListAt p (p.getMem (s.getReg .x2 - 120)) (k + 1) = st.1
  lay : kListAt p L (n - k - 1) = (layM st).tail

set_option maxHeartbeats 1000000 in
/-- **Room for the round's root**: `0x8000bd94`, `grow_one` when full. -/
theorem rootsRoom (hG : GrowOneFreshSpec 0x8000d7bc 8 8) {s v w t u : MachineState} {a L : Word}
    {n k : ℕ} {st : List K × List K} (hpre : VsoPre s) (h : RM s v w t u a n k st L) :
    ∃ p, Reaches Image.code u p ∧ (Dead Image.code p ∨ RQ s v w t p a n k st L) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have sp := h.pf.sp
  have H := h.h
  obtain ⟨hL8, hLw, hLt⟩ := H.Lb
  obtain ⟨hR8, hRw, hRt⟩ := H.Rb
  have hRL := H.RL
  have hrc := H.rcap
  have hk := H.klt
  have hht := h.pf.heap.hi
  simp only [heapEnd] at hht
  have hsw := h.pf.sw
  have hnu : heapNext u = heapNext t := by simp only [heapNext, h.nx]
  generalize hRdef : t.getMem (s.getReg .x2 - 120) = R at hR8 hRw hRt hRL
  generalize hCdef : t.getMem (s.getReg .x2 - 128) = C at hrc hRt hRL
  have m120 : u.getMem (s.getReg .x2 - 120) = R := by rw [h.m120, hRdef]
  have m128 : u.getMem (s.getReg .x2 - 128) = C := by rw [h.m128, hCdef]
  have m112 : u.getMem (s.getReg .x2 - 112) = BitVec.ofNat 64 (k + 1) := by rw [h.m112, H.rlen]
  have rts := h.rts
  rw [hRdef] at rts
  have hk1 : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by rw [BitVec.toNat_ofNat]; omega
  -- `0x8000bd94`
  obtain ⟨u₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bd94_spec h.pc (by
    rv_eval [sp]; valid_access hst.valid [hb])
  have hm₁ := b8000bd94_mem_same h₁
  have k₁ := b8000bd94_keeps h₁
  have P₁ := h.pf.same hpre hm₁ (k₁ .x2 (by decide))
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₁.sp
  have x21₁ : u₁.getReg .x21 = R := by rw [b8000bd94_x21 h₁, h.x26, hRdef]
  have e912 : u.getMem (u.getReg .x2 + 912) = C := by rw [sp]; rv_eval [m128]
  by_cases hfull : k + 1 = C.toNat
  · -- full: `grow_one(S - 128)`
    have pc₁ := b8000bd94_pc_not_taken h₁ (by
      rw [h.x20, e912]; apply BitVec.eq_of_toNat_eq; rw [hk1, hfull])
    obtain ⟨u₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000bda0_spec pc₁ trivial
    have hm₂ := b8000bda0_mem_same h₂
    have k₂ := b8000bda0_keeps h₂
    have P₂ := P₁.same hpre hm₂ (k₂ .x2 (by decide))
    have sp₂ : u₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₂.sp
    have hm (y : Word) : u₂.getMem y = u.getMem y := by rw [hm₂, hm₁]
    have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 128 := by rw [b8000bda0_x10 h₂, sp₁]; rv_eval []
    have hsl : stackLo u₂ growOneStack = s.getReg .x2 - 1200 := by
      simp only [stackLo, growOneStack, sp₂]; rv_eval []
    have hn₂ : heapNext u₂ = heapNext t := by simp only [heapNext, hm]; exact hnu
    have vp : vecPtr u₂ (s.getReg .x2 - 128) = R := by simp only [vecPtr]; rv_eval [hm, m120]
    have vc : vecCap u₂ (s.getReg .x2 - 128) = C := by simp only [vecCap]; rw [hm, m128]
    obtain ⟨u₃, r₃, ⟨hpc₃, hpres₃, hpost₃, hnew₃⟩ | hd₃⟩ := hG.call (Reaches.refl u₂) (b8000bda0_pc h₂)
      { heap := P₂.heap
        self := by rw [x10₂]; valid_sub hst.valid [hb]
        raw := by
          rw [x10₂]; simp only [RawVecOk, Buf]; rw [vp, vc, hn₂]
          exact ⟨hR8, Or.inr ⟨by have := hpre.heap.lo; simp only [heapStart] at this ⊢; omega, by omega⟩⟩
        stack := hst.sub 1040 sp₂ (by decide) (by decide) (by decide) (by decide) (by decide)
        selfFree := by rw [x10₂]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
        selfStack := by rw [x10₂, hsl]; addr_omega [hb] }
    swap
    · exact ⟨u₃, r₁.trans (r₂.trans r₃), Or.inl hd₃⟩
    have F₃ := DFrame.of_byteFrame hpost₃.frame
    rw [x10₂, hsl] at F₃
    have hcap := hpost₃.cap
    have hraw := hpost₃.raw
    have hby := hpost₃.bytes
    have hmo := hpost₃.mono
    rw [x10₂, vc] at hcap hby
    rw [x10₂] at hraw hnew₃
    rw [vp] at hby
    simp only [RawVecOk, Buf] at hraw
    generalize hR'def : vecPtr u₃ (s.getReg .x2 - 128) = R' at hby hraw hnew₃
    generalize hC'def : vecCap u₃ (s.getReg .x2 - 128) = C' at hcap hraw hnew₃
    have hh₃ := hpost₃.heap.hi
    simp only [heapEnd] at hh₃
    have hRL' : L.toNat + 8 * n ≤ R'.toNat ∧ R'.toNat + 8 * C'.toNat ≤ heapNext u₃ := by
      rcases hnew₃.2 with h0 | h0
      · omega
      · rw [hn₂] at h0; constructor <;> omega
    have P₃ := P₂.step hpre F₃ (fun y hy ↦ by
        rcases hy with hy | hy | hy | hy
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb]))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb])))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hy)))))
        · exact glw_heap (by simp only [Fresh] at hy; have := P₂.wt; omega) hy.2)
      hpost₃.heap hmo (hpres₃ .x2 (by decide))
    -- `0x8000bdac`
    obtain ⟨u₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000bdac_spec
      (by rw [hpc₃, returnAddress_eq, b8000bda0_x1 h₂]; decide) (by
        rv_eval [(hpres₃ .x2 (by decide)).trans sp₂]; valid_access hst.valid [hb])
    have hm₄ := b8000bdac_mem_same h₄
    have k₄ := b8000bdac_keeps h₄
    have P₄ := P₃.same hpre hm₄ (k₄ .x2 (by decide))
    have kS (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 128).toNat ∨
        (s.getReg .x2 - 112).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
        u₄.getMem y = u.getMem y := by
      rw [hm₄, F₃ y fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw <;> rcases hy with hy | hy
        all_goals first
          | addr_omega [hw, hi, hy, hb]
          | addr_omega [hw, hi, hy, hb, hnx]
          | (simp only [Fresh] at hw; addr_omega [hw.2, hi, hy, hb, hh₃, hab]), hm]
    have kH (y : Word) (h1 : heapNext s ≤ y.toNat) (h2 : y.toNat + 8 ≤ heapNext t) :
        u₄.getMem y = u.getMem y := by
      rw [hm₄, F₃ y fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw
        · addr_omega [hw, hi, h2, hht, hab, hb, hnu]
        · addr_omega [hw, hi, h2, hht, hab, hb, hnu]
        · addr_omega [hw, hi, h2, hht, hnu]
        · simp only [Fresh] at hw; rw [hn₂] at hw; addr_omega [hw.1, hi, h2], hm]
    have m120₄ : u₄.getMem (s.getReg .x2 - 120) = R' := by
      rw [hm₄, ← hR'def]; simp only [vecPtr]; rv_eval []
    have m128₄ : u₄.getMem (s.getReg .x2 - 128) = C' := by rw [hm₄, ← hC'def]; rfl
    have hn₄ : heapNext u₄ = heapNext u₃ := by simp only [heapNext, hm₄]
    have r5 (q : Reg) (hq : q ∈ calleeSaved) (h4 : u₄.getReg q = u₃.getReg q)
        (h2 : u₂.getReg q = u₁.getReg q) (h1 : u₁.getReg q = u.getReg q) : u₄.getReg q = u.getReg q := by
      rw [h4, hpres₃ q hq, h2, h1]
    refine ⟨u₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr {
      h := H
      pf := P₄
      sl := ((h.sl.keep' hpre (DFrame.of_same hm fun _ ↦ False) fun _ h ↦ h.elim).keep' hpre F₃
          fun y hy ↦ by
            rcases hy with hy | hy | hy | hy
            · exact Or.inr (Or.inl (by addr_omega [hy, hb]))
            · exact Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb])))
            · exact Or.inr (Or.inr (Or.inr (Or.inl hy)))
            · simp only [Fresh] at hy
              exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by have := P₂.wt; omega,
                by simp only [heapEnd]; omega⟩)))).keep' hpre
        (DFrame.of_same hm₄ fun _ ↦ False) fun _ h ↦ h.elim
      pc := b8000bdac_pc h₄
      x9 := by rw [r5 .x9 (by decide) (k₄ .x9 (by decide)) (k₂ .x9 (by decide)) (k₁ .x9 (by decide)), h.x9]
      x19 := by
        rw [r5 .x19 (by decide) (k₄ .x19 (by decide)) (k₂ .x19 (by decide)) (k₁ .x19 (by decide)), h.x19]
      x20 := by
        rw [r5 .x20 (by decide) (k₄ .x20 (by decide)) (k₂ .x20 (by decide)) (k₁ .x20 (by decide)), h.x20]
      x23 := by
        rw [r5 .x23 (by decide) (k₄ .x23 (by decide)) (k₂ .x23 (by decide)) (k₁ .x23 (by decide))]
        exact h.x23
      x27 := by
        rw [r5 .x27 (by decide) (k₄ .x27 (by decide)) (k₂ .x27 (by decide)) (k₁ .x27 (by decide)), h.x27]
      x21 := by
        rw [b8000bdac_x21 h₄, (hpres₃ .x2 (by decide)).trans sp₂, m120₄, ← hm₄]; rv_eval [m120₄]
      m792 := by rw [kS _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m792
      m112 := by rw [kS _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact m112
      rcap := by rw [m128₄]; omega
      Rb := by rw [m120₄, m128₄, hn₄]; exact ⟨hraw.1, by have := P₂.wt; omega, hRL'.2⟩
      RL := by rw [m120₄, m128₄]; exact Or.inr hRL'.1
      ht := by rw [hn₄]; omega
      rts := by
        rw [m120₄, ← rts]
        exact kListAt_congr fun i hi ↦ by
          rw [hm₄]
          exact (getMem_eq_of_bytesAt hby hraw.1 hR8 (by omega) (by omega)).trans (hm _)
      lay := by
        rw [← h.lay]
        exact kListAt_congr fun i hi ↦ kH _ (by addr_omega [hi, hLw, hsw, hLt, hht])
          (by addr_omega [hi, hLt, hht, hk]) }⟩
  · -- room enough
    have hn₁ : heapNext u₁ = heapNext t := by simp only [heapNext, hm₁]; exact hnu
    have pc₁ := b8000bd94_pc_taken h₁ (by
      rw [h.x20, e912]; intro he; have := congrArg BitVec.toNat he; rw [hk1] at this; exact hfull this)
    refine ⟨u₁, r₁, Or.inr {
      h := H
      pf := P₁
      sl := h.sl.keep' hpre (DFrame.of_same hm₁ fun _ ↦ False) fun _ h ↦ h.elim
      pc := pc₁
      x9 := by rw [k₁ .x9 (by decide), h.x9]
      x19 := by rw [k₁ .x19 (by decide), h.x19]
      x20 := by rw [k₁ .x20 (by decide), h.x20]
      x23 := by rw [k₁ .x23 (by decide)]; exact h.x23
      x27 := by rw [k₁ .x27 (by decide), h.x27]
      x21 := by rw [x21₁, hm₁, m120]
      m792 := by rw [hm₁]; exact h.m792
      m112 := by rw [hm₁]; exact m112
      rcap := by rw [hm₁, m128]; omega
      Rb := by rw [hm₁, hm₁, m120, m128, hn₁]; exact ⟨hR8, hRw, hRt⟩
      RL := by rw [hm₁, hm₁, m120, m128]; exact hRL
      ht := by rw [hn₁]
      rts := by rw [hm₁, m120, ← rts]; exact kListAt_congr fun i _ ↦ hm₁ _
      lay := by rw [← h.lay]; exact kListAt_congr fun i _ ↦ hm₁ _ }⟩

set_option maxHeartbeats 1000000 in
/-- **The round's root pushed**: `0x8000bcf8`, on to the next round or out of the loop. -/
theorem rootsPush {s v w t p : MachineState} {a L : Word} {n k : ℕ} {st : List K × List K}
    (hpre : VsoPre s) (h : RQ s v w t p a n k st L) :
    ∃ q, Reaches Image.code p q ∧
      ((k + 1 < n ∧ RH s v w q a n (k + 1) (st.1 ++ [(layM st).headD 0], (layM st).tail) L) ∨
        (k + 1 = n ∧ RX s v w q a n (st.1 ++ [(layM st).headD 0]) L)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have sp := h.pf.sp
  have H := h.h
  obtain ⟨hL8, hLw, hLt⟩ := H.Lb
  have hk := H.klt
  have hht := h.pf.heap.hi
  simp only [heapEnd] at hht
  have hsw := h.pf.sw
  have hpt := h.ht
  obtain ⟨hR8, hRw, hRt⟩ := h.Rb
  have hRL := h.RL
  have hrc := h.rcap
  generalize hRdef : p.getMem (s.getReg .x2 - 120) = R at hR8 hRw hRt hRL
  generalize hCdef : p.getMem (s.getReg .x2 - 128) = C at hrc hRt hRL
  have x21 : p.getReg .x21 = R := by rw [h.x21, hRdef]
  have hRR : Region R (8 * C.toNat) := heap_region (by have := hpre.heap.lo; simp only [heapStart] at this; omega)
    (by simp only [heapEnd]; omega) hR8
  obtain ⟨q, r, hq⟩ := Sym.BlockSpec.reaches b8000bcf8_spec h.pc (by
    rv_eval [sp, x21, h.x27]
    rw [ofNat_mul8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRR (by addr_omega [hRt, hht, hrc]) (by addr_omega [hRt, hht, hrc])
          (by addr_omega [hRt, hht, hR8, hrc])
      | addr_omega [hRt, hht, hrc, hab, hb])
  have kq := b8000bcf8_keeps hq
  have F : DFrame p q fun y ↦ Within y (s.getReg .x2 - 112) 8 ∨
      Within y (R + BitVec.ofNat 64 (8 * (k + 1))) 8 :=
    (holds_dframe hq).mono fun y ⟨k', hk', hw⟩ ↦ by
      simp only [b8000bcf8, List.mem_cons, List.not_mem_nil, or_false] at hk'
      rcases hk' with rfl | rfl <;> rv_eval [sp, x21, h.x27] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · rw [ofNat_mul8] at hw; exact Or.inr hw
  have nq : q.getMem nextAddr = p.getMem nextAddr := F _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hRt, hht, hrc]
  have hnq : heapNext q = heapNext p := by simp only [heapNext, nq]
  have P := h.pf.step hpre F (fun y hy ↦ by
      rcases hy with hy | hy
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb]))))
      · exact glw_heap (by addr_omega [hy, hRw, hrc, hRt, hht]) (by
          have : (q.getMem nextAddr).toNat = heapNext q := rfl
          addr_omega [hy, this, hnq, hRt, hht, hrc]))
    ⟨by rw [hnq]; exact h.pf.heap.lo, by rw [hnq]; exact h.pf.heap.hi⟩ (by rw [hnq])
    (kq .x2 (by decide))
  have sl := h.sl.keep' hpre F fun y hy ↦ by
    rcases hy with hy | hy
    · exact Or.inr (Or.inl (by addr_omega [hy, hb]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hy, hRw, hsw, hrc, hRt, hht],
        by simp only [heapEnd]; addr_omega [hy, hRt, hht, hrc]⟩)))
  have kS (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 112).toNat ∨
      (s.getReg .x2 - 104).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      q.getMem y = p.getMem y :=
    F y fun i hi hw ↦ by
      rcases hw with hw | hw <;> rcases hy with hy | hy
      all_goals first | addr_omega [hw, hi, hy, hb] | addr_omega [hw, hi, hy, hb, hRt, hht, hab, hrc]
  have m120 : q.getMem (s.getReg .x2 - 120) = R := by
    rw [kS _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩), hRdef]
  have m128 : q.getMem (s.getReg .x2 - 128) = C := by
    rw [kS _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩), hCdef]
  have m112 : q.getMem (s.getReg .x2 - 112) = BitVec.ofNat 64 (k + 2) := by
    have := b8000bcf8_m_x2_928 hq; rw [sp, h.x20] at this; rv_eval [] at this
    rw [this]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega
  have mR : q.getMem (R + BitVec.ofNat 64 (8 * (k + 1))) = p.getReg .x23 := by
    have := b8000bcf8_m1 hq; rw [x21, h.x27, ofNat_mul8] at this; exact this
  have hl : st.2 ≠ [] := by
    intro he; have := H.len2; rw [he] at this; simp at this; omega
  have hlen : (layM st).length = n - k := by simp [layM, H.len2]
  have rts : kListAt q R (k + 2) = st.1 ++ [(layM st).headD 0] := by
    rw [kListAt_succ, mR, ← h.x23, ← h.rts, hRdef]
    congr 1
    exact kListAt_congr fun i hi ↦ F _ fun j hj hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hj, hi, hRt, hht, hab, hb, hrc]
      · addr_omega [hw, hj, hi, hRt, hht, hrc]
  have lay : kListAt q L (n - (k + 1)) = (layM st).tail := by
    rw [show n - (k + 1) = n - k - 1 by omega, ← h.lay]
    exact kListAt_congr fun i hi ↦ F _ fun j hj hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hj, hi, hLt, hpt, hht, hab, hb]
      · rcases hRL with h0 | h0 <;> addr_omega [hw, hj, hi, h0, hLt, hpt, hht, hrc, hRt]
  have hloop : Model.Pcs.subspaceRootsRust n = (Model.Pcs.subspaceRootsLoop (n - (k + 1))
      (st.1 ++ [(layM st).headD 0], (layM st).tail)).map (·.1) := by
    rw [H.loop, show n - k = n - (k + 1) + 1 by omega, rootsLoop_succ _ _ _ (rootsStep' hl)]
  have m792 : q.getMem (s.getReg .x2 - 792) = BitVec.ofNat 64 (k + 1) := by
    rw [kS _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m792
  have m832 : q.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 n := sl.m832
  have hk1 : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by rw [BitVec.toNat_ofNat]; omega
  have hn1 : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  have e248 : p.getMem (p.getReg .x2 + 248) = BitVec.ofNat 64 (k + 1) := by rw [sp]; rv_eval [h.m792]
  have e208 : p.getMem (p.getReg .x2 + 208) = BitVec.ofNat 64 n := by rw [sp]; rv_eval [h.sl.m832]
  have x26 : q.getReg .x26 = BitVec.ofNat 64 n := by rw [b8000bcf8_x26 hq, e208]
  have x20 : q.getReg .x20 = BitVec.ofNat 64 (k + 2) := by
    rw [b8000bcf8_x20 hq, h.x20]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega
  have Rb : R.toNat % 8 = 0 ∧ heapNext w ≤ R.toNat ∧ R.toNat + 8 * C.toNat ≤ heapNext q := by
    rw [hnq]; exact ⟨hR8, hRw, hRt⟩
  by_cases hend : k + 1 = n
  · refine ⟨q, r, Or.inr ⟨hend, {
      pf := P
      sl := sl
      pc := b8000bcf8_pc_taken hq (by rw [e248, e208, hend])
      roots := by rw [hloop, ← hend, Nat.sub_self]; rfl
      rlen := by simp [H.len1]; omega
      x20 := by rw [x20, ← hend]
      x26 := x26
      Rb := by rw [m120]; exact ⟨hR8, hRw, by rw [hnq]; omega⟩
      rts := by rw [m120, ← hend]; exact rts }⟩⟩
  · refine ⟨q, r, Or.inl ⟨by omega, {
      pf := P
      sl := sl
      pc := b8000bcf8_pc_not_taken hq (by
        rw [e248, e208]; intro he; have := congrArg BitVec.toNat he; rw [hk1, hn1] at this
        exact hend this)
      klt := by omega
      loop := hloop
      len1 := by simp [H.len1]
      len2 := by simp [hlen]; omega
      x9 := by
        rw [b8000bcf8_x9 hq, h.x9]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega
      x13 := by rw [b8000bcf8_x13 hq, e248]
      x19 := by
        rw [b8000bcf8_x19 hq, h.x19]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]; omega
      x20 := by rw [x20]
      x21 := by rw [kq .x21 (by decide), x21, m120]
      Lb := ⟨hL8, hLw, by rw [hnq]; omega⟩
      lay := lay
      rcap := by rw [m128]; omega
      rlen := by rw [m112]
      Rb := by rw [m120, m128]; exact Rb
      RL := by rw [m120, m128]; exact hRL
      rts := by rw [m120]; exact rts }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
