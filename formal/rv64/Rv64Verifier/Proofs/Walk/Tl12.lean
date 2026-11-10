import Rv64Verifier.Proofs.Walk.MapLoop12

/-!
# `walk`: `block_kappas` (R12), its buffer

From `0x80003210` (`Flt12 .. 165`): `blocks`' buffer `G` into `s1`, `try_allocate_in(101)` for
`block_kappas`' buffer `BK`, its `Vec` at `sp + 1728` (over `blocks`' header), `reserve(101)` (room
enough), to the map loop at `0x8000328c` (`bkAlloc`); `r12` then runs the loop to `0x800032b8`, the
call of `stack_offsets` (`AtR13`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At the map loop's start: `blocks` in `G`, `BK` new. -/
structure Bk12 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 : Nat) (G BK : Word) : Prop where
  base : Base12 OI s u A k R Q B lo lo2 lo3
  gal : G.toNat % 8 = 0
  glo : lo3 ≤ G.toNat
  ghi : G.toNat + 808 ≤ BK.toNat
  gvals : ∀ i < 101, u.getMem (G + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 ((blk 165).getD i 0)
  bkal : BK.toNat % 8 = 0
  bkhi : BK.toNat + 808 ≤ heapNext u
  kp : u.getReg .x10 = vecPtr u (s.getReg .x2 - 1344)
  map : Map12 u u G BK 0
  x9 : u.getReg .x9 = G
  x11 : u.getReg .x11 = BK
  x24 : u.getReg .x24 = 165
  x25 : u.getReg .x25 = 101
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)

set_option maxRecDepth 8192 in
/-- From `0x80003210` to the map loop. -/
theorem bkAlloc (hTA : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000d628)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x80003210)
    (h : Flt12 OI s u A k R Q B lo lo2 lo3 165) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x8000328c ∧ ∃ G BK, Bk12 OI s t A k R Q B lo lo2 lo3 G BK)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have Bs := h.base
  have I := Bs.k11.at11.base.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have hne := blk_ne h.pos
  have hlen : (blk 165).length = 101 := blk_165_length
  obtain ⟨G, hGd⟩ : ∃ G, vecPtr u (s.getReg .x2 - 928) = G := ⟨_, rfl⟩
  obtain ⟨g1, g2, g3, g4⟩ := h.bv.bounds hne
  rw [hGd] at g1 g2 g3
  have gfr := h.bv.fresh
  rw [hGd] at gfr
  rw [hlen] at g4
  simp only [heapStart] at g2
  have gv0 : ∀ i < 101, u.getMem (G + BitVec.ofNat 64 (8 * i)) =
      BitVec.ofNat 64 ((blk 165).getD i 0) := fun i hi ↦ by
    rw [← hGd]; exact h.bv.vals i (by omega)
  have hl3 := Bs.lo3le
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003210_spec hpc (by
    rv_eval [sp]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have m₁ := b80003210_mem_same h₁
  have k₁ := b80003210_keeps h₁
  have e1736 : s.getReg .x2 - 2656 + 1736 = s.getReg .x2 - 928 + 8 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x9₁ : u₁.getReg .x9 = G := by rw [b80003210_x9 h₁, sp, e1736]; exact hGd
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003220_spec (b80003210_pc h₁) (by rv_eval [])
  have m₂ (a : Word) : u₂.getMem a = u.getMem a := by rw [b80003220_mem_same h₂, m₁]
  have k₂ := b80003220_keeps h₂
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide)]; exact sp
  have B₂ := Bs.same hpre m₂ (by rw [sp₂, sp])
  have I₂ := B₂.k11.at11.base.inv
  have hn₂ : heapNext u₂ = heapNext u := by simp only [heapNext, m₂]
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 928 := by
    rw [b80003220_x10 h₂, k₁ .x2 (by decide), sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₂ : u₂.getReg .x11 = 101 := by
    rw [b80003220_x11 h₂, k₁ .x25 (by decide), h.x25, hlen]; rfl
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab hx
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have pre : TryAllocPre .x13 .x14 u₂ := {
    heap := I₂.heap
    out := by
      rw [x10₂]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩)
    align := by rw [b80003220_x13 h₂]; decide
    size := by rw [b80003220_x14 h₂]; decide
    stack := stk10 hpre I₂ (by decide) (by decide)
    outFree := by
      rw [x10₂]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by simp only [Apart]; addr_omega [hx, hb1]⟩
    outStack := by rw [x10₂, stackLo_callee I₂]; simp only [Apart]; addr_omega [hb1] }
  obtain ⟨t, hr, ⟨hpct, hp, post, -⟩ | hd⟩ := hTA u₂ (b80003220_pc h₂) pre
  swap
  · exact ⟨t, hr₁.trans (hr₂.trans hr), Or.inl hd⟩
  have fr := post.frame.dframe
  rw [x10₂] at fr
  have ok := post.ok
  rw [x10₂, x11₂, b80003220_x13 h₂, b80003220_x14 h₂] at ok
  have hht := post.heap.hi
  have hhc := I₂.heap.hi
  have hmono := post.mono
  simp only [heapEnd] at hht hhc
  have Bt := B₂.keep hpre fr (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; omega)
      · rw [stackLo_callee I₂] at ha
        exact Or.inr (Or.inl (by simp only [Within, tryAllocStack] at ha ⊢; addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))) post.heap hmono
    (hp .x2 (by decide))
  have gvt : ∀ i < 101, t.getMem (G + BitVec.ofNat 64 (8 * i)) =
      BitVec.ofNat 64 ((blk 165).getD i 0) := fun i hi ↦ by
    rw [fr.getMem_of (fun x hx hw' ↦ by
        simp only [Within] at hx
        rcases hw' with h2 | h2 | h2 | h2
        · simp only [Within] at h2; addr_omega [hx, h2, hb1, g2, g3, hhc, hn₂, hi, g4]
        · rw [stackLo_callee I₂] at h2; simp only [Within, tryAllocStack] at h2
          addr_omega [hx, h2, hb1, g2, g3, hhc, hn₂, hi, g4]
        · simp only [Within, nextAddr] at h2; addr_omega [hx, h2, g2, g3, hhc, hn₂, hi, g4]
        · simp only [Fresh] at h2; addr_omega [hx, h2, g2, g3, hn₂, hi, g4])
      (by addr_omega [g2, g3, hhc, hn₂, hi, g4]), m₂]
    exact gv0 i hi
  have pct : t.pc = 0x8000323c := by rw [hpct, returnAddress_eq, b80003220_x1 h₂]; decide
  have spt : t.getReg .x2 = s.getReg .x2 - 2656 := by rw [hp .x2 (by decide)]; exact sp₂
  obtain ⟨t₁, hrt₁, ht₁⟩ := Sym.BlockSpec.reaches b8000323c_spec pct (by
    rv_eval [spt]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have e1728 : s.getReg .x2 - 2656 + 1728 = s.getReg .x2 - 928 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases hz : t.getMem (s.getReg .x2 - 928) = 0
  swap
  · exact ⟨t₁, hr₁.trans (hr₂.trans (hr.trans hrt₁)),
      Or.inl (trapAt (b8000323c_pc_taken ht₁ (by rw [spt, e1728]; exact hz)))⟩
  have pc₁ := b8000323c_pc_not_taken ht₁ (by rw [spt, e1728]; exact hz)
  obtain ⟨o1, o2⟩ := ok hz
  have e808 : (101 : Word).toNat * (8 : Word).toNat = 808 := rfl
  rw [e808] at o2
  obtain ⟨BK, hBKd⟩ : ∃ BK, t.getMem (s.getReg .x2 - 928 + 16) = BK := ⟨_, rfl⟩
  rw [hBKd] at o2
  simp only [NewBuf] at o2
  obtain ⟨bk1, bk2⟩ := o2
  have bk3 : heapNext u ≤ BK.toNat ∧ BK.toNat + 808 ≤ heapNext t := by
    rcases bk2 with h0 | h0
    · omega
    · rw [hn₂] at h0; exact h0
  have mt₁ := b8000323c_mem_same ht₁
  have kt₁ := b8000323c_keeps ht₁
  have spt₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [kt₁ .x2 (by decide)]; exact spt
  obtain ⟨t₂, hrt₂, ht₂⟩ := Sym.BlockSpec.reaches b80003244_spec pc₁ (by
    rv_eval [spt₁]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have fr₂ := (b80003244_frame ht₂ (by rw [spt₁]; addr_omega [hb1])).dframe
  rw [spt₁, e1728] at fr₂
  have kt₂ := b80003244_keeps ht₂
  have hn₂' : heapNext t₂ = heapNext t := by
    simp only [heapNext]
    rw [fr₂.getMem_of (fun y hy hw ↦ by simp only [Within, nextAddr] at hy hw; addr_omega [hy, hw, hb1])
      (by decide), mt₁]
  have hvt₂ : HeapOk t₂ := ⟨hn₂' ▸ post.heap.lo, hn₂' ▸ post.heap.hi⟩
  have B₃ := Bt.keep hpre (fun a ha hw8 ↦ (fr₂ a ha hw8).trans (mt₁ a)) (fun a ha ↦ Or.inl (by
      simp only [Within] at ha ⊢; omega)) hvt₂ hn₂'.ge
    (by rw [kt₂ .x2 (by decide), spt₁, spt])
  have e1736' : s.getReg .x2 - 2656 + 1736 = s.getReg .x2 - 928 + 8 := e1736
  have e1744 : s.getReg .x2 - 2656 + 1744 = s.getReg .x2 - 928 + 16 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have w0 : t₂.getMem (s.getReg .x2 - 928) = 101 := by
    have := b80003244_m_x2_1728 ht₂; rw [spt₁, e1728, e1736, mt₁] at this; rw [this, o1]
  have w8 : t₂.getMem (s.getReg .x2 - 928 + 8) = BK := by
    have := b80003244_m_x2_1736 ht₂; rw [spt₁, e1736, e1744, mt₁] at this; rw [this, hBKd]
  have w16 : t₂.getMem (s.getReg .x2 - 928 + 16) = 0 := by
    have := b80003244_m_x2_1744 ht₂; rw [spt₁, e1744] at this; exact this
  have x10₂' : t₂.getReg .x10 = s.getReg .x2 - 928 := by
    rw [b80003244_x10 ht₂, spt₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₂' : t₂.getReg .x11 = 101 := by
    rw [b80003244_x11 ht₂, kt₁ .x25 (by decide), hp .x25 (by decide), k₂ .x25 (by decide),
      k₁ .x25 (by decide), h.x25, hlen]; rfl
  obtain ⟨t₃, hrt₃, ⟨hpct₃, hp₃, -, m₃⟩ | hd⟩ := hRF t₂ (b80003244_pc ht₂) ⟨by
      rw [x10₂']; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩), by
      rw [x10₂', x11₂']; simp only [vecLen, vecCap]; rw [w0, w16]; decide⟩
  swap
  · exact ⟨t₃, hr₁.trans (hr₂.trans (hr.trans (hrt₁.trans (hrt₂.trans hrt₃)))), Or.inl hd⟩
  have pc₃ : t₃.pc = 0x80003268 := by rw [hpct₃, returnAddress_eq, b80003244_x1 ht₂]; decide
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [hp₃ .x2 (by decide), kt₂ .x2 (by decide)]; exact spt₁
  obtain ⟨t₄, hrt₄, ht₄⟩ := Sym.BlockSpec.reaches b80003268_spec pc₃ (by
    rv_eval [sp₃]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have kt₄ := b80003268_keeps ht₄
  have rg₃ (r : Reg) (hr : r ∈ ([.x2, .x9, .x18, .x23, .x25, .x26] : List Reg)) :
      t₃.getReg r = u₁.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [hp₃ _ (by decide), kt₂ _ (by decide), kt₁ _ (by decide), hp _ (by decide), k₂ _ (by decide)]
  have x25₃ : t₃.getReg .x25 = 101 := by
    rw [rg₃ .x25 (by decide), k₁ .x25 (by decide), h.x25, hlen]; rfl
  have pc₄ := b80003268_pc_not_taken ht₄ (by rw [x25₃]; decide)
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := by rw [kt₄ .x2 (by decide)]; exact sp₃
  obtain ⟨t₅, hrt₅, ht₅⟩ := Sym.BlockSpec.reaches b80003278_spec pc₄ (by
    rv_eval [sp₄]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have kt₅ := b80003278_keeps ht₅
  have m₅ (a : Word) : t₅.getMem a = t₂.getMem a := by
    rw [b80003278_mem_same ht₅, b80003268_mem_same ht₄, m₃]
  have m₄ (a : Word) : t₄.getMem a = t₂.getMem a := by rw [b80003268_mem_same ht₄, m₃]
  have m₃' (a : Word) : t₃.getMem a = t₂.getMem a := m₃ a
  have e1320 : s.getReg .x2 - 2656 + 1320 = s.getReg .x2 - 1344 + 8 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1328 : s.getReg .x2 - 2656 + 1328 = s.getReg .x2 - 1344 + 16 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hlK : vecLen t₂ (s.getReg .x2 - 1344) = 165 := by
    apply BitVec.eq_of_toNat_eq; rw [B₃.kv.len, kapPre_length A k 6 (le_refl 6), kapLen_six]; rfl
  have x11₄ : t₄.getReg .x11 = BK := by rw [b80003268_x11 ht₄, sp₃, e1736, m₃', w8]
  have x12₄ : t₄.getReg .x12 = 0 := by rw [b80003268_x12 ht₄, sp₃, e1744, m₃', w16]
  have x24₄ : t₄.getReg .x24 = 165 := by
    rw [b80003268_x24 ht₄, sp₃, e1328, m₃']; exact hlK
  have hn₅ : heapNext t₅ = heapNext t₂ := by simp only [heapNext, m₅]
  have rg (r : Reg) (hr : r ∈ ([.x2, .x18, .x23, .x25, .x26] : List Reg)) :
      t₅.getReg r = u.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [kt₅ _ (by decide), kt₄ _ (by decide), rg₃ _ (by decide), k₁ _ (by decide)]
  have x9₅ : t₅.getReg .x9 = G := by
    rw [kt₅ .x9 (by decide), kt₄ .x9 (by decide), rg₃ .x9 (by decide)]; exact x9₁
  have gv₅ : ∀ i < 101, t₅.getMem (G + BitVec.ofNat 64 (8 * i)) =
      BitVec.ofNat 64 ((blk 165).getD i 0) := fun i hi ↦ by
    rw [m₅, fr₂.getMem_of (fun x hx hw ↦ by
        simp only [Within] at hx hw; addr_omega [hx, hw, hb1, g2, g3, hhc, hn₂, hi, g4])
      (by addr_omega [g2, g3, hhc, hn₂, hi, g4]), mt₁]
    exact gvt i hi
  refine ⟨t₅, hr₁.trans (hr₂.trans (hr.trans (hrt₁.trans (hrt₂.trans (hrt₃.trans (hrt₄.trans
    hrt₅)))))), Or.inr ⟨b80003278_pc ht₅, G, BK, {
      base := B₃.same hpre m₅ (by rw [rg .x2 (by decide), kt₂ .x2 (by decide), spt₁, sp])
      gal := g1
      glo := gfr
      ghi := by omega
      gvals := gv₅
      bkal := bk1
      bkhi := by rw [hn₅, hn₂']; exact bk3.2
      kp := by rw [b80003278_x10 ht₅, sp₄, e1320, m₄]; simp only [vecPtr, m₅]
      map := {
        pc := b80003278_pc ht₅
        lt := by decide
        x12 := by rw [kt₅ .x12 (by decide), x12₄]; rfl
        x13 := by rw [b80003278_x13 ht₅, x11₄, x12₄]; simp
        x14 := by rw [b80003278_x14 ht₅, kt₄ .x9 (by decide), rg₃ .x9 (by decide), x9₁]; simp
        x15 := by rw [b80003278_x15 ht₅, kt₄ .x25 (by decide), x25₃]; rfl
        regs := fun _ _ ↦ rfl
        fr := Layout.DFrame.refl _ _
        vals := fun i hi ↦ absurd hi (Nat.not_lt_zero _) }
      x9 := x9₅
      x11 := by rw [kt₅ .x11 (by decide)]; exact x11₄
      x24 := by rw [kt₅ .x24 (by decide)]; exact x24₄
      x25 := by rw [rg .x25 (by decide), h.x25, hlen]; rfl
      x18 := by rw [rg .x18 (by decide)]; exact h.x18
      x23 := by rw [rg .x23 (by decide)]; exact h.x23
      x26 := by rw [rg .x26 (by decide)]; exact h.x26 }⟩⟩

/-- At `0x800032b8`, the call of `stack_offsets(block_kappas)`: `blocks` in `G`, `block_kappas`
in `BK` (`x11`, its length `101` in `x12`). -/
structure AtR13 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 : Nat) (G BK : Word) : Prop where
  base : Base12 OI s u A k R Q B lo lo2 lo3
  gal : G.toNat % 8 = 0
  glo : lo3 ≤ G.toNat
  ghi : G.toNat + 808 ≤ BK.toNat
  gvals : ∀ i < 101, u.getMem (G + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 ((blk 165).getD i 0)
  bkal : BK.toNat % 8 = 0
  bkhi : BK.toNat + 808 ≤ heapNext u
  bkvals : ∀ i < 101, u.getMem (BK + BitVec.ofNat 64 (8 * i)) =
    BitVec.ofNat 64 ((kapPre A k 6).getD ((blk 165).getD i 0) 0)
  x9 : u.getReg .x9 = G
  x11 : u.getReg .x11 = BK
  x12 : u.getReg .x12 = 101
  x24 : u.getReg .x24 = 165
  x25 : u.getReg .x25 = 101
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)

/-- The map loop, from `Bk12` to `AtR13`. -/
theorem bkMap {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} {G BK : Word} (hpre : WalkPre s)
    (h : Bk12 OI s u A k R Q B lo lo2 lo3 G BK) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x800032b8 ∧ AtR13 OI s t A k R Q B lo lo2 lo3 G BK := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have Bs := h.base
  obtain ⟨c1, c2, c3, c4⟩ := Bs.kv.bounds (kapPre_ne A k (le_refl 6))
  rw [kapPre_length A k 6 (le_refl 6), kapLen_six] at c4
  have kb := Bs.kbelow
  have hhu := Bs.k11.at11.base.inv.heap.hi
  simp only [heapStart, heapEnd] at c2 hhu
  have gl := h.glo
  have gh := h.ghi
  have bh := h.bkhi
  rw [← h.kp] at c1 c2 c3 kb
  obtain ⟨t, hr, pct, rg, x12, fr, vals⟩ := mapLoop h.gal h.bkal c1 (by omega) c2 gh (by omega)
    (by omega) h.x24 h.gvals _ 0 u rfl h.map
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw; addr_omega [hy, hw, bh, hhu]) (by decide))
  have hv : HeapOk t := ⟨hn ▸ Bs.k11.at11.base.inv.heap.lo, hn ▸ Bs.k11.at11.base.inv.heap.hi⟩
  have B' := Bs.keep hpre fr (fun a ha ↦ by
      simp only [Within] at ha
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hn]; omega⟩))) hv hn.ge
    (rg .x2 (by decide))
  refine ⟨t, hr, pct, {
    base := B'
    gal := h.gal
    glo := gl
    ghi := gh
    gvals := fun i hi ↦ by
      rw [fr.getMem_of (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, gh, gl, hi, bh, hhu])
        (by addr_omega [gh, gl, hi, bh, hhu])]
      exact h.gvals i hi
    bkal := h.bkal
    bkhi := by rw [hn]; exact bh
    bkvals := fun i hi ↦ by
      rw [vals i hi, h.kp]
      exact Bs.kv.vals _ (by rw [kapPre_length A k 6 (le_refl 6), kapLen_six]; exact blk_165_lt i hi)
    x9 := by rw [rg .x9 (by decide)]; exact h.x9
    x11 := by rw [rg .x11 (by decide)]; exact h.x11
    x12 := x12
    x24 := by rw [rg .x24 (by decide)]; exact h.x24
    x25 := by rw [rg .x25 (by decide)]; exact h.x25
    x18 := by rw [rg .x18 (by decide)]; exact h.x18
    x23 := by rw [rg .x23 (by decide)]; exact h.x23
    x26 := by rw [rg .x26 (by decide)]; exact h.x26 }⟩

/-- R12: from `0x800031dc` (`kappas` built) to `stack_offsets`' call at `0x800032b8`. -/
theorem r12 (hAS : AllocSpec) (hTA : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000d628)
    (hRS : ReserveFreshSpec 0x8000d628 8 8)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x800031dc)
    (h : Lat11 OI s u A k R Q B lo lo2 6) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x800032b8 ∧ ∃ G BK, AtR13 OI s t A k R Q B lo lo2 (heapNext u) G BK)) := by
  obtain ⟨t₁, hr₁, hd | ⟨hpc₁, h₁⟩⟩ := blkFilter hAS hRS hpre hpc h
  · exact ⟨t₁, hr₁, Or.inl hd⟩
  obtain ⟨t₂, hr₂, hd | ⟨-, G, BK, h₂⟩⟩ := bkAlloc hTA hRF hpre hpc₁ h₁
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  obtain ⟨t₃, hr₃, hpc₃, h₃⟩ := bkMap hpre h₂
  exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨hpc₃, G, BK, h₃⟩⟩

end Rv64Verifier.Proofs.Walk
