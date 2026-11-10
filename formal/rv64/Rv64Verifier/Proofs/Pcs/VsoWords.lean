import Rv64Verifier.Proofs.Pcs.VsoLevelM

/-!
# `verify_stacked_opening`'s level loop: the leaves as slices

After the Merkle checks (`0x8000b0dc`) the level collects its leaves as `&[K]` slices: a new buffer
of `n` pairs (`try_allocate_in(S - 384, n, 0, 8, 16)`, its pointer kept at `S - 832`), and the loop
at `0x8000b120` copying each path's leaf pointer and length (the path's `8` and `16`) into pair `j`
(`copyLoop`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Pair `i` of the slices at `P` holds path `i`'s leaf pointer and length, as `t0` has them. -/
def Sliced (t t0 : MachineState) (P Q : Word) (j : ℕ) : Prop :=
  ∀ i < j, t.getMem (P + BitVec.ofNat 64 (16 * i)) = t0.getMem (Q + BitVec.ofNat 64 (56 * i + 8)) ∧
    t.getMem (P + BitVec.ofNat 64 (16 * i + 8)) = t0.getMem (Q + BitVec.ofNat 64 (56 * i + 16))

/-- **The copy loop**, from pair `j` at `0x8000b120` to its exit at `0x8000b13c`. -/
theorem copyLoop {P Q : Word} {n : ℕ} (hP : Region P (16 * n)) (hQ : Region Q (56 * n))
    (hPQ : Apart P (16 * n) Q (56 * n)) (t0 : MachineState) :
    ∀ k j (t : MachineState), j + k = n → 0 < k → t.pc = 0x8000b120 →
      t.getReg .x10 = P + BitVec.ofNat 64 (16 * j + 8) →
      t.getReg .x11 = Q + BitVec.ofNat 64 (56 * j + 16) →
      t.getReg .x12 = P + BitVec.ofNat 64 (16 * n + 8) →
      DFrame t0 t (Within · P (16 * n)) → Sliced t t0 P Q j →
      ∃ t', Reaches Image.code t t' ∧ t'.pc = 0x8000b13c ∧ Sliced t' t0 P Q n ∧
        DFrame t0 t' (Within · P (16 * n)) ∧
        ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x15, .x16, .x17, .x18, .x19,
          .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg),
          t'.getReg r = t.getReg r := by
  have hPb := Region.bounds hP
  have hQb := Region.bounds hQ
  intro k
  induction k with
  | zero => intro j t _ h0; omega
  | succ k ih =>
    intro j t hjk _ hpc h10 h11 h12 hfr hcp
    have hj : j < n := by omega
    obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b120_spec hpc (by
      rv_eval [h10, h11]
      and_intros
      · exact Region.valid hP (by addr_omega [hPb, hj]) (by addr_omega [hPb, hj])
          (by addr_omega [hPb, hj])
      · exact Region.valid hP (by addr_omega [hPb, hj]) (by addr_omega [hPb, hj])
          (by addr_omega [hPb, hj])
      · exact Region.valid hQ (by addr_omega [hQb, hj]) (by addr_omega [hQb, hj])
          (by addr_omega [hQb, hj])
      · exact Region.valid hQ (by addr_omega [hQb, hj]) (by addr_omega [hQb, hj])
          (by addr_omega [hQb, hj]))
    have k₁ := b8000b120_keeps h₁
    have f₁ := DFrame.of_memFrame (b8000b120_frame h₁ (by rw [h10]; addr_omega [hPb, hj]))
    rw [h10, show P + BitVec.ofNat 64 (16 * j + 8) - 8 = P + BitVec.ofNat 64 (16 * j) by
      addr_omega [hPb, hj]] at f₁
    have fr₁ : DFrame t0 t₁ (Within · P (16 * n)) :=
      hfr.trans f₁ fun a ha ↦ by addr_omega [ha, hPb, hj]
    have kQ (o : ℕ) (ho : o + 8 ≤ 56 * n) :
        t.getMem (Q + BitVec.ofNat 64 o) = t0.getMem (Q + BitVec.ofNat 64 o) :=
      hfr _ fun i hi hw ↦ by addr_omega [hw, hi, hPQ, hPb, hQb, ho]
    have m0 := b8000b120_m_x10_0 h₁
    have m8 := b8000b120_m_x10_n8 h₁
    rw [h10, h11, show P + BitVec.ofNat 64 (16 * j + 8) - 8 = P + BitVec.ofNat 64 (16 * j) by
      addr_omega [hPb, hj], show Q + BitVec.ofNat 64 (56 * j + 16) - 8 =
        Q + BitVec.ofNat 64 (56 * j + 8) by addr_omega [hQb, hj]] at m8
    rw [h10, h11] at m0
    have cp₁ : Sliced t₁ t0 P Q (j + 1) := fun i hi ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · obtain ⟨e1, e2⟩ := hcp i hi
        refine ⟨?_, ?_⟩
        · rw [← e1]; exact f₁ _ fun x hx hw ↦ by addr_omega [hw, hx, hPb, hj, hi]
        · rw [← e2]; exact f₁ _ fun x hx hw ↦ by addr_omega [hw, hx, hPb, hj, hi]
      · exact ⟨by rw [m8, kQ _ (by omega)], by rw [m0, kQ _ (by omega)]⟩
    have x10₁ : t₁.getReg .x10 = P + BitVec.ofNat 64 (16 * (j + 1) + 8) := by
      rw [b8000b120_x10 h₁, h10]; addr_omega [hPb, hj]
    have x11₁ : t₁.getReg .x11 = Q + BitVec.ofNat 64 (56 * (j + 1) + 16) := by
      rw [b8000b120_x11 h₁, h11]; addr_omega [hQb, hj]
    have x12₁ : t₁.getReg .x12 = P + BitVec.ofNat 64 (16 * n + 8) := by
      rw [k₁ .x12 (by decide), h12]
    by_cases hlast : j + 1 = n
    · have hpc₁ := b8000b120_pc_not_taken h₁ (by rw [h10, h12]; addr_omega [hPb, hlast])
      refine ⟨t₁, hr₁, hpc₁, hlast ▸ cp₁, fr₁, fun r hr ↦ k₁ r hr⟩
    · have hpc₁ := b8000b120_pc_taken h₁ (by
        rw [h10, h12]; intro he
        have := congrArg BitVec.toNat he
        addr_omega [this, hPb, hj, hlast])
      obtain ⟨t', hr', hpc', cp', fr', kr'⟩ := ih (j + 1) t₁ (by omega) (by omega) hpc₁ x10₁ x11₁
        x12₁ fr₁ cp₁
      exact ⟨t', hr₁.trans hr', hpc', cp', fr', fun r hr ↦ (kr' r hr).trans (k₁ r hr)⟩

/-- `try_allocate_in(S - 384, a1, _, 8, 16)`: a buffer of `a1` pairs. -/
theorem callTryAlloc16 (hT : TryAllocZeroedSpec) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x800049ac) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 384) (hx13 : t.getReg .x13 = 8)
    (hx14 : t.getReg .x14 = 16) (hheap : HeapOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      (v.getMem (s.getReg .x2 - 384) = 0 → v.getMem (s.getReg .x2 - 376) = t.getReg .x11 ∧
        NewBuf t v (v.getMem (s.getReg .x2 - 368)) ((t.getReg .x11).toNat * 16) 8) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 1088) 48 ∨
        Within a nextAddr 8 ∨ Fresh t v a)) := by
  have hst := hpre.stack
  have hb := bounds hpre
  have hsl : stackLo t tryAllocStack = s.getReg .x2 - 1088 := by
    simp only [stackLo, tryAllocStack, hsp]; rv_eval []
  have hnx := hst.next
  have hab := hst.above
  simp only [vso_stack] at hnx hab
  have hpreT : TryAllocPre .x13 .x14 t := {
    heap := hheap
    out := by rw [hx10]; valid_sub hst.valid [hb]
    align := by rw [hx13]; decide
    size := by rw [hx14]; decide
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx, hb]⟩
    outStack := by rw [hx10, hsl]; addr_omega [hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, -⟩ | hdead⟩ := hT.call (Reaches.refl t) hpc hpreT
  · have hok := hpost.ok
    have hfr := DFrame.of_byteFrame hpost.frame
    rw [hx10, hx14, hx13] at hok
    rw [hx10, hsl] at hfr
    refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, fun h0 ↦ ?_, hfr⟩⟩
    obtain ⟨h1, h2⟩ := hok h0
    rw [show s.getReg .x2 - 384 + 8 = s.getReg .x2 - 376 by rv_eval []] at h1
    rw [show s.getReg .x2 - 384 + 16 = s.getReg .x2 - 368 by rv_eval [],
      show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl] at h2
    exact ⟨h1, h2⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- At `0x8000b13c`, from `m` at `0x8000b0dc`: pair `j` of the new buffer at `S - 832` holds path
`j`'s leaf pointer and length. -/
structure Slices (s m t : MachineState) : Prop where
  pc : t.pc = 0x8000b13c
  sp : t.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s t (t.getMem nextAddr)
  fr : DFrame m t fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 1088) 48 ∨
    Within a (s.getReg .x2 - 832) 8 ∨ Within a nextAddr 8 ∨ Fresh m t a
  heap : HeapOk t
  mono : heapNext m ≤ heapNext t
  regs : ∀ r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
    t.getReg r = m.getReg r
  buf : NewBuf m t (t.getMem (s.getReg .x2 - 832)) (16 * (m.getReg .x20).toNat) 8
  sliced : Sliced t m (t.getMem (s.getReg .x2 - 832)) (m.getReg .x22) (m.getReg .x20).toNat

/-- **The slices**, from `0x8000b0dc` to `0x8000b13c`, or a dead end (an allocation failure). -/
theorem slices (hT : TryAllocZeroedSpec) {s m : MachineState} {lo : ℕ} (hpre : VsoPre s)
    (hpc : m.pc = 0x8000b0dc) (hsp : m.getReg .x2 = s.getReg .x2 - 1040)
    (hinv : InvR s m (m.getMem nextAddr)) (hlo : lo ≤ heapNext m)
    (hQ : (m.getReg .x20).toNat = 0 ∨ Region (m.getReg .x22) (56 * (m.getReg .x20).toNat) ∧
      Clear s lo (m.getReg .x22) (56 * (m.getReg .x20).toNat)) :
    ∃ t, Reaches Image.code m t ∧ (Dead Image.code t ∨ Slices s m t) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsm := stack_mapped hpre
  have hmh := hinv.heap hpre.heap
  have hmlo : heapNext s ≤ heapNext m := hinv.mono
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b0dc_spec hpc trivial
  have k₁ := b8000b0dc_keeps h₁
  have hm₁ := b8000b0dc_mem_same h₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₁ .x2 (by decide), hsp]
  have hn₁ : heapNext t₁ = heapNext m := by simp only [heapNext, hm₁]
  obtain ⟨t₂, hr₂, hv₂⟩ := callTryAlloc16 hT hpre (b8000b0dc_pc h₁) sp₁
    (by rw [b8000b0dc_x10 h₁, hsp]; rv_eval []) (b8000b0dc_x13 h₁) (b8000b0dc_x14 h₁)
    ⟨by rw [hn₁]; exact hmh.lo, by rw [hn₁]; exact hmh.hi⟩
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, hok₂, X₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres₂ .x2 (by decide), sp₁]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000b0f8_spec
    (by rw [hpc₂, returnAddress_eq, b8000b0dc_x1 h₁]; decide) (by
      rv_eval [sp₂]; valid_access hst.valid [hb])
  have q656 : t₂.getMem (t₂.getReg .x2 + 656) = t₂.getMem (s.getReg .x2 - 384) := by
    rw [sp₂]; rv_eval []
  by_cases hok : t₂.getMem (s.getReg .x2 - 384) = 0
  swap
  · have hpc₃ := b8000b0f8_pc_taken h₃ (by rw [q656]; exact hok)
    exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl (dead_of_fetch (by rw [hpc₃]; exact trap))⟩
  have hpc₃ := b8000b0f8_pc_not_taken h₃ (by rw [q656]; exact hok)
  obtain ⟨-, hnew⟩ := hok₂ hok
  rw [b8000b0dc_x11 h₁] at hnew
  have k₃ := b8000b0f8_keeps h₃
  have hm₃ := b8000b0f8_mem_same h₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₃ .x2 (by decide), sp₂]
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000b100_spec hpc₃ (by
    rv_eval [sp₃]; and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000b100_keeps h₄
  have f₄ := DFrame.of_memFrame (b8000b100_frame h₄ (by rw [sp₃]; addr_omega [hb]))
  rw [sp₃, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by rv_eval []] at f₄
  have m208 := b8000b100_m_x2_208 h₄
  rw [sp₃] at m208
  rv_eval [hm₃] at m208
  set P := t₂.getMem (s.getReg .x2 - 368) with hPd
  set n := (m.getReg .x20).toNat with hnd
  set Q := m.getReg .x22 with hQd
  have reg₄ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : t₄.getReg r = m.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k₄ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide),
      k₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide),
      hpres₂ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide),
      k₁ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide)]
  have hhi₂ := hheap₂.hi
  have hP1 : P.toNat % 8 = 0 := hnew.1
  have hP2 : n * 16 = 0 ∨ heapNext m ≤ P.toNat ∧ P.toNat + n * 16 ≤ heapNext t₂ := by
    rw [← hn₁]; exact hnew.2
  -- the frame from `m` to the copy's start
  have X₄ : DFrame m t₄ fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
      Within a (s.getReg .x2 - 1088) 48 ∨ Within a (s.getReg .x2 - 832) 8 ∨ Within a nextAddr 8 ∨
      Fresh m t₂ a :=
    (((DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · simp only [Fresh] at ha ⊢; rw [hn₁] at ha
          exact Or.inr (Or.inr (Or.inr (Or.inr ha)))).trans
      (DFrame.of_same hm₃ fun _ ↦ False) fun _ h ↦ h.elim).trans f₄ fun a ha ↦ Or.inr (Or.inr (Or.inl ha))
  have nx₄ : t₄.getMem nextAddr = t₂.getMem nextAddr := by
    rw [f₄ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx], hm₃]
  -- the path's words, kept
  have kQ {t : MachineState} (hX : DFrame m t fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
      Within a (s.getReg .x2 - 1088) 48 ∨ Within a (s.getReg .x2 - 832) 8 ∨ Within a nextAddr 8 ∨
      Fresh m t₂ a) (hn0 : n ≠ 0) (o : ℕ) (ho : o + 8 ≤ 56 * n) :
      t.getMem (Q + BitVec.ofNat 64 o) = m.getMem (Q + BitVec.ofNat 64 o) := by
    rcases hQ with h0 | ⟨hQr, ⟨hq1, hq2, hq3⟩, -⟩
    · exact absurd h0 hn0
    have hQb := Region.bounds hQr
    refine hX _ fun i hi hw ↦ ?_
    rcases hw with hw | hw | hw | hw | hw
    · addr_omega [hw, hi, hq2, hQb, ho, hb]
    · addr_omega [hw, hi, hq2, hQb, ho, hb]
    · addr_omega [hw, hi, hq2, hQb, ho, hb]
    · addr_omega [hw, hi, hq3, hQb, ho]
    · simp only [Fresh] at hw
      rcases hq1 with h | h
      · addr_omega [hw.1, hi, h, hlo, hQb, ho]
      · addr_omega [hw.2, hi, h, hhi₂, hQb, ho]
  -- the end, from any state the copy reaches
  have fin (t : MachineState) (hr : Reaches Image.code m t) (hpc : t.pc = 0x8000b13c)
      (hsp' : t.getReg .x2 = s.getReg .x2 - 1040) (hfr : DFrame t₄ t (Within · P (16 * n)))
      (hreg : ∀ r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
        t.getReg r = t₄.getReg r) (hsl : Sliced t m P Q n) :
      ∃ t, Reaches Image.code m t ∧ (Dead Image.code t ∨ Slices s m t) := by
    have hPm : ∀ y, Within y P (16 * n) → ¬ Within y nextAddr 8 ∧
        ¬ Within y (s.getReg .x2 - 832) 8 := fun y hy ↦ by
      rcases hP2 with h0 | ⟨h1, h2⟩
      · simp only [Within] at hy; omega
      · exact ⟨by addr_omega [hy, h2, hhi₂], by addr_omega [hy, h2, hhi₂, hsm]⟩
    have nx : t.getMem nextAddr = t₂.getMem nextAddr := by
      rw [hfr _ fun i hi hw ↦ (hPm _ hw).1 (by addr_omega [hi]), nx₄]
    have hn : heapNext t = heapNext t₂ := by simp only [heapNext, nx]
    have P832 : t.getMem (s.getReg .x2 - 832) = P := by
      rw [hfr _ fun i hi hw ↦ (hPm _ hw).2 (by addr_omega [hi, hb]), m208]
    have X' : DFrame m t fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
        Within a (s.getReg .x2 - 1088) 48 ∨ Within a (s.getReg .x2 - 832) 8 ∨
        Within a nextAddr 8 ∨ Fresh m t₂ a :=
      X₄.trans hfr fun a ha ↦ by
        rcases hP2 with h0 | ⟨h1, h2⟩
        · simp only [Within] at ha; omega
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, h1], by addr_omega [ha, h2]⟩)))
    have X : DFrame m t fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
        Within a (s.getReg .x2 - 1088) 48 ∨ Within a (s.getReg .x2 - 832) 8 ∨
        Within a nextAddr 8 ∨ Fresh m t a :=
      X'.mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · simp only [Fresh] at ha ⊢; rw [hn]; exact Or.inr (Or.inr (Or.inr (Or.inr ha)))
    have hheap : HeapOk t := ⟨by rw [hn]; exact hheap₂.lo, by rw [hn]; exact hhi₂⟩
    have hmono : heapNext m ≤ heapNext t := by rw [hn, ← hn₁]; exact hmono₂
    refine ⟨t, hr, Or.inr {
      pc := hpc
      sp := hsp'
      inv := Inv.step' hpre hinv X (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hmono hheap.hi
        (by rw [hsp', hsp])
      fr := X
      heap := hheap
      mono := hmono
      regs := fun r hr ↦ (hreg r hr).trans (reg₄ r hr)
      buf := by
        rw [P832]
        refine ⟨hP1, ?_⟩
        rcases hP2 with h0 | ⟨h1, h2⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨h1, by rw [hn]; omega⟩
      sliced := by rw [P832]; exact hsl }⟩
    · rcases ha with ha | ha | ha | ha | ha
      · exact frame_wr hpre (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
      · exact frame_wr hpre (by addr_omega [ha, hb])
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapNext] at ha; exact ha.2⟩))
    · rcases ha with ha | ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx]
      · simp only [Fresh, heapNext] at ha; addr_omega [ha.2, hb, hheap.hi]
  by_cases hz : n = 0
  · have hpc₄ := b8000b100_pc_taken h₄ (by
      rw [k₃ .x20 (by decide), hpres₂ .x20 (by decide), k₁ .x20 (by decide)]
      exact BitVec.eq_of_toNat_eq hz)
    exact fin t₄ (hr₁.trans (hr₂.trans (hr₃.trans hr₄))) hpc₄ (by rw [k₄ .x2 (by decide), sp₃])
      (DFrame.refl _ _) (fun _ _ ↦ rfl) fun i hi ↦ absurd hi (by omega)
  have hpc₄ := b8000b100_pc_not_taken h₄ (by
    rw [k₃ .x20 (by decide), hpres₂ .x20 (by decide), k₁ .x20 (by decide)]
    intro h; exact hz (by rw [hnd, h]; rfl))
  obtain ⟨hQr, hQc⟩ : Region Q (56 * n) ∧ Clear s lo Q (56 * n) := by
    rcases hQ with h0 | h0
    · exact absurd h0 hz
    · exact h0
  have hQb := Region.bounds hQr
  obtain ⟨h1, h2⟩ : heapNext m ≤ P.toNat ∧ P.toNat + n * 16 ≤ heapNext t₂ := by
    rcases hP2 with h0 | h0
    · omega
    · exact h0
  have hhs := hmh.lo
  have hPr : Region P (16 * n) :=
    heap_region (by simp only [heapStart] at hhs; omega) (by omega) hP1
  have hPb := Region.bounds hPr
  have hPQ : Apart P (16 * n) Q (56 * n) := by
    obtain ⟨⟨hq1, -, -⟩, -⟩ := hQc
    simp only [Apart]
    rcases hq1 with h | h
    · omega
    · simp only [heapEnd] at h hhi₂; omega
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₄ .x2 (by decide), sp₃]
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000b10c_spec hpc₄ (by
    rv_eval [sp₄]; valid_access hst.valid [hb])
  have k₅ := b8000b10c_keeps h₅
  have hm₅ := b8000b10c_mem_same h₅
  have e208 : t₄.getMem (t₄.getReg .x2 + 208) = P := by
    rw [sp₄, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by rv_eval [], m208]
  have e20 : t₄.getReg .x20 = BitVec.ofNat 64 n := by
    rw [reg₄ .x20 (by decide)]; exact ofNat_toNat_eq rfl
  have x10₅ : t₅.getReg .x10 = P + BitVec.ofNat 64 (16 * 0 + 8) := by
    rw [b8000b10c_x10 h₅, e208]; rfl
  have x11₅ : t₅.getReg .x11 = Q + BitVec.ofNat 64 (56 * 0 + 16) := by
    rw [b8000b10c_x11 h₅, reg₄ .x22 (by decide)]; rfl
  have x12₅ : t₅.getReg .x12 = P + BitVec.ofNat 64 (16 * n + 8) := by
    rw [b8000b10c_x12 h₅, e208, e20]; addr_omega [hPb]
  obtain ⟨t', hr', hpc', sl', fr', kr'⟩ := copyLoop hPr hQr hPQ t₅ n 0 t₅ (by omega) (by omega)
    (b8000b10c_pc h₅) x10₅ x11₅ x12₅ (DFrame.refl _ _) fun i hi ↦ absurd hi (Nat.not_lt_zero _)
  have kQ' (o : ℕ) (ho : o + 8 ≤ 56 * n) :
      t₅.getMem (Q + BitVec.ofNat 64 o) = m.getMem (Q + BitVec.ofNat 64 o) := by
    rw [hm₅]; exact kQ X₄ hz o ho
  refine fin t' (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr'))))) hpc'
    (by rw [kr' .x2 (by decide), k₅ .x2 (by decide), sp₄])
    ((DFrame.of_same hm₅ (Within · P (16 * n))).trans fr' fun _ h ↦ h) (fun r hr ↦ ?_)
    fun i hi ↦ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [kr' r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide),
      k₅ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide)]
  · obtain ⟨e1, e2⟩ := sl' i hi
    exact ⟨by rw [e1, kQ' _ (by omega)], by rw [e2, kQ' _ (by omega)]⟩

/-- **After the Merkle checks, the slices**: the leaves of the phase the checks read. -/
theorem Merkled.toSlices (hT : TryAllocZeroedSpec) {s : MachineState} {x : LCtx}
    {h t u v w m : MachineState} {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs) :
    ∃ t', Reaches Image.code m t' ∧ (Dead Image.code t' ∨ Slices s m t') := by
  have hP := (hm.mi.phase hm.mo.hdr).paths
  unfold BufOk at hP
  rw [← hm.mo.x20, ← hm.mo.x22] at hP
  exact slices hT hpre hm.mo.pc hm.mo.sp hm.mo.inv hm.mo.mono hP

end Rv64Verifier.Proofs.Pcs.Vso
