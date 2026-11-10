import Rv64Verifier.Proofs.Pcs.VsoGlueRootsBase

/-!
# `verify_stacked_opening`'s final level: the subspace roots, set up

`0x8000bbb0` keeps the queries' and their weights' pointers at `S - 856` and `S - 824` and their
counts in `s7` and `s3`, and allocates the roots' buffer (`Bump::alloc(8, 8)`, a trap on null);
`0x8000bbdc` makes `vec![K(1)]` at `S - 128` and calls `try_allocate_in(S - 464, n, 0, 8, 8)` for
the layer, a trap on `Err`; `0x8000bc18` moves the layer's `RawVec` to `S - 160`, length `0`, keeps
the point's length and the fold start at `S - 816` and `S - 808`, and branches on `n = 0` (`RA`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- After `0x8000bc18`: the roots `[1]` at `R` (a `Vec` at `S - 128`), the layer's buffer at `L`
(a `Vec` of capacity `n` and length `0` at `S - 160`). -/
structure RA (s v w t : MachineState) (a : Word) (n : ℕ) (R L : Word) : Prop where
  pf : RPF s v w t
  pc : t.pc = if n = 0 then 0x8000bc38 else 0x8000bc50
  x19 : t.getReg .x19 = w.getMem (a + 40)
  x21 : t.getReg .x21 = R
  x23 : t.getReg .x23 = w.getMem (a + 16)
  x26 : t.getReg .x26 = BitVec.ofNat 64 n
  m856 : t.getMem (s.getReg .x2 - 856) = w.getMem (a + 8)
  m824 : t.getMem (s.getReg .x2 - 824) = w.getMem (a + 32)
  m816 : t.getMem (s.getReg .x2 - 816) = w.getReg .x18
  m808 : t.getMem (s.getReg .x2 - 808) = w.getReg .x9
  hn : (w.getReg .x18).toNat = (w.getReg .x9).toNat + n
  keep : ∀ y, GK s y → t.getMem y = w.getMem y
  m128 : t.getMem (s.getReg .x2 - 128) = 1
  m120 : t.getMem (s.getReg .x2 - 120) = R
  m112 : t.getMem (s.getReg .x2 - 112) = 1
  r0 : t.getMem R = 1
  Rb : R.toNat % 8 = 0 ∧ heapNext w ≤ R.toNat ∧ R.toNat + 8 ≤ heapNext t
  m160 : t.getMem (s.getReg .x2 - 160) = BitVec.ofNat 64 n
  m152 : t.getMem (s.getReg .x2 - 152) = L
  m144 : t.getMem (s.getReg .x2 - 144) = 0
  Lb : n = 0 ∨ L.toNat % 8 = 0 ∧ R.toNat + 8 ≤ L.toNat ∧ L.toNat + 8 * n ≤ heapNext t

/-- `try_allocate_in(S - 464, a1, _, 8, 8)`: a buffer of `a1` words. -/
theorem callTryAlloc464 (hT : TryAllocZeroedSpec) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x800049ac) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 464) (hx13 : t.getReg .x13 = 8)
    (hx14 : t.getReg .x14 = 8) (hheap : HeapOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      (v.getMem (s.getReg .x2 - 464) = 0 → v.getMem (s.getReg .x2 - 456) = t.getReg .x11 ∧
        NewBuf t v (v.getMem (s.getReg .x2 - 448)) ((t.getReg .x11).toNat * 8) 8) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x2 - 1088) 48 ∨
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
    rw [show s.getReg .x2 - 464 + 8 = s.getReg .x2 - 456 by rv_eval []] at h1
    rw [show s.getReg .x2 - 464 + 16 = s.getReg .x2 - 448 by rv_eval [],
      show (8 : Word).toNat = 8 from rfl] at h2
    exact ⟨h1, h2⟩
  · exact ⟨v, hr, Or.inl hdead⟩

set_option maxHeartbeats 1000000 in
/-- **The roots' set-up**: `0x8000bbb0` to the branch on `n = 0`. -/
theorem rootsSetup (hA : AllocSpec) (hT : TryAllocZeroedSpec) {s v w : MachineState} {a : Word}
    {n : ℕ} (hpre : VsoPre s) (h : QA s v w a n) :
    ∃ t, Reaches Image.code w t ∧ (Dead Image.code t ∨ ∃ R L, RA s v w t a n R L) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have hsp := h.gs.sp
  obtain ⟨ha1, ha2, ha8⟩ := h.claim
  have hhv := h.gs.heap.hi
  have hvw := h.gs.mono
  have hhs := hpre.heap.lo
  simp only [heapEnd] at hhv
  have hR : Region a 88 := heap_region (by simp only [heapStart, heapNext] at hhs ha1 ⊢; omega)
    (by simp only [heapEnd]; omega) ha8
  have P₀ := RPF.init h.gs
  -- `0x8000bbb0`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bbb0_spec h.pc (by
    rv_eval [hsp, h.x8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hR (by addr_omega [ha2, hhv]) (by addr_omega [ha2, hhv])
          (by addr_omega [ha2, hhv, ha8])
      | addr_omega [ha2, hhv, hvw, hab, hb])
  have k₁ := b8000bbb0_keeps h₁
  have F₁ : DFrame w t₁ fun y ↦ Within y (s.getReg .x2 - 856) 8 ∨ Within y (s.getReg .x2 - 824) 8 :=
    (holds_dframe h₁).mono fun y ⟨k, hk, hw⟩ ↦ by
      simp only [b8000bbb0, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [hsp] at hw
      · exact Or.inr (by addr_omega [hw, hb])
      · exact Or.inl (by addr_omega [hw, hb])
  obtain ⟨P₁, n₁⟩ := P₀.stepS hpre F₁ (fun y hy ↦ by
    rcases hy with hy | hy <;> exact Or.inr (Or.inl (by addr_omega [hy, hb]))) (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₁.sp
  -- `Bump::alloc(8, 8)`
  obtain ⟨t₂, r₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd₂⟩ := hA.call (Reaches.refl t₁) (b8000bbb0_pc h₁)
    ⟨P₁.heap, by rw [b8000bbb0_x10 h₁]; decide⟩
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd₂⟩
  have hR8 := hpost₂.aligned
  have hRa := hpost₂.above
  have hRn := hpost₂.next
  rw [b8000bbb0_x10 h₁] at hR8
  rw [b8000bbb0_x11 h₁] at hRn
  change _ % 8 = 0 at hR8
  change heapNext t₂ = _ + 8 at hRn
  generalize hRdef : t₂.getReg .x10 = R at hR8 hRa hRn
  have F₂ : DFrame t₁ t₂ fun y ↦ Within y nextAddr 8 := fun y hy ↦ hpost₂.mem y fun he ↦
    hy 0 (by decide) (by rw [he, add_ofNat_zero]; simp only [Within]; omega)
  have P₂ := P₁.step hpre F₂ (fun y hy ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hy))))))
    hpost₂.heap (by omega) (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₂.sp
  have hh₂ := P₂.heap.hi
  simp only [heapEnd] at hh₂
  -- `0x8000bbd8`, a trap on null
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000bbd8_spec
    (by rw [hpc₂, returnAddress_eq, b8000bbb0_x1 h₁]; decide) trivial
  by_cases hz : R = 0
  · refine ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl (dead_of_fetch ?_)⟩
    rw [b8000bbd8_pc_taken h₃ (by rw [hRdef, hz])]
    exact trap
  have P₃ := P₂.same hpre (b8000bbd8_mem_same h₃) (b8000bbd8_keeps h₃ .x2 (by decide))
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₃.sp
  have x10₃ : t₃.getReg .x10 = R := by rw [b8000bbd8_keeps h₃ .x10 (by decide), hRdef]
  have hRlo : 0x20 ≤ R.toNat := by
    have := hpre.heap.lo; have := P₁.wt; have := P₁.sw
    simp only [heapStart] at *; omega
  have hRR : Region R 8 := heap_region hRlo (by simp only [heapEnd]; omega) hR8
  -- `0x8000bbdc`: `vec![K(1)]`, `try_allocate_in`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000bbdc_spec (b8000bbd8_pc_not_taken h₃
    (by rw [hRdef]; exact hz)) (by
      rv_eval [sp₃, x10₃]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hRR (by addr_omega [hRn, hh₂]) (by addr_omega [hRn, hh₂])
            (by addr_omega [hRn, hh₂, hR8])
        | addr_omega [hRn, hh₂, hab, hb])
  have k₄ := b8000bbdc_keeps h₄
  have F₄ : DFrame t₃ t₄ fun y ↦ Within y R 8 ∨ Within y (s.getReg .x2 - 128) 24 :=
    (holds_dframe h₄).mono fun y ⟨k, hk, hw⟩ ↦ by
      simp only [b8000bbdc, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rv_eval [sp₃, x10₃] at hw
      all_goals first
        | exact Or.inl hw
        | exact Or.inr (by addr_omega [hw, hb])
  have n₄ : t₄.getMem nextAddr = t₃.getMem nextAddr := F₄ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hRn, hh₂]
    · addr_omega [hw, hi, hb, hnx]
  have hn₄ : heapNext t₄ = heapNext t₂ := by
    simp only [heapNext, n₄, b8000bbd8_mem_same h₃]
  have P₄ := P₃.step hpre F₄ (fun y hy ↦ by
      rcases hy with hy | hy
      · exact glw_heap (by have := P₁.wt; simp only [Within] at hy; omega)
          (by have : (t₄.getMem nextAddr).toNat = heapNext t₄ := rfl; simp only [Within] at hy; omega)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb])))))
    ⟨by rw [hn₄]; exact P₂.heap.lo, by rw [hn₄]; exact P₂.heap.hi⟩
    (by rw [hn₄, ← hn₄]; simp only [heapNext, n₄]; exact Nat.le_refl _) (k₄ .x2 (by decide))
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₄.sp
  have x11₄ : t₄.getReg .x11 = BitVec.ofNat 64 n := by
    rw [b8000bbdc_x11 h₄, b8000bbd8_keeps h₃ .x26 (by decide), hpres₂ .x26 (by decide),
      k₁ .x26 (by decide), h.x26]
  obtain ⟨t₅, r₅, hv₅⟩ := callTryAlloc464 hT hpre (b8000bbdc_pc h₄) sp₄
    (by rw [b8000bbdc_x10 h₄, sp₃]; rv_eval []) (b8000bbdc_x13 h₄) (b8000bbdc_x14 h₄) P₄.heap
  rcases hv₅ with hd₅ | ⟨hpc₅, hpres₅, hheap₅, hmono₅, hok₅, F₅⟩
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl hd₅⟩
  have P₅ := P₄.step hpre F₅ (fun y hy ↦ by
      rcases hy with hy | hy | hy | hy
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hy)))))
      · exact glw_heap (by have := P₄.wt; simp only [Fresh] at hy; omega) hy.2)
    hheap₅ hmono₅ (hpres₅ .x2 (by decide))
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₅.sp
  -- `0x8000bc10`, a trap on `Err`
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b8000bc10_spec
    (by rw [hpc₅, returnAddress_eq, b8000bbdc_x1 h₄]; decide) (by
      rv_eval [sp₅]; valid_access hst.valid [hb])
  by_cases he : t₅.getMem (s.getReg .x2 - 464) = 0
  swap
  · refine ⟨t₆, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆)))), Or.inl (dead_of_fetch ?_)⟩
    rw [b8000bc10_pc_taken h₆ (by rv_eval [sp₅]; exact he)]
    exact trap
  have pc₆ := b8000bc10_pc_not_taken h₆ (by rv_eval [sp₅]; exact he)
  obtain ⟨hcap, hnb⟩ := hok₅ he
  rw [x11₄] at hcap hnb
  have hm₆ := b8000bc10_mem_same h₆
  have P₆ := P₅.same hpre hm₆ (b8000bc10_keeps h₆ .x2 (by decide))
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₆.sp
  -- `0x8000bc18`
  obtain ⟨t₇, r₇, h₇⟩ := Sym.BlockSpec.reaches b8000bc18_spec pc₆ (by
    rv_eval [sp₆]; and_intros <;> valid_access hst.valid [hb])
  have k₇ := b8000bc18_keeps h₇
  have F₇ : DFrame t₆ t₇ fun y ↦ Within y (s.getReg .x2 - 816) 16 ∨
      Within y (s.getReg .x2 - 160) 24 :=
    (holds_dframe h₇).mono fun y ⟨k, hk, hw⟩ ↦ by
      simp only [b8000bc18, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> rv_eval [sp₆] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (by addr_omega [hw, hb])
  obtain ⟨P₇, n₇⟩ := P₆.stepS hpre F₇ (fun y hy ↦ by
    rcases hy with hy | hy
    · exact Or.inr (Or.inl (by addr_omega [hy, hb]))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb]))))) (k₇ .x2 (by decide))
  -- what the steps kept
  have hh₅ := hheap₅.hi
  simp only [heapEnd] at hh₅
  have hm₃ := b8000bbd8_mem_same h₃
  have k01 (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 856).toNat ∨
      (s.getReg .x2 - 848).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 824).toNat ∨
      (s.getReg .x2 - 816).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₁.getMem y = w.getMem y :=
    F₁ y fun i hi hw ↦ by rcases hw with hw | hw <;> rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb]
  have k14 (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 128).toNat ∨
      (s.getReg .x2 - 104).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₄.getMem y = t₁.getMem y := by
    rw [F₄ y fun i hi hw ↦ by
        rcases hw with hw | hw <;> rcases hy with hy | hy
        all_goals first | addr_omega [hw, hi, hy, hb] | addr_omega [hw, hi, hy, hb, hRn, hh₂, hab],
      hm₃, F₂ y fun i hi hw ↦ by rcases hy with hy | hy <;> addr_omega [hw, hi, hy, hb, hnx]]
  have k47 (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 816).toNat ∨
      (s.getReg .x2 - 800).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat ∨
      (s.getReg .x2 - 440).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 160).toNat ∨
      (s.getReg .x2 - 136).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₇.getMem y = t₄.getMem y := by
    rw [F₇ y fun i hi hw ↦ by
        rcases hw with hw | hw <;> rcases hy with hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb],
      hm₆, F₅ y fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw <;> rcases hy with hy | hy | hy | hy
        all_goals first
          | addr_omega [hw, hi, hy, hb]
          | addr_omega [hw, hi, hy, hb, hnx]
          | (simp only [Fresh] at hw; addr_omega [hw.2, hi, hy, hb, hh₅, hab])]
  have kR : t₇.getMem R = t₄.getMem R := by
    rw [F₇ R fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hRn, hh₂, hab],
      hm₆, F₅ R fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw
        · addr_omega [hw, hi, hb, hRn, hh₂, hab]
        · addr_omega [hw, hi, hb, hRn, hh₂, hab]
        · addr_omega [hw, hi, hRn, hh₂]
        · simp only [Fresh] at hw; rw [hn₄] at hw; addr_omega [hw.1, hi, hRn]]
  -- registers
  have x18₆ : t₆.getReg .x18 = w.getReg .x18 := by
    rw [b8000bc10_keeps h₆ .x18 (by decide), hpres₅ .x18 (by decide), k₄ .x18 (by decide),
      b8000bbd8_keeps h₃ .x18 (by decide), hpres₂ .x18 (by decide), k₁ .x18 (by decide)]
  have x9₆ : t₆.getReg .x9 = w.getReg .x9 := by
    rw [b8000bc10_keeps h₆ .x9 (by decide), hpres₅ .x9 (by decide), k₄ .x9 (by decide),
      b8000bbd8_keeps h₃ .x9 (by decide), hpres₂ .x9 (by decide), k₁ .x9 (by decide)]
  have hn := h.x18
  have L₇ : t₇.getMem (s.getReg .x2 - 152) = t₅.getMem (s.getReg .x2 - 448) := by
    have := b8000bc18_m_x2_888 h₇; rw [sp₆] at this; rv_eval [] at this; rw [this, hm₆]
  have hn₇ : heapNext t₇ = heapNext t₅ := by simp only [heapNext, n₇, hm₆]
  have hn₅ := hmono₅
  refine ⟨t₇, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans r₇))))), Or.inr
    ⟨R, t₅.getMem (s.getReg .x2 - 448), {
    pf := P₇
    pc := by
      by_cases h0 : n = 0
      · simp only [h0, ↓reduceIte]
        exact b8000bc18_pc_not_taken h₇ (by
          rw [x18₆, x9₆]; apply BitVec.eq_of_toNat_eq; omega)
      · simp only [h0, ↓reduceIte]
        exact b8000bc18_pc_taken h₇ (by
          rw [x18₆, x9₆]; intro he; have := congrArg BitVec.toNat he; omega)
    x19 := by
      rw [k₇ .x19 (by decide), b8000bc10_keeps h₆ .x19 (by decide), hpres₅ .x19 (by decide),
        k₄ .x19 (by decide), b8000bbd8_keeps h₃ .x19 (by decide), hpres₂ .x19 (by decide),
        b8000bbb0_x19 h₁, h.x8]
    x21 := by
      rw [k₇ .x21 (by decide), b8000bc10_keeps h₆ .x21 (by decide), hpres₅ .x21 (by decide),
        b8000bbdc_x21 h₄, x10₃]
    x23 := by
      rw [k₇ .x23 (by decide), b8000bc10_keeps h₆ .x23 (by decide), hpres₅ .x23 (by decide),
        k₄ .x23 (by decide), b8000bbd8_keeps h₃ .x23 (by decide), hpres₂ .x23 (by decide),
        b8000bbb0_x23 h₁, h.x8]
    x26 := by
      rw [k₇ .x26 (by decide), b8000bc10_keeps h₆ .x26 (by decide), hpres₅ .x26 (by decide),
        k₄ .x26 (by decide), b8000bbd8_keeps h₃ .x26 (by decide), hpres₂ .x26 (by decide),
        k₁ .x26 (by decide), h.x26]
    m856 := by
      rw [k47 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        k14 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]
      have := b8000bbb0_m_x2_184 h₁; rw [hsp, h.x8] at this; rv_eval [] at this; exact this
    m824 := by
      rw [k47 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        k14 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]
      have := b8000bbb0_m_x2_216 h₁; rw [hsp, h.x8] at this; rv_eval [] at this; exact this
    m816 := by
      have := b8000bc18_m_x2_224 h₇; rw [sp₆, x18₆] at this; rv_eval [] at this; exact this
    m808 := by
      have := b8000bc18_m_x2_232 h₇; rw [sp₆, x9₆] at this; rv_eval [] at this; exact this
    hn := hn
    keep := fun y hy ↦ by
      simp only [GK] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (rw [k47 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
            k14 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
            k01 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)])
        | (rw [k47 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
            k14 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
            k01 _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))])
        | (rw [k47 _ (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))),
            k14 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
            k01 _ (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩))])
    m128 := by
      rw [k47 _ (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)))]
      have := b8000bbdc_m_x2_912 h₄; rw [sp₃] at this; rv_eval [] at this; exact this
    m120 := by
      rw [k47 _ (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)))]
      have := b8000bbdc_m_x2_920 h₄; rw [sp₃, x10₃] at this; rv_eval [] at this; exact this
    m112 := by
      rw [k47 _ (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)))]
      have := b8000bbdc_m_x2_928 h₄; rw [sp₃] at this; rv_eval [] at this; exact this
    r0 := by
      rw [kR]; have := b8000bbdc_m_x10_0 h₄; rw [x10₃] at this; exact this
    Rb := ⟨hR8, by have := P₁.wt; omega, by have := hmono₅; rw [hn₄] at this; omega⟩
    m160 := by
      have := b8000bc18_m_x2_880 h₇; rw [sp₆] at this; rv_eval [] at this
      rw [this, hm₆]; exact hcap
    m152 := L₇
    m144 := by have := b8000bc18_m_x2_896 h₇; rw [sp₆] at this; rv_eval [] at this; exact this
    Lb := by
      by_cases h0 : n = 0
      · exact Or.inl h0
      right
      have hnn : (BitVec.ofNat 64 n).toNat = n := by
        rw [BitVec.toNat_ofNat]; have := (w.getReg .x18).isLt; omega
      obtain ⟨hL8, hLb⟩ := hnb
      rw [hnn] at hLb
      rcases hLb with hz' | hz'
      · omega
      · rw [hn₄] at hz'; exact ⟨hL8, by omega, by omega⟩ }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
