import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Blocks.F68

/-!
# `verifier::multilinear::selector_point`

```rust
fn selector_point(selector: u64, length: usize) -> Vec<E> {
    (0..length).map(|bit| E::new(selector >> bit & 1, 0, 0)).collect()
}
```

compiled at `0x8000e1bc` (`Blocks/F68.lean`), with `S` the entry's `sp`: `0x8000e1bc` saves
`ra`, `s0`..`s2` in a 64-byte frame (`s0` = the result, `s1` = the length, `s2` = the selector)
and calls `try_allocate_in(S - 56, length, 0, 8, 24)`; `0x8000e1f8` traps on `Err`;
`0x8000e200` makes the `Vec` at `S - 56` and calls `reserve(S - 56, length)`, which has room
(`reserve_fast`); `0x8000e224` returns empty for no bits; `0x8000e22c` points `a1` past element
`0`'s `c0`; the loop (`0x8000e24c`) writes element `a2` and counts; `0x8000e270` copies the `Vec`
out, restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.SelectorPoint
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts
  Rv64Verifier.MultilinearWords Rv64Verifier.Blocks.F68
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18)]

def kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s selectorStack) 80

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 64 slots kept (W s) nx

theorem bounds {s : MachineState} (h : SelectorPre s) :
    0x78000070 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.out (by decide)
  simp only [selectorStack, tryAllocStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem stack64 {s : MachineState} (h : SelectorPre s) : RtStack s 64 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : SelectorPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := bounds hpre
  have hs := hpre.outStack
  exact FnInv.step (m := 32) h (stack64 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hs, hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : SelectorPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

theorem Inv.saved {s u : MachineState} {nx : Word} (h : Inv s u nx) :
    u.getReg .x2 = s.getReg .x2 - 64 ∧ u.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧
      u.getMem (s.getReg .x2 - 16) = s.getReg .x8 ∧ u.getMem (s.getReg .x2 - 24) = s.getReg .x9 ∧
      u.getMem (s.getReg .x2 - 32) = s.getReg .x18 := by
  have hsp := h.sp
  have sl := h.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at hsp sl
  exact ⟨hsp, sl⟩

/-- The new buffer `P`, `n` elements, below `nx`. -/
structure BufOk (s : MachineState) (P nx : Word) : Prop where
  align : P.toNat % 8 = 0
  range : (s.getReg .x12).toNat = 0 ∨
    (heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ nx.toNat)
  fits : nx.toNat ≤ heapEnd
  lo : heapNext s ≤ nx.toNat

/-- The `Vec` at `S - 56`, the result's address in `s0`, the length in `s1`, the selector in
`s2`. -/
structure Mid (s u : MachineState) (P : Word) : Prop where
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x12
  x18 : u.getReg .x18 = s.getReg .x11
  cap : u.getMem (s.getReg .x2 - 56) = s.getReg .x12
  ptr : u.getMem (s.getReg .x2 - 48) = P

/-- At the loop head, before element `k`. -/
structure LoopInv (s u : MachineState) (nx P : Word) (k : Nat) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x8000e24c
  lt : k < (s.getReg .x12).toNat
  x10 : u.getReg .x10 = s.getReg .x12
  x11 : u.getReg .x11 = P + BitVec.ofNat 64 (24 * k) + 8
  x12 : u.getReg .x12 = BitVec.ofNat 64 k
  elems : ∀ j < k, eAt u (P + BitVec.ofNat 64 (24 * j)) = Model.bitE (s.getReg .x11) j

/-- At the epilogue, every element written. -/
structure ExitInv (s u : MachineState) (nx P : Word) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x8000e270
  x10 : u.getReg .x10 = s.getReg .x12
  elems : ∀ j < (s.getReg .x12).toNat,
    eAt u (P + BitVec.ofNat 64 (24 * j)) = Model.bitE (s.getReg .x11) j

theorem heap_valid {a : Word} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat + 8 ≤ heapEnd)
    (h3 : a.toNat % 8 = 0) : Sym.validAccess 8 a = true := by
  rw [Sym.validAccess_eight]
  simp only [heapEnd] at h2
  omega

theorem limbs_bitE (n : Word) (k : Nat) :
    Model.limbs (Model.bitE n k) = ((n >>> (k % 64)) &&& 1#64, 0, 0) := by
  rfl

/-! ## The loop -/

def measure (u : MachineState) : Nat := (u.getReg .x9).toNat - (u.getReg .x12).toNat

def Done (s u : MachineState) (nx P : Word) : Prop := ExitInv s u nx P ∨ Dead Image.code u

theorem body {s : MachineState} (hpre : SelectorPre s) {nx P : Word} (hP : BufOk s P nx)
    (u : MachineState) (hinv : ∃ k, LoopInv s u nx P k) :
    (∃ v, Reaches Image.code u v ∧ Done s v nx P) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ k, LoopInv s v nx P k) ∧ measure v < measure u) := by
  obtain ⟨k, hu⟩ := hinv
  have hk := hu.lt
  have hPa := hP.align
  have hPf := hP.fits
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ nx.toNat := by
    rcases hP.range with h | h
    · omega
    · exact h
  have hlo := hpre.heap.lo
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000e24c_spec hu.pc (by
    rv_eval [hu.x11]
    and_intros <;> exact heap_valid (by addr_omega [hPr, hlo, hk, hPf])
      (by addr_omega [hPr, hk, hPf]) (by addr_omega [hPa, hPr, hk, hPf]))
  have k₁ := b8000e24c_keeps h
  have m₀ : v.getMem (u.getReg .x11 - 8) = (u.getReg .x18 >>> ((u.getReg .x12).toNat % 64)) &&& 1 :=
    h.mem_eq 2 (by decide) (by rv_eval []) (by rv_eval [])
  have m₁ := b8000e24c_m_x11_0 h
  have m₂ := b8000e24c_m_x11_8 h
  have hm := b8000e24c_frame h (by rw [hu.x11]; constructor <;> addr_omega [hPr, hlo, hk, hPf])
  rw [hu.x11, hu.x18, hu.x12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)] at m₀
  rw [hu.x11] at m₁ m₂ hm
  rv_eval [] at m₀ m₁ m₂ hm
  have hnew : eAt v (P + BitVec.ofNat 64 (24 * k)) = Model.bitE (s.getReg .x11) k := by
    apply eAt_eq_of_limbs
    rw [limbs_bitE]
    rv_eval [m₀, m₁, m₂]
  have hfresh (a : Word) (ha : Within a (P + BitVec.ofNat 64 (24 * k)) 24) :
      heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat := by
    addr_omega [ha, hPr, hk, hPf]
  have inv' := hu.inv.step hpre (ByteFrame.of_memFrame hm (by addr_omega [hPa, hPr, hk, hPf])
      (by decide) (h.unaligned (by rv_eval [hu.x11]; and_intros <;> addr_omega [hPa, hPr, hk, hPf])))
    (fun a ha ↦ Or.inr (Or.inr (hfresh a ha)))
    ((hm _ fun hw ↦ by have := hfresh _ hw; addr_omega [this, hPf]).trans
      hu.inv.next)
    (Nat.le_refl _) hPf fun r hr ↦ k₁ r (mem_of_mem hr _)
  have hsame (a : Word) (ha : ¬ Within a (P + BitVec.ofNat 64 (24 * k)) 24) :
      v.getMem a = u.getMem a := hm a ha
  have hsp := (bounds hpre)
  have hmid : Mid s v P := {
    x8 := (k₁ .x8 (by decide)).trans hu.x8
    x9 := (k₁ .x9 (by decide)).trans hu.x9
    x18 := (k₁ .x18 (by decide)).trans hu.x18
    cap := (hsame _ (by addr_omega [hPr, hk, hPf, hsp])).trans hu.cap
    ptr := (hsame _ (by addr_omega [hPr, hk, hPf, hsp])).trans hu.ptr }
  have hel (j : Nat) (hj : j < k + 1) :
      eAt v (P + BitVec.ofNat 64 (24 * j)) = Model.bitE (s.getReg .x11) j := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hm.eAt (by addr_omega [hj, hk, hPr, hPf]) (by addr_omega [hj, hk, hPr, hPf])]
      exact hu.elems j hj
    · exact hnew
  have hx12 : v.getReg .x12 = BitVec.ofNat 64 (k + 1) := by
    rw [b8000e24c_x12 h, hu.x12]; addr_omega [hk]
  have hx11 : v.getReg .x11 = P + BitVec.ofNat 64 (24 * (k + 1)) + 8 := by
    rw [b8000e24c_x11 h, hu.x11]; addr_omega [hk, hPr, hPf]
  by_cases hlast : k + 1 = (s.getReg .x12).toNat
  · refine Or.inl ⟨v, hr, Or.inl {
      toMid := hmid
      inv := inv'
      pc := b8000e24c_pc_not_taken h (by rw [hu.x9, hu.x12]; addr_omega [hlast])
      x10 := (k₁ .x10 (by decide)).trans hu.x10
      elems := fun j hj ↦ hel j (by omega) }⟩
  · refine Or.inr ⟨v, hr, ⟨k + 1, {
      toMid := hmid
      inv := inv'
      pc := b8000e24c_pc_taken h (by rw [hu.x9, hu.x12]; addr_omega [hlast, hk])
      lt := by omega
      x10 := (k₁ .x10 (by decide)).trans hu.x10
      x11 := hx11
      x12 := hx12
      elems := hel }⟩, ?_⟩
    simp only [measure]
    rw [hmid.x9, hx12, hu.x9, hu.x12]
    addr_omega [hk]

/-! ## The epilogue -/

theorem exit {s u : MachineState} {nx P : Word} (hpre : SelectorPre s) (hP : BufOk s P nx)
    (hu : ExitInv s u nx P) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ SelectorPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hPa := hP.align
  have hPf := hP.fits
  obtain ⟨hsp, sl1, sl2, sl3, sl4⟩ := hu.inv.saved
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000e270_spec hu.pc (by
    rv_eval [hsp, hu.x8]
    and_intros <;> first
      | addr_omega [hb, hos]
      | valid_access hpre.stack.valid [hb]
      | valid_access hpre.out [hb])
  have k := b8000e270_keeps ht
  have pc := b8000e270_pc ht
  have x2 := b8000e270_x2 ht
  have x8 := b8000e270_x8 ht
  have x9 := b8000e270_x9 ht
  have x18 := b8000e270_x18 ht
  have m₀ := b8000e270_m_x8_0 ht
  have m₁ := b8000e270_m_x8_8 ht
  have m₂ := b8000e270_m_x8_16 ht
  have hm := b8000e270_frame ht (by rw [hu.x8]; addr_omega [hb])
  rw [hu.x8] at m₀ m₁ m₂ hm
  rv_eval [hsp, sl1, sl2, sl3, sl4, hu.cap, hu.ptr, hu.x10] at pc x2 x8 x9 x18 m₀ m₁ m₂
  have bf := ByteFrame.of_memFrame hm (by addr_omega [hb]) (by decide)
    (ht.unaligned (by rv_eval [hu.x8]; and_intros <;> addr_omega [hb]))
  have hnt : t.getMem nextAddr = nx := (hm _ (by addr_omega [hof.2, hb])).trans hu.inv.next
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hbf := hu.inv.frame bf (fun a ha ↦ Or.inl ha) hnt
  have hlo := hpre.heap.lo
  have hPlo := hP.lo
  refine ⟨t, hr, Or.inl ⟨pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 ((k .x19 (by decide)).trans (hu.inv.kept .x19 (by decide))) fun r hr' ↦ ?_,
    { heap := ⟨by omega, by omega⟩
      mono := by omega
      vec := ⟨?_, ?_⟩
      len := by simp only [vecLen, m₂]
      elems := ?_
      fresh := ?_
      frame := hbf.mono fun a ha ↦ ?_ }⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k _ (by decide)).trans (hu.inv.kept _ (by decide))
  · simp only [RawVecOk, Buf, vecPtr, vecCap, m₀, m₁]
    refine ⟨hPa, ?_⟩
    rcases hP.range with h0 | h0
    · exact Or.inl (by rw [h0])
    · exact Or.inr ⟨by omega, by rw [hn]; omega⟩
  · simp only [vecLen, vecCap, m₀, m₂, le_refl]
  · simp only [vecEs, vecPtr, vecLen, m₁, m₂, eListAt, Model.selectorPointRust]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ nx.toNat := by
      rcases hP.range with h | h
      · omega
      · exact h
    rw [hm.eAt (by addr_omega [hj, hPr, hPf, hof.1, hb]) (by addr_omega [hj, hPr, hPf])]
    exact hu.elems j hj
  · simp only [NewBuf, vecPtr, m₁]
    refine ⟨hPa, ?_⟩
    rcases hP.range with h0 | h0
    · exact Or.inl (by rw [h0])
    · exact Or.inr ⟨h0.1, by rw [hn]; omega⟩
  · rcases ha with ha | ha | ha | ha
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn] at ha ⊢; exact ha)))

/-! ## `selector_point` -/

/-- **`selector_point` meets its contract**, given `try_allocate_in`'s. -/
theorem selector_point_spec (hT : TryAllocZeroedSpec) : SelectorSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000e1bc_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000e1bc_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack64 hpre)
    (by rw [b8000e1bc_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000e1bc_m_x2_n8 h₁, b8000e1bc_m_x2_n16 h₁, b8000e1bc_m_x2_n24 h₁,
        b8000e1bc_m_x2_n32 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    ((b8000e1bc_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 64 := b8000e1bc_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 56 := b8000e1bc_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = stackLo s selectorStack := by
    simp only [stackLo, tryAllocStack, selectorStack, hsp₁]
    rw [Sym.sub_sub_lit]; rfl
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b8000e1bc_x13 h₁]; decide
    size := by rw [b8000e1bc_x14 h₁]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; exact hab, by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b8000e1bc_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := inv₁.step hpre hfr₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₁] at ha
        exact Or.inr (Or.inr ha))
    rfl (by rw [← heapNext, ← heapNext, ← hn₁]; exact hpost₂.mono) hpost₂.heap.hi
    fun r hr ↦ hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 64 := (hpres₂.reg .x2).trans hsp₁
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000e1f8_spec
    (by rw [hpc₂, returnAddress_eq, b8000e1bc_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 56)) 0 with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b8000e1f8_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b8000e1f8_keeps h₃
  have hm₃ := b8000e1f8_mem_same h₃
  have inv₃ := inv₂.same hpre hm₃ k₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁, b8000e1bc_x11 h₁] at hcap hbuf
  rw [b8000e1bc_x14 h₁, b8000e1bc_x13 h₁] at hbuf
  rv_eval [] at hcap hbuf
  obtain ⟨P, hP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 40) := ⟨_, rfl⟩
  rw [← hP] at hbuf
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 64 := (k₃ .x2 (by decide)).trans hsp₂
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₃.getReg r = t₁.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  -- the `Vec` at `S - 56`, then `reserve`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000e200_spec
    (b8000e1f8_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000e200_keeps h₄
  have v₀ := b8000e200_m_x2_8 h₄
  have v₁ := b8000e200_m_x2_16 h₄
  have v₂ := b8000e200_m_x2_24 h₄
  have hm₄ := b8000e200_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rv_eval [hsp₃, hm₃] at v₀ v₁ v₂ hm₄
  rw [hcap] at v₀
  rw [← hP] at v₁
  have inv₄ := inv₃.step hpre (ByteFrame.of_memFrame hm₄ (by addr_omega [hb]) (by decide)
      (h₄.unaligned (by rv_eval [hsp₃]; and_intros <;> addr_omega [hb])))
    (fun a ha ↦ Or.inl (Or.inr (by addr_omega [ha, hb])))
    ((hm₄ _ (by addr_omega [hb, hnx8])).trans inv₃.next) (Nat.le_refl _) inv₃.fits
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 56 := by rw [b8000e200_x10 h₄, hsp₃]; rv_eval []
  have hx11₄ : t₄.getReg .x11 = s.getReg .x12 := by
    rw [b8000e200_x11 h₄, hreg .x9 (by decide), b8000e1bc_x9 h₁]
  obtain ⟨t₅, hr₅, hpc₅, hpres₅, hx10₅, hm₅⟩ := reserve_fast (b8000e200_pc h₄)
    (by rw [hx10₄]; valid_sub hst.valid [hb])
    (by rw [hx10₄, hx11₄]; rv_eval [v₀, v₂]; simp)
  have inv₅ := inv₄.same hpre hm₅ (l := calleeSaved) hpres₅ (by decide)
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 64 := by
    rw [hpres₅.reg .x2, k₄ .x2 (by decide), hsp₃]
  have hreg₅ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₅.getReg r = t₁.getReg r := by
    rw [hpres₅ r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _),
      hreg r hr]
  have hmid₅ : Mid s t₅ P := {
    x8 := by rw [hreg₅ .x8 (by decide), b8000e1bc_x8 h₁]
    x9 := by rw [hreg₅ .x9 (by decide), b8000e1bc_x9 h₁]
    x18 := by rw [hreg₅ .x18 (by decide), b8000e1bc_x18 h₁]
    cap := by rw [hm₅]; exact v₀
    ptr := by rw [hm₅]; exact v₁ }
  -- the length so far, zero
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000e224_spec
    (by rw [hpc₅, returnAddress_eq, b8000e200_x1 h₄]; decide) (by
      rv_eval [hsp₅]
      valid_access hst.valid [hb])
  have k₆ := b8000e224_keeps h₆
  have hm₆ := b8000e224_mem_same h₆
  have inv₆ := inv₅.same hpre hm₆ k₆
  have hx10₆ : t₆.getReg .x10 = 0 := by
    rw [b8000e224_x10 h₆, hsp₅]; rv_eval [hm₅, v₂]
  have hmid₆ : Mid s t₆ P := {
    x8 := (k₆ .x8 (by decide)).trans hmid₅.x8
    x9 := (k₆ .x9 (by decide)).trans hmid₅.x9
    x18 := (k₆ .x18 (by decide)).trans hmid₅.x18
    cap := (hm₆ _).trans hmid₅.cap
    ptr := (hm₆ _).trans hmid₅.ptr }
  have hBuf : BufOk s P (t₂.getMem nextAddr) := {
    align := hbuf.1
    range := by
      rcases hbuf.2 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr ⟨hn₁ ▸ h.1, h.2⟩
    fits := hpost₂.heap.hi
    lo := by have := hpost₂.mono; rw [hn₁] at this; exact this }
  have hreach := hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))
  by_cases h0 : s.getReg .x12 = 0
  · have hz : (s.getReg .x12).toNat = 0 := by rw [h0]; rfl
    obtain ⟨t, hr, ht⟩ := exit hpre hBuf {
      toMid := hmid₆, inv := inv₆
      pc := b8000e224_pc_taken h₆ (by rw [hmid₅.x9]; exact h0)
      x10 := by rw [hx10₆, h0]
      elems := fun j hj ↦ by omega }
    exact ⟨t, hreach.trans hr, ht⟩
  have hlen : 0 < (s.getReg .x12).toNat := by
    rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) h0
    · exact h
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000e22c_spec
    (b8000e224_pc_not_taken h₆ (by rw [hmid₅.x9]; exact h0)) (by
      rv_eval [k₆ .x2 (by decide), hsp₅]
      valid_access hst.valid [hb])
  have k₇ := b8000e22c_keeps h₇
  have hm₇ := b8000e22c_mem_same h₇
  have inv₇ := inv₆.same hpre hm₇ k₇
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤
      (t₂.getMem nextAddr).toNat := by
    rcases hBuf.range with h | h
    · omega
    · exact h
  have hPf := hBuf.fits
  obtain ⟨t, hr, ht⟩ := Reaches.loop (fun u ↦ ∃ k, LoopInv s u (t₂.getMem nextAddr) P k)
    measure (fun u ↦ Done s u (t₂.getMem nextAddr) P) (body hpre hBuf) t₇ ⟨0, {
      toMid := {
        x8 := (k₇ .x8 (by decide)).trans hmid₆.x8
        x9 := (k₇ .x9 (by decide)).trans hmid₆.x9
        x18 := (k₇ .x18 (by decide)).trans hmid₆.x18
        cap := (hm₇ _).trans hmid₆.cap
        ptr := (hm₇ _).trans hmid₆.ptr }
      inv := inv₇
      pc := b8000e22c_pc h₇
      lt := hlen
      x10 := by rw [b8000e22c_x10 h₇, hx10₆, hmid₆.x9]; simp
      x11 := by
        rw [b8000e22c_x11 h₇, hx10₆, k₆ .x2 (by decide), hsp₅]
        rv_eval [hm₆, hmid₅.ptr]
        simp
      x12 := by rw [b8000e22c_x12 h₇]; rfl
      elems := fun j hj ↦ absurd hj (Nat.not_lt_zero j) }⟩
  rcases ht with ht | hdead
  · obtain ⟨t', hr', ht'⟩ := exit hpre hBuf ht
    exact ⟨t', hreach.trans (hr₇.trans (hr.trans hr')), ht'⟩
  · exact ⟨t, hreach.trans (hr₇.trans hr), Or.inr hdead⟩

end Rv64Verifier.Proofs.Multilinear.SelectorPoint
