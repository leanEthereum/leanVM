import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Blocks.F18

/-!
# `<E as SpecFromElem>::from_elem`, `vec![x; n]`

compiled at `0x80005360` (`Blocks/F18.lean`), with `S` the entry's `sp`: `0x80005360` saves
`ra`, `s0`..`s2` in a 64-byte frame (`s0` = the result, `s1` = the element, `s2` = `n`) and calls
`try_allocate_in(S - 56, n, 0, 8, 24)`; `0x8000539c` traps on `Err`; `0x800053a4` makes the
`Vec` at `S - 56` and calls `reserve(S - 56, n)`, which has room (`reserve_fast`); `0x800053c8`
points `a1` at element `0`; for `n ≥ 2` the loop at `0x80005400` copies the element `n - 1`
times, then `0x80005420` sets the length to `n - 1`; `0x8000542c` returns empty for `n = 0`;
`0x80005430` writes the last copy; `0x8000544c` copies the `Vec` out, restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.FromElem
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts
  Rv64Verifier.MultilinearWords Rv64Verifier.Blocks.F18
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18)]

def kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s fromElemStack) 80

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 64 slots kept (W s) nx

theorem bounds {s : MachineState} (h : FromElemPre s) :
    0x78000070 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.out (by decide)
  simp only [fromElemStack, tryAllocStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem stack64 {s : MachineState} (h : FromElemPre s) : RtStack s 64 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : FromElemPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := bounds hpre
  have hs := hpre.outStack
  exact FnInv.step (m := 32) h (stack64 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hs, hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : FromElemPre s) (h : Inv s u nx)
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


/-- The `Vec` at `S - 56`, the result's address in `s0`, the element's in `s1`, `n` in `s2`. -/
structure Mid (s u : MachineState) (P : Word) : Prop where
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x11
  x18 : u.getReg .x18 = s.getReg .x12
  cap : u.getMem (s.getReg .x2 - 56) = s.getReg .x12
  ptr : u.getMem (s.getReg .x2 - 48) = P

/-- The element, as the entry holds it. -/
def X (s : MachineState) : E := eAt s (s.getReg .x11)

/-- In the copy loop, before copy `k`, `k + 1 < n`. -/
structure LoopInv (s u : MachineState) (nx P : Word) (k : Nat) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x80005400
  lt : k + 1 < (s.getReg .x12).toNat
  x10 : u.getReg .x10 = 0
  x11 : u.getReg .x11 = P + BitVec.ofNat 64 (24 * k)
  x12 : u.getReg .x12 = P + BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - 1))
  elems : ∀ j < k, eAt u (P + BitVec.ofNat 64 (24 * j)) = X s

/-- Before the last copy. -/
structure LastInv (s u : MachineState) (nx P : Word) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x80005430
  pos : 0 < (s.getReg .x12).toNat
  x10 : u.getReg .x10 = BitVec.ofNat 64 ((s.getReg .x12).toNat - 1)
  x11 : u.getReg .x11 = P + BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - 1))
  elems : ∀ j < (s.getReg .x12).toNat - 1, eAt u (P + BitVec.ofNat 64 (24 * j)) = X s

/-- At the epilogue, every copy written. -/
structure ExitInv (s u : MachineState) (nx P : Word) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x8000544c
  x10 : u.getReg .x10 = s.getReg .x12
  elems : ∀ j < (s.getReg .x12).toNat, eAt u (P + BitVec.ofNat 64 (24 * j)) = X s

/-- The element is never written. -/
theorem elem_eq {s u : MachineState} {nx : Word} (hpre : FromElemPre s) (h : Inv s u nx)
    (c : Nat) (hc : c = 0 ∨ c = 8 ∨ c = 16) :
    u.getMem (s.getReg .x11 + BitVec.ofNat 64 c) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 c) := by
  have hb := bounds hpre
  have he := ValidMemRange.bounds hpre.elem (by decide)
  have hef := hpre.elemFree
  have hes := hpre.elemStack
  have heo := hpre.elemOut
  have hfit := h.fits
  simp only [Outside] at hef
  refine h.mem.getMem fun i hi hw ↦ ?_
  rcases hw with (hw | hw) | hw | hw | hw
  · addr_omega [hw, hi, hc, he, heo]
  · addr_omega [hw, hi, hc, he, hes, hb]
  · addr_omega [hw, hi, hc, he, hes, hb]
  · addr_omega [hw, hi, hc, he, hef.2]
  · addr_omega [hw, hi, hc, he, hef.1, hfit]

theorem heap_valid {a : Word} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat + 8 ≤ heapEnd)
    (h3 : a.toNat % 8 = 0) : Sym.validAccess 8 a = true := by
  rw [Sym.validAccess_eight]
  simp only [heapEnd] at h2
  omega

/-- One copy of the element to `p`, a block writing `p`, `p + 8`, `p + 16` from `[s1]`. -/
theorem copy_eAt {s u v : MachineState} {nx p : Word} (hpre : FromElemPre s) (h : Inv s u nx)
    (hx9 : u.getReg .x9 = s.getReg .x11)
    (m₀ : v.getMem p = u.getMem (u.getReg .x9))
    (m₁ : v.getMem (p + 8) = u.getMem (u.getReg .x9 + 8))
    (m₂ : v.getMem (p + 16) = u.getMem (u.getReg .x9 + 16)) : eAt v p = X s := by
  have e0 := elem_eq hpre h 0 (Or.inl rfl)
  have e1 := elem_eq hpre h 8 (Or.inr (Or.inl rfl))
  have e2 := elem_eq hpre h 16 (Or.inr (Or.inr rfl))
  rv_eval [] at e0 e1 e2
  unfold X eAt
  rw [m₀, m₁, m₂, hx9, e0, e1, e2]

/-! ## The loops -/

def measure (u : MachineState) : Nat := (u.getReg .x12).toNat - (u.getReg .x11).toNat

def Done (s u : MachineState) (nx P : Word) : Prop := LastInv s u nx P ∨ Dead Image.code u

theorem body {s : MachineState} (hpre : FromElemPre s) {nx P : Word} (hP : BufOk s P nx)
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
  have he := ValidMemRange.bounds hpre.elem (by decide)
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b80005400_spec hu.pc (by
    rv_eval [hu.x11, hu.x9]
    and_intros <;> first
      | valid_access hpre.elem [he]
      | exact heap_valid (by addr_omega [hPr, hlo, hk, hPf])
          (by addr_omega [hPr, hk, hPf]) (by addr_omega [hPa, hPr, hk, hPf]))
  have k₁ := b80005400_keeps h
  have m₀ := b80005400_m_x11_0 h
  have m₁ := b80005400_m_x11_8 h
  have m₂ := b80005400_m_x11_16 h
  have hm := b80005400_frame h (by rw [hu.x11]; addr_omega [hPr, hlo, hk, hPf])
  rw [hu.x11] at m₀ m₁ m₂ hm
  have hnew := copy_eAt hpre hu.inv hu.x9 m₀ m₁ m₂
  have hfresh (a : Word) (ha : Within a (P + BitVec.ofNat 64 (24 * k)) 24) :
      heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat := by
    addr_omega [ha, hPr, hk, hPf]
  have inv' := hu.inv.step hpre (ByteFrame.of_memFrame hm (by addr_omega [hPa, hPr, hk, hPf])
      (by decide) (h.unaligned (by rv_eval [hu.x11]; and_intros <;> addr_omega [hPa, hPr, hk, hPf])))
    (fun a ha ↦ Or.inr (Or.inr (hfresh a ha)))
    ((hm _ fun hw ↦ by have := hfresh _ hw; addr_omega [this, hPf]).trans hu.inv.next)
    (Nat.le_refl _) hPf fun r hr ↦ k₁ r (mem_of_mem hr _)
  have hsp := (bounds hpre)
  have hmid : Mid s v P := {
    x8 := (k₁ .x8 (by decide)).trans hu.x8
    x9 := (k₁ .x9 (by decide)).trans hu.x9
    x18 := (k₁ .x18 (by decide)).trans hu.x18
    cap := (hm _ (by addr_omega [hPr, hk, hPf, hsp])).trans hu.cap
    ptr := (hm _ (by addr_omega [hPr, hk, hPf, hsp])).trans hu.ptr }
  have hel (j : Nat) (hj : j < k + 1) : eAt v (P + BitVec.ofNat 64 (24 * j)) = X s := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hm.eAt (by addr_omega [hj, hk, hPr, hPf]) (by addr_omega [hj, hk, hPr, hPf])]
      exact hu.elems j hj
    · exact hnew
  have hx11 : v.getReg .x11 = P + BitVec.ofNat 64 (24 * (k + 1)) := by
    rw [b80005400_x11 h, hu.x11]; addr_omega [hk, hPr, hPf]
  by_cases hlast : k + 2 = (s.getReg .x12).toNat
  · -- the length `n - 1`, then the last copy
    obtain ⟨w, hr', h'⟩ := Sym.BlockSpec.reaches b80005420_spec
      (b80005400_pc_not_taken h (by rw [hu.x11, hu.x12]; addr_omega [hlast, hPr, hPf])) trivial
    have k₂ := b80005420_keeps h'
    refine Or.inl ⟨w, hr.trans hr', Or.inl {
      x8 := (k₂ .x8 (by decide)).trans hmid.x8
      x9 := (k₂ .x9 (by decide)).trans hmid.x9
      x18 := (k₂ .x18 (by decide)).trans hmid.x18
      cap := (b80005420_mem_same h' _).trans hmid.cap
      ptr := (b80005420_mem_same h' _).trans hmid.ptr
      inv := inv'.same hpre (b80005420_mem_same h') k₂
      pc := b80005420_pc h'
      pos := by omega
      x10 := by
        rw [b80005420_x10 h', k₁ .x10 (by decide), hu.x10, k₁ .x18 (by decide), hu.x18]
        addr_omega [hlast]
      x11 := by rw [k₂ .x11 (by decide), hx11]; congr 3; omega
      elems := fun j hj ↦ by
        unfold eAt
        rw [b80005420_mem_same h', b80005420_mem_same h', b80005420_mem_same h']
        exact hel j (by omega) }⟩
  · refine Or.inr ⟨v, hr, ⟨k + 1, {
      toMid := hmid
      inv := inv'
      pc := b80005400_pc_taken h (by rw [hu.x11, hu.x12]; addr_omega [hlast, hk, hPr, hPf])
      lt := by omega
      x10 := (k₁ .x10 (by decide)).trans hu.x10
      x11 := hx11
      x12 := (k₁ .x12 (by decide)).trans hu.x12
      elems := hel }⟩, ?_⟩
    simp only [measure]
    rw [k₁ .x12 (by decide), hx11, hu.x12, hu.x11]
    addr_omega [hk, hPr, hPf]

/-- The last copy. -/
theorem last {s u : MachineState} {nx P : Word} (hpre : FromElemPre s) (hP : BufOk s P nx)
    (hu : LastInv s u nx P) : ∃ v, Reaches Image.code u v ∧ ExitInv s v nx P := by
  have hk := hu.pos
  have hPa := hP.align
  have hPf := hP.fits
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ nx.toNat := by
    rcases hP.range with h | h
    · omega
    · exact h
  have hlo := hpre.heap.lo
  have he := ValidMemRange.bounds hpre.elem (by decide)
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b80005430_spec hu.pc (by
    rv_eval [hu.x11, hu.x9]
    and_intros <;> first
      | valid_access hpre.elem [he]
      | exact heap_valid (by addr_omega [hPr, hlo, hk, hPf])
          (by addr_omega [hPr, hk, hPf]) (by addr_omega [hPa, hPr, hk, hPf]))
  have k₁ := b80005430_keeps h
  have m₀ := b80005430_m_x11_0 h
  have m₁ := b80005430_m_x11_8 h
  have m₂ := b80005430_m_x11_16 h
  have hm := b80005430_frame h (by rw [hu.x11]; addr_omega [hPr, hlo, hk, hPf])
  rw [hu.x11] at m₀ m₁ m₂ hm
  have hnew := copy_eAt hpre hu.inv hu.x9 m₀ m₁ m₂
  have hfresh (a : Word) (ha : Within a (P + BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - 1)))
      24) : heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat := by
    addr_omega [ha, hPr, hk, hPf]
  have hsp := (bounds hpre)
  refine ⟨v, hr, {
    x8 := (k₁ .x8 (by decide)).trans hu.x8
    x9 := (k₁ .x9 (by decide)).trans hu.x9
    x18 := (k₁ .x18 (by decide)).trans hu.x18
    cap := (hm _ (by addr_omega [hPr, hk, hPf, hsp])).trans hu.cap
    ptr := (hm _ (by addr_omega [hPr, hk, hPf, hsp])).trans hu.ptr
    inv := hu.inv.step hpre (ByteFrame.of_memFrame hm (by addr_omega [hPa, hPr, hk, hPf])
        (by decide) (h.unaligned (by rv_eval [hu.x11]; and_intros <;> addr_omega [hPa, hPr, hk, hPf])))
      (fun a ha ↦ Or.inr (Or.inr (hfresh a ha)))
      ((hm _ fun hw ↦ by have := hfresh _ hw; addr_omega [this, hPf]).trans hu.inv.next)
      (Nat.le_refl _) hPf fun r hr ↦ k₁ r (mem_of_mem hr _)
    pc := b80005430_pc h
    x10 := by rw [b80005430_x10 h, hu.x10]; addr_omega [hk]
    elems := fun j hj ↦ by
      rcases Nat.lt_or_ge j ((s.getReg .x12).toNat - 1) with hj' | hj'
      · rw [hm.eAt (by addr_omega [hj', hk, hPr, hPf]) (by addr_omega [hj', hk, hPr, hPf])]
        exact hu.elems j hj'
      · rw [show j = (s.getReg .x12).toNat - 1 by omega]; exact hnew }⟩

/-! ## The epilogue -/

theorem exit {s u : MachineState} {nx P : Word} (hpre : FromElemPre s) (hP : BufOk s P nx)
    (hu : ExitInv s u nx P) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ FromElemPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hPa := hP.align
  have hPf := hP.fits
  obtain ⟨hsp, sl1, sl2, sl3, sl4⟩ := hu.inv.saved
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000544c_spec hu.pc (by
    rv_eval [hsp, hu.x8]
    and_intros <;> first
      | addr_omega [hb, hos]
      | valid_access hpre.stack.valid [hb]
      | valid_access hpre.out [hb])
  have k := b8000544c_keeps ht
  have pc := b8000544c_pc ht
  have x2 := b8000544c_x2 ht
  have x8 := b8000544c_x8 ht
  have x9 := b8000544c_x9 ht
  have x18 := b8000544c_x18 ht
  have m₀ := b8000544c_m_x8_0 ht
  have m₁ := b8000544c_m_x8_8 ht
  have m₂ := b8000544c_m_x8_16 ht
  have hm := b8000544c_frame ht (by rw [hu.x8]; addr_omega [hb])
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
  · simp only [vecEs, vecPtr, vecLen, m₁, m₂, eListAt]
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun e he ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
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

/-! ## `from_elem` -/

/-- **`from_elem` meets its contract**, given `try_allocate_in`'s. -/
theorem from_elem_spec (hT : TryAllocZeroedSpec) : FromElemSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005360_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80005360_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack64 hpre)
    (by rw [b80005360_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b80005360_m_x2_n8 h₁, b80005360_m_x2_n16 h₁, b80005360_m_x2_n24 h₁,
        b80005360_m_x2_n32 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    ((b80005360_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 64 := b80005360_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 56 := b80005360_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = stackLo s fromElemStack := by
    simp only [stackLo, tryAllocStack, fromElemStack, hsp₁]
    rw [Sym.sub_sub_lit]; rfl
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b80005360_x13 h₁]; decide
    size := by rw [b80005360_x14 h₁]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; exact hab, by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b80005360_pc h₁) hpre₁
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
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000539c_spec
    (by rw [hpc₂, returnAddress_eq, b80005360_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 56)) 0 with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b8000539c_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b8000539c_keeps h₃
  have hm₃ := b8000539c_mem_same h₃
  have inv₃ := inv₂.same hpre hm₃ k₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁, b80005360_x11 h₁] at hcap hbuf
  rw [b80005360_x14 h₁, b80005360_x13 h₁] at hbuf
  rv_eval [] at hcap hbuf
  obtain ⟨P, hP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 40) := ⟨_, rfl⟩
  rw [← hP] at hbuf
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 64 := (k₃ .x2 (by decide)).trans hsp₂
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₃.getReg r = t₁.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800053a4_spec
    (b8000539c_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b800053a4_keeps h₄
  have v₀ := b800053a4_m_x2_8 h₄
  have v₁ := b800053a4_m_x2_16 h₄
  have v₂ := b800053a4_m_x2_24 h₄
  have hm₄ := b800053a4_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rv_eval [hsp₃, hm₃] at v₀ v₁ v₂ hm₄
  rw [hcap] at v₀
  rw [← hP] at v₁
  have inv₄ := inv₃.step hpre (ByteFrame.of_memFrame hm₄ (by addr_omega [hb]) (by decide)
      (h₄.unaligned (by rv_eval [hsp₃]; and_intros <;> addr_omega [hb])))
    (fun a ha ↦ Or.inl (Or.inr (by addr_omega [ha, hb])))
    ((hm₄ _ (by addr_omega [hb, hnx8])).trans inv₃.next) (Nat.le_refl _) inv₃.fits
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 56 := by rw [b800053a4_x10 h₄, hsp₃]; rv_eval []
  have hx11₄ : t₄.getReg .x11 = s.getReg .x12 := by
    rw [b800053a4_x11 h₄, hreg .x18 (by decide), b80005360_x18 h₁]
  obtain ⟨t₅, hr₅, hpc₅, hpres₅, hx10₅, hm₅⟩ := reserve_fast (b800053a4_pc h₄)
    (by rw [hx10₄]; valid_sub hst.valid [hb])
    (by rw [hx10₄, hx11₄]; rv_eval [v₀, v₂]; simp)
  have inv₅ := inv₄.same hpre hm₅ (l := calleeSaved) hpres₅ (by decide)
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 64 := by
    rw [hpres₅.reg .x2, k₄ .x2 (by decide), hsp₃]
  have hreg₅ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₅.getReg r = t₁.getReg r := by
    rw [hpres₅ r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _),
      hreg r hr]
  have hmid₅ : Mid s t₅ P := {
    x8 := by rw [hreg₅ .x8 (by decide), b80005360_x8 h₁]
    x9 := by rw [hreg₅ .x9 (by decide), b80005360_x9 h₁]
    x18 := by rw [hreg₅ .x18 (by decide), b80005360_x18 h₁]
    cap := by rw [hm₅]; exact v₀
    ptr := by rw [hm₅]; exact v₁ }
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800053c8_spec
    (by rw [hpc₅, returnAddress_eq, b800053a4_x1 h₄]; decide) (by
      rv_eval [hsp₅]
      and_intros <;> valid_access hst.valid [hb])
  have k₆ := b800053c8_keeps h₆
  have hm₆ := b800053c8_mem_same h₆
  have inv₆ := inv₅.same hpre hm₆ k₆
  have hl₆ : t₅.getMem (s.getReg .x2 - 40) = 0 := by rw [hm₅]; exact v₂
  have hp₆ : t₅.getMem (s.getReg .x2 - 48) = P := hmid₅.ptr
  have hx10₆ : t₆.getReg .x10 = 0 := by rw [b800053c8_x10 h₆, hsp₅]; rv_eval [hl₆]
  have hx11₆ : t₆.getReg .x11 = P := by rw [b800053c8_x11 h₆, hsp₅]; rv_eval [hl₆, hp₆]
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
  have hPr : (s.getReg .x12).toNat = 0 ∨ (heapNext s ≤ P.toNat ∧
      P.toNat + (s.getReg .x12).toNat * 24 ≤ (t₂.getMem nextAddr).toNat) := hBuf.range
  have hPf := hBuf.fits
  -- the last copy, then the epilogue
  have finish (u : MachineState) (hu : Reaches Image.code s u) (hl : LastInv s u (t₂.getMem nextAddr) P) :
      ∃ t, Reaches Image.code s t ∧
        ((t.pc = returnAddress s ∧ Preserves s t ∧ FromElemPost s t) ∨ Dead Image.code t) := by
    obtain ⟨v, hv, hx⟩ := last hpre hBuf hl
    obtain ⟨t, ht, hres⟩ := exit hpre hBuf hx
    exact ⟨t, hu.trans (hv.trans ht), hres⟩
  by_cases hlt : (s.getReg .x12).toNat < 2
  · have hpc₇ := b800053c8_pc_taken h₆ (by rw [hmid₅.x18]; exact hlt)
    obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000542c_spec hpc₇ trivial
    have k₇ := b8000542c_keeps h₇
    have hm₇ := b8000542c_mem_same h₇
    have inv₇ := inv₆.same hpre hm₇ k₇
    have hmid₇ : Mid s t₇ P := {
      x8 := (k₇ .x8 (by decide)).trans hmid₆.x8
      x9 := (k₇ .x9 (by decide)).trans hmid₆.x9
      x18 := (k₇ .x18 (by decide)).trans hmid₆.x18
      cap := (hm₇ _).trans hmid₆.cap
      ptr := (hm₇ _).trans hmid₆.ptr }
    by_cases h0 : s.getReg .x12 = 0
    · have hz : (s.getReg .x12).toNat = 0 := by rw [h0]; rfl
      obtain ⟨t, hr, ht⟩ := exit hpre hBuf {
        toMid := hmid₇, inv := inv₇
        pc := b8000542c_pc_taken h₇ (by rw [hmid₆.x18]; exact h0)
        x10 := by rw [k₇ .x10 (by decide), hx10₆, h0]
        elems := fun j hj ↦ by omega }
      exact ⟨t, hreach.trans (hr₇.trans hr), ht⟩
    · have h1 : (s.getReg .x12).toNat = 1 := by
        have : (s.getReg .x12).toNat ≠ 0 := fun h ↦ h0 (BitVec.eq_of_toNat_eq h)
        omega
      exact finish t₇ (hreach.trans hr₇) {
        toMid := hmid₇, inv := inv₇
        pc := b8000542c_pc_not_taken h₇ (by rw [hmid₆.x18]; exact h0)
        pos := by omega
        x10 := by rw [k₇ .x10 (by decide), hx10₆, h1]; rfl
        x11 := by rw [k₇ .x11 (by decide), hx11₆, h1]; simp
        elems := fun j hj ↦ by omega }
  have hPr' : heapNext s ≤ P.toNat ∧
      P.toNat + (s.getReg .x12).toNat * 24 ≤ (t₂.getMem nextAddr).toNat := by
    rcases hPr with h | h
    · omega
    · exact h
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800053e8_spec
    (b800053c8_pc_not_taken h₆ (by rw [hmid₅.x18]; show 2 ≤ _; omega)) trivial
  have k₇ := b800053e8_keeps h₇
  have hm₇ := b800053e8_mem_same h₇
  have inv₇ := inv₆.same hpre hm₇ k₇
  obtain ⟨t, hr, ht⟩ := Reaches.loop (fun u ↦ ∃ k, LoopInv s u (t₂.getMem nextAddr) P k)
    measure (fun u ↦ Done s u (t₂.getMem nextAddr) P) (body hpre hBuf) t₇ ⟨0, {
      toMid := {
        x8 := (k₇ .x8 (by decide)).trans hmid₆.x8
        x9 := (k₇ .x9 (by decide)).trans hmid₆.x9
        x18 := (k₇ .x18 (by decide)).trans hmid₆.x18
        cap := (hm₇ _).trans hmid₆.cap
        ptr := (hm₇ _).trans hmid₆.ptr }
      inv := inv₇
      pc := b800053e8_pc h₇
      lt := by omega
      x10 := (k₇ .x10 (by decide)).trans hx10₆
      x11 := by rw [k₇ .x11 (by decide), hx11₆]; simp
      x12 := by
        rw [b800053e8_x12 h₇, b800053c8_x13 h₆, k₆ .x18 (by decide), hmid₅.x18, b800053c8_x12 h₆,
          hsp₅]
        rv_eval [hl₆, hp₆]
        addr_omega [hPr', hPf, hlt]
      elems := fun j hj ↦ absurd hj (Nat.not_lt_zero j) }⟩
  rcases ht with ht | hdead
  · exact finish t (hreach.trans (hr₇.trans hr)) ht
  · exact ⟨t, hreach.trans (hr₇.trans hr), Or.inr hdead⟩

end Rv64Verifier.Proofs.Multilinear.FromElem
