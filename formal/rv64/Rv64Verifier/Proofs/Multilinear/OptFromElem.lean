import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Proofs.Bus.Contracts
import Rv64Verifier.Blocks.F77

/-!
# `<Option<E> as SpecFromElem>::from_elem`, `vec![x; n]`

compiled at `0x80010724` (`Blocks/F77.lean`) as `from_elem` for `E` is (`FromElem.lean`), with
`S` the entry's `sp`: `0x80010724` saves `ra`, `s0`..`s2` in an 80-byte frame (`s0` = the result,
`s1` = the element, `s2` = `n`) and calls `try_allocate_in(S - 56, n, 0, 8, 32)`; `0x80010760`
traps on `Err`; `0x80010768` makes the `Vec` at `S - 80` and calls `reserve(S - 80, n)`, which has
room; `0x8001078c` points `a1` at element `0`; for `n ≥ 2`, `0x800107a4` reads the tag and the loop
at `0x800107fc` writes `n - 1` clones (`0x800107bc` copies a `Some`'s value to `S - 56`, a `None`
takes tag `0` at `0x80010800`, `0x800107d8` writes the clone), `0x80010810` sets the length to
`n - 1`; `0x80010808` returns empty for `n = 0`; `0x80010818` moves the element into the last
slot; `0x8001083c` copies the `Vec` out, restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.OptFromElem
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F77
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18)]

def kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- What the function writes besides its frame: the result and the stack from `S - 128` up to the
saved registers. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (s.getReg .x2 - 128) 96

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 80 slots kept (W s) nx

theorem outValid {s : MachineState} (h : Bus.OptFromElemPre s) :
    ValidMemRange (s.getReg .x10) 3 := by
  intro i hi
  have ho := h.out
  exact Transcript.Region.valid ho (by addr_omega [ho, hi]) (by addr_omega [ho, hi])
    (by addr_omega [ho, hi])

theorem elemValid {s : MachineState} (h : Bus.OptFromElemPre s) :
    ValidMemRange (s.getReg .x11) 4 := by
  intro i hi
  have ho := h.elem
  exact Transcript.Region.valid ho (by addr_omega [ho, hi]) (by addr_omega [ho, hi])
    (by addr_omega [ho, hi])

theorem bounds {s : MachineState} (h : Bus.OptFromElemPre s) :
    0x780000f0 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds (outValid h) (by decide)
  simp only [Bus.optFromElemStack, reserveStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem stack80 {s : MachineState} (h : Bus.OptFromElemPre s) : RtStack s 80 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : Bus.OptFromElemPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := bounds hpre
  have hs := hpre.outStack
  exact FnInv.step (m := 32) h (stack80 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hs, hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : Bus.OptFromElemPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

theorem Inv.saved {s u : MachineState} {nx : Word} (h : Inv s u nx) :
    u.getReg .x2 = s.getReg .x2 - 80 ∧ u.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧
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
    (heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 32 ≤ nx.toNat)
  fits : nx.toNat ≤ heapEnd
  lo : heapNext s ≤ nx.toNat

/-- The `Vec` at `S - 80`, the result's address in `s0`, the element's in `s1`, `n` in `s2`. -/
structure Mid (s u : MachineState) (P : Word) : Prop where
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x11
  x18 : u.getReg .x18 = s.getReg .x12
  cap : u.getMem (s.getReg .x2 - 80) = s.getReg .x12
  ptr : u.getMem (s.getReg .x2 - 72) = P

/-- The element, as the entry holds it. -/
def X (s : MachineState) : Option E := Transcript.optEAt s (s.getReg .x11)

/-- In the clone loop, before clone `k`, `k + 1 < n`; the tag in `a2`. -/
structure LoopInv (s u : MachineState) (nx P : Word) (k : Nat) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x800107fc
  lt : k + 1 < (s.getReg .x12).toNat
  x10 : u.getReg .x10 = 0
  x11 : u.getReg .x11 = P + BitVec.ofNat 64 (32 * k)
  x12 : u.getReg .x12 = s.getMem (s.getReg .x11)
  x13 : u.getReg .x13 = P + BitVec.ofNat 64 (32 * ((s.getReg .x12).toNat - 1))
  elems : ∀ j < k, Transcript.optEAt u (P + BitVec.ofNat 64 (32 * j)) = X s

/-- Before the last copy. -/
structure LastInv (s u : MachineState) (nx P : Word) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x80010818
  pos : 0 < (s.getReg .x12).toNat
  x10 : u.getReg .x10 = BitVec.ofNat 64 ((s.getReg .x12).toNat - 1)
  x11 : u.getReg .x11 = P + BitVec.ofNat 64 (32 * ((s.getReg .x12).toNat - 1))
  elems : ∀ j < (s.getReg .x12).toNat - 1,
    Transcript.optEAt u (P + BitVec.ofNat 64 (32 * j)) = X s

/-- At the epilogue, every element written. -/
structure ExitInv (s u : MachineState) (nx P : Word) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x8001083c
  x10 : u.getReg .x10 = s.getReg .x12
  elems : ∀ j < (s.getReg .x12).toNat, Transcript.optEAt u (P + BitVec.ofNat 64 (32 * j)) = X s

/-- The element is never written. -/
theorem elem_eq {s u : MachineState} {nx : Word} (hpre : Bus.OptFromElemPre s) (h : Inv s u nx)
    (c : Nat) (hc : c = 0 ∨ c = 8 ∨ c = 16 ∨ c = 24) :
    u.getMem (s.getReg .x11 + BitVec.ofNat 64 c) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 c) := by
  have hb := bounds hpre
  have he := ValidMemRange.bounds (elemValid hpre) (by decide)
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

theorem elem_eqs {s u : MachineState} {nx : Word} (hpre : Bus.OptFromElemPre s) (h : Inv s u nx) :
    u.getMem (s.getReg .x11) = s.getMem (s.getReg .x11) ∧
      u.getMem (s.getReg .x11 + 8) = s.getMem (s.getReg .x11 + 8) ∧
      u.getMem (s.getReg .x11 + 16) = s.getMem (s.getReg .x11 + 16) ∧
      u.getMem (s.getReg .x11 + 24) = s.getMem (s.getReg .x11 + 24) := by
  have e0 := elem_eq hpre h 0 (Or.inl rfl)
  have e1 := elem_eq hpre h 8 (Or.inr (Or.inl rfl))
  have e2 := elem_eq hpre h 16 (Or.inr (Or.inr (Or.inl rfl)))
  have e3 := elem_eq hpre h 24 (Or.inr (Or.inr (Or.inr rfl)))
  simp only [BitVec.add_zero] at e0
  exact ⟨e0, e1, e2, e3⟩

theorem heap_valid {a : Word} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat + 8 ≤ heapEnd)
    (h3 : a.toNat % 8 = 0) : Sym.validAccess 8 a = true := by
  rw [Sym.validAccess_eight]
  simp only [heapEnd] at h2
  omega

/-- A slot whose tag is nonzero exactly when the element's is, and whose value is the element's
when that tag is nonzero, holds the element. -/
theorem optEAt_of {s v : MachineState} {p : Word}
    (htag : v.getMem p = 0 ↔ s.getMem (s.getReg .x11) = 0)
    (hval : s.getMem (s.getReg .x11) ≠ 0 → eAt v (p + 8) = eAt s (s.getReg .x11 + 8)) :
    Transcript.optEAt v p = X s := by
  unfold X Transcript.optEAt
  by_cases h0 : s.getMem (s.getReg .x11) = 0
  · simp only [htag, h0, ↓reduceIte]
  · simp only [htag, h0, ↓reduceIte, hval h0]

theorem optEAt_congr {u v : MachineState} {p : Word} (e0 : v.getMem p = u.getMem p)
    (e1 : v.getMem (p + 8) = u.getMem (p + 8)) (e2 : v.getMem (p + 8 + 8) = u.getMem (p + 8 + 8))
    (e3 : v.getMem (p + 8 + 16) = u.getMem (p + 8 + 16)) :
    Transcript.optEAt v p = Transcript.optEAt u p := by
  unfold Transcript.optEAt eAt
  rw [e0, e1, e2, e3]

/-! ## The loop -/

def measure (u : MachineState) : Nat := (u.getReg .x13).toNat - (u.getReg .x11).toNat

def Done (s u : MachineState) (nx P : Word) : Prop := LastInv s u nx P ∨ Dead Image.code u

theorem body {s : MachineState} (hpre : Bus.OptFromElemPre s) {nx P : Word} (hP : BufOk s P nx)
    (u : MachineState) (hinv : ∃ k, LoopInv s u nx P k) :
    (∃ v, Reaches Image.code u v ∧ Done s v nx P) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ k, LoopInv s v nx P k) ∧ measure v < measure u) := by
  obtain ⟨k, hu⟩ := hinv
  have hk := hu.lt
  have hPa := hP.align
  have hPf := hP.fits
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 32 ≤ nx.toNat := by
    rcases hP.range with h | h
    · omega
    · exact h
  have hlo := hpre.heap.lo
  have hb := bounds hpre
  have he := ValidMemRange.bounds (elemValid hpre) (by decide)
  obtain ⟨hsp, -⟩ := hu.inv.saved
  obtain ⟨e0, e1, e2, e3⟩ := elem_eqs hpre hu.inv
  -- the tag: a `Some` copies its value to `S - 56` first
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800107fc_spec hu.pc (by rv_eval [])
  have k₁ := b800107fc_keeps h₁
  have hm₁ := b800107fc_mem_same h₁
  have pre (w : MachineState) (hw : Reaches Image.code u w) (hpcw : w.pc = 0x800107d8)
      (hm : ∀ a, ¬ Within a (s.getReg .x2 - 56) 24 → w.getMem a = u.getMem a)
      (hun : ∀ a, a.toNat % 8 ≠ 0 → w.getMem a = u.getMem a)
      (hreg : ∀ r ∈ [Reg.x2, .x8, .x9, .x10, .x11, .x12, .x13, .x18] ++ kept,
        w.getReg r = u.getReg r)
      (htag : w.getReg .x14 = 0 ↔ s.getMem (s.getReg .x11) = 0)
      (hval : s.getMem (s.getReg .x11) ≠ 0 →
        eAt w (s.getReg .x2 - 56) = eAt s (s.getReg .x11 + 8)) :
      (∃ v, Reaches Image.code u v ∧ Done s v nx P) ∨
        (∃ v, Reaches Image.code u v ∧ (∃ k, LoopInv s v nx P k) ∧ measure v < measure u) := by
    have hsw : w.getReg .x2 = s.getReg .x2 - 80 := (hreg .x2 (by decide)).trans hsp
    have hx11 : w.getReg .x11 = P + BitVec.ofNat 64 (32 * k) := (hreg .x11 (by decide)).trans hu.x11
    obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b800107d8_spec hpcw (by
      rv_eval [hx11, hsw]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | exact heap_valid (by addr_omega [hPr, hlo, hk, hPf])
            (by addr_omega [hPr, hk, hPf]) (by addr_omega [hPa, hPr, hk, hPf]))
    have k₂ := b800107d8_keeps h
    have m₀ := b800107d8_m_x11_0 h
    have m₁ := b800107d8_m_x11_8 h
    have m₂ := b800107d8_m_x11_16 h
    have m₃ := b800107d8_m_x11_24 h
    have hm₂ := b800107d8_frame h (by rw [hx11]; addr_omega [hPr, hlo, hk, hPf])
    rw [hx11] at m₀ m₁ m₂ m₃ hm₂
    rw [hsw] at m₁ m₂ m₃
    rv_eval [] at m₁ m₂ m₃
    have hfresh (a : Word) (ha : Within a (P + BitVec.ofNat 64 (32 * k)) 32) :
        heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat := by
      addr_omega [ha, hPr, hk, hPf]
    have hmw : ∀ a, ¬ Within a (s.getReg .x2 - 56) 24 → ¬ Within a (P + BitVec.ofNat 64 (32 * k)) 32 →
        v.getMem a = u.getMem a := fun a h1 h2 ↦ (hm₂ a h2).trans (hm a h1)
    have bfw : ByteFrame u v fun a ↦ Within a (s.getReg .x2 - 56) 24 ∨
        Within a (P + BitVec.ofNat 64 (32 * k)) 32 :=
      ByteFrame.of_dwords (fun a _ ha ↦ hmw a (fun h' ↦ ha (Or.inl h')) fun h' ↦ ha (Or.inr h'))
        (fun a ha ↦ (h.unaligned (by
          rv_eval [hx11]; and_intros <;> addr_omega [hPa, hPr, hk, hPf]) a ha).trans (hun a ha))
        fun a ha ↦ by
          rcases ha with ha | ha
          · exact Or.inl (within_of_alignDown (by addr_omega [hb]) (by decide) ha)
          · exact Or.inr (within_of_alignDown (by addr_omega [hPa, hPr, hk, hPf]) (by decide) ha)
    have inv' := hu.inv.step hpre bfw (fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
        · exact Or.inr (Or.inr (hfresh a ha)))
      ((bfw.getMem fun i hi ha ↦ by
          rcases ha with ha | ha
          · addr_omega [ha, hi, hb, hpre.stack.next]
          · have := hfresh _ ha; addr_omega [this, hPf, hi]).trans hu.inv.next)
      (Nat.le_refl _) hPf fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (hreg r (mem_of_mem hr _))
    have hnew : Transcript.optEAt v (P + BitVec.ofNat 64 (32 * k)) = X s := by
      refine optEAt_of (by rw [m₀]; exact htag) fun h0 ↦ ?_
      rw [← hval h0]
      apply eAt_congr <;> rv_eval [m₁, m₂, m₃]
    have hmid : Mid s v P := {
      x8 := by rw [k₂ .x8 (by decide), hreg .x8 (by decide)]; exact hu.x8
      x9 := by rw [k₂ .x9 (by decide), hreg .x9 (by decide)]; exact hu.x9
      x18 := by rw [k₂ .x18 (by decide), hreg .x18 (by decide)]; exact hu.x18
      cap := by
        rw [bfw.getMem fun i hi ha ↦ by
          rcases ha with ha | ha
          · addr_omega [ha, hi, hb]
          · have := hfresh _ ha; addr_omega [this, hi, hb, hPf]]
        exact hu.cap
      ptr := by
        rw [bfw.getMem fun i hi ha ↦ by
          rcases ha with ha | ha
          · addr_omega [ha, hi, hb]
          · have := hfresh _ ha; addr_omega [this, hi, hb, hPf]]
        exact hu.ptr }
    have hel (j : Nat) (hj : j < k + 1) :
        Transcript.optEAt v (P + BitVec.ofNat 64 (32 * j)) = X s := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hq (a : Word) (h1 : (P + BitVec.ofNat 64 (32 * j)).toNat ≤ a.toNat)
            (h2 : a.toNat < (P + BitVec.ofNat 64 (32 * j)).toNat + 32) : v.getMem a = u.getMem a :=
          hmw a (by addr_omega [h1, h2, hj, hk, hPr, hPf, hb]) (by addr_omega [h1, h2, hj, hk, hPr, hPf])
        rw [← hu.elems j hj]
        exact optEAt_congr (hq _ (by addr_omega [hj, hk, hPr, hPf]) (by addr_omega [hj, hk, hPr, hPf]))
          (hq _ (by addr_omega [hj, hk, hPr, hPf]) (by addr_omega [hj, hk, hPr, hPf]))
          (hq _ (by addr_omega [hj, hk, hPr, hPf]) (by addr_omega [hj, hk, hPr, hPf]))
          (hq _ (by addr_omega [hj, hk, hPr, hPf]) (by addr_omega [hj, hk, hPr, hPf]))
      · exact hnew
    have hx13 : u.getReg .x13 = P + BitVec.ofNat 64 (32 * ((s.getReg .x12).toNat - 1)) := hu.x13
    have hx11v : v.getReg .x11 = P + BitVec.ofNat 64 (32 * (k + 1)) := by
      rw [b800107d8_x11 h, hx11]; addr_omega [hk, hPr, hPf]
    by_cases hlast : k + 2 = (s.getReg .x12).toNat
    · -- the length `n - 1`, then the last copy
      obtain ⟨w', hr', h'⟩ := Sym.BlockSpec.reaches b80010810_spec
        (b800107d8_pc_taken h (by rw [hx11, hreg .x13 (by decide), hx13]; addr_omega [hlast, hPr, hPf]))
        (by rv_eval [])
      have k₃ := b80010810_keeps h'
      have hm₃ := b80010810_mem_same h'
      refine Or.inl ⟨w', hw.trans (hr.trans hr'), Or.inl {
        x8 := (k₃ .x8 (by decide)).trans hmid.x8
        x9 := (k₃ .x9 (by decide)).trans hmid.x9
        x18 := (k₃ .x18 (by decide)).trans hmid.x18
        cap := (hm₃ _).trans hmid.cap
        ptr := (hm₃ _).trans hmid.ptr
        inv := inv'.same hpre hm₃ k₃
        pc := b80010810_pc h'
        pos := by omega
        x10 := by
          rw [b80010810_x10 h', k₂ .x10 (by decide), hreg .x10 (by decide), hu.x10,
            k₂ .x18 (by decide), hreg .x18 (by decide), hu.x18]
          addr_omega [hlast]
        x11 := by rw [k₃ .x11 (by decide), hx11v]; congr 3; omega
        elems := fun j hj ↦
          (optEAt_congr (hm₃ _) (hm₃ _) (hm₃ _) (hm₃ _)).trans (hel j (by omega)) }⟩
    · refine Or.inr ⟨v, hw.trans hr, ⟨k + 1, {
        toMid := hmid
        inv := inv'
        pc := b800107d8_pc_not_taken h (by
          rw [hx11, hreg .x13 (by decide), hx13]; addr_omega [hlast, hk, hPr, hPf])
        lt := by omega
        x10 := by rw [k₂ .x10 (by decide), hreg .x10 (by decide)]; exact hu.x10
        x11 := hx11v
        x12 := by rw [k₂ .x12 (by decide), hreg .x12 (by decide)]; exact hu.x12
        x13 := by rw [k₂ .x13 (by decide), hreg .x13 (by decide)]; exact hu.x13
        elems := hel }⟩, ?_⟩
      simp only [measure]
      rw [k₂ .x13 (by decide), hreg .x13 (by decide), hx11v, hu.x13, hu.x11]
      addr_omega [hk, hPr, hPf]
  have htag₀ : u.getReg .x12 = s.getMem (s.getReg .x11) := hu.x12
  by_cases h0 : s.getMem (s.getReg .x11) = 0
  · obtain ⟨w, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80010800_spec
      (b800107fc_pc_not_taken h₁ (htag₀.trans h0)) (by rv_eval [])
    have k₂ := b80010800_keeps h₂
    have hm₂ := b80010800_mem_same h₂
    exact pre w (hr₁.trans hr₂) (b80010800_pc h₂) (fun a _ ↦ (hm₂ a).trans (hm₁ a))
      (fun a _ ↦ (hm₂ a).trans (hm₁ a))
      (fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _)))
      (by rw [b80010800_x14 h₂]; exact ⟨fun _ ↦ h0, fun _ ↦ rfl⟩) fun h ↦ absurd h0 h
  · obtain ⟨w, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800107bc_spec
      (b800107fc_pc_taken h₁ (htag₀ ▸ h0)) (by
        rv_eval [(k₁ .x2 (by decide)).trans hsp, (k₁ .x9 (by decide)).trans hu.x9]
        and_intros <;> first | valid_access hpre.stack.valid [hb] | valid_access (elemValid hpre) [he])
    have k₂ := b800107bc_keeps h₂
    have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 80 := (k₁ .x2 (by decide)).trans hsp
    have hx9₁ : u₁.getReg .x9 = s.getReg .x11 := (k₁ .x9 (by decide)).trans hu.x9
    have hm₂ := b800107bc_frame h₂ (by rw [hsp₁]; addr_omega [hb])
    rw [hsp₁] at hm₂
    rv_eval [] at hm₂
    have v₀ := b800107bc_m_x2_24 h₂
    have v₁ := b800107bc_m_x2_32 h₂
    have v₂ := b800107bc_m_x2_40 h₂
    rw [hsp₁, hx9₁] at v₀ v₁ v₂
    rv_eval [hm₁, e1, e2, e3] at v₀ v₁ v₂
    exact pre w (hr₁.trans hr₂) (b800107bc_pc h₂) (fun a ha ↦ (hm₂ a ha).trans (hm₁ a))
      (fun a ha ↦ (h₂.unaligned (by rv_eval [hsp₁]; and_intros <;> addr_omega [hb]) a ha).trans
        (hm₁ a))
      (fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _)))
      (by rw [b800107bc_x14 h₂]; exact ⟨fun h ↦ absurd h (by decide), fun h ↦ absurd h h0⟩)
      fun _ ↦ by apply eAt_congr <;> rv_eval [v₀, v₁, v₂]

/-- The last copy, the element moved in. -/
theorem last {s u : MachineState} {nx P : Word} (hpre : Bus.OptFromElemPre s) (hP : BufOk s P nx)
    (hu : LastInv s u nx P) : ∃ v, Reaches Image.code u v ∧ ExitInv s v nx P := by
  have hk := hu.pos
  have hPa := hP.align
  have hPf := hP.fits
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 32 ≤ nx.toNat := by
    rcases hP.range with h | h
    · omega
    · exact h
  have hlo := hpre.heap.lo
  have hb := bounds hpre
  have he := ValidMemRange.bounds (elemValid hpre) (by decide)
  obtain ⟨e0, e1, e2, e3⟩ := elem_eqs hpre hu.inv
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b80010818_spec hu.pc (by
    rv_eval [hu.x11, hu.x9]
    and_intros <;> first
      | valid_access (elemValid hpre) [he]
      | exact heap_valid (by addr_omega [hPr, hlo, hk, hPf])
          (by addr_omega [hPr, hk, hPf]) (by addr_omega [hPa, hPr, hk, hPf]))
  have k₁ := b80010818_keeps h
  have m₀ := b80010818_m_x11_0 h
  have m₁ := b80010818_m_x11_8 h
  have m₂ := b80010818_m_x11_16 h
  have m₃ := b80010818_m_x11_24 h
  have hm := b80010818_frame h (by rw [hu.x11]; addr_omega [hPr, hlo, hk, hPf])
  rw [hu.x11] at m₀ m₁ m₂ m₃ hm
  rw [hu.x9] at m₀ m₁ m₂ m₃
  rw [e0] at m₀
  rw [e1] at m₁
  rw [e2] at m₂
  rw [e3] at m₃
  have hnew : Transcript.optEAt v (P + BitVec.ofNat 64 (32 * ((s.getReg .x12).toNat - 1))) = X s :=
    optEAt_of (by rw [m₀]) fun _ ↦ by apply eAt_congr <;> rv_eval [m₁, m₂, m₃]
  have hfresh (a : Word) (ha : Within a (P + BitVec.ofNat 64 (32 * ((s.getReg .x12).toNat - 1)))
      32) : heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat := by
    addr_omega [ha, hPr, hk, hPf]
  refine ⟨v, hr, {
    x8 := (k₁ .x8 (by decide)).trans hu.x8
    x9 := (k₁ .x9 (by decide)).trans hu.x9
    x18 := (k₁ .x18 (by decide)).trans hu.x18
    cap := (hm _ (by addr_omega [hPr, hk, hPf, hb])).trans hu.cap
    ptr := (hm _ (by addr_omega [hPr, hk, hPf, hb])).trans hu.ptr
    inv := hu.inv.step hpre (ByteFrame.of_memFrame hm (by addr_omega [hPa, hPr, hk, hPf])
        (by decide) (h.unaligned (by rv_eval [hu.x11]; and_intros <;> addr_omega [hPa, hPr, hk, hPf])))
      (fun a ha ↦ Or.inr (Or.inr (hfresh a ha)))
      ((hm _ fun hw ↦ by have := hfresh _ hw; addr_omega [this, hPf]).trans hu.inv.next)
      (Nat.le_refl _) hPf fun r hr ↦ k₁ r (mem_of_mem hr _)
    pc := b80010818_pc h
    x10 := by rw [b80010818_x10 h, hu.x10]; addr_omega [hk]
    elems := fun j hj ↦ by
      rcases Nat.lt_or_ge j ((s.getReg .x12).toNat - 1) with hj' | hj'
      · have hq (a : Word) (h1 : (P + BitVec.ofNat 64 (32 * j)).toNat ≤ a.toNat)
            (h2 : a.toNat < (P + BitVec.ofNat 64 (32 * j)).toNat + 32) : v.getMem a = u.getMem a :=
          hm a (by addr_omega [h1, h2, hj', hk, hPr, hPf])
        rw [← hu.elems j hj']
        exact optEAt_congr (hq _ (by addr_omega [hj', hk, hPr, hPf]) (by addr_omega [hj', hk, hPr, hPf]))
          (hq _ (by addr_omega [hj', hk, hPr, hPf]) (by addr_omega [hj', hk, hPr, hPf]))
          (hq _ (by addr_omega [hj', hk, hPr, hPf]) (by addr_omega [hj', hk, hPr, hPf]))
          (hq _ (by addr_omega [hj', hk, hPr, hPf]) (by addr_omega [hj', hk, hPr, hPf]))
      · rw [show j = (s.getReg .x12).toNat - 1 by omega]; exact hnew }⟩

/-! ## The epilogue -/

theorem exit {s u : MachineState} {nx P : Word} (hpre : Bus.OptFromElemPre s) (hP : BufOk s P nx)
    (hPle : P.toNat ≤ nx.toNat) (hu : ExitInv s u nx P) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
      Bus.OptFromElemPost s t ∧ (vecPtr t (s.getReg .x10)).toNat ≤ heapNext t) ∨
        Dead Image.code t) := by
  have hb := bounds hpre
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hPa := hP.align
  have hPf := hP.fits
  obtain ⟨hsp, sl1, sl2, sl3, sl4⟩ := hu.inv.saved
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8001083c_spec hu.pc (by
    rv_eval [hsp, hu.x8]
    and_intros <;> first
      | addr_omega [hb, hos]
      | valid_access hpre.stack.valid [hb]
      | valid_access (outValid hpre) [hb])
  have k := b8001083c_keeps ht
  have pc := b8001083c_pc ht
  have x2 := b8001083c_x2 ht
  have x8 := b8001083c_x8 ht
  have x9 := b8001083c_x9 ht
  have x18 := b8001083c_x18 ht
  have m₀ := b8001083c_m_x8_0 ht
  have m₁ := b8001083c_m_x8_8 ht
  have m₂ := b8001083c_m_x8_16 ht
  have hm := b8001083c_frame ht (by rw [hu.x8]; addr_omega [hb])
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
      frame := hbf.mono fun a ha ↦ ?_ }, by simp only [vecPtr, m₁, hn]; exact hPle⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k _ (by decide)).trans (hu.inv.kept _ (by decide))
  · simp only [RawVecOk, Buf, vecPtr, vecCap, m₀, m₁]
    refine ⟨hPa, ?_⟩
    rcases hP.range with h0 | h0
    · exact Or.inl (by rw [h0])
    · exact Or.inr ⟨by omega, by rw [hn]; omega⟩
  · simp only [vecLen, vecCap, m₀, m₂, le_refl]
  · simp only [vecPtr, m₁, Transcript.optEListAt]
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun e he ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    rw [List.mem_range] at hj
    have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 32 ≤ nx.toNat := by
      rcases hP.range with h | h
      · omega
      · exact h
    have hq (a : Word) (h1 : (P + BitVec.ofNat 64 (32 * j)).toNat ≤ a.toNat)
        (h2 : a.toNat < (P + BitVec.ofNat 64 (32 * j)).toNat + 32) : t.getMem a = u.getMem a :=
      hm a (by addr_omega [h1, h2, hj, hPr, hPf, hof.1, hb])
    rw [optEAt_congr (hq _ (by addr_omega [hj, hPr, hPf]) (by addr_omega [hj, hPr, hPf]))
      (hq _ (by addr_omega [hj, hPr, hPf]) (by addr_omega [hj, hPr, hPf]))
      (hq _ (by addr_omega [hj, hPr, hPf]) (by addr_omega [hj, hPr, hPf]))
      (hq _ (by addr_omega [hj, hPr, hPf]) (by addr_omega [hj, hPr, hPf]))]
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

/-- **`<Option<E>>::from_elem` meets its contract**, given `try_allocate_in`'s and `reserve`'s
(room enough), and the buffer lies below `NEXT` (dangling, at the alignment, when empty). -/
theorem opt_from_elem_below (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x8001086c) :
    FunSpec Image.code 0x80010724 Bus.OptFromElemPre fun s t ↦
      Bus.OptFromElemPost s t ∧ (vecPtr t (s.getReg .x10)).toNat ≤ heapNext t := by
  intro s hpc hpre
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010724_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80010724_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack80 hpre)
    (by rw [b80010724_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b80010724_m_x2_n8 h₁, b80010724_m_x2_n16 h₁, b80010724_m_x2_n24 h₁,
        b80010724_m_x2_n32 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    ((b80010724_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 80 := b80010724_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 56 := b80010724_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = s.getReg .x2 - 128 := by
    simp only [stackLo, tryAllocStack, hsp₁, Sym.sub_sub_lit]; rfl
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b80010724_x13 h₁]; decide
    size := by rw [b80010724_x14 h₁]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b80010724_pc h₁) hpre₁
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
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 80 := (hpres₂.reg .x2).trans hsp₁
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010760_spec
    (by rw [hpc₂, returnAddress_eq, b80010724_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 56)) 0 with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b80010760_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b80010760_keeps h₃
  have hm₃ := b80010760_mem_same h₃
  have inv₃ := inv₂.same hpre hm₃ k₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  have hdang := hpost₂.dangling (by rw [hx10₁]; exact htag)
  rw [hx10₁, b80010724_x11 h₁, b80010724_x13 h₁] at hdang
  rw [hx10₁, b80010724_x11 h₁] at hcap hbuf
  rw [b80010724_x14 h₁, b80010724_x13 h₁] at hbuf
  rv_eval [] at hcap hbuf hdang
  obtain ⟨P, hP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 40) := ⟨_, rfl⟩
  rw [← hP] at hbuf hdang
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 80 := (k₃ .x2 (by decide)).trans hsp₂
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₃.getReg r = t₁.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80010768_spec
    (b80010760_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b80010768_keeps h₄
  have v₀ := b80010768_m_x2_0 h₄
  have v₁ := b80010768_m_x2_8 h₄
  have v₂ := b80010768_m_x2_16 h₄
  have hm₄ := b80010768_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rw [hsp₃] at v₀ v₁ v₂ hm₄
  rv_eval [hm₃] at v₀ v₁ v₂
  rw [hcap] at v₀
  rw [← hP] at v₁
  have inv₄ := inv₃.step hpre (ByteFrame.of_memFrame hm₄ (by addr_omega [hb]) (by decide)
      (h₄.unaligned (by rv_eval [hsp₃]; and_intros <;> addr_omega [hb])))
    (fun a ha ↦ Or.inl (Or.inr (by addr_omega [ha, hb])))
    ((hm₄ _ (by addr_omega [hb, hnx8])).trans inv₃.next) (Nat.le_refl _) inv₃.fits
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 80 := by rw [b80010768_x10 h₄, hsp₃]
  have hx11₄ : t₄.getReg .x11 = s.getReg .x12 := by
    rw [b80010768_x11 h₄, hreg .x18 (by decide), b80010724_x18 h₁]
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, -, hm₅⟩ | hdead⟩ := hR.call hr₄ (b80010768_pc h₄)
    ⟨by rw [hx10₄]; valid_sub hst.valid [hb], by
      simp only [vecLen, vecCap]
      rw [hx10₄, hx11₄, show s.getReg .x2 - 80 + 16 = s.getReg .x2 - 64 by rv_eval [], v₀, v₂]
      simp⟩
  swap
  · exact ⟨t₅, hr₂.trans (hr₃.trans hr₅), Or.inr hdead⟩
  have inv₅ := inv₄.same hpre hm₅ (l := calleeSaved) hpres₅ (by decide)
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 80 := by
    rw [hpres₅.reg .x2, k₄ .x2 (by decide), hsp₃]
  have hreg₅ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₅.getReg r = t₁.getReg r := by
    rw [hpres₅ r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _),
      hreg r hr]
  have hmid₅ : Mid s t₅ P := {
    x8 := by rw [hreg₅ .x8 (by decide), b80010724_x8 h₁]
    x9 := by rw [hreg₅ .x9 (by decide), b80010724_x9 h₁]
    x18 := by rw [hreg₅ .x18 (by decide), b80010724_x18 h₁]
    cap := by rw [hm₅]; exact v₀
    ptr := by rw [hm₅]; exact v₁ }
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8001078c_spec
    (by rw [hpc₅, returnAddress_eq, b80010768_x1 h₄]; decide) (by
      rv_eval [hsp₅]
      and_intros <;> valid_access hst.valid [hb])
  have k₆ := b8001078c_keeps h₆
  have hm₆ := b8001078c_mem_same h₆
  have inv₆ := inv₅.same hpre hm₆ k₆
  have hl₆ : t₅.getMem (s.getReg .x2 - 64) = 0 := by rw [hm₅]; exact v₂
  have hp₆ : t₅.getMem (s.getReg .x2 - 72) = P := hmid₅.ptr
  have hx10₆ : t₆.getReg .x10 = 0 := by rw [b8001078c_x10 h₆, hsp₅]; rv_eval [hl₆]
  have hx11₆ : t₆.getReg .x11 = P := by rw [b8001078c_x11 h₆, hsp₅]; rv_eval [hl₆, hp₆]
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
  have hreach := hr₂.trans (hr₃.trans (hr₅.trans hr₆))
  have hPr : (s.getReg .x12).toNat = 0 ∨ (heapNext s ≤ P.toNat ∧
      P.toNat + (s.getReg .x12).toNat * 32 ≤ (t₂.getMem nextAddr).toNat) := hBuf.range
  have hPf := hBuf.fits
  have hPle : P.toNat ≤ (t₂.getMem nextAddr).toNat := by
    have hlo := hheap.lo
    simp only [heapStart, heapNext] at hlo
    have hm2 := hpost₂.mono
    rw [hn₁] at hm2
    simp only [heapNext] at hm2
    rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h0 | h0
    · rw [hdang (BitVec.eq_of_toNat_eq h0)]
      exact Nat.le_trans (Nat.le_trans (by decide) hlo) hm2
    · rcases hPr with h | h
      · omega
      · omega
  have finish (u : MachineState) (hu : Reaches Image.code s u)
      (hl : LastInv s u (t₂.getMem nextAddr) P) : ∃ t, Reaches Image.code s t ∧
        ((t.pc = returnAddress s ∧ Preserves s t ∧ Bus.OptFromElemPost s t ∧
          (vecPtr t (s.getReg .x10)).toNat ≤ heapNext t) ∨ Dead Image.code t) := by
    obtain ⟨v, hv, hx⟩ := last hpre hBuf hl
    obtain ⟨t, ht, hres⟩ := exit hpre hBuf hPle hx
    exact ⟨t, hu.trans (hv.trans ht), hres⟩
  by_cases hlt : (s.getReg .x12).toNat < 2
  · have hpc₇ := b8001078c_pc_taken h₆ (by rw [hmid₅.x18]; exact hlt)
    obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80010808_spec hpc₇ (by rv_eval [])
    have k₇ := b80010808_keeps h₇
    have hm₇ := b80010808_mem_same h₇
    have inv₇ := inv₆.same hpre hm₇ k₇
    have hmid₇ : Mid s t₇ P := {
      x8 := (k₇ .x8 (by decide)).trans hmid₆.x8
      x9 := (k₇ .x9 (by decide)).trans hmid₆.x9
      x18 := (k₇ .x18 (by decide)).trans hmid₆.x18
      cap := (hm₇ _).trans hmid₆.cap
      ptr := (hm₇ _).trans hmid₆.ptr }
    by_cases h0 : s.getReg .x12 = 0
    · obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8001080c_spec
        (b80010808_pc_not_taken h₇ (by rw [hmid₆.x18]; exact h0)) (by rv_eval [])
      have k₈ := b8001080c_keeps h₈
      have hm₈ := b8001080c_mem_same h₈
      obtain ⟨t, hr, ht⟩ := exit hpre hBuf hPle {
        x8 := (k₈ .x8 (by decide)).trans hmid₇.x8
        x9 := (k₈ .x9 (by decide)).trans hmid₇.x9
        x18 := (k₈ .x18 (by decide)).trans hmid₇.x18
        cap := (hm₈ _).trans hmid₇.cap
        ptr := (hm₈ _).trans hmid₇.ptr
        inv := inv₇.same hpre hm₈ k₈
        pc := b8001080c_pc h₈
        x10 := by rw [k₈ .x10 (by decide), k₇ .x10 (by decide), hx10₆, h0]
        elems := fun j hj ↦ by rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j) }
      exact ⟨t, hreach.trans (hr₇.trans (hr₈.trans hr)), ht⟩
    · have h1 : (s.getReg .x12).toNat = 1 := by
        have : (s.getReg .x12).toNat ≠ 0 := fun h ↦ h0 (BitVec.eq_of_toNat_eq h)
        omega
      exact finish t₇ (hreach.trans hr₇) {
        toMid := hmid₇, inv := inv₇
        pc := b80010808_pc_taken h₇ (by rw [hmid₆.x18]; exact h0)
        pos := by omega
        x10 := by rw [k₇ .x10 (by decide), hx10₆, h1]; rfl
        x11 := by rw [k₇ .x11 (by decide), hx11₆, h1]; simp
        elems := fun j hj ↦ by omega }
  have hPr' : heapNext s ≤ P.toNat ∧
      P.toNat + (s.getReg .x12).toNat * 32 ≤ (t₂.getMem nextAddr).toNat := by
    rcases hPr with h | h
    · omega
    · exact h
  have hsp₆ : t₆.getReg .x2 = s.getReg .x2 - 80 := (k₆ .x2 (by decide)).trans hsp₅
  have he := ValidMemRange.bounds (elemValid hpre) (by decide)
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800107a4_spec
    (b8001078c_pc_not_taken h₆ (by rw [hmid₅.x18]; show 2 ≤ _; omega)) (by
      rv_eval [hmid₆.x9]; valid_access (elemValid hpre) [he])
  have k₇ := b800107a4_keeps h₇
  have hm₇ := b800107a4_mem_same h₇
  have inv₇ := inv₆.same hpre hm₇ k₇
  obtain ⟨e0, -, -, -⟩ := elem_eqs hpre inv₆
  obtain ⟨t, hr, ht⟩ := Reaches.loop (fun u ↦ ∃ k, LoopInv s u (t₂.getMem nextAddr) P k)
    measure (fun u ↦ Done s u (t₂.getMem nextAddr) P) (body hpre hBuf) t₇ ⟨0, {
      toMid := {
        x8 := (k₇ .x8 (by decide)).trans hmid₆.x8
        x9 := (k₇ .x9 (by decide)).trans hmid₆.x9
        x18 := (k₇ .x18 (by decide)).trans hmid₆.x18
        cap := (hm₇ _).trans hmid₆.cap
        ptr := (hm₇ _).trans hmid₆.ptr }
      inv := inv₇
      pc := b800107a4_pc h₇
      lt := by omega
      x10 := (k₇ .x10 (by decide)).trans hx10₆
      x11 := by rw [k₇ .x11 (by decide), hx11₆]; simp
      x12 := by rw [b800107a4_x12 h₇, hmid₆.x9, e0]
      x13 := by
        rw [b800107a4_x13 h₇, b8001078c_x14 h₆, b8001078c_x13 h₆, k₆ .x18 (by decide), hmid₅.x18,
          hsp₅]
        rv_eval [hl₆, hp₆]
        addr_omega [hPr', hPf, hlt]
      elems := fun j hj ↦ absurd hj (Nat.not_lt_zero j) }⟩
  rcases ht with ht | hdead
  · exact finish t (hreach.trans (hr₇.trans hr)) ht
  · exact ⟨t, hreach.trans (hr₇.trans hr), Or.inr hdead⟩

/-- `opt_from_elem_below` without the pointer's bound. -/
theorem opt_from_elem_spec (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x8001086c) :
    Bus.OptFromElemSpec := fun s hpc hpre ↦ by
  obtain ⟨t, hr, h⟩ := opt_from_elem_below hT hR s hpc hpre
  exact ⟨t, hr, h.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, c.1⟩⟩

end Rv64Verifier.Proofs.Multilinear.OptFromElem
