import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Blocks.F28

/-!
# `verifier::field::powers`

```rust
pub fn powers(base: E, count: usize) -> Vec<E> {
    let mut out = Vec::with_capacity(count);
    let mut power = ONE;
    for _ in 0..count {
        out.push(power);
        power *= base;
    }
    out
}
```

compiled at `0x80007dfc` (`Blocks/F28.lean`), with `S` the entry's `sp`: `0x80007dfc` saves `ra`,
`s0`..`s6` in a 144-byte frame (`s0` = the result, `s1` = `count`, `s2` = the base) and calls
`try_allocate_in(S - 88, count, 0, 8, 24)`; `0x80007e48` traps on `Err`; `0x80007e50` makes the
`Vec` at `S - 136` (`s3` = the capacity, `s4` = the buffer) and `power = ONE` at `S - 112`;
`0x80007e78` zeroes the offset `s5` and the length `s6`; the loop at `0x80007edc` grows the
`Vec` when full (never: the capacity is `count`), `0x80007e84` pushes `power` and calls
`mul(S - 88, power, base)`, `0x80007ebc` makes the product the power; `0x80007ef8` copies the
`Vec` out, restores and returns.

`mul`'s contract frames doublewords, so the frame here (`Dw`) is of doublewords: one outside
what may be written, either unaligned or with its eight bytes outside, keeps its value.
-/

namespace Rv64Verifier.Proofs.Multilinear.Powers
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords Rv64Verifier.Blocks.F28
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the run may have written while `NEXT` reached `nx`. -/
@[rv_addr] def PW (s : MachineState) (nx a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s powersStack) powersStack ∨
    Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)

def keptRegs : List Reg := [.x23, .x24, .x25, .x26, .x27]

structure Inv (s u : MachineState) (nx : Word) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 144
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : u.getMem (s.getReg .x2 - 64) = s.getReg .x22
  kept : ∀ r ∈ keptRegs, u.getReg r = s.getReg r
  dw : DwFrame s u (PW s nx)
  next : u.getMem nextAddr = nx
  mono : heapNext s ≤ nx.toNat
  fits : nx.toNat ≤ heapEnd

theorem bounds {s : MachineState} (h : PowersPre s) :
    0x78000000 + 1168 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.out (by decide)
  simp only [powersStack, mulStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- A step writing `X`, within what may be written and below the saved registers. -/
theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop} (hpre : PowersPre s)
    (h : Inv s u nx) (hX : DwFrame u v X) (hsub : ∀ a, X a → PW s nx' a)
    (hslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - 64) 64)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: keptRegs, v.getReg r = u.getReg r) : Inv s v nx' := by
  have hb := bounds hpre
  have slot (o : Nat) (h1 : 8 ≤ o) (h2 : o ≤ 64) (h3 : o % 8 = 0) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
    hX _ (fun hx ↦ hslot _ hx (by addr_omega [hb, h1, h2]))
      (Or.inr fun i hi hx ↦ hslot _ hx (by addr_omega [hb, h1, h2, hi]))
  have mono (a : Word) (ha : PW s nx a) : PW s nx' a := by
    simp only [PW] at ha ⊢
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨ha.1, by omega⟩))
  refine ⟨(hr _ (by decide)).trans h.sp, (slot 8 (by decide) (by decide) rfl).trans h.ra,
    (slot 16 (by decide) (by decide) rfl).trans h.s0, (slot 24 (by decide) (by decide) rfl).trans h.s1,
    (slot 32 (by decide) (by decide) rfl).trans h.s2, (slot 40 (by decide) (by decide) rfl).trans h.s3,
    (slot 48 (by decide) (by decide) rfl).trans h.s4, (slot 56 (by decide) (by decide) rfl).trans h.s5,
    (slot 64 (by decide) (by decide) rfl).trans h.s6,
    fun r hr' ↦ (hr r (List.mem_cons_of_mem _ hr')).trans (h.kept r hr'), ?_, hnx,
    Nat.le_trans h.mono hle, hend⟩
  intro a ha hb'
  rw [hX a (fun hx ↦ ha (hsub a hx)) (by
      rcases hb' with hb' | hb'
      · exact Or.inl hb'
      · exact Or.inr fun i hi hx ↦ hb' i hi (hsub _ hx))]
  exact h.dw a (fun hx ↦ ha (mono a hx)) (by
    rcases hb' with hb' | hb'
    · exact Or.inl hb'
    · exact Or.inr fun i hi hx ↦ hb' i hi (mono _ hx))

/-- `.rodata` from the frame: it misses what may be written. -/
theorem rodataOk {s u : MachineState} {nx : Word} (hpre : PowersPre s) (h : Inv s u nx) :
    RodataOk u := by
  have hb := bounds hpre
  have hro := hpre.stack.rodata
  have hor := hpre.outRodata
  have hfit := h.fits
  have miss (a : Word) (ha : Within a rodataBase Rv64Verifier.rodataSize) :
      ¬ PW s nx a := by
    simp only [PW]
    rintro (hw | hw | hw | hw)
    · addr_omega [hw, ha, hor]
    · addr_omega [hw, ha, hro, hb]
    · addr_omega [hw, ha]
    · addr_omega [hw, ha, hfit]
  intro p hp
  have hin := within_of_mem_rodataWords hp
  rw [h.dw p.1 (miss _ (by addr_omega [hin])) (by
    by_cases h8 : p.1.toNat % 8 = 0
    · exact Or.inr fun i hi ↦ miss _ (by addr_omega [hin, hi, h8])
    · exact Or.inl h8)]
  exact hpre.rodata p hp

/-- The base is never written. -/
theorem base_eq {s u : MachineState} {nx : Word} (hpre : PowersPre s) (h : Inv s u nx) :
    eAt u (s.getReg .x11) = eAt s (s.getReg .x11) := by
  have hb := bounds hpre
  have he := ValidMemRange.bounds hpre.base (by decide)
  have hef := hpre.baseFree
  have hes := hpre.baseStack
  have heo := hpre.baseOut
  have hfit := h.fits
  simp only [Outside] at hef
  have miss (a : Word) (h1 : (s.getReg .x11).toNat ≤ a.toNat)
      (h2 : a.toNat < (s.getReg .x11).toNat + 24) : ¬ PW s nx a := by
    simp only [PW]
    rintro (hw | hw | hw | hw)
    · addr_omega [hw, h1, h2, he, heo]
    · addr_omega [hw, h1, h2, he, hes, hb]
    · addr_omega [hw, h1, h2, he, hef.2]
    · addr_omega [hw, h1, h2, he, hef.1, hfit]
  have w (c : Nat) (hc : c = 0 ∨ c = 8 ∨ c = 16) :
      u.getMem (s.getReg .x11 + BitVec.ofNat 64 c) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 c) :=
    h.dw _ (miss _ (by addr_omega [hc, he]) (by addr_omega [hc, he]))
      (Or.inr fun i hi ↦ miss _ (by addr_omega [hc, he, hi]) (by addr_omega [hc, he, hi]))
  have e0 := w 0 (Or.inl rfl)
  have e1 := w 8 (Or.inr (Or.inl rfl))
  have e2 := w 16 (Or.inr (Or.inr rfl))
  rv_eval [] at e0 e1 e2
  unfold eAt
  rw [e0, e1, e2]

theorem powersFrom_eq (acc b : E) (n : Nat) :
    LeanVM.Protocol.Verifier.powersFrom acc b n = (List.range n).map fun j ↦ acc * b ^ j := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [LeanVM.Protocol.Verifier.powersFrom, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, pow_zero, mul_one]
    refine congrArg (List.cons acc) (List.map_congr_left fun j _ ↦ ?_)
    show acc * b * b ^ j = acc * b ^ (j + 1)
    rw [pow_succ', mul_assoc]

theorem heap_valid {a : Word} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat + 8 ≤ heapEnd)
    (h3 : a.toNat % 8 = 0) : Sym.validAccess 8 a = true := by
  rw [Sym.validAccess_eight]
  simp only [heapEnd] at h2
  omega

/-- The buffer `P` of `count` elements, below `nx`. -/
structure BufOk (s : MachineState) (P nx : Word) : Prop where
  align : P.toNat % 8 = 0
  range : (s.getReg .x12).toNat = 0 ∨
    (heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ nx.toNat)

/-- The registers and the `Vec` at `S - 136` through the loop. -/
structure Mid (s u : MachineState) (P : Word) : Prop where
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x12
  x18 : u.getReg .x18 = s.getReg .x11
  x19 : u.getReg .x19 = s.getReg .x12
  x20 : u.getReg .x20 = P
  cap : u.getMem (s.getReg .x2 - 136) = s.getReg .x12
  ptr : u.getMem (s.getReg .x2 - 128) = P

/-- At `0x80007edc`, `k` powers pushed. -/
structure LoopInv (s u : MachineState) (nx P : Word) (k : Nat) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x80007edc
  lt : k < (s.getReg .x12).toNat
  x21 : u.getReg .x21 = BitVec.ofNat 64 (24 * k)
  x22 : u.getReg .x22 = BitVec.ofNat 64 k
  len : u.getMem (s.getReg .x2 - 120) = BitVec.ofNat 64 k
  power : eAt u (s.getReg .x2 - 112) = eAt s (s.getReg .x11) ^ k
  elems : ∀ j < k, eAt u (P + BitVec.ofNat 64 (24 * j)) = eAt s (s.getReg .x11) ^ j

/-- At the epilogue, every power pushed. -/
structure ExitInv (s u : MachineState) (nx P : Word) : Prop extends Mid s u P where
  inv : Inv s u nx
  pc : u.pc = 0x80007ef8
  len : u.getMem (s.getReg .x2 - 120) = s.getReg .x12
  elems : ∀ j < (s.getReg .x12).toNat,
    eAt u (P + BitVec.ofNat 64 (24 * j)) = eAt s (s.getReg .x11) ^ j

def measure (u : MachineState) : Nat := (u.getReg .x9).toNat - (u.getReg .x22).toNat

def Done (s u : MachineState) (nx P : Word) : Prop := ExitInv s u nx P ∨ Dead Image.code u

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : PowersPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: keptRegs, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (DwFrame.same hm fun _ ↦ False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    ((hm _).trans h.next) (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

/-- The end of an iteration: the loop head again, or the epilogue. -/
theorem body_tail {s u w w' : MachineState} {nx P : Word} {k : Nat}
    (hu : LoopInv s u nx P k) (hr : Reaches Image.code u w') (h₄ : b80007ebc.Holds w w')
    (hmid : Mid s w' P) (inv₄ : Inv s w' nx) (hx9 : w.getReg .x9 = s.getReg .x12)
    (hx22 : w.getReg .x22 = BitVec.ofNat 64 (k + 1))
    (hx21 : w.getReg .x21 = BitVec.ofNat 64 (24 * k))
    (hlen : w'.getMem (s.getReg .x2 - 120) = BitVec.ofNat 64 (k + 1))
    (hpw : eAt w' (s.getReg .x2 - 112) = eAt s (s.getReg .x11) ^ (k + 1))
    (hel : ∀ j < k + 1, eAt w' (P + BitVec.ofNat 64 (24 * j)) = eAt s (s.getReg .x11) ^ j)
    (hbound : 24 * (s.getReg .x12).toNat < 2 ^ 32) :
    (∃ v, Reaches Image.code u v ∧ Done s v nx P) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ k, LoopInv s v nx P k) ∧ measure v < measure u) := by
  have hk := hu.lt
  have k₄ := b80007ebc_keeps h₄
  by_cases hlast : k + 1 = (s.getReg .x12).toNat
  · refine Or.inl ⟨w', hr, Or.inl {
      toMid := hmid
      inv := inv₄
      pc := b80007ebc_pc_taken h₄ (by rw [hx9, hx22]; addr_omega [hlast])
      len := by rw [hlen]; addr_omega [hlast]
      elems := fun j hj ↦ hel j (by omega) }⟩
  · refine Or.inr ⟨w', hr, ⟨k + 1, {
      toMid := hmid
      inv := inv₄
      pc := b80007ebc_pc_not_taken h₄ (by rw [hx9, hx22]; addr_omega [hlast, hk, hbound])
      lt := by omega
      x21 := by rw [b80007ebc_x21 h₄, hx21]; addr_omega [hk, hbound]
      x22 := (k₄ .x22 (by decide)).trans hx22
      len := hlen
      power := hpw
      elems := hel }⟩, ?_⟩
    simp only [measure]
    rw [hmid.x9, k₄ .x22 (by decide), hx22, hu.x9, hu.x22]
    addr_omega [hk, hbound]

theorem body (hMul : MulSpec) {s : MachineState} (hpre : PowersPre s) {nx P : Word}
    (hP : BufOk s P nx) (u : MachineState) (hinv : ∃ k, LoopInv s u nx P k) :
    (∃ v, Reaches Image.code u v ∧ Done s v nx P) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ k, LoopInv s v nx P k) ∧ measure v < measure u) := by
  obtain ⟨k, hu⟩ := hinv
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hk := hu.lt
  have hPa := hP.align
  have hPf := hu.inv.fits
  have hPm := hu.inv.mono
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ nx.toNat := by
    rcases hP.range with h | h
    · omega
    · exact h
  have hlo := hpre.heap.lo
  have hsp := hu.inv.sp
  have hbs := hpre.baseStack
  have hB := ValidMemRange.bounds hpre.base (by decide)
  -- `0x80007edc`: room left
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007edc_spec hu.pc trivial
  have k₁ := b80007edc_keeps h₁
  have hm₁ := b80007edc_mem_same h₁
  have hpc₁ := b80007edc_pc_taken h₁ (by rw [hu.x22, hu.x19]; addr_omega [hk, hPr, hPf])
  have inv₁ := hu.inv.same hpre hm₁ k₁
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 144 := (k₁ .x2 (by decide)).trans hsp
  have hx20₁ : u₁.getReg .x20 = P := (k₁ .x20 (by decide)).trans hu.x20
  have hx21₁ : u₁.getReg .x21 = BitVec.ofNat 64 (24 * k) := (k₁ .x21 (by decide)).trans hu.x21
  have hx22₁ : u₁.getReg .x22 = BitVec.ofNat 64 k := (k₁ .x22 (by decide)).trans hu.x22
  -- `0x80007e84`: push `power`, call `mul`
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007e84_spec hpc₁ (by
    rv_eval [hsp₁, hx20₁, hx21₁]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact heap_valid (by addr_omega [hPr, hlo, hk, hPf]) (by addr_omega [hPr, hk, hPf])
          (by addr_omega [hPa, hPr, hk, hPf])
      | addr_omega [hPr, hk, hPf, hab, hb])
  have k₂ := b80007e84_keeps h₂
  have hm₂ : ∀ a, ¬ Within a (s.getReg .x2 - 120) 8 →
      ¬ Within a (P + BitVec.ofNat 64 (24 * k)) 24 → v.getMem a = u₁.getMem a :=
    fun a h1 h2 ↦ h₂.frame a (by
      rv_eval [hsp₁, hx20₁, hx21₁]
      and_intros <;> first | addr_omega [h1, hb] | addr_omega [h2, hPr, hk, hPf])
  have l₂ := b80007e84_m_x2_24 h₂
  have c₀ := b80007e84_m3 h₂
  have c₁ := b80007e84_m2 h₂
  have c₂ := b80007e84_m1 h₂
  rv_eval [hsp₁, hx20₁, hx21₁, hx22₁, hm₁] at l₂ c₀ c₁ c₂
  have hfr (a : Word) (ha : Within a (P + BitVec.ofNat 64 (24 * k)) 24) :
      heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat := by addr_omega [ha, hPr, hk, hPf]
  have inv₂ := inv₁.step hpre (DwFrame.of_two hm₂)
    (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inr (hfr a ha))))
    (fun a ha ↦ by
      rcases ha with ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hPr, hk, hPf, hab, hb])
    ((hm₂ _ (by addr_omega [hb, hnx8]) (fun h ↦ by have := hfr _ h; addr_omega [this, hPf])).trans
      inv₁.next) (Nat.le_refl _) hPf fun r hr ↦ k₂ r (mem_of_mem hr _)
  have hsp₂ : v.getReg .x2 = s.getReg .x2 - 144 := (k₂ .x2 (by decide)).trans hsp₁
  have hu₁v (a : Word) (h1 : ¬ Within a (s.getReg .x2 - 120) 8)
      (h2 : ¬ Within a (P + BitVec.ofNat 64 (24 * k)) 24) : v.getMem a = u.getMem a :=
    (hm₂ a h1 h2).trans (hm₁ a)
  have epow : eAt v (s.getReg .x2 - 112) = eAt s (s.getReg .x11) ^ k := by
    rw [← hu.power]; unfold eAt
    rw [hu₁v _ (by addr_omega [hb]) (by addr_omega [hb, hPr, hk, hPf, hab]),
      hu₁v (s.getReg .x2 - 112 + 8) (by addr_omega [hb]) (by addr_omega [hb, hPr, hk, hPf, hab]),
      hu₁v (s.getReg .x2 - 112 + 16) (by addr_omega [hb]) (by addr_omega [hb, hPr, hk, hPf, hab])]
  have enew : eAt v (P + BitVec.ofNat 64 (24 * k)) = eAt s (s.getReg .x11) ^ k := by
    rw [← hu.power]; unfold eAt; rw [c₀]; rv_eval [c₁, c₂]
  have hx10 : v.getReg .x10 = s.getReg .x2 - 88 := by rw [b80007e84_x10 h₂, hsp₁]; rv_eval []
  have hx11 : v.getReg .x11 = s.getReg .x2 - 112 := by rw [b80007e84_x11 h₂, hsp₁]; rv_eval []
  have hx12 : v.getReg .x12 = s.getReg .x11 := by
    rw [b80007e84_x12 h₂, k₁ .x18 (by decide), hu.x18]
  have hpre₂ : MulPre v := {
    out := by rw [hx10]; valid_sub hst.valid [hb]
    lhs := by rw [hx11]; valid_sub hst.valid [hb]
    rhs := by rw [hx12]; exact hpre.base
    stack := ⟨by valid_sub hst.valid [hb, hsp₂], by addr_omega [hb, hsp₂]⟩
    outLhs := by rw [hx10, hx11]; addr_omega [hb]
    outRhs := by rw [hx10, hx12]; addr_omega [hb, hbs, hB]
    outStack := by rw [hx10]; addr_omega [hb, hsp₂]
    lhsStack := by rw [hx11]; addr_omega [hb, hsp₂]
    rhsStack := by rw [hx12]; addr_omega [hb, hsp₂, hbs, hB]
    rodata := rodataOk hpre inv₂
    stackRodata := by addr_omega [hb, hsp₂, hst.rodata] }
  obtain ⟨w, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hdead⟩ := hMul.call hr₂ (b80007e84_pc h₂) hpre₂
  swap
  · exact Or.inl ⟨w, hr₁.trans hr₃, Or.inr hdead⟩
  have hprod := hpost₃.value
  rw [hx10, hx11, hx12, epow, base_eq hpre inv₂] at hprod
  have hfr₃ := hpost₃.frame
  rw [hx10] at hfr₃
  have hsl₃ : stackLo v mulStack = s.getReg .x2 - 1168 := by
    simp only [stackLo, hsp₂, mulStack]; rv_eval []
  rw [hsl₃] at hfr₃
  have inv₃ := inv₂.step hpre (DwFrame.of_two hfr₃)
    (fun a ha ↦ Or.inr (Or.inl (by rcases ha with ha | ha <;> addr_omega [ha, hb])))
    (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb])
    ((hfr₃ _ (by addr_omega [hb, hnx8]) (by addr_omega [hb, hnx8])).trans inv₂.next)
    (Nat.le_refl _) hPf fun r hr ↦ hpres₃ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hsp₃ : w.getReg .x2 = s.getReg .x2 - 144 := (hpres₃.reg .x2).trans hsp₂
  -- `0x80007ebc`: the product is the power
  obtain ⟨w', hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007ebc_spec
    (by rw [hpc₃, returnAddress_eq, b80007e84_x1 h₂]; decide) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b80007ebc_keeps h₄
  have hm₄ := b80007ebc_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rw [hsp₃] at hm₄
  rv_eval [] at hm₄
  have p₀ := b80007ebc_m_x2_32 h₄
  have p₁ := b80007ebc_m_x2_40 h₄
  have p₂ := b80007ebc_m_x2_48 h₄
  rv_eval [hsp₃] at p₀ p₁ p₂
  have inv₄ := inv₃.step hpre (DwFrame.of_mem hm₄)
    (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb]))) (fun a ha ↦ by addr_omega [ha, hb])
    ((hm₄ _ (by addr_omega [hb, hnx8])).trans inv₃.next) (Nat.le_refl _) hPf
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  -- what `w'` holds
  have hww (a : Word) (h1 : ¬ Within a (s.getReg .x2 - 112) 24)
      (h2 : ¬ Within a (s.getReg .x2 - 88) 24) (h3 : ¬ Within a (s.getReg .x2 - 1168) 1024) :
      w'.getMem a = v.getMem a := (hm₄ a h1).trans (hfr₃ a h2 h3)
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x22]) :
      w'.getReg r = v.getReg r := by
    rw [k₄ r (mem_of_mem hr _), hpres₃ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have hreg' (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20]) :
      v.getReg r = u.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hpw : eAt w' (s.getReg .x2 - 112) = eAt s (s.getReg .x11) ^ (k + 1) := by
    rw [pow_succ, ← hprod]; unfold eAt; rw [p₀]; rv_eval [p₁, p₂]
  have hel (j : Nat) (hj : j < k + 1) :
      eAt w' (P + BitVec.ofNat 64 (24 * j)) = eAt s (s.getReg .x11) ^ j := by
    have hw' : eAt w' (P + BitVec.ofNat 64 (24 * j)) = eAt v (P + BitVec.ofNat 64 (24 * j)) := by
      unfold eAt
      rw [hww _ (by addr_omega [hj, hk, hPr, hPf, hab, hb]) (by addr_omega [hj, hk, hPr, hPf, hab, hb])
          (by addr_omega [hj, hk, hPr, hPf, hab, hb]),
        hww (P + BitVec.ofNat 64 (24 * j) + 8) (by addr_omega [hj, hk, hPr, hPf, hab, hb])
          (by addr_omega [hj, hk, hPr, hPf, hab, hb]) (by addr_omega [hj, hk, hPr, hPf, hab, hb]),
        hww (P + BitVec.ofNat 64 (24 * j) + 16) (by addr_omega [hj, hk, hPr, hPf, hab, hb])
          (by addr_omega [hj, hk, hPr, hPf, hab, hb]) (by addr_omega [hj, hk, hPr, hPf, hab, hb])]
    rw [hw']
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [← hu.elems j hj]
      unfold eAt
      rw [hu₁v _ (by addr_omega [hj, hk, hPr, hPf, hab, hb]) (by addr_omega [hj, hk, hPr, hPf]),
        hu₁v (P + BitVec.ofNat 64 (24 * j) + 8) (by addr_omega [hj, hk, hPr, hPf, hab, hb])
          (by addr_omega [hj, hk, hPr, hPf]),
        hu₁v (P + BitVec.ofNat 64 (24 * j) + 16) (by addr_omega [hj, hk, hPr, hPf, hab, hb])
          (by addr_omega [hj, hk, hPr, hPf])]
    · exact enew
  have hmid : Mid s w' P := {
    x8 := by rw [hreg .x8 (by decide), hreg' .x8 (by decide), hu.x8]
    x9 := by rw [hreg .x9 (by decide), hreg' .x9 (by decide), hu.x9]
    x18 := by rw [hreg .x18 (by decide), hreg' .x18 (by decide), hu.x18]
    x19 := by rw [hreg .x19 (by decide), hreg' .x19 (by decide), hu.x19]
    x20 := by rw [hreg .x20 (by decide), hreg' .x20 (by decide), hu.x20]
    cap := by
      rw [hww _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]),
        hu₁v _ (by addr_omega [hb]) (by addr_omega [hb, hPr, hk, hPf, hab])]
      exact hu.cap
    ptr := by
      rw [hww _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]),
        hu₁v _ (by addr_omega [hb]) (by addr_omega [hb, hPr, hk, hPf, hab])]
      exact hu.ptr }
  have hlen : w'.getMem (s.getReg .x2 - 120) = BitVec.ofNat 64 (k + 1) := by
    rw [hww _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]), l₂]
    addr_omega [hk, hPr, hPf]
  have hx22 : w.getReg .x22 = BitVec.ofNat 64 (k + 1) := by
    rw [hpres₃.reg .x22, b80007e84_x22 h₂, hx22₁]; addr_omega [hk, hPr, hPf]
  have hx9 : w.getReg .x9 = s.getReg .x12 := by
    rw [hpres₃.reg .x9, hreg' .x9 (by decide), hu.x9]
  exact body_tail hu (hr₁.trans (hr₃.trans hr₄)) h₄ hmid inv₄ hx9 hx22
    (by rw [hpres₃.reg .x21, k₂ .x21 (by decide), hx21₁]) hlen hpw hel
    (by have := hPr.2; have := hPf; simp only [heapEnd] at *; omega)

/-! ## The epilogue -/

theorem exit {s u : MachineState} {nx P : Word} (hpre : PowersPre s) (hP : BufOk s P nx)
    (hu : ExitInv s u nx P) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ PowersPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hret := ValidMemRange.bounds hpre.out (by decide)
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hPa := hP.align
  have hPf := hu.inv.fits
  have hPm := hu.inv.mono
  have hlo := hpre.heap.lo
  have hab := hpre.stack.above
  have hsp := hu.inv.sp
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80007ef8_spec hu.pc (by
    rv_eval [hsp, hu.x8]
    and_intros <;> first
      | addr_omega [hb, hos]
      | valid_access hpre.stack.valid [hb]
      | valid_access hpre.out [hret])
  have k := b80007ef8_keeps ht
  have pc := b80007ef8_pc ht
  have x2 := b80007ef8_x2 ht
  have x8 := b80007ef8_x8 ht
  have x9 := b80007ef8_x9 ht
  have x18 := b80007ef8_x18 ht
  have x19 := b80007ef8_x19 ht
  have x20 := b80007ef8_x20 ht
  have x21 := b80007ef8_x21 ht
  have x22 := b80007ef8_x22 ht
  have m₀ := b80007ef8_m_x8_0 ht
  have m₁ := b80007ef8_m_x8_8 ht
  have m₂ := b80007ef8_m_x8_16 ht
  have hm := b80007ef8_frame ht (by rw [hu.x8]; addr_omega [hret])
  rw [hu.x8] at m₀ m₁ m₂ hm
  rv_eval [hsp, hu.inv.ra, hu.inv.s0, hu.inv.s1, hu.inv.s2, hu.inv.s3, hu.inv.s4, hu.inv.s5,
    hu.inv.s6, hu.cap, hu.ptr, hu.len] at pc x2 x8 x9 x18 x19 x20 x21 x22 m₀ m₁ m₂
  have hnt : t.getMem nextAddr = nx := (hm _ (by addr_omega [hof.2, hret])).trans hu.inv.next
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hPr : (s.getReg .x12).toNat = 0 ∨
      (heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ nx.toNat) := hP.range
  refine ⟨t, hr, Or.inl ⟨pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_, {
      heap := ⟨by rw [hn]; exact Nat.le_trans hlo hPm, by rw [hn]; exact hPf⟩
      mono := by rw [hn]; exact hPm
      vec := ⟨?_, ?_⟩
      len := by simp only [vecLen, m₂]
      elems := ?_
      fresh := ?_
      frame := fun a ha ↦ ?_ }⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x20
    · exact x21
    · exact x22
    all_goals exact (k _ (by decide)).trans (hu.inv.kept _ (by decide))
  · simp only [RawVecOk, Buf, vecPtr, vecCap, m₀, m₁]
    refine ⟨hPa, ?_⟩
    rcases hPr with h0 | h0
    · exact Or.inl (by rw [h0])
    · exact Or.inr ⟨by simp only [heapStart, heapNext] at hlo h0 ⊢; omega, by rw [hn]; omega⟩
  · simp only [vecLen, vecCap, m₀, m₂, le_refl]
  · simp only [vecEs, vecPtr, vecLen, m₁, m₂, eListAt, LeanVM.Protocol.Verifier.powers,
      powersFrom_eq, one_mul]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hPr' : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ nx.toNat := by
      rcases hPr with h | h
      · omega
      · exact h
    rw [hm.eAt (by addr_omega [hj, hPr', hPf, hof.1, hret]) (by addr_omega [hj, hPr', hPf])]
    exact hu.elems j hj
  · simp only [NewBuf, vecPtr, m₁]
    refine ⟨hPa, ?_⟩
    rcases hPr with h0 | h0
    · exact Or.inl (by rw [h0])
    · exact Or.inr ⟨h0.1, by rw [hn]; omega⟩
  · have hsub (b : Word) (hb' : PW s nx b) : PowersW s t b := by
      simp only [PW] at hb'
      rcases hb' with hw | hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn]; exact hw)))
    have h0 := ha 0 (by decide)
    simp only [BitVec.add_zero] at h0
    rw [hm a (fun hw ↦ h0 (Or.inl hw))]
    exact hu.inv.dw a (fun hw ↦ h0 (hsub a hw)) (Or.inr fun i hi hw ↦ ha i hi (hsub _ hw))

/-! ## `powers` -/

/-- **`powers` meets its contract**, given `try_allocate_in`'s and `mul`'s. -/
theorem powers_spec (hT : TryAllocZeroedSpec) (hMul : MulSpec) : PowersSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007dfc_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80007dfc_keeps h₁
  have hm₁ := b80007dfc_frame h₁ (by addr_omega [hb])
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := {
    sp := b80007dfc_x2 h₁
    ra := b80007dfc_m_x2_n8 h₁
    s0 := b80007dfc_m_x2_n16 h₁
    s1 := b80007dfc_m_x2_n24 h₁
    s2 := b80007dfc_m_x2_n32 h₁
    s3 := b80007dfc_m_x2_n40 h₁
    s4 := b80007dfc_m_x2_n48 h₁
    s5 := b80007dfc_m_x2_n56 h₁
    s6 := b80007dfc_m_x2_n64 h₁
    kept := fun r hr ↦ k₁ r (mem_of_mem hr _)
    dw := fun a ha _ ↦ hm₁ a fun hw ↦ ha (Or.inr (Or.inl (by addr_omega [hw, hb])))
    next := hm₁ _ (by addr_omega [hb, hnx8])
    mono := Nat.le_refl _
    fits := hheap.hi }
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 144 := b80007dfc_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 88 := b80007dfc_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = s.getReg .x2 - 192 := by
    simp only [stackLo, tryAllocStack, hsp₁]; rv_eval []
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b80007dfc_x13 h₁]; decide
    size := by rw [b80007dfc_x14 h₁]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b80007dfc_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := inv₁.step hpre (DwFrame.of_byte hfr₂)
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh, hn₁] at ha
        exact Or.inr (Or.inr (Or.inr ha)))
    (fun a ha ↦ by
      have := hpost₂.heap.hi
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx8]
      · simp only [Fresh] at ha; addr_omega [ha, hb, hab, this])
    rfl (by rw [← heapNext, ← heapNext, ← hn₁]; exact hpost₂.mono) hpost₂.heap.hi
    fun r hr ↦ hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 144 := (hpres₂.reg .x2).trans hsp₁
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007e48_spec
    (by rw [hpc₂, returnAddress_eq, b80007dfc_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 88)) 0 with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b80007e48_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b80007e48_keeps h₃
  have hm₃ := b80007e48_mem_same h₃
  have inv₃ := inv₂.same hpre hm₃ k₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁, b80007dfc_x11 h₁] at hcap hbuf
  rw [b80007dfc_x14 h₁, b80007dfc_x13 h₁] at hbuf
  rv_eval [] at hcap hbuf
  obtain ⟨P, hP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 72) := ⟨_, rfl⟩
  rw [← hP] at hbuf
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 144 := (k₃ .x2 (by decide)).trans hsp₂
  have hBuf : BufOk s P (t₂.getMem nextAddr) := {
    align := hbuf.1
    range := by
      rcases hbuf.2 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr ⟨hn₁ ▸ h.1, h.2⟩ }
  -- the `Vec` and `power = ONE`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007e50_spec
    (b80007e48_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b80007e50_keeps h₄
  have hm₄ := b80007e50_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rw [hsp₃] at hm₄
  rv_eval [] at hm₄
  have v₀ := b80007e50_m_x2_8 h₄
  have v₁ := b80007e50_m_x2_16 h₄
  have v₂ := b80007e50_m_x2_24 h₄
  have w₀ := b80007e50_m_x2_32 h₄
  have w₁ := b80007e50_m_x2_40 h₄
  have w₂ := b80007e50_m_x2_48 h₄
  rv_eval [hsp₃, hm₃] at v₀ v₁ v₂ w₀ w₁ w₂
  rw [hcap] at v₀
  rw [← hP] at v₁
  have inv₄ := inv₃.step hpre (DwFrame.of_mem hm₄)
    (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb]))) (fun a ha ↦ by addr_omega [ha, hb])
    ((hm₄ _ (by addr_omega [hb, hnx8])).trans inv₃.next) (Nat.le_refl _) inv₃.fits
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₄.getReg r = t₁.getReg r := by
    rw [k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have hmid₄ : Mid s t₄ P := {
    x8 := by rw [hreg .x8 (by decide), b80007dfc_x8 h₁]
    x9 := by rw [hreg .x9 (by decide), b80007dfc_x9 h₁]
    x18 := by rw [hreg .x18 (by decide), b80007dfc_x18 h₁]
    x19 := by rw [b80007e50_x19 h₄, hsp₃]; rv_eval [hm₃, hcap]
    x20 := by rw [b80007e50_x20 h₄, hsp₃]; rv_eval [hm₃, hP]
    cap := v₀
    ptr := v₁ }
  have hreach := hr₂.trans (hr₃.trans hr₄)
  by_cases h0 : s.getReg .x12 = 0
  · obtain ⟨t, hr, ht⟩ := exit hpre hBuf {
      toMid := hmid₄
      inv := inv₄
      pc := b80007e50_pc_taken h₄ (by
        rw [k₃ .x9 (by decide), hpres₂.reg .x9, b80007dfc_x9 h₁]; exact h0)
      len := by rw [v₂, h0]
      elems := fun j hj ↦ by
        have : (s.getReg .x12).toNat = 0 := by rw [h0]; rfl
        omega }
    exact ⟨t, hreach.trans hr, ht⟩
  have hlen : 0 < (s.getReg .x12).toNat := by
    rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) h0
    · exact h
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80007e78_spec
    (b80007e50_pc_not_taken h₄ (by
      rw [k₃ .x9 (by decide), hpres₂.reg .x9, b80007dfc_x9 h₁]; exact h0)) trivial
  have k₅ := b80007e78_keeps h₅
  have hm₅ := b80007e78_mem_same h₅
  obtain ⟨t, hr, ht⟩ := Reaches.loop (fun u ↦ ∃ k, LoopInv s u (t₂.getMem nextAddr) P k)
    measure (fun u ↦ Done s u (t₂.getMem nextAddr) P) (body hMul hpre hBuf) t₅ ⟨0, {
      x8 := (k₅ .x8 (by decide)).trans hmid₄.x8
      x9 := (k₅ .x9 (by decide)).trans hmid₄.x9
      x18 := (k₅ .x18 (by decide)).trans hmid₄.x18
      x19 := (k₅ .x19 (by decide)).trans hmid₄.x19
      x20 := (k₅ .x20 (by decide)).trans hmid₄.x20
      cap := (hm₅ _).trans hmid₄.cap
      ptr := (hm₅ _).trans hmid₄.ptr
      inv := inv₄.same hpre hm₅ k₅
      pc := b80007e78_pc h₅
      lt := hlen
      x21 := by rw [b80007e78_x21 h₅]; rfl
      x22 := by rw [b80007e78_x22 h₅]; rfl
      len := by rw [hm₅, v₂]; rfl
      power := by
        rw [pow_zero]
        apply eAt_eq_of_limbs
        rw [limbs_one]
        rv_eval [hm₅, w₀, w₁, w₂]
      elems := fun j hj ↦ absurd hj (Nat.not_lt_zero j) }⟩
  rcases ht with ht | hdead
  · obtain ⟨t', hr', ht'⟩ := exit hpre hBuf ht
    exact ⟨t', hreach.trans (hr₅.trans (hr.trans hr')), ht'⟩
  · exact ⟨t, hreach.trans (hr₅.trans hr), Or.inr hdead⟩

end Rv64Verifier.Proofs.Multilinear.Powers
