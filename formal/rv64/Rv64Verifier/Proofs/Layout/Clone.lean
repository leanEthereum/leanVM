import Rv64Verifier.Proofs.Layout.CloneLemmas
import Rv64Verifier.Blocks.F24

/-!
# `<Vec<Form> as Clone>::clone`, at `0x80006104`

```rust
fn clone(&self) -> Vec<Form> {          // `self` a slice: `a1`/`a2`
    let mut v = Vec::with_capacity(self.len());
    for form in self { v.push_within_capacity(form.clone()) }
    v
}
```

compiled (`Blocks/F24.lean`): `0x80006104` makes a 128-byte frame (`sp'` = the entry's `sp - 128`),
saves `ra`, `s0`..`s11` and calls `try_allocate_in(sp', len, 0, 8, 24)`; `0x80006164` traps on an
error; `0x8000616c` returns an empty `Vec` for an empty slice (`0x8000620c`); `0x80006178` sets up
the loop: `s2` walks the slice, `s8` the buffer's length fields, `s9` and `s10` count down. The loop
head `0x800061b0` calls `try_allocate_in(sp', len, 0, 8, 48)` for the form's terms (`0x800061d8`
traps on an error), `0x800061e0`/`0x800061ec` `memcpy` them unless empty, and `0x80006190` writes the
clone's header and advances. `0x8000620c` writes the `Vec` (capacity and length `len`) to `a0`,
restores and returns.
-/

namespace Rv64Verifier.Layout.Clone
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Blocks.F24
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The `j`-th source form. -/
def src (s : MachineState) (j : Nat) : Word := s.getReg .x11 + BitVec.ofNat 64 (24 * j)

/-- The `j`-th slot of the new buffer `P`. -/
def slot (P : Word) (j : Nat) : Word := P + BitVec.ofNat 64 (24 * j)

theorem trap : Image.code.fetch 0x80006254 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem _root_.Rv64Verifier.Layout.ClonePre.bounds {s : MachineState} (hpre : ClonePre s) :
    0x78000000 + 176 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := hpre.stack.bounds (by decide) (by decide)
  have ha := hpre.stack.above
  have ho := ValidMemRange.bounds hpre.out (by decide)
  simp only [cloneStack, tryAllocStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- The slice: in a data window, its forms' bytes before the stack and the free heap. -/
theorem src_bounds {s : MachineState} (hpre : ClonePre s) :
    (s.getReg .x11).toNat + 24 * (s.getReg .x12).toNat < 2 ^ 64 ∧
      ((s.getReg .x12).toNat = 0 ∨ ((s.getReg .x11).toNat % 8 = 0 ∧ (s.getReg .x11).toNat + 24 * (s.getReg .x12).toNat ≤ 0xc0000008)) := by
  rcases Nat.eq_zero_or_pos ((s.getReg .x12).toNat) with h | h
  · have := (s.getReg .x11).isLt; exact ⟨by omega, Or.inl h⟩
  · have := ValidMemRange.bounds hpre.src (by omega); exact ⟨by omega, Or.inr ⟨this.2.1, by omega⟩⟩

/-- The sources miss the stack, `NEXT` and the heap allocated since the entry. -/
theorem srcApart {s u : MachineState} (hpre : ClonePre s) (hu : heapNext u ≤ 0x78000000) {x : Word}
    (hx : Within x (s.getReg .x11) (24 * (s.getReg .x12).toNat) ∨ formsDeep s (s.getReg .x11) ((s.getReg .x12).toNat) x) :
    ¬ (Within x (s.getReg .x2 - 176) 176 ∨ Within x nextAddr 8 ∨ Fresh s u x) := by
  have hb := hpre.bounds
  have hab := hpre.stack.above
  have hss := hpre.srcStack
  have hsf := hpre.srcFree
  have hshi := hpre.heap.hi
  simp only [cloneStack, tryAllocStack, stackLo, heapEnd, Nat.reduceAdd] at hab hss
  simp only [Outside, heapNext, heapEnd] at hsf hshi
  intro h
  rcases hx with hx | ⟨j, hj, hxj⟩
  · rcases h with h | h | h
    · addr_omega [hx, h, hss, hb]
    · addr_omega [hx, h, hsf.2]
    · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hsf.1, hu]
  · have hbl := formBuf_below (hpre.srcOk j hj) hxj
    simp only [heapNext, heapStart] at hbl
    rcases h with h | h | h
    · addr_omega [hbl, h, hb, hab, hshi]
    · addr_omega [hbl, h, hshi]
    · simp only [Fresh, heapNext] at h; omega

/-- `k` forms cloned into the buffer `P` allocated below `nr`: the stack below the saved registers,
`NEXT` and what is allocated changed. -/
structure Core (s t₁ : MachineState) (P : Word) (nr : Nat) (u : MachineState) (k : Nat) : Prop where
  heap : HeapOk u
  mono : nr ≤ heapNext u
  saved : ∀ a : Word, (s.getReg .x2).toNat - 104 ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2).toNat →
    u.getMem a = t₁.getMem a
  frame : DFrame s u fun x ↦ Within x (s.getReg .x2 - 176) 176 ∨ Within x nextAddr 8 ∨ Fresh s u x
  new : ∀ j < k, formOf u (slot P j) = formOf s (src s j) ∧ FormOk u (slot P j) ∧
    ∀ x, formBuf u (slot P j) x → nr ≤ x.toNat ∧ x.toNat < heapNext u
  caps : ∀ j < k, vecCap u (slot P j) = vecLen s (src s j)
  dang : ∀ j < k, vecLen s (src s j) = 0 → vecPtr u (slot P j) = 8

/-- What the outer allocation gave: `P`, aligned, of `len` slots, allocated between the entry's
`NEXT` and `nr`. -/
structure Base (s : MachineState) (P : Word) (nr : Nat) : Prop where
  al : P.toNat % 8 = 0
  buf : (s.getReg .x12).toNat = 0 ∨ (heapNext s ≤ P.toNat ∧ P.toNat + 24 * (s.getReg .x12).toNat ≤ nr)
  nr : heapNext s ≤ nr ∧ nr ≤ 0x78000000

/-- The `j`-th source at `u` is the entry's. -/
theorem src_same {s t₁ u : MachineState} {P : Word} {nr k : Nat} (hpre : ClonePre s)
    (hbase : Base s P nr) (hc : Core s t₁ P nr u k) {j : Nat} (hj : j < (s.getReg .x12).toNat) :
    formOf u (src s j) = formOf s (src s j) ∧ FormOk u (src s j) ∧
      vecLen u (src s j) = vecLen s (src s j) ∧ vecPtr u (src s j) = vecPtr s (src s j) := by
  have hhi := hc.heap.hi
  simp only [heapNext, heapEnd] at hhi
  have hsb := src_bounds hpre
  have hf := hc.frame
  have ha := fun x hx ↦ srcApart hpre hhi (x := x) hx
  have hh : ∀ x, Within x (src s j) 24 → Within x (s.getReg .x11) (24 * (s.getReg .x12).toNat) ∨
      formsDeep s (s.getReg .x11) ((s.getReg .x12).toNat) x :=
    fun x hx ↦ Or.inl (by simp only [src] at hx; addr_omega [hx, hj, hsb.1])
  have hfo := formOf_frame hf (hpre.srcOk j hj) (fun x hx ↦ ha x (hh x hx))
    (fun x hx ↦ ha x (Or.inr ⟨j, hj, hx⟩)) (by addr_omega [hj, hsb.1]) hpre.heap
    (hbase.nr.1.trans hc.mono)
  refine ⟨hfo.1, hfo.2, ?_, ?_⟩
  · simp only [vecLen]
    exact hf.getMem_of (fun x hx ↦ ha x (hh x (by simp only [src] at hx ⊢; addr_omega [hx, hj, hsb.1])))
      (by simp only [src]; addr_omega [hj, hsb.1])
  · simp only [vecPtr]
    exact hf.getMem_of (fun x hx ↦ ha x (hh x (by simp only [src] at hx ⊢; addr_omega [hx, hj, hsb.1])))
      (by simp only [src]; addr_omega [hj, hsb.1])

/-- At the loop head, `k` forms cloned. -/
structure Inv (s t₁ : MachineState) (P : Word) (nr : Nat) (u : MachineState) (k : Nat) : Prop
    extends Core s t₁ P nr u k where
  lt : k < (s.getReg .x12).toNat
  pc : u.pc = 0x800061b0
  sp : u.getReg .x2 = s.getReg .x2 - 128
  x8 : u.getReg .x8 = s.getReg .x12
  x9 : u.getReg .x9 = s.getReg .x10
  x18 : u.getReg .x18 = src s k
  x22 : u.getReg .x22 = s.getReg .x12
  x23 : u.getReg .x23 = P
  x24 : u.getReg .x24 = slot P k + 16
  x25 : u.getReg .x25 = BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - k))
  x26 : u.getReg .x26 = s.getReg .x12 - BitVec.ofNat 64 k

/-- The clone of form `k`, before its header is written: at `0x80006190`, its terms copied into a
new buffer `p`. -/
structure Cloned (s u y : MachineState) (k : Nat) (p : Word) : Prop where
  pc : y.pc = 0x80006190
  regs : ∀ q ∈ [Reg.x2, .x8, .x9, .x18, .x22, .x23, .x24, .x25, .x26], y.getReg q = u.getReg q
  x27 : y.getReg .x27 = vecLen s (src s k)
  x21 : y.getReg .x21 = p
  x19 : y.getReg .x19 = vecLen s (src s k)
  heap : HeapOk y
  mono : heapNext u ≤ heapNext y
  fresh : NewBuf u y p ((vecLen s (src s k)).toNat * 48) 8
  copy : ∀ k', k' % 8 = 0 → k' + 8 ≤ 48 * (vecLen s (src s k)).toNat →
    y.getMem (p + BitVec.ofNat 64 k') = s.getMem (vecPtr s (src s k) + BitVec.ofNat 64 k')
  frame : DFrame u y fun x ↦ Within x (s.getReg .x2 - 176) 72 ∨ Within x nextAddr 8 ∨ Fresh u y x
  dang : vecLen s (src s k) = 0 → p = 8

/-- `try_allocate_in` and `memcpy` for form `k`. -/
theorem cloneStep (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s t₁ u : MachineState}
    {P : Word} {nr k : Nat} (hpre : ClonePre s) (hbase : Base s P nr) (hi : Inv s t₁ P nr u k) :
    ∃ y, Reaches Image.code u y ∧ ((∃ p, Cloned s u y k p) ∨ Dead Image.code y) := by
  have hk := hi.lt
  have hb := hpre.bounds
  have hsb₀ := src_bounds hpre
  have hsrc : (s.getReg .x11).toNat % 8 = 0 ∧ (s.getReg .x11).toNat + 24 * (s.getReg .x12).toNat ≤
      0xc0000008 := by
    rcases hsb₀.2 with h | h
    · omega
    · exact h
  have hst := hpre.stack
  have hab := hst.above
  have hnx := hst.next
  simp only [cloneStack, tryAllocStack, stackLo, heapEnd] at hab hnx
  obtain ⟨hfs, hok, hlen, hptr⟩ := src_same hpre hbase hi.toCore hk
  have hsv := hpre.src
  have hx18 := hi.x18
  simp only [src] at hx18
  -- the count is not zero
  obtain ⟨v₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b800061b0_spec hi.pc trivial
  have hx25 : u.getReg .x25 ≠ 0 := by
    rw [hi.x25]; intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; simp at this; omega
  have k₀ := b800061b0_keeps h₀
  have hm₀ := b800061b0_mem_same h₀
  -- the call to `try_allocate_in`
  obtain ⟨v, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800061b4_spec
    (b800061b0_pc_not_taken h₀ hx25) (by
      rv_eval [k₀ .x18 (by decide), hx18]
      and_intros <;> valid_access hsv [hsrc, hk])
  have k₁ := b800061b4_keeps h₁
  have x18₀ : v₀.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (24 * k) := by
    rw [k₀ .x18 (by decide), hx18]
  have x2₁ : v.getReg .x2 = s.getReg .x2 - 128 := by
    rw [k₁ .x2 (by decide), k₀ .x2 (by decide), hi.sp]
  have x10₁ : v.getReg .x10 = s.getReg .x2 - 128 := by
    rw [b800061b4_x10 h₁, k₀ .x2 (by decide), hi.sp]
  have x11₁ : v.getReg .x11 = vecLen s (src s k) := by
    rw [b800061b4_x11 h₁, x18₀, hm₀, ← hlen]; rfl
  have x19₁ : v.getReg .x19 = vecLen s (src s k) := by
    rw [b800061b4_x19 h₁, x18₀, hm₀, ← hlen]; rfl
  have x20₁ : v.getReg .x20 = vecPtr s (src s k) := by
    rw [b800061b4_x20 h₁, x18₀, hm₀, ← hptr]; rfl
  have hm₁ (a : Word) : v.getMem a = u.getMem a := (b800061b4_mem_same h₁ a).trans (hm₀ a)
  have hnext₁ : heapNext v = heapNext u := by simp only [heapNext, hm₁]
  have hheap₁ : HeapOk v := ⟨hnext₁ ▸ hi.heap.lo, hnext₁ ▸ hi.heap.hi⟩
  have hta : TryAllocPre .x13 .x14 v := {
    heap := hheap₁
    out := by rw [x10₁]; valid_sub hst.valid [hb]
    align := by rw [b800061b4_x13 h₁]; decide
    size := by rw [b800061b4_x14 h₁]; decide
    stack := hst.inner (k := 128) x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]
      have := hheap₁.hi
      simp only [Outside, heapNext, heapEnd] at this ⊢
      exact ⟨Or.inr (by addr_omega [hb, hab]), by addr_omega [hb, hnx]⟩
    outStack := by rw [x10₁]; addr_omega [hb, x2₁] }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost, -⟩ | hdead⟩ := hT.call hr₁ (b800061b4_pc h₁) hta
  swap
  · exact ⟨w, hr₀.trans hr₂, Or.inr hdead⟩
  have hwf := hpost.frame.dframe
  rw [x10₁, show stackLo v tryAllocStack = s.getReg .x2 - 176 by
    simp only [stackLo, x2₁, tryAllocStack]; rv_eval []] at hwf
  have x2₂ : w.getReg .x2 = s.getReg .x2 - 128 := (hpres₂.reg .x2).trans x2₁
  -- the error check
  obtain ⟨w₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800061d8_spec
    (by rw [hpc₂, returnAddress_eq, b800061b4_x1 h₁]; decide) (by
      rv_eval [x2₂]
      valid_access hst.valid [hb])
  have hok₂ := hpost.ok
  rw [x10₁] at hok₂
  by_cases htag : w.getMem (s.getReg .x2 - 128) = 0
  swap
  · exact ⟨w₂, hr₀.trans (hr₂.trans hr₃), Or.inr (dead_of_fetch (by
      rw [b800061d8_pc_taken h₃ (by rwa [x2₂])]; exact trap))⟩
  obtain ⟨hcap₂, hnew₂⟩ := hok₂ htag
  rw [x11₁, b800061b4_x14 h₁, b800061b4_x13 h₁] at hnew₂
  rw [x11₁] at hcap₂
  have k₃ := b800061d8_keeps h₃
  have hm₃ := b800061d8_mem_same h₃
  obtain ⟨w₃, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800061e0_spec
    (b800061d8_pc_not_taken h₃ (by rwa [x2₂])) (by
      rv_eval [k₃ .x2 (by decide), x2₂]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b800061e0_keeps h₄
  have hm₄ := b800061e0_mem_same h₄
  obtain ⟨p, hp⟩ : ∃ p, p = w.getMem (s.getReg .x2 - 112) := ⟨_, rfl⟩
  have x21₄ : w₃.getReg .x21 = p := by
    rw [b800061e0_x21 h₄, k₃ .x2 (by decide), x2₂, hm₃, hp]; rv_eval []
  have x27₄ : w₃.getReg .x27 = vecLen s (src s k) := by
    rw [b800061e0_x27 h₄, k₃ .x2 (by decide), x2₂, hm₃, ← hcap₂]
  have x19₂ : w₂.getReg .x19 = vecLen s (src s k) := by
    rw [k₃ .x19 (by decide), hpres₂.reg .x19, x19₁]
  have x19₄ : w₃.getReg .x19 = vecLen s (src s k) := by rw [k₄ .x19 (by decide), x19₂]
  have hnewp : NewBuf v w p ((vecLen s (src s k)).toNat * 48) 8 := by
    rw [hp]; simpa only [show s.getReg .x2 - 128 + 16 = s.getReg .x2 - 112 by rv_eval [],
      show (48 : Word).toNat = 48 from rfl, show (8 : Word).toNat = 8 from rfl] using hnew₂
  have hnext₄ : heapNext w₃ = heapNext w := by simp only [heapNext, hm₄, hm₃]
  have hf₄ : DFrame u w₃ fun x ↦ Within x (s.getReg .x2 - 176) 72 ∨ Within x nextAddr 8 ∨
      Fresh u w₃ x :=
    (((DFrame.of_same hm₁ fun _ ↦ False).union hwf).union
      ((DFrame.of_same hm₃ fun _ ↦ False).union (DFrame.of_same hm₄ fun _ ↦ False))).mono
      fun x h ↦ by
        rcases h with (h | h | h | h | h) | h | h
        · exact h.elim
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by simpa only [Fresh, hnext₁, hnext₄] using h))
        · exact h.elim
        · exact h.elim
  have hregs₄ : ∀ q ∈ [Reg.x2, .x8, .x9, .x18, .x22, .x23, .x24, .x25, .x26],
      w₃.getReg q = u.getReg q := fun q hq ↦ by
    rw [k₄ q (mem_of_mem hq _), k₃ q (mem_of_mem hq _), hpres₂ q (mem_of_mem hq _),
      k₁ q (mem_of_mem hq _), k₀ q (mem_of_mem hq _)]
  have hheap₄ : HeapOk w₃ := ⟨hnext₄ ▸ hpost.heap.lo, hnext₄ ▸ hpost.heap.hi⟩
  have hmono₄ : heapNext u ≤ heapNext w₃ := by rw [hnext₄, ← hnext₁]; exact hpost.mono
  have hdg : vecLen s (src s k) = 0 → p = 8 := fun hz0 ↦ by
    have h8 := hpost.dangling (by rw [x10₁]; exact htag) (by rw [x11₁]; exact hz0)
    rw [x10₁, b800061b4_x13 h₁, show s.getReg .x2 - 128 + 16 = s.getReg .x2 - 112 by rv_eval []]
      at h8
    rw [hp]; exact h8
  by_cases hz : vecLen s (src s k) = 0
  · refine ⟨w₃, hr₀.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl ⟨p, b800061e0_pc_taken h₄
      (by rw [x19₂, hz]), hregs₄, x27₄, x21₄, x19₄, hheap₄, hmono₄, ?_, ?_, hf₄, hdg⟩⟩
    · simp only [NewBuf, hnext₁.symm, hnext₄] at hnewp ⊢; exact hnewp
    · intro k' _ hk'; rw [hz] at hk'; simp at hk'
  have hlz : 0 < (vecLen s (src s k)).toNat := by
    rcases Nat.eq_zero_or_pos (vecLen s (src s k)).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) hz
    · exact h
  have hnp := hnewp
  simp only [NewBuf] at hnp
  have hp8 := hnp.1
  have hpb : heapNext v ≤ p.toNat ∧ p.toNat + (vecLen s (src s k)).toNat * 48 ≤ heapNext w := by
    rcases hnp.2 with h | h
    · exfalso; rw [Nat.mul_eq_zero] at h; omega
    · exact h
  have hwhi := hpost.heap.hi
  have hslen := hok.vec.len
  have hsraw := hok.vec.raw
  simp only [RawVecOk, Buf] at hsraw
  rw [hlen] at hslen
  rw [hptr] at hsraw
  have hsb : heapStart ≤ (vecPtr s (src s k)).toNat ∧ (vecPtr s (src s k)).toNat +
      (vecCap u (src s k)).toNat * 48 ≤ heapNext u := by
    rcases hsraw.2 with h | h
    · exfalso; rw [Nat.mul_eq_zero] at h; omega
    · exact h
  have hnext₁' := hnext₁
  simp only [heapNext, heapStart, heapEnd] at hpb hwhi hsb hnext₁
  obtain ⟨w₄, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800061ec_spec
    (b800061e0_pc_not_taken h₄ (by rw [x19₂]; exact hz)) trivial
  have k₅ := b800061ec_keeps h₅
  have hm₅ := b800061ec_mem_same h₅
  have x12₅ : (w₄.getReg .x12).toNat = 48 * (vecLen s (src s k)).toNat := by
    rw [b800061ec_x12 h₅, x19₄]
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul]
    simp only [show (32 : Word).toNat = 32 from rfl, show (16 : Word).toNat = 16 from rfl]
    omega
  have x10₅ : w₄.getReg .x10 = p := by rw [b800061ec_x10 h₅, x21₄]
  have x11₅ : w₄.getReg .x11 = vecPtr s (src s k) := by
    rw [b800061ec_x11 h₅, k₄ .x20 (by decide), k₃ .x20 (by decide), hpres₂.reg .x20, x20₁]
  have x2₅ : w₄.getReg .x2 = s.getReg .x2 - 128 := by
    rw [k₅ .x2 (by decide), hregs₄ .x2 (by decide), hi.sp]
  have hmc : MemcpyPre w₄ := {
    dst := by rw [x10₅, x12₅]; simp only [Mapped]; omega
    src := by rw [x11₅, x12₅]; simp only [Mapped]; omega
    apart := by rw [x10₅, x11₅, x12₅]; simp only [Apart]; omega
    stack := (hst.inner (k := 128) x2₅ (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [x10₅, x12₅]; addr_omega [hpb, hwhi, x2₅, hb]
    srcStack := by rw [x11₅, x12₅]; addr_omega [hsb, hnext₁, hwhi, x2₅, hb, hpb] }
  obtain ⟨mc, hr₆, ⟨hpc₆, hpres₆, hmpost⟩ | hdead⟩ := hM.call hr₅ (b800061ec_pc h₅) hmc
  swap
  · exact ⟨mc, hr₀.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₆))), Or.inr hdead⟩
  obtain ⟨y, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80006208_spec
    (by rw [hpc₆, returnAddress_eq, b800061ec_x1 h₅]; decide) trivial
  have k₇ := b80006208_keeps h₇
  have hm₇ := b80006208_mem_same h₇
  have hmf := hmpost.frame.dframe
  rw [x10₅, x12₅, show stackLo w₄ memcpyStack = s.getReg .x2 - 144 by
    simp only [stackLo, x2₅, memcpyStack]; rv_eval []] at hmf
  have hny : heapNext y = heapNext w := by
    simp only [heapNext, hm₇]
    rw [hmf.getMem_of (fun x hx h ↦ by
      rcases h with h | h
      · addr_omega [hx, h, hpb, hwhi]
      · addr_omega [hx, h, hb, hnx]) (by decide), hm₅, hm₄, hm₃]
  refine ⟨y, hr₀.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₆.trans hr₇)))), Or.inl ⟨p,
    b80006208_pc h₇, fun q hq ↦ ?_, ?_, ?_, ?_, ⟨hny ▸ hpost.heap.lo, hny ▸ hpost.heap.hi⟩, ?_, ?_,
    ?_, ?_, hdg⟩⟩
  · rw [k₇ q (mem_of_mem hq _), hpres₆ q (mem_of_mem hq _), k₅ q (mem_of_mem hq _), hregs₄ q hq]
  · rw [k₇ .x27 (by decide), hpres₆.reg .x27, k₅ .x27 (by decide), x27₄]
  · rw [k₇ .x21 (by decide), hpres₆.reg .x21, k₅ .x21 (by decide), x21₄]
  · rw [k₇ .x19 (by decide), hpres₆.reg .x19, k₅ .x19 (by decide), x19₄]
  · rw [hny, ← hnext₁']; exact hpost.mono
  · have h' := hnewp
    simp only [NewBuf, hny] at h' ⊢
    rw [hnext₁'] at h'
    exact h'
  · intro k' hk8 hk'
    have hbt := hmpost.bytes
    rw [x10₅, x11₅, x12₅] at hbt
    have hcs := (hpre.srcOk k hk).vec.len
    have hcs' : (vecLen s (src s k)).toNat ≤ (vecCap s (src s k)).toNat := hcs
    have hsk' : s.getMem (vecPtr s (src s k) + BitVec.ofNat 64 k') =
        u.getMem (vecPtr s (src s k) + BitVec.ofNat 64 k') := by
      have hhi := hi.heap.hi
      simp only [heapNext, heapEnd] at hhi
      have hfr := hi.frame.getMem_of (a := vecPtr s (src s k) + BitVec.ofNat 64 k')
        (fun x hx h ↦ srcApart hpre hhi (Or.inr ⟨k, hk, by
          show formBuf s (src s k) x
          simp only [formBuf]; addr_omega [hx, hcs', hk', hsb, hslen]⟩) h)
        (by addr_omega [hsb, hslen, hk'])
      exact hfr.symm
    rw [hm₇, getMem_eq_of_bytesAt hbt hp8 hsraw.1 hk8 hk', hm₅, hm₄, hm₃, hsk']
    rw [hwf.getMem_of (fun x hx h ↦ by
      rcases h with h | h | h | h
      · addr_omega [hx, h, hsb, hslen, hk', hb, hwhi, hpb, hnext₁, hab]
      · addr_omega [hx, h, hsb, hslen, hk', hb, hwhi, hpb, hnext₁, hab]
      · addr_omega [hx, h, hsb, hslen, hk', hwhi, hpb, hnext₁]
      · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hsb, hslen, hk', hnext₁])
      (by addr_omega [hsb, hslen, hk']), hm₁]
  · refine ((((hf₄.union (DFrame.of_same hm₅ fun _ ↦ False)).union hmf).union
      (DFrame.of_same hm₇ fun _ ↦ False))).mono fun x h ↦ ?_
    rcases h with (((h | h | h) | h) | h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ?_)
      simp only [Fresh] at h ⊢
      rw [hny, ← hnext₄]; exact h
    · exact h.elim
    · refine Or.inr (Or.inr ?_)
      simp only [Fresh]
      rw [hny]
      simp only [heapNext]
      addr_omega [h, hpb, hnext₁]
    · exact Or.inl (by addr_omega [h, hb])
    · exact h.elim

/-- At the epilogue, every form cloned. -/
structure AtExit (s t₁ : MachineState) (P : Word) (nr : Nat) (u : MachineState) : Prop
    extends Core s t₁ P nr u (s.getReg .x12).toNat where
  pc : u.pc = 0x8000620c
  sp : u.getReg .x2 = s.getReg .x2 - 128
  x8 : u.getReg .x8 = s.getReg .x12
  x9 : u.getReg .x9 = s.getReg .x10
  x22 : u.getReg .x22 = s.getReg .x12
  x23 : u.getReg .x23 = P

/-- The loop is over: at the epilogue, or at a dead end. -/
def Done (s t₁ : MachineState) (P : Word) (nr : Nat) (u : MachineState) : Prop :=
  AtExit s t₁ P nr u ∨ Dead Image.code u

/-- One iteration: form `k` cloned into its slot. -/
theorem body (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s t₁ : MachineState}
    {P : Word} {nr : Nat} (hpre : ClonePre s) (hbase : Base s P nr) (u : MachineState)
    (hu : ∃ k, Inv s t₁ P nr u k) :
    (∃ z, Reaches Image.code u z ∧ Done s t₁ P nr z) ∨
      (∃ z, Reaches Image.code u z ∧ (∃ k, Inv s t₁ P nr z k) ∧
        (z.getReg .x26).toNat < (u.getReg .x26).toNat) := by
  obtain ⟨k, hi⟩ := hu
  obtain ⟨y, hry, ⟨p, hc⟩ | hdead⟩ := cloneStep hT hM hpre hbase hi
  swap
  · exact Or.inl ⟨y, hry, Or.inr hdead⟩
  have hk := hi.lt
  have hb := hpre.bounds
  have hP8 := hbase.al
  have hPb : heapNext s ≤ P.toNat ∧ P.toNat + 24 * (s.getReg .x12).toNat ≤ nr := by
    rcases hbase.buf with h | h
    · omega
    · exact h
  have hnr := hbase.nr
  have hnu := hi.mono
  have hny := hc.mono
  have hyhi := hc.heap.hi
  have hsn := hpre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hPb hnr hnu hny hyhi hsn
  have hx24 : y.getReg .x24 = slot P k + 16 := (hc.regs .x24 (by decide)).trans hi.x24
  have hslb : (slot P k).toNat = P.toNat + 24 * k := by
    simp only [slot]; addr_omega [hPb, hk, hnr]
  have hPv : ValidMemRange P (3 * (s.getReg .x12).toNat) :=
    validMemRange_of hP8 (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨z, hrz, h⟩ := Sym.BlockSpec.reaches b80006190_spec hc.pc (by
    rv_eval [hx24, slot]
    and_intros <;> valid_access hPv [hPb, hk, hnr])
  have k₂ := b80006190_keeps h
  have hmf := b80006190_frame h (by rw [hx24]; addr_omega [hslb, hPb, hk, hnr])
  rw [hx24, show slot P k + 16 - 16 = slot P k by rv_eval []] at hmf
  have w0 := b80006190_m_x24_n16 h
  have w8 := b80006190_m_x24_n8 h
  have w16 := b80006190_m_x24_0 h
  rw [hx24, show slot P k + 16 - 16 = slot P k by rv_eval [], hc.x27] at w0
  rw [hx24, show slot P k + 16 - 8 = slot P k + 8 by rv_eval [], hc.x21] at w8
  rw [hx24, hc.x19] at w16
  have hfz : DFrame u z fun x ↦ (Within x (s.getReg .x2 - 176) 72 ∨ Within x nextAddr 8 ∨
      Fresh u y x) ∨ Within x (slot P k) 24 := hc.frame.union hmf.dframe
  have hnz : z.getMem nextAddr = y.getMem nextAddr :=
    hmf nextAddr (by addr_omega [hslb, hPb, hk, hnr])
  have hnextz : heapNext z = heapNext y := by simp only [heapNext, hnz]
  have hfr := hc.fresh
  simp only [NewBuf, heapNext] at hfr
  have hW : ∀ x : Word, nr ≤ x.toNat → x.toNat < heapNext u →
      ¬ ((Within x (s.getReg .x2 - 176) 72 ∨ Within x nextAddr 8 ∨ Fresh u y x) ∨
        Within x (slot P k) 24) := by
    intro x h0 h1 h3
    simp only [heapNext] at h1
    rcases h3 with (h3 | h3 | h3) | h3
    · addr_omega [h1, h3, hb, hyhi, hny]
    · addr_omega [h1, h3, hyhi, hny]
    · simp only [Fresh, heapNext] at h3; omega
    · addr_omega [h0, h3, hslb, hPb, hk]
  have hWs : ∀ j, j < k → ∀ x, Within x (slot P j) 24 →
      ¬ ((Within x (s.getReg .x2 - 176) 72 ∨ Within x nextAddr 8 ∨ Fresh u y x) ∨
        Within x (slot P k) 24) := by
    intro j hj x hx h3
    have hsj : (slot P j).toNat = P.toNat + 24 * j := by
      simp only [slot]; addr_omega [hPb, hk, hnr, hj]
    rcases h3 with (h3 | h3 | h3) | h3
    · addr_omega [hx, hsj, h3, hb, hPb, hk, hj, hnr]
    · addr_omega [hx, hsj, h3, hPb, hk, hj, hnr]
    · simp only [Fresh, heapNext] at h3; addr_omega [hx, hsj, h3, hPb, hk, hj, hnr, hnu]
    · addr_omega [hx, hsj, h3, hslb, hj]
  have hcl := clone_form (u := s) (src := src s k) (e := slot P k) (p := p) (hpre.srcOk k hk)
    hpre.heap w0 w8 w16
    (by
      simp only [NewBuf, heapNext, hnz]
      rcases hfr.2 with h0 | h0
      · exact ⟨hfr.1, Or.inl h0⟩
      · exact ⟨hfr.1, Or.inr ⟨by omega, h0.2⟩⟩)
    (fun k' hk8 hk' ↦ by
      rw [hmf (p + BitVec.ofNat 64 k') (by
        rcases hfr.2 with h0 | h0
        · rw [Nat.mul_eq_zero] at h0; omega
        · addr_omega [h0, hk', hslb, hPb, hk, hnr, hnu, hyhi])]
      exact hc.copy k' hk8 hk')
  have hcore : Core s t₁ P nr z (k + 1) := {
    heap := ⟨hnextz ▸ hc.heap.lo, hnextz ▸ hc.heap.hi⟩
    mono := by rw [hnextz]; exact hi.mono.trans hc.mono
    saved := fun a h1 h2 ↦ by
      have hnx := hpre.stack.next
      simp only [cloneStack, tryAllocStack, stackLo] at hnx
      rw [hfz.getMem_of (a := a) (fun x hx h ↦ by
        rcases h with (h | h | h) | h
        · addr_omega [hx, h, h1, h2, hb]
        · addr_omega [hx, h, h1, h2, hb, hnx]
        · simp only [Fresh, heapNext] at h; addr_omega [hx, h, h1, h2, hb, hyhi]
        · addr_omega [hx, h, h1, h2, hb, hslb, hPb, hnr, hk]) (by addr_omega [h2, hb])]
      exact hi.saved a h1 h2
    frame := (hi.frame.union hfz).mono fun x h ↦ by
      rcases h with (h | h | h) | ((h | h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ?_)
        simp only [Fresh, hnextz] at h ⊢; simp only [heapNext] at h ⊢; omega
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ?_)
        simp only [Fresh, hnextz] at h ⊢; simp only [heapNext] at h ⊢; omega
      · refine Or.inr (Or.inr ?_)
        simp only [Fresh, hnextz]; simp only [heapNext]
        addr_omega [h, hslb, hPb, hk, hnr, hnu, hny]
    new := fun j hj ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hv, hok, hbf⟩ := hi.new j hj
        have hsj : (slot P j).toNat = P.toNat + 24 * j := by
          simp only [slot]; addr_omega [hPb, hk, hnr, hj]
        have hbd : ∀ x, formBuf u (slot P j) x → ¬ ((Within x (s.getReg .x2 - 176) 72 ∨
            Within x nextAddr 8 ∨ Fresh u y x) ∨ Within x (slot P k) 24) := fun x hx ↦ by
          have h' := hbf x hx
          simp only [heapNext] at h'
          exact hW x h'.1 (by simp only [heapNext]; omega)
        have hfo := formOf_frame hfz hok (hWs j hj) hbd (by addr_omega [hsj, hPb, hk, hnr, hj])
          hi.heap (by rw [hnextz]; exact hc.mono)
        refine ⟨hfo.1.trans hv, hfo.2, fun x hx ↦ ?_⟩
        rw [formBuf_frame hfz (hWs j hj) (by addr_omega [hsj, hPb, hk, hnr, hj])] at hx
        have h' := hbf x hx
        rw [hnextz]
        simp only [heapNext] at h' ⊢
        omega
      · refine ⟨hcl.1, hcl.2.1, fun x hx ↦ ?_⟩
        simp only [formBuf, vecPtr, vecCap, w0, w8] at hx
        rw [hnextz]
        simp only [heapNext]
        rcases hfr.2 with h0 | h0
        · rw [Nat.mul_eq_zero] at h0; simp only [Within] at hx; omega
        · simp only [Within] at hx; omega
    caps := fun j hj ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hsj : (slot P j).toNat = P.toNat + 24 * j := by
          simp only [slot]; addr_omega [hPb, hk, hnr, hj]
        rw [← hi.caps j hj]
        simp only [vecCap]
        exact hfz.getMem_of (fun x hx ↦ hWs j hj x (by addr_omega [hx, hsj, hPb, hk, hj, hnr]))
          (by addr_omega [hsj, hPb, hk, hnr, hj])
      · simp only [vecCap]; exact w0
    dang := fun j hj ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hsj : (slot P j).toNat = P.toNat + 24 * j := by
          simp only [slot]; addr_omega [hPb, hk, hnr, hj]
        intro h0
        rw [← hi.dang j hj h0]
        simp only [vecPtr]
        exact hfz.getMem_of (fun x hx ↦ hWs j hj x (by addr_omega [hx, hsj, hPb, hk, hj, hnr]))
          (by addr_omega [hsj, hPb, hk, hnr, hj])
      · intro h0
        simp only [vecPtr]; rw [w8]; exact hc.dang h0 }
  have x26y : y.getReg .x26 = s.getReg .x12 - BitVec.ofNat 64 k :=
    (hc.regs .x26 (by decide)).trans hi.x26
  have hz2 : z.getReg .x2 = s.getReg .x2 - 128 := by
    rw [k₂ .x2 (by decide), hc.regs .x2 (by decide), hi.sp]
  have hzr (q : Reg) (hq : q ∈ [Reg.x8, .x9, .x22, .x23]) : z.getReg q = u.getReg q := by
    rw [k₂ q (mem_of_mem hq _), hc.regs q (mem_of_mem hq _)]
  have hlt := (s.getReg .x12).isLt
  by_cases hlast : k + 1 = (s.getReg .x12).toNat
  · refine Or.inl ⟨z, hry.trans hrz, Or.inl ⟨hlast ▸ hcore, b80006190_pc_taken h (by
      rw [x26y]; addr_omega [hk, hlast, hlt]), hz2, (hzr .x8 (by decide)).trans hi.x8,
      (hzr .x9 (by decide)).trans hi.x9, (hzr .x22 (by decide)).trans hi.x22,
      (hzr .x23 (by decide)).trans hi.x23⟩⟩
  · have hk1 : k + 1 < (s.getReg .x12).toNat := by omega
    have hsrcb := src_bounds hpre
    refine Or.inr ⟨z, hry.trans hrz, ⟨k + 1, { hcore with
      lt := hk1
      pc := b80006190_pc_not_taken h (by rw [x26y]; addr_omega [hk, hk1, hlt])
      sp := hz2
      x8 := (hzr .x8 (by decide)).trans hi.x8
      x9 := (hzr .x9 (by decide)).trans hi.x9
      x18 := by
        rw [b80006190_x18 h, hc.regs .x18 (by decide), hi.x18]
        simp only [src]; addr_omega [hsrcb.1, hk1]
      x22 := (hzr .x22 (by decide)).trans hi.x22
      x23 := (hzr .x23 (by decide)).trans hi.x23
      x24 := by
        rw [b80006190_x24 h, hx24]
        simp only [slot]; addr_omega [hPb, hk1, hnr]
      x25 := by
        rw [b80006190_x25 h, hc.regs .x25 (by decide), hi.x25]
        addr_omega [hsrcb.1, hk1]
      x26 := by rw [b80006190_x26 h, x26y]; addr_omega [hk, hk1, hlt] }⟩, ?_⟩
    rw [b80006190_x26 h, x26y, hi.x26]
    addr_omega [hk, hk1, hlt]

/-- The epilogue: the `Vec` written to `a0`, the registers restored. -/
theorem exit {s t₁ u : MachineState} {P : Word} {nr : Nat} (hpre : ClonePre s)
    (hbase : Base s P nr) (h₁ : b80006104.Holds s t₁) (he : AtExit s t₁ P nr u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      NewFormVec s t (s.getReg .x10) cloneStack ∧
      formVecOf t (s.getReg .x10) = formsAt s (s.getReg .x11) (s.getReg .x12).toNat ∧
      (∀ i < (s.getReg .x12).toNat,
        vecCap t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) = vecLen s (src s i)) ∧
      ∀ i < (s.getReg .x12).toNat, vecLen s (src s i) = 0 →
        vecPtr t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) = 8 := by
  have hb := hpre.bounds
  have hst := hpre.stack
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [cloneStack, tryAllocStack, stackLo] at hos
  simp only [Outside, heapNext, heapEnd] at hof
  obtain ⟨t, hrt, h⟩ := Sym.BlockSpec.reaches b8000620c_spec he.pc (by
    rv_eval [he.sp, he.x9]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access hpre.out [hb]
      | addr_omega [hb, hos])
  have hmf := b8000620c_frame h (by rw [he.x9]; addr_omega [hb])
  rw [he.x9] at hmf
  have o0 := b8000620c_m_x9_0 h
  have o8 := b8000620c_m_x9_8 h
  have o16 := b8000620c_m_x9_16 h
  rw [he.x9, he.x22] at o0
  rw [he.x9, he.x23] at o8
  rw [he.x9, he.x8] at o16
  have hsv (a : Word) (h1 : (s.getReg .x2).toNat - 104 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat) : u.getMem a = t₁.getMem a := he.saved a h1 h2
  have pc := b8000620c_pc h
  have r₁ := b8000620c_x1 h
  have r₂ := b8000620c_x2 h
  have r₈ := b8000620c_x8 h
  have r₉ := b8000620c_x9 h
  have r₁₈ := b8000620c_x18 h
  have r₁₉ := b8000620c_x19 h
  have r₂₀ := b8000620c_x20 h
  have r₂₁ := b8000620c_x21 h
  have r₂₂ := b8000620c_x22 h
  have r₂₃ := b8000620c_x23 h
  have r₂₄ := b8000620c_x24 h
  have r₂₅ := b8000620c_x25 h
  have r₂₆ := b8000620c_x26 h
  have r₂₇ := b8000620c_x27 h
  rw [he.sp] at pc r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀ r₂₁ r₂₂ r₂₃ r₂₄ r₂₅ r₂₆ r₂₇
  rv_eval [] at pc r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀ r₂₁ r₂₂ r₂₃ r₂₄ r₂₅ r₂₆ r₂₇
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n8 h₁] at pc r₁
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n16 h₁] at r₈
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n24 h₁] at r₉
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n32 h₁] at r₁₈
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n40 h₁] at r₁₉
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n48 h₁] at r₂₀
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n56 h₁] at r₂₁
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n64 h₁] at r₂₂
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n72 h₁] at r₂₃
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n80 h₁] at r₂₄
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n88 h₁] at r₂₅
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n96 h₁] at r₂₆
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80006104_m_x2_n104 h₁] at r₂₇
  -- the numbers
  have hP8 := hbase.al
  have hPb := hbase.buf
  have hnr := hbase.nr
  have hnu := he.mono
  have huhi := he.heap.hi
  have hsn := hpre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hPb hnr hnu huhi hsn
  have hnt : heapNext t = heapNext u := by
    simp only [heapNext]; rw [hmf _ (by addr_omega [hof.2, hb])]
  have hW : ∀ x : Word, (s.getMem nextAddr).toNat ≤ x.toNat → x.toNat < (u.getMem nextAddr).toNat →
      ¬ Within x (s.getReg .x10) 24 := by
    intro x h1 h2 h3
    addr_omega [h1, h2, h3, hof.1, huhi]
  have hn' : ∀ j < (s.getReg .x12).toNat, formOf t (slot P j) = formOf s (src s j) ∧
      FormOk t (slot P j) ∧ ∀ x, formBuf t (slot P j) x → nr ≤ x.toNat ∧ x.toNat < heapNext t := by
    intro j hj
    obtain ⟨hv, hok, hbf⟩ := he.new j hj
    have hPb' : heapNext s ≤ P.toNat ∧ P.toNat + 24 * (s.getReg .x12).toNat ≤ nr := by
      simp only [heapNext]; rcases hPb with h | h
      · omega
      · exact h
    simp only [heapNext] at hPb'
    have hsj : (slot P j).toNat = P.toNat + 24 * j := by
      simp only [slot]; addr_omega [hPb', hj, hnr]
    have hhd : ∀ x, Within x (slot P j) 24 → ¬ Within x (s.getReg .x10) 24 := fun x hx ↦
      hW x (by addr_omega [hx, hsj, hPb']) (by addr_omega [hx, hsj, hPb', hj, hnu])
    have hbd : ∀ x, formBuf u (slot P j) x → ¬ Within x (s.getReg .x10) 24 := fun x hx ↦ by
      have := hbf x hx
      simp only [heapNext] at this
      exact hW x (by omega) this.2
    have hfo := formOf_frame hmf.dframe hok hhd hbd (by addr_omega [hsj, hPb', hj, hnr]) he.heap
      hnt.ge
    refine ⟨hfo.1.trans hv, hfo.2, fun x hx ↦ ?_⟩
    rw [formBuf_frame hmf.dframe hhd (by addr_omega [hsj, hPb', hj, hnr])] at hx
    rw [hnt]; exact hbf x hx
  have hcaps : ∀ j < (s.getReg .x12).toNat, vecCap t (slot P j) = vecLen s (src s j) := by
    intro j hj
    have hPb' : heapNext s ≤ P.toNat ∧ P.toNat + 24 * (s.getReg .x12).toNat ≤ nr := by
      simp only [heapNext]; rcases hPb with h | h
      · omega
      · exact h
    simp only [heapNext] at hPb'
    have hsj : (slot P j).toNat = P.toNat + 24 * j := by
      simp only [slot]; addr_omega [hPb', hj, hnr]
    rw [← he.caps j hj]
    simp only [vecCap]
    exact hmf.dframe.getMem_of (fun x hx ↦ hW x (by addr_omega [hx, hsj, hPb'])
      (by addr_omega [hx, hsj, hPb', hj, hnu])) (by addr_omega [hsj, hPb', hj, hnr])
  have hdang : ∀ j < (s.getReg .x12).toNat, vecLen s (src s j) = 0 → vecPtr t (slot P j) = 8 := by
    intro j hj h0
    have hPb' : heapNext s ≤ P.toNat ∧ P.toNat + 24 * (s.getReg .x12).toNat ≤ nr := by
      simp only [heapNext]; rcases hPb with h | h
      · omega
      · exact h
    simp only [heapNext] at hPb'
    have hsj : (slot P j).toNat = P.toNat + 24 * j := by
      simp only [slot]; addr_omega [hPb', hj, hnr]
    rw [← he.dang j hj h0]
    simp only [vecPtr]
    exact hmf.dframe.getMem_of (fun x hx ↦ hW x (by addr_omega [hx, hsj, hPb', hj, hnr])
      (by addr_omega [hx, hsj, hPb', hj, hnu, hnr])) (by addr_omega [hsj, hPb', hj, hnr])
  have hptr : vecPtr t (s.getReg .x10) = P := o8
  have hcap : vecCap t (s.getReg .x10) = s.getReg .x12 := o0
  have hlen : vecLen t (s.getReg .x10) = s.getReg .x12 := o16
  refine ⟨t, hrt, pc.trans (returnAddress_eq s).symm, preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun q hq ↦ ?_,
    ⟨⟨hnt ▸ he.heap.lo, hnt ▸ he.heap.hi⟩, by rw [hnt]; simp only [heapNext]; omega,
      ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₂₀
    · exact r₂₁
    · exact r₂₂
    · exact r₂₃
    · exact r₂₄
    · exact r₂₅
    · exact r₂₆
    · exact r₂₇
  · simp only [RawVecOk, Buf, hptr, hcap, hnt]
    refine ⟨hP8, ?_⟩
    simp only [heapNext, heapStart]
    rcases hPb with h0 | h0
    · left; omega
    · right; omega
  · rw [hcap, hlen]
  · intro i hi
    rw [hlen] at hi
    rw [hptr]
    exact (hn' i hi).2.1
  · intro x ⟨i, hi, hx⟩ hb'
    rw [hlen] at hi
    rw [hptr] at hx
    simp only [formVecBuf, hptr, hcap, Within] at hb'
    have := (hn' i hi).2.2 x hx
    rcases hPb with h0 | h0
    · omega
    · omega
  · intro x hx
    simp only [Fresh, hnt]
    simp only [heapNext]
    rcases hx with hx | ⟨i, hi, hx⟩
    · simp only [formVecBuf, hptr, hcap, Within] at hx
      rcases hPb with h0 | h0
      · omega
      · omega
    · rw [hlen] at hi
      rw [hptr] at hx
      have := (hn' i hi).2.2 x hx
      rw [hnt] at this
      simp only [heapNext] at this
      omega
  · refine (he.frame.union hmf.dframe).mono fun x h ↦ ?_
    rcases h with (h | h | h) | h
    · exact Or.inr (Or.inl (by simp only [stackLo, cloneStack, tryAllocStack]; addr_omega [h, hb]))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hnt] using h)))
    · exact Or.inl h
  · simp only [formVecOf, formsAt, hptr, hlen]
    apply List.map_congr_left
    intro i hi
    exact (hn' i (List.mem_range.mp hi)).1
  · intro i hi
    rw [hptr]
    exact hcaps i hi
  · intro i hi
    rw [hptr]
    exact hdang i hi

/-- `CloneSpec`, and each clone's capacity its source's length. -/
def CloneCapsSpec : Prop := FunSpec Image.code 0x80006104 ClonePre fun s t ↦
  (NewFormVec s t (s.getReg .x10) cloneStack ∧
    formVecOf t (s.getReg .x10) = formsAt s (s.getReg .x11) (s.getReg .x12).toNat) ∧
  (∀ i < (s.getReg .x12).toNat, vecCap t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) =
    vecLen s (s.getReg .x11 + BitVec.ofNat 64 (24 * i))) ∧
  ∀ i < (s.getReg .x12).toNat, vecLen s (s.getReg .x11 + BitVec.ofNat 64 (24 * i)) = 0 →
    vecPtr t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) = 8

/-- `<Vec<Form> as Clone>::clone` meets `CloneCapsSpec`, given `try_allocate_in`'s and
`memcpy`'s. -/
theorem clone_caps_spec (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) :
    CloneCapsSpec := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hst := hpre.stack
  have hnx := hst.next
  have hab := hst.above
  simp only [cloneStack, tryAllocStack, stackLo, heapEnd] at hnx hab
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006104_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80006104_keeps h₁
  have hm₁ := b80006104_frame h₁ (by addr_omega [hb])
  have x2₁ := b80006104_x2 h₁
  have x10₁ := b80006104_x10 h₁
  have hn₁ : t₁.getMem nextAddr = s.getMem nextAddr := hm₁ _ (by addr_omega [hnx, hb])
  have hnext₁ : heapNext t₁ = heapNext s := by simp only [heapNext, hn₁]
  have hta : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hnext₁ ▸ hpre.heap.lo, hnext₁ ▸ hpre.heap.hi⟩
    out := by rw [x10₁]; valid_sub hst.valid [hb]
    align := by rw [b80006104_x13 h₁]; decide
    size := by rw [b80006104_x14 h₁]; decide
    stack := hst.inner (k := 128) x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]; simp only [Outside, heapEnd]
      exact ⟨Or.inr (by addr_omega [hb, hab]), by addr_omega [hb, hnx]⟩
    outStack := by rw [x10₁]; addr_omega [hb, x2₁] }
  obtain ⟨r, hr₂, ⟨hpc₂, hpres₂, hpost, -⟩ | hdead⟩ := hT.call hr₁ (b80006104_pc h₁) hta
  swap
  · exact ⟨r, hr₂, Or.inr hdead⟩
  have hwf := hpost.frame.dframe
  rw [x10₁, show stackLo t₁ tryAllocStack = s.getReg .x2 - 176 by
    simp only [stackLo, x2₁, tryAllocStack]; rv_eval []] at hwf
  have x2₂ : r.getReg .x2 = s.getReg .x2 - 128 := (hpres₂.reg .x2).trans x2₁
  obtain ⟨r₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006164_spec
    (by rw [hpc₂, returnAddress_eq, b80006104_x1 h₁]; decide) (by
      rv_eval [x2₂]
      valid_access hst.valid [hb])
  by_cases htag : r.getMem (s.getReg .x2 - 128) = 0
  swap
  · exact ⟨r₂, hr₂.trans hr₃, Or.inr (dead_of_fetch (by
      rw [b80006164_pc_taken h₃ (by rwa [x2₂])]; exact trap))⟩
  have hok₂ := hpost.ok
  rw [x10₁] at hok₂
  obtain ⟨hcap₂, hnew₂⟩ := hok₂ htag
  rw [b80006104_x11 h₁, b80006104_x14 h₁, b80006104_x13 h₁] at hnew₂
  rw [b80006104_x11 h₁] at hcap₂
  rw [show s.getReg .x2 - 128 + 8 = s.getReg .x2 - 120 by rv_eval []] at hcap₂
  rw [show s.getReg .x2 - 128 + 16 = s.getReg .x2 - 112 by rv_eval []] at hnew₂
  obtain ⟨P, hP⟩ : ∃ P, P = r.getMem (s.getReg .x2 - 112) := ⟨_, rfl⟩
  rw [← hP] at hnew₂
  have hnb := hnew₂
  simp only [NewBuf, show (24 : Word).toNat = 24 from rfl, show (8 : Word).toNat = 8 from rfl]
    at hnb
  have hbase : Base s P (heapNext r) := {
    al := hnb.1
    buf := by
      rcases hnb.2 with h0 | h0
      · left; omega
      · right; rw [← hnext₁]; omega
    nr := ⟨by rw [← hnext₁]; exact hpost.mono, hpost.heap.hi⟩ }
  have k₃ := b80006164_keeps h₃
  have hm₃ := b80006164_mem_same h₃
  have hcore₀ (v : MachineState) (hv : ∀ a, v.getMem a = r.getMem a) :
      Core s t₁ P (heapNext r) v 0 := by
    have hnv : heapNext v = heapNext r := by simp only [heapNext, hv]
    have hrhi := hpost.heap.hi
    simp only [heapNext, heapEnd] at hrhi
    exact {
      heap := ⟨hnv ▸ hpost.heap.lo, hnv ▸ hpost.heap.hi⟩
      mono := hnv.ge
      saved := fun a h1 h2 ↦ by
        rw [hv]
        refine hwf.getMem_of (fun x hx h ↦ ?_) (by addr_omega [h2, hb])
        rcases h with h | h | h | h
        · addr_omega [hx, h, h1, h2, hb]
        · addr_omega [hx, h, h1, h2, hb]
        · addr_omega [hx, h, h1, h2, hb, hnx]
        · simp only [Fresh, heapNext] at h; addr_omega [hx, h, h1, h2, hb, hrhi, hab]
      frame := ((hm₁.dframe.union hwf).union (DFrame.of_same hv fun _ ↦ False)).mono fun x h ↦ by
        rcases h with (h | h | h | h | h) | h
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by simpa only [Fresh, hnext₁, hnv] using h))
        · exact h.elim
      new := fun j hj ↦ absurd hj (Nat.not_lt_zero _)
      caps := fun j hj ↦ absurd hj (Nat.not_lt_zero _)
      dang := fun j hj ↦ absurd hj (Nat.not_lt_zero _) }
  have hfin : ∀ v, Reaches Image.code s v → Done s t₁ P (heapNext r) v → ∃ t,
      Reaches Image.code s t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
        ((NewFormVec s t (s.getReg .x10) cloneStack ∧
          formVecOf t (s.getReg .x10) = formsAt s (s.getReg .x11) (s.getReg .x12).toNat) ∧
        (∀ i < (s.getReg .x12).toNat,
          vecCap t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) =
            vecLen s (s.getReg .x11 + BitVec.ofNat 64 (24 * i))) ∧
        ∀ i < (s.getReg .x12).toNat, vecLen s (s.getReg .x11 + BitVec.ofNat 64 (24 * i)) = 0 →
          vecPtr t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) = 8)) ∨
        Dead Image.code t) := by
    intro v hv hd
    rcases hd with he | hd
    · obtain ⟨t, hvt, hpc', hpres, hnew, hval, hcap, hdang⟩ := exit hpre hbase h₁ he
      exact ⟨t, hv.trans hvt, Or.inl ⟨hpc', hpres, ⟨hnew, hval⟩, hcap, hdang⟩⟩
    · exact ⟨v, hv, Or.inr hd⟩
  have hreg (q : Reg) (hq : q ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27]) : r₂.getReg q = t₁.getReg q := by
    rw [k₃ q (mem_of_mem hq _), hpres₂ q (mem_of_mem hq _)]
  obtain ⟨r₃, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000616c_spec
    (b80006164_pc_not_taken h₃ (by rwa [x2₂])) (by
      rv_eval [k₃ .x2 (by decide), x2₂]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000616c_keeps h₄
  have hm₄ := b8000616c_mem_same h₄
  have x2₃ : r₂.getReg .x2 = s.getReg .x2 - 128 := (k₃ .x2 (by decide)).trans x2₂
  have x22₄ : r₃.getReg .x22 = s.getReg .x12 := by
    rw [b8000616c_x22 h₄, x2₃, hm₃]; rv_eval []; exact hcap₂
  have x23₄ : r₃.getReg .x23 = P := by
    rw [b8000616c_x23 h₄, x2₃, hm₃, hP]; rv_eval []
  have hmr (a : Word) : r₃.getMem a = r.getMem a := (hm₄ a).trans (hm₃ a)
  by_cases hz : s.getReg .x12 = 0
  · -- an empty slice
    have hn0 : (s.getReg .x12).toNat = 0 := by rw [hz]; rfl
    refine hfin r₃ (hr₂.trans (hr₃.trans hr₄)) (Or.inl {
      toCore := hn0 ▸ hcore₀ r₃ hmr
      pc := b8000616c_pc_taken h₄ (by rw [x2₃, hm₃]; rv_eval []; rw [hcap₂, hz])
      sp := (k₄ .x2 (by decide)).trans x2₃
      x8 := by rw [k₄ .x8 (by decide), hreg .x8 (by decide), b80006104_x8 h₁]
      x9 := by rw [k₄ .x9 (by decide), hreg .x9 (by decide), b80006104_x9 h₁]
      x22 := x22₄
      x23 := x23₄ })
  obtain ⟨r₄, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80006178_spec
    (b8000616c_pc_not_taken h₄ (by rw [x2₃, hm₃]; rv_eval []; rw [hcap₂]; exact hz)) trivial
  have k₅ := b80006178_keeps h₅
  have hm₅ := b80006178_mem_same h₅
  have x8₄ : r₃.getReg .x8 = s.getReg .x12 := by
    rw [k₄ .x8 (by decide), hreg .x8 (by decide), b80006104_x8 h₁]
  have hlt := (s.getReg .x12).isLt
  have hn : 0 < (s.getReg .x12).toNat := by
    rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) hz
    · exact h
  have hsrcb := src_bounds hpre
  have inv₀ : Inv s t₁ P (heapNext r) r₄ 0 := {
    toCore := hcore₀ r₄ fun a ↦ (hm₅ a).trans (hmr a)
    lt := hn
    pc := b80006178_pc h₅
    sp := by rw [k₅ .x2 (by decide), k₄ .x2 (by decide), x2₃]
    x8 := by rw [k₅ .x8 (by decide), x8₄]
    x9 := by rw [k₅ .x9 (by decide), k₄ .x9 (by decide), hreg .x9 (by decide), b80006104_x9 h₁]
    x18 := by
      rw [k₅ .x18 (by decide), k₄ .x18 (by decide), hreg .x18 (by decide), b80006104_x18 h₁]
      simp [src]
    x22 := by rw [k₅ .x22 (by decide), x22₄]
    x23 := by rw [k₅ .x23 (by decide), x23₄]
    x24 := by rw [b80006178_x24 h₅, x23₄]; simp [slot]
    x25 := by
      rw [b80006178_x25 h₅, x8₄]
      simp only [Nat.sub_zero]
      addr_omega [hsrcb.1]
    x26 := by rw [b80006178_x26 h₅, x22₄]; simp }
  obtain ⟨v, hv, hd⟩ := Reaches.loop (fun v ↦ ∃ k, Inv s t₁ P (heapNext r) v k)
    (fun v ↦ (v.getReg .x26).toNat) (Done s t₁ P (heapNext r)) (body hT hM hpre hbase) r₄ ⟨0, inv₀⟩
  exact hfin v (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hv)))) hd

/-- **`<Vec<Form> as Clone>::clone` meets its contract**, given `try_allocate_in`'s and
`memcpy`'s. -/
theorem clone_spec (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) : CloneSpec := by
  intro s hpc hpre
  obtain ⟨t, hr, h | h⟩ := clone_caps_spec hT hM s hpc hpre
  · exact ⟨t, hr, Or.inl ⟨h.1, h.2.1, h.2.2.1⟩⟩
  · exact ⟨t, hr, Or.inr h⟩

end Rv64Verifier.Layout.Clone
