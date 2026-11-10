import Rv64Verifier.Proofs.Layout.ContractsVec
import Rv64Verifier.Proofs.Layout.VecLemmas
import Rv64Verifier.Blocks.F22

/-!
# `Vec<BusBlock>::extend_trusted`, at `0x80005f94`: contract and frame

```rust
let block = |coordinates: &Vec<Form>| BusBlock {
    log_rows: height, rows: table_rows[table.opcode], coordinates: coordinates.clone(),
    owner: table.opcode };
push.extend(table.flushes.push.iter().map(block));
```

`a0` is the `Vec<BusBlock>` (48-byte elements: the coordinates' header at `+0`, `log_rows` at `+24`,
`rows` at `+32`, `owner` at `+40`), `a1` the iterator: the slice of `Vec<Form>`s from `itStart` to
`itEnd`, then the closure's captures, pointers to `height`, to `rows` and to the table (whose
`opcode` is at `+72`). Compiled (`Blocks/F22.lean`), with `S` the entry's `sp`: `0x80005f94` saves
`ra`, `s0`..`s9` in a 144-byte frame and calls `reserve(a0, k)`, `k` the slice's length (its
byte length over 24, by a multiplication by the inverse of 3); `0x80006000` exits at once on an
empty slice; `0x80006008` loads the captures; the loop at `0x80006034` reads `height` and `rows`,
clones the next `Vec<Form>` to `S - 136` and `0x80006050` writes the block; `0x80006084` stores the
length and returns.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Model.LayoutMirror

/-- Its 144-byte frame and the deeper of `reserve`'s and `clone`'s stacks. -/
@[rv_addr] def extendStack : Nat := 144 + cloneStack

/-- The iterator at `a1`. -/
def itStart (s : MachineState) : Word := s.getMem (s.getReg .x11)
def itEnd (s : MachineState) : Word := s.getMem (s.getReg .x11 + 8)
def itHeight (s : MachineState) : Word := s.getMem (s.getReg .x11 + 16)
def itRows (s : MachineState) : Word := s.getMem (s.getReg .x11 + 24)
def itTable (s : MachineState) : Word := s.getMem (s.getReg .x11 + 32)

/-- The slice's length. -/
def itLen (s : MachineState) : Nat := ((itEnd s).toNat - (itStart s).toNat) / 24

/-- The `i`-th `Vec<Form>` of the slice. -/
def itElem (s : MachineState) (i : Nat) : Word := itStart s + BitVec.ofNat 64 (24 * i)

/-- What the call reads: the iterator, the slice, its forms, and the three captured values. -/
@[rv_addr] def ExtRead (s : MachineState) (x : Word) : Prop :=
  Within x (s.getReg .x11) 40 ∨ Within x (itStart s) (24 * itLen s) ∨
    (∃ i < itLen s, formVecDeep s (itElem s i) x) ∨ Within x (itHeight s) 8 ∨
    Within x (itRows s) 8 ∨ Within x (itTable s + 72) 8

/-- The `Vec`'s header and buffer. -/
@[rv_addr] def ExtSelf (s : MachineState) (x : Word) : Prop :=
  Within x (s.getReg .x10) 24 ∨
    Within x (vecPtr s (s.getReg .x10)) (48 * (vecCap s (s.getReg .x10)).toNat)

structure ExtendPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s extendStack
  self : ValidMemRange (s.getReg .x10) 3
  vec : VecOk s (s.getReg .x10) 48 8
  selfFree : Outside s (s.getReg .x10) 24
  selfStack : Apart (s.getReg .x10) 24 (stackLo s extendStack) extendStack
  selfBuf : Apart (s.getReg .x10) 24 (vecPtr s (s.getReg .x10)) (48 * (vecCap s (s.getReg .x10)).toNat)
  iter : ValidMemRange (s.getReg .x11) 5
  bounds : (itStart s).toNat ≤ (itEnd s).toNat
  whole : ((itEnd s).toNat - (itStart s).toNat) % 24 = 0
  src : ValidMemRange (itStart s) (3 * itLen s)
  elems : ∀ i < itLen s, FormVecOk s (itElem s i)
  /-- an empty buffer's pointer too misses the free heap -/
  elemsPtr : ∀ i < itLen s, (vecPtr s (itElem s i)).toNat ≤ heapNext s ∨
    heapEnd ≤ (vecPtr s (itElem s i)).toNat
  height : ValidMemRange (itHeight s) 1
  rows : ValidMemRange (itRows s) 1
  owner : ValidMemRange (itTable s + 72) 1
  kept : ∀ x, ExtRead s x → (x.toNat < heapNext s ∨ heapEnd ≤ x.toNat) ∧ ¬ Within x nextAddr 8 ∧
    ¬ Within x (stackLo s extendStack) extendStack ∧ ¬ ExtSelf s x

/-- Block `b` is the closure's block for the `Vec<Form>` at `e`: its coordinates a clone whose
buffers were all allocated by the call. -/
structure NewBlock (s t : MachineState) (b e : Word) : Prop where
  logRows : t.getMem (b + 24) = s.getMem (itHeight s)
  rows : t.getMem (b + 32) = s.getMem (itRows s)
  owner : t.getMem (b + 40) = s.getMem (itTable s + 72)
  ok : FormVecOk t b
  value : formVecOf t b = formVecOf s e
  fresh : ∀ x, formVecDeep t b x → Fresh s t x

/-- The blocks appended after the old ones, whose bytes the buffer keeps; memory changed only in the
`Vec`'s header and old buffer, the stack, `NEXT` and what the call allocates. -/
structure ExtendPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  vec : VecOk t (s.getReg .x10) 48 8
  len : (vecLen t (s.getReg .x10)).toNat = (vecLen s (s.getReg .x10)).toNat + itLen s
  old : bytesAt t (vecPtr t (s.getReg .x10)) (48 * (vecLen s (s.getReg .x10)).toNat) =
    bytesAt s (vecPtr s (s.getReg .x10)) (48 * (vecLen s (s.getReg .x10)).toNat)
  buf : (vecPtr t (s.getReg .x10) = vecPtr s (s.getReg .x10) ∧
      vecCap t (s.getReg .x10) = vecCap s (s.getReg .x10)) ∨
    NewBuf s t (vecPtr t (s.getReg .x10)) (48 * (vecCap t (s.getReg .x10)).toNat) 8
  new : ∀ i < itLen s, NewBlock s t
    (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (48 * ((vecLen s (s.getReg .x10)).toNat + i)))
    (itElem s i)
  frame : DFrame s t fun a ↦ ExtSelf s a ∨ Within a (stackLo s extendStack) extendStack ∨
    Within a nextAddr 8 ∨ Fresh s t a

def ExtendSpec : Prop := FunSpec Image.code 0x80005f94 ExtendPre ExtendPost

namespace Extend
open Rv64Verifier.Sym Rv64Verifier.Blocks.F22
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) :=
  [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19), (48, .x20), (56, .x21), (64, .x22),
    (72, .x23), (80, .x24), (88, .x25)]

def kept : List Reg := [.x26, .x27]

/-- What the function writes besides its saved registers: the `Vec`, and the stack below them. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  ExtSelf s a ∨ Within a (stackLo s extendStack) 232

/-- Inside the function: `sp` 144 below the entry's, the saved registers in the frame's top 88
bytes, memory changed only in `W`, the frame, `NEXT` and the heap allocated since entry. -/
structure Inv (s u : MachineState) (nx : Word) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 144
  saved : ∀ p ∈ slots, u.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2
  regs : ∀ r ∈ kept, u.getReg r = s.getReg r
  mem : DFrame s u fun a ↦ W s a ∨ Within a (stackLo s 144) 144 ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)
  next : u.getMem nextAddr = nx
  mono : heapNext s ≤ nx.toNat
  fits : nx.toNat ≤ heapEnd

theorem bounds {s : MachineState} (h : ExtendPre s) :
    0xa0000140 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s extendStack).toNat = (s.getReg .x2).toNat - 320 := by
  have hb := h.stack.bounds (by decide) (by decide)
  have hab := h.stack.above
  have hv := h.stack.valid 1 (by simp only [extendStack, cloneStack, tryAllocStack]; decide)
  have h1 := (Sym.validAccess_eight _).mp (validAccess_of_dword hv)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  simp only [extendStack, cloneStack, tryAllocStack, heapEnd, Nat.reduceAdd] at hb hab h1 ⊢
  omega

/-- The old buffer lies in the heap below `NEXT`, so below the stack. -/
theorem buf_bounds {s : MachineState} (h : ExtendPre s) :
    (vecPtr s (s.getReg .x10)).toNat % 8 = 0 ∧ ((vecCap s (s.getReg .x10)).toNat = 0 ∨
      heapStart ≤ (vecPtr s (s.getReg .x10)).toNat ∧
      (vecPtr s (s.getReg .x10)).toNat + 48 * (vecCap s (s.getReg .x10)).toNat ≤ heapNext s) := by
  have := vecBuf_bounds h.vec (by decide)
  rcases this.2 with h0 | h0
  · exact ⟨this.1, Or.inl h0⟩
  · exact ⟨this.1, Or.inr ⟨h0.1, by omega⟩⟩

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : ExtendPre s) (h : Inv s u nx) (hX : DFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := bounds hpre
  have hs := hpre.selfStack
  have hbb := buf_bounds hpre
  have hab := hpre.stack.above
  have hhi := hpre.heap.hi
  have hn8 := hpre.stack.next
  refine ⟨(hr _ (by decide)).trans h.sp, fun p hp ↦ ?_,
    fun r hr' ↦ (hr r (List.mem_cons_of_mem _ hr')).trans (h.regs r hr'),
    (h.mem.union hX).mono fun a ha ↦ ?_, hnx, Nat.le_trans h.mono hle, hend⟩
  · have h1 : 8 ≤ p.1 ∧ p.1 ≤ 88 := (show ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 ≤ 88 by decide) p hp
    rw [← h.saved p hp]
    refine hX.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [h1, hb])
    rcases hXsub x hw with hx' | hx' | hx'
    · simp only [W, ExtSelf] at hx'
      rcases hx' with (hx' | hx') | hx' <;> addr_omega [hx, hx', h1, hb, hs, hbb, hab, hhi]
    · addr_omega [hx, hx', h1, hb, hn8]
    · addr_omega [hx, hx', h1, hb, hab, hend]
  · rcases ha with (ha | ha | ha | ha) | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨ha.1, Nat.lt_of_lt_of_le ha.2 hle⟩))
    · rcases hXsub a ha with hx | hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx))

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : ExtendPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

theorem Inv.slotVals {s u : MachineState} {nx : Word} (h : Inv s u nx) :
    u.getReg .x2 = s.getReg .x2 - 144 ∧ u.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧
      u.getMem (s.getReg .x2 - 16) = s.getReg .x8 ∧ u.getMem (s.getReg .x2 - 24) = s.getReg .x9 ∧
      u.getMem (s.getReg .x2 - 32) = s.getReg .x18 ∧ u.getMem (s.getReg .x2 - 40) = s.getReg .x19 ∧
      u.getMem (s.getReg .x2 - 48) = s.getReg .x20 ∧ u.getMem (s.getReg .x2 - 56) = s.getReg .x21 ∧
      u.getMem (s.getReg .x2 - 64) = s.getReg .x22 ∧ u.getMem (s.getReg .x2 - 72) = s.getReg .x23 ∧
      u.getMem (s.getReg .x2 - 80) = s.getReg .x24 ∧ u.getMem (s.getReg .x2 - 88) = s.getReg .x25 := by
  have hsp := h.sp
  have sl := h.saved
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at hsp sl
  exact ⟨hsp, sl⟩

/-- What the call reads is never written. -/
theorem Inv.dframe {s u : MachineState} {nx : Word} (hpre : ExtendPre s) (h : Inv s u nx) :
    DFrame s u fun x ↦ ¬ ExtRead s x := by
  have hb := bounds hpre
  have hfit := h.fits
  refine h.mem.mono fun x hw hr ↦ ?_
  obtain ⟨h1, h2, h3, h4⟩ := hpre.kept x hr
  simp only [W] at hw
  rcases hw with (hw | hw) | hw | hw | hw
  · exact h4 hw
  · exact h3 (by addr_omega [hw, hb])
  · exact h3 (by addr_omega [hw, hb])
  · exact h2 hw
  · simp only [heapNext] at hw h1; addr_omega [hw, h1, hfit]

/-- A doubleword the call reads is unchanged. -/
theorem Inv.read {s u : MachineState} {nx : Word} (hpre : ExtendPre s) (h : Inv s u nx) {a : Word}
    (ha : ∀ x, Within x a 8 → ExtRead s x) (hw : a.toNat + 8 ≤ 2 ^ 64) : u.getMem a = s.getMem a :=
  (h.dframe hpre).getMem_of (fun x hx hn ↦ hn (ha x hx)) hw

/-- Two ranges with no byte in common are apart. -/
theorem apart_of {a b : Word} {n m : Nat} (h : ∀ x, Within x a n → ¬ Within x b m) :
    Apart a n b m := by
  refine Classical.byContradiction fun hc ↦ ?_
  simp only [Apart, not_or] at hc
  by_cases hab : a.toNat ≤ b.toNat
  · exact h b (by simp only [Within]; omega) (by simp only [Within]; omega)
  · exact h a (by simp only [Within]; omega) (by simp only [Within]; omega)

/-- Aligned whole doublewords the frame misses keep their bytes. -/
theorem DFrame.bytesAt_al {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    {n : Nat} (hp : p.toNat % 8 = 0) (hn : n % 8 = 0) (hw : p.toNat + n ≤ 2 ^ 64)
    (hx : ∀ x, Within x p n → ¬ w x) : bytesAt t p n = bytesAt s p n := by
  refine bytesAt_eq_iff.mpr fun i hi ↦ ?_
  have hal := toNat_alignDown (p + BitVec.ofNat 64 i)
  have hpi : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [byteAt_eq, byteAt_eq, h.getMem_of (fun x hx' ↦ hx x (by addr_omega [hx', hal, hpi, hi, hp, hn, hw]))
    (by addr_omega [hal, hpi, hi, hp, hn, hw])]

theorem bytesAt_prefix {s t : MachineState} {a b : Word} {n N : Nat}
    (h : bytesAt t a N = bytesAt s b N) (hn : n ≤ N) : bytesAt t a n = bytesAt s b n :=
  bytesAt_eq_iff.mpr fun i hi ↦ bytesAt_eq_iff.mp h i (by omega)

/-- The inverse of `3` modulo `2^64` divides exactly. -/
theorem div3 (x : Word) (h : x.toNat % 3 = 0) :
    x * 0xaaaaaaaaaaaaaaab = BitVec.ofNat 64 (x.toNat / 3) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have := x.isLt
  show x.toNat * 0xaaaaaaaaaaaaaaab % 2 ^ 64 = x.toNat / 3 % 2 ^ 64
  omega

end Extend

end Rv64Verifier.Layout
