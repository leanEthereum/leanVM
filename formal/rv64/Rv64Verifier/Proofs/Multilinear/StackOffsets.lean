import Rv64Verifier.Proofs.Multilinear.StackLog
import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Proofs.Multilinear.FromElem

/-!
# `verifier::multilinear::stack_offsets`

```rust
pub fn stack_offsets(sizes: &[usize]) -> (Vec<u64>, usize) {
    let mut offsets = vec![0; sizes.len()];
    let mut total = 0;
    let largest = sizes.iter().copied().max().unwrap_or(0);
    for size in (0..=largest).rev() {
        for (index, &block) in sizes.iter().enumerate() {
            if block == size {
                offsets[index] = total;
                total += 1 << size;
            }
        }
    }
    (offsets, log2_ceil(total))
}
```

compiled at `0x80006258` (`Blocks/F25.lean`), with `S` the entry's `sp`: `0x80006258` saves `ra`,
`s0`..`s2` in a 64-byte frame (`s0` = `n`, `s1` = the result, `s2` = the sizes) and calls
`try_allocate_in(S - 56, n, 1, 8, 8)` (zeroed); `0x80006294` traps on `Err`; `0x8000629c`..
`0x800062d4` find `largest` (the loop at `0x800062c4`); `0x800062d8` loads the buffer `P` and its
capacity; the outer loop at `0x800062f4` (`a5` = `size`) runs the inner one at `0x80006328`
(`a6` = `index`, trapping unless `index < n`, never); `0x80006340` computes `log2_ceil(total)`
(`StackLog.lean`); `0x800063f8` writes the result, restores and returns.
-/

namespace Rv64Verifier.MultilinearContracts
open RiscvZkvm.Rv64 Rv64Verifier.Runtime

/-- `stack_offsets`' 64-byte frame and `try_allocate_in`'s stack below it. -/
@[rv_addr] def stackOffsetsStack : Nat := 64 + tryAllocStack

/-- The sizes, `n` doublewords from `a1`. -/
def sizesAt (s : MachineState) : List Nat :=
  (s.readWords (s.getReg .x11) (s.getReg .x12).toNat).map BitVec.toNat

/-- `a0` = the result (`(Vec<u64>, usize)`, 32 bytes), `a1`/`a2` = the sizes, the pointer arbitrary
when empty. -/
structure StackOffsetsPre (s : MachineState) : Prop where
  heap : HeapOk s
  out : Transcript.Region (s.getReg .x10) 32
  sizes : (s.getReg .x12).toNat = 0 ∨
    Transcript.Region (s.getReg .x11) (8 * (s.getReg .x12).toNat)
  stack : RtStack s stackOffsetsStack
  outFree : Outside s (s.getReg .x10) 32
  outStack : Apart (s.getReg .x10) 32 (stackLo s stackOffsetsStack) stackOffsetsStack
  sizesFree : (s.getReg .x12).toNat = 0 ∨ Outside s (s.getReg .x11) (8 * (s.getReg .x12).toNat)
  sizesStack : Apart (s.getReg .x11) (8 * (s.getReg .x12).toNat) (stackLo s stackOffsetsStack)
    stackOffsetsStack
  sizesOut : Apart (s.getReg .x11) (8 * (s.getReg .x12).toNat) (s.getReg .x10) 32

/-- `(offsets, log2_ceil(total))` as `stackOffsetsRust` computes them: a new `Vec<u64>` at `a0`,
the log size at `a0 + 24`; memory changes only in the result, the stack, `NEXT` and the new
allocation. -/
structure StackOffsetsPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  vec : VecOk t (s.getReg .x10) 8 8
  len : vecLen t (s.getReg .x10) = s.getReg .x12
  offsets : vecWords t (s.getReg .x10) = (Model.stackOffsetsRust (sizesAt s)).1
  log : (t.getMem (s.getReg .x10 + 24)).toNat = (Model.stackOffsetsRust (sizesAt s)).2
  fresh : NewBuf s t (vecPtr t (s.getReg .x10)) (8 * (s.getReg .x12).toNat) 8
  frame : ByteFrame s t fun a ↦ Within a (s.getReg .x10) 32 ∨
    Within a (stackLo s stackOffsetsStack) stackOffsetsStack ∨ Within a nextAddr 8 ∨ Fresh s t a

abbrev StackOffsetsSpec : Prop := FunSpec Image.code 0x80006258 StackOffsetsPre StackOffsetsPost

end Rv64Verifier.MultilinearContracts

namespace Rv64Verifier.Proofs.Multilinear.StackOffsets
open RiscvZkvm.Rv64 LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts
  Rv64Verifier.MultilinearWords Rv64Verifier.Blocks.F25
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18)]

def kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- What the function writes besides its saved registers: the result, and the stack below them. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 32 ∨ Within a (stackLo s stackOffsetsStack) 80

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 64 slots kept (W s) nx

theorem outValid {s : MachineState} (h : StackOffsetsPre s) : ValidMemRange (s.getReg .x10) 4 := by
  intro i hi
  have ho := h.out
  exact Transcript.Region.valid ho (by addr_omega [ho, hi]) (by addr_omega [ho, hi])
    (by addr_omega [ho, hi])

theorem bounds {s : MachineState} (h : StackOffsetsPre s) :
    0x78000070 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 32 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds (outValid h) (by decide)
  simp only [stackOffsetsStack, tryAllocStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem stack64 {s : MachineState} (h : StackOffsetsPre s) : RtStack s 64 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : StackOffsetsPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := bounds hpre
  have hs := hpre.outStack
  exact FnInv.step (m := 32) h (stack64 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hs, hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : StackOffsetsPre s) (h : Inv s u nx)
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

/-- The sizes are never written. -/
theorem size_eq {s u : MachineState} {nx : Word} (hpre : StackOffsetsPre s) (h : Inv s u nx)
    {i : Nat} (hi : i < (s.getReg .x12).toNat) :
    u.getMem (s.getReg .x11 + BitVec.ofNat 64 (8 * i)) =
      s.getMem (s.getReg .x11 + BitVec.ofNat 64 (8 * i)) := by
  have hb := bounds hpre
  have hr := hpre.sizes.resolve_left (by omega)
  have hr1 := hr.1
  have hf := hpre.sizesFree.resolve_left (by omega)
  have hs := hpre.sizesStack
  have ho := hpre.sizesOut
  have hfit := h.fits
  simp only [Outside] at hf
  refine h.mem.getMem fun j hj hw ↦ ?_
  rcases hw with (hw | hw) | hw | hw | hw
  · addr_omega [hw, hj, hi, hr1, ho]
  · addr_omega [hw, hj, hi, hr1, hs, hb]
  · addr_omega [hw, hj, hi, hr1, hs, hb]
  · addr_omega [hw, hj, hi, hr1, hf.2]
  · addr_omega [hw, hj, hi, hr1, hf.1, hfit]

theorem sizesAt_getD (s : MachineState) {i : Nat} (hi : i < (s.getReg .x12).toNat) :
    (sizesAt s).getD i 0 = (s.getMem (s.getReg .x11 + BitVec.ofNat 64 (8 * i))).toNat := by
  rw [sizesAt, readWords_eq_map]
  simp [List.getD_eq_getElem?_getD, hi]

theorem sizesAt_length (s : MachineState) : (sizesAt s).length = (s.getReg .x12).toNat := by
  simp [sizesAt, readWords_eq_map]

/-- An aligned doubleword whose bytes are zero is zero. -/
theorem getMem_zero {t : MachineState} {a : Word} (ha : a.toNat % 8 = 0)
    (h : ∀ i < 8, byteAt t (a + BitVec.ofNat 64 i) = 0) : t.getMem a = 0 :=
  eq_of_extractByte fun i hi ↦ by
    rw [← byteAt_add ha hi, h i hi]
    interval_cases i <;> decide

theorem words_zero {t : MachineState} {P : Word} {n : Nat} (hP : P.toNat % 8 = 0)
    (hb : P.toNat + 8 * n ≤ 2 ^ 64) (hz : bytesAt t P (n * 8) = List.replicate (n * 8) 0) :
    t.readWords P n = List.replicate n 0 := by
  have hall := (List.eq_replicate_iff.mp hz).2
  rw [readWords_eq_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp only [List.length_map, List.length_range] at h1
  refine getMem_zero (by addr_omega [hP, hb, h1]) fun k hk ↦ ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hall _ (List.mem_map.mpr ⟨8 * i + k, List.mem_range.mpr (by omega), rfl⟩)

/-- One doubleword written, the rest kept. -/
theorem readWords_set {u v : MachineState} {P x : Word} {n i : Nat} (hi : i < n)
    (hP : P.toNat + 8 * n ≤ 2 ^ 64)
    (hfr : ∀ a, a ≠ P + BitVec.ofNat 64 (8 * i) → v.getMem a = u.getMem a)
    (hx : v.getMem (P + BitVec.ofNat 64 (8 * i)) = x) :
    v.readWords P n = (u.readWords P n).set i x := by
  rw [readWords_eq_map, readWords_eq_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_set]
  split
  · rename_i hij
    subst hij
    simp only [List.getElem_map, List.getElem_range]
    exact hx
  · rename_i hij
    simp only [List.getElem_map, List.getElem_range]
    exact hfr _ (by addr_omega [hi, h1, hij, hP])

/-- A branch's target, with its condition. -/
theorem pc_cases {c : Prop} [Decidable c] {p a b : Word} (h : p = if c then a else b) :
    (p = a ∧ c) ∨ (p = b ∧ ¬ c) := by
  by_cases hc : c
  · exact Or.inl ⟨h.trans (ite_eq_left_of_eq_true _ _ (eq_true hc)), hc⟩
  · exact Or.inr ⟨h.trans (ite_eq_right_of_eq_false _ _ (eq_false hc)), hc⟩

theorem sat_eq (v : Word) : v - (if BitVec.ult 0 v = true then 1 else 0) = Model.satSubOne v := by
  unfold Model.satSubOne
  by_cases hv : v = 0#64
  · subst hv; decide
  · have hu : BitVec.ult 0 v = true := by
      rw [BitVec.ult, decide_eq_true_iff]
      have : v.toNat ≠ 0 := fun h ↦ hv (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [show (0 : Word).toNat = 0 from rfl]
      omega
    simp only [hu, ↓reduceIte, hv]
    rfl

theorem fm_succ (l : List Nat) {j : Nat} (hj : j < l.length) :
    (l.take (j + 1)).foldl max 0 = max ((l.take j).foldl max 0) (l.getD j 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.getD_eq_getElem _ _ hj]

theorem fm_le (l : List Nat) : ∀ x ∈ l, x ≤ l.foldl max 0 := (Model.le_foldl_max l 0).2

/-- The passes for the sizes from `k` to `L`. -/
def upto (s : MachineState) (L k : Nat) : List (BitVec 64) × BitVec 64 :=
  ((List.range' k (L + 1 - k)).reverse).foldl (Model.stackPass (sizesAt s))
    (List.replicate (sizesAt s).length 0#64, 0#64)

theorem upto_pred (s : MachineState) {L c : Nat} (hc : c ≤ L) :
    upto s L c = Model.stackPass (sizesAt s) (upto s L (c + 1)) c := by
  unfold upto
  rw [show L + 1 - c = (L + 1 - (c + 1)) + 1 by omega, List.range'_succ, List.reverse_cons,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem upto_zero (s : MachineState) (L : Nat) :
    upto s L 0 = (List.range (L + 1)).reverse.foldl
      (Model.stackPass (sizesAt s)) (List.replicate (sizesAt s).length 0#64, 0#64) := by
  unfold upto
  rw [List.range_eq_range', Nat.sub_zero]

theorem upto_top (s : MachineState) (L : Nat) :
    upto s L (L + 1) = (List.replicate (sizesAt s).length 0#64, 0#64) := by
  simp [upto]

/-- The buffer `P`, `n` doublewords, below `nx`. -/
structure BufOk (s : MachineState) (P nx : Word) : Prop where
  align : P.toNat % 8 = 0
  range : (s.getReg .x12).toNat = 0 ∨
    (heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 8 ≤ nx.toNat)
  fits : nx.toNat ≤ heapEnd
  lo : heapNext s ≤ nx.toNat

/-- `n` in `s0`, the result's address in `s1`, the sizes in `s2`. -/
structure Regs (s u : MachineState) : Prop where
  x8 : u.getReg .x8 = s.getReg .x12
  x9 : u.getReg .x9 = s.getReg .x10
  x18 : u.getReg .x18 = s.getReg .x11

def regs : List Reg := [.x2, .x8, .x9, .x18] ++ kept

theorem Regs.step {s u v : MachineState} (h : Regs s u) (hr : ∀ r ∈ [Reg.x8, .x9, .x18],
    v.getReg r = u.getReg r) : Regs s v :=
  ⟨(hr _ (by decide)).trans h.x8, (hr _ (by decide)).trans h.x9, (hr _ (by decide)).trans h.x18⟩

/-- Before the passes: the capacity at `S - 48`, the buffer at `S - 40`, zero. -/
structure Mid (s u : MachineState) (nx P : Word) : Prop extends Regs s u where
  inv : Inv s u nx
  cap : u.getMem (s.getReg .x2 - 48) = s.getReg .x12
  ptr : u.getMem (s.getReg .x2 - 40) = P
  zero : u.readWords P (s.getReg .x12).toNat = List.replicate (s.getReg .x12).toNat 0

theorem Mid.same {s u v : MachineState} {nx P : Word} (hpre : StackOffsetsPre s)
    (h : Mid s u nx P) (hm : ∀ a, v.getMem a = u.getMem a) (hr : ∀ r ∈ regs, v.getReg r = u.getReg r) :
    Mid s v nx P :=
  { toRegs := h.toRegs.step fun r hr' ↦ hr r (by simp only [regs]; exact mem_of_mem hr' _)
    inv := h.inv.same hpre hm (l := regs) hr (by decide)
    cap := (hm _).trans h.cap
    ptr := (hm _).trans h.ptr
    zero := by
      have hz := h.zero
      rw [readWords_eq_map] at hz ⊢
      simp only [hm]
      exact hz }

/-- In the loop for `largest`, at element `j`. -/
structure MInv (s u : MachineState) (nx P : Word) (j : Nat) : Prop extends Mid s u nx P where
  pc : u.pc = 0x800062c4
  pos : 1 ≤ j
  lt : j < (s.getReg .x12).toNat
  x10 : u.getReg .x10 = s.getReg .x11 + BitVec.ofNat 64 (8 * j)
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (8 * (s.getReg .x12).toNat)
  x12 : u.getReg .x12 = s.getReg .x12 * 8
  x16 : (u.getReg .x16).toNat = ((sizesAt s).take j).foldl max 0

/-- `largest` found, at `0x800062d8`. -/
structure MDone (s u : MachineState) (nx P : Word) : Prop extends Mid s u nx P where
  pc : u.pc = 0x800062d8
  x12 : u.getReg .x12 = s.getReg .x12 * 8
  x16 : (u.getReg .x16).toNat = (sizesAt s).foldl max 0

theorem max_body {s : MachineState} (hpre : StackOffsetsPre s) {nx P : Word} (u : MachineState)
    (hinv : ∃ j, MInv s u nx P j) :
    (∃ v, Reaches Image.code u v ∧ MDone s v nx P) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ j, MInv s v nx P j) ∧
        (s.getReg .x11 + BitVec.ofNat 64 (8 * (s.getReg .x12).toNat)).toNat - (v.getReg .x10).toNat <
          (s.getReg .x11 + BitVec.ofNat 64 (8 * (s.getReg .x12).toNat)).toNat - (u.getReg .x10).toNat) := by
  obtain ⟨j, hu⟩ := hinv
  have hj := hu.lt
  have hr := hpre.sizes.resolve_left (by omega)
  have hr1 := hr.1
  have hlen := sizesAt_length s
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800062c4_spec hu.pc (by
    rv_eval [hu.x10]
    exact Transcript.Region.valid hr (by addr_omega [hr1, hj]) (by addr_omega [hr1, hj])
      (by addr_omega [hr1, hj, hr.2]))
  have k₁ := b800062c4_keeps h₁
  have hm₁ := b800062c4_mem_same h₁
  have hv : (u.getMem (u.getReg .x10)).toNat = (sizesAt s).getD j 0 := by
    rw [hu.x10, size_eq hpre hu.inv hj, sizesAt_getD s hj]
  have hstep (w : MachineState) (hw : Reaches Image.code u₁ w) (hpcw : w.pc = 0x800062bc)
      (hmw : ∀ a, w.getMem a = u.getMem a) (hrw : ∀ r ∈ regs ++ [Reg.x10, .x11, .x12],
        w.getReg r = u.getReg r)
      (hx16 : (w.getReg .x16).toNat = ((sizesAt s).take (j + 1)).foldl max 0) :
      (∃ v, Reaches Image.code u v ∧ MDone s v nx P) ∨
        (∃ v, Reaches Image.code u v ∧ (∃ j, MInv s v nx P j) ∧
          (s.getReg .x11 + BitVec.ofNat 64 (8 * (s.getReg .x12).toNat)).toNat - (v.getReg .x10).toNat <
            (s.getReg .x11 + BitVec.ofNat 64 (8 * (s.getReg .x12).toNat)).toNat - (u.getReg .x10).toNat) := by
    obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800062bc_spec hpcw (by rv_eval [])
    have k₂ := b800062bc_keeps h₂
    have hm₂ := b800062bc_mem_same h₂
    have mid := hu.toMid.same hpre (fun a ↦ (hm₂ a).trans (hmw a)) fun r hr' ↦
      (k₂ r (mem_of_mem hr' _)).trans (hrw r (by simp only [List.mem_append]; exact Or.inl hr'))
    have e10 : w.getReg .x10 = s.getReg .x11 + BitVec.ofNat 64 (8 * j) :=
      (hrw .x10 (by decide)).trans hu.x10
    have e11 : w.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (8 * (s.getReg .x12).toNat) :=
      (hrw .x11 (by decide)).trans hu.x11
    have hx10 : v.getReg .x10 = s.getReg .x11 + BitVec.ofNat 64 (8 * (j + 1)) := by
      rw [b800062bc_x10 h₂, e10]; addr_omega [hr1, hj]
    by_cases hlast : j + 1 = (s.getReg .x12).toNat
    · refine Or.inl ⟨v, hr₁.trans (hw.trans hr₂), {
        toMid := mid
        pc := b800062bc_pc_taken h₂ (by rw [e10, e11]; addr_omega [hr1, hj, hlast])
        x12 := (k₂ .x12 (by decide)).trans ((hrw .x12 (by decide)).trans hu.x12)
        x16 := by
          rw [k₂ .x16 (by decide), hx16, hlast, ← hlen, List.take_length] }⟩
    · refine Or.inr ⟨v, hr₁.trans (hw.trans hr₂), ⟨j + 1, {
        toMid := mid
        pc := b800062bc_pc_not_taken h₂ (by rw [e10, e11]; addr_omega [hr1, hj, hlast])
        pos := by omega
        lt := by omega
        x10 := hx10
        x11 := (k₂ .x11 (by decide)).trans e11
        x12 := (k₂ .x12 (by decide)).trans ((hrw .x12 (by decide)).trans hu.x12)
        x16 := (congrArg BitVec.toNat (k₂ .x16 (by decide))).trans hx16 }⟩, ?_⟩
      rw [hx10, hu.x10]
      addr_omega [hr1, hj, hlast]
  have hfm := fm_succ (sizesAt s) (j := j) (by omega)
  by_cases hlt : (u.getMem (u.getReg .x10)).toNat < (u.getReg .x16).toNat
  · exact hstep u₁ (Reaches.refl _) (b800062c4_pc_taken h₁ hlt) hm₁
      (fun r hr' ↦ k₁ r (mem_of_mem hr' _)) (by
        rw [k₁ .x16 (by decide), hfm, ← hu.x16, ← hv]; omega)
  · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800062cc_spec
      (b800062c4_pc_not_taken h₁ (by omega)) (by rv_eval [])
    have k₂ := b800062cc_keeps h₂
    exact hstep u₂ hr₂ (b800062cc_pc h₂) (fun a ↦ (b800062cc_mem_same h₂ a).trans (hm₁ a))
      (fun r hr' ↦ (k₂ r (mem_of_mem hr' _)).trans (k₁ r (mem_of_mem hr' _))) (by
        rw [b800062cc_x16 h₂, b800062c4_x13 h₁, hfm, ← hu.x16, ← hv]; omega)

theorem foldl_max_lt (B : Nat) : ∀ (l : List Nat) (a : Nat), a < B → (∀ x ∈ l, x < B) →
    l.foldl max a < B
  | [], _, ha, _ => ha
  | x :: l, a, ha, hl => foldl_max_lt B l (max a x) (by have := hl x (by simp); omega)
      fun y hy ↦ hl y (by simp [hy])

theorem largest_lt (s : MachineState) : (sizesAt s).foldl max 0 < 2 ^ 64 :=
  foldl_max_lt _ _ 0 (by norm_num) fun x hx ↦ by
    simp only [sizesAt, List.mem_map] at hx
    obtain ⟨w, -, rfl⟩ := hx
    exact w.isLt

/-- `largest`. -/
abbrev LL (s : MachineState) : Nat := (sizesAt s).foldl max 0

/-- In the passes: the registers, the capacity in `a0`, the buffer `P` in `a1` holding `st.1`,
`8n` in `a2`, `st.2` in `a3`, `1` in `a4`. -/
structure PSt (s u : MachineState) (nx P : Word) (st : List (BitVec 64) × BitVec 64) : Prop
    extends Regs s u where
  inv : Inv s u nx
  x10 : u.getReg .x10 = s.getReg .x12
  x11 : u.getReg .x11 = P
  x12 : u.getReg .x12 = s.getReg .x12 * 8
  x13 : u.getReg .x13 = st.2
  x14 : u.getReg .x14 = 1
  buf : u.readWords P (s.getReg .x12).toNat = st.1

def pregs : List Reg := regs ++ [.x10, .x11, .x12, .x13, .x14]

theorem PSt.same {s u v : MachineState} {nx P : Word} {st : List (BitVec 64) × BitVec 64}
    (hpre : StackOffsetsPre s) (h : PSt s u nx P st) (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ pregs, v.getReg r = u.getReg r) : PSt s v nx P st :=
  { toRegs := h.toRegs.step fun r hr' ↦ hr r (by simp only [pregs, regs]; exact mem_of_mem hr' _)
    inv := h.inv.same hpre hm (l := pregs) hr (by decide)
    x10 := (hr _ (by decide)).trans h.x10
    x11 := (hr _ (by decide)).trans h.x11
    x12 := (hr _ (by decide)).trans h.x12
    x13 := (hr _ (by decide)).trans h.x13
    x14 := (hr _ (by decide)).trans h.x14
    buf := by
      have hz := h.buf
      rw [readWords_eq_map] at hz ⊢
      simp only [hm]
      exact hz }

/-- At `0x800062f4`, the passes for the sizes above `c` done. -/
structure OInv (s u : MachineState) (nx P : Word) (c : Nat) : Prop
    extends PSt s u nx P (upto s (LL s) (c + 1)) where
  pc : u.pc = 0x800062f4
  le : c ≤ LL s
  x16 : (u.getReg .x16).toNat = c

/-- At `0x80006328`, in the pass for `c`, before block `i`. -/
structure IInv (s u : MachineState) (nx P : Word) (c i : Nat) : Prop
    extends PSt s u nx P ((List.range i).foldl (Model.stackStep (sizesAt s) c) (upto s (LL s) (c + 1))) where
  pc : u.pc = 0x80006328
  le : c ≤ LL s
  lt : i < (s.getReg .x12).toNat
  x15 : u.getReg .x15 = BitVec.ofNat 64 c
  x16 : u.getReg .x16 = BitVec.ofNat 64 i
  x5 : u.getReg .x5 = BitVec.ofNat 64 (8 * ((s.getReg .x12).toNat - i))
  x6 : u.getReg .x6 = P + BitVec.ofNat 64 (8 * i)
  x7 : u.getReg .x7 = s.getReg .x11 + BitVec.ofNat 64 (8 * i)
  x17 : u.getReg .x17 = 1#64 <<< (c % 64)

/-- At `0x800062ec`, the pass for `c` done. -/
structure PDone (s u : MachineState) (nx P : Word) (c : Nat) : Prop
    extends PSt s u nx P (upto s (LL s) c) where
  pc : u.pc = 0x800062ec
  le : c ≤ LL s
  x15 : u.getReg .x15 = BitVec.ofNat 64 c

theorem stackPass_eq (s : MachineState) (st : List (BitVec 64) × BitVec 64) (c : Nat) :
    Model.stackPass (sizesAt s) st c =
      (List.range (s.getReg .x12).toNat).foldl (Model.stackStep (sizesAt s) c) st := by
  rw [Model.stackPass, sizesAt_length]

theorem inner_body {s : MachineState} (hpre : StackOffsetsPre s) {nx P : Word} (hP : BufOk s P nx)
    {c : Nat} (u : MachineState) (hinv : ∃ i, IInv s u nx P c i) :
    (∃ v, Reaches Image.code u v ∧ (PDone s v nx P c ∨ Dead Image.code v)) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ i, IInv s v nx P c i) ∧
        (v.getReg .x5).toNat < (u.getReg .x5).toNat) := by
  obtain ⟨i, hu⟩ := hinv
  have hi := hu.lt
  have hc := hu.le
  have hL : LL s < 2 ^ 64 := largest_lt s
  have hr := hpre.sizes.resolve_left (by omega)
  have hr1 := hr.1
  have hPa := hP.align
  have hPf := hP.fits
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 8 ≤ nx.toNat :=
    hP.range.resolve_left (by omega)
  have hlo := hpre.heap.lo
  have hN8 : P.toNat + 8 * (s.getReg .x12).toNat ≤ 0x78000000 := by
    have h1 := hPr.2
    have h2 := hPf
    simp only [heapEnd] at h2
    omega
  have hN : P.toNat + 8 * (s.getReg .x12).toNat ≤ 2 ^ 64 := by omega
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006328_spec hu.pc (by
    rv_eval [hu.x7]
    exact Transcript.Region.valid hr (by addr_omega [hr1, hi]) (by addr_omega [hr1, hi])
      (by addr_omega [hr1, hi, hr.2]))
  have k₁ := b80006328_keeps h₁
  have hm₁ := b80006328_mem_same h₁
  have hsz : u.getMem (u.getReg .x7) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 (8 * i)) := by
    rw [hu.x7, size_eq hpre hu.inv hi]
  have hgd := sizesAt_getD s hi
  have hcn : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- the step to `0x80006314`, `st` to `st'`
  have hstep (w : MachineState) (hw : Reaches Image.code u w) (hpcw : w.pc = 0x80006314)
      (st' : List (BitVec 64) × BitVec 64)
      (hst' : st' = Model.stackStep (sizesAt s) c
        ((List.range i).foldl (Model.stackStep (sizesAt s) c) (upto s (LL s) (c + 1))) i)
      (hps : PSt s w nx P st')
      (hrw : ∀ r ∈ [Reg.x5, .x6, .x7, .x15, .x16, .x17], w.getReg r = u.getReg r) :
      (∃ v, Reaches Image.code u v ∧ (PDone s v nx P c ∨ Dead Image.code v)) ∨
        (∃ v, Reaches Image.code u v ∧ (∃ i, IInv s v nx P c i) ∧
          (v.getReg .x5).toNat < (u.getReg .x5).toNat) := by
    obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006314_spec hpcw (by rv_eval [])
    have k₂ := b80006314_keeps h₂
    have ps := hps.same hpre (b80006314_mem_same h₂) fun r hr' ↦ k₂ r (mem_of_mem hr' _)
    have e5 : w.getReg .x5 = BitVec.ofNat 64 (8 * ((s.getReg .x12).toNat - i)) :=
      (hrw _ (by decide)).trans hu.x5
    have hfold : (List.range (i + 1)).foldl (Model.stackStep (sizesAt s) c)
        (upto s (LL s) (c + 1)) = st' := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hst']
    by_cases hlast : i + 1 = (s.getReg .x12).toNat
    · refine Or.inl ⟨v, hw.trans hr₂, Or.inl {
        toPSt := by
          rw [upto_pred s hc, stackPass_eq, ← hlast, hfold]
          exact ps
        pc := b80006314_pc_taken h₂ (by rw [e5]; addr_omega [hlast, hN8])
        le := hc
        x15 := (k₂ .x15 (by decide)).trans ((hrw _ (by decide)).trans hu.x15) }⟩
    · refine Or.inr ⟨v, hw.trans hr₂, ⟨i + 1, {
        toPSt := by rw [hfold]; exact ps
        pc := b80006314_pc_not_taken h₂ (by rw [e5]; addr_omega [hlast, hi, hN8])
        le := hc
        lt := by omega
        x15 := (k₂ .x15 (by decide)).trans ((hrw _ (by decide)).trans hu.x15)
        x16 := by
          rw [b80006314_x16 h₂, hrw _ (by decide), hu.x16]; addr_omega [hi, hN8]
        x5 := by rw [b80006314_x5 h₂, e5]; addr_omega [hi, hN8, hlast]
        x6 := by
          rw [b80006314_x6 h₂, hrw _ (by decide), hu.x6]; addr_omega [hi, hN8]
        x7 := by
          rw [b80006314_x7 h₂, hrw _ (by decide), hu.x7]; addr_omega [hi, hr1]
        x17 := (k₂ .x17 (by decide)).trans ((hrw _ (by decide)).trans hu.x17) }⟩, ?_⟩
      rw [b80006314_x5 h₂, e5, hu.x5]
      addr_omega [hi, hN8, hlast]
  by_cases heq : u.getMem (u.getReg .x7) = u.getReg .x15
  · have hgc : (sizesAt s).getD i 0 = c := by
      rw [hgd, ← hcn, ← hu.x15, ← heq, hsz]
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006330_spec
      (b80006328_pc_not_taken h₁ heq) (by rv_eval [])
    have k₂ := b80006330_keeps h₂
    have hx8 : (u₁.getReg .x8).toNat = (s.getReg .x12).toNat := by
      rw [k₁ .x8 (by decide), hu.x8]
    have hx16 : (u₁.getReg .x16).toNat = i := by
      rw [k₁ .x16 (by decide), hu.x16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx6 : u₂.getReg .x6 = P + BitVec.ofNat 64 (8 * i) := by
      rw [k₂ .x6 (by decide), k₁ .x6 (by decide), hu.x6]
    obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006334_spec
      (b80006330_pc_not_taken h₂ (by rw [hx16, hx8]; exact hi)) (by
        rv_eval [hx6]
        exact FromElem.heap_valid (by addr_omega [hPa, hPr, hlo, hi, hPf])
          (by addr_omega [hPr, hi, hPf]) (by addr_omega [hPa, hPr, hi, hPf]))
    have k₃ := b80006334_keeps h₃
    have hm₃ := b80006334_frame h₃ (by rw [hx6]; addr_omega [hPr, hi, hPf])
    rw [hx6] at hm₃
    have m₃ := b80006334_m_x6_0 h₃
    rw [hx6] at m₃
    have hmw (a : Word) (ha : a ≠ P + BitVec.ofNat 64 (8 * i)) : w.getMem a = u.getMem a := by
      rw [h₃.frame a (by rv_eval [hx6]; exact ha), b80006330_mem_same h₂, hm₁]
    have hfresh (a : Word) (ha : Within a (P + BitVec.ofNat 64 (8 * i)) 8) :
        heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat := by
      addr_omega [ha, hPr, hi, hPf]
    have bf : ByteFrame u w (Within · (P + BitVec.ofNat 64 (8 * i)) 8) :=
      ByteFrame.of_single (by addr_omega [hPa, hPr, hi, hPf]) hmw
    have hreg (r : Reg) (hr' : r ∈ ([.x2, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x14, .x15,
        .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg)) :
        w.getReg r = u.getReg r := by
      rw [k₃ r (mem_of_mem hr' _), k₂ r (mem_of_mem hr' _), k₁ r (mem_of_mem hr' _)]
    have hx13 : w.getReg .x13 = u.getReg .x13 + 1#64 <<< (c % 64) := by
      rw [b80006334_x13 h₃, k₂ .x13 (by decide), k₁ .x13 (by decide), k₂ .x17 (by decide),
        k₁ .x17 (by decide), hu.x17]
    have hm13 : w.getMem (P + BitVec.ofNat 64 (8 * i)) = u.getReg .x13 := by
      rw [m₃, k₂ .x13 (by decide), k₁ .x13 (by decide)]
    refine hstep w (hr₁.trans (hr₂.trans hr₃)) (b80006334_pc h₃) _ rfl {
      toRegs := hu.toRegs.step fun r hr' ↦ hreg r (mem_of_mem hr' _)
      inv := hu.inv.step hpre bf (fun a ha ↦ Or.inr (Or.inr (hfresh a ha)))
        ((hmw _ (by addr_omega [hPr, hi, hPf])).trans hu.inv.next) (Nat.le_refl _) hPf
        fun r hr' ↦ hreg r (mem_of_mem hr' _)
      x10 := (hreg .x10 (by decide)).trans hu.x10
      x11 := (hreg .x11 (by decide)).trans hu.x11
      x12 := (hreg .x12 (by decide)).trans hu.x12
      x13 := by
        simp only [Model.stackStep, hgc, ↓reduceIte]
        rw [hx13, hu.x13]
      x14 := (hreg .x14 (by decide)).trans hu.x14
      buf := by
        simp only [Model.stackStep, hgc, ↓reduceIte]
        rw [readWords_set hi hN hmw hm13, hu.buf, hu.x13] } fun r hr' ↦
      hreg r (mem_of_mem hr' _)
  · have hgc : (sizesAt s).getD i 0 ≠ c := fun h ↦ heq (by
      rw [hsz, hu.x15]
      apply BitVec.eq_of_toNat_eq
      rw [hcn, ← h, hgd])
    refine hstep u₁ hr₁ (b80006328_pc_taken h₁ heq) _ rfl ?_ fun r hr' ↦ k₁ r (mem_of_mem hr' _)
    simp only [Model.stackStep, hgc, ↓reduceIte]
    exact hu.toPSt.same hpre hm₁ fun r hr' ↦ k₁ r (mem_of_mem hr' _)

/-- At `0x80006340`, every pass done. -/
structure Last (s u : MachineState) (nx P : Word) : Prop extends PSt s u nx P (upto s (LL s) 0) where
  pc : u.pc = 0x80006340

theorem outer_head {s : MachineState} (hpre : StackOffsetsPre s) {nx P : Word} (hP : BufOk s P nx)
    {c : Nat} {u : MachineState} (hu : OInv s u nx P c) :
    ∃ v, Reaches Image.code u v ∧ (IInv s v nx P c 0 ∨ PDone s v nx P c) := by
  have hc := hu.le
  have hL : LL s < 2 ^ 64 := largest_lt s
  have hcn : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800062f4_spec hu.pc (by rv_eval [])
  have k₁ := b800062f4_keeps h₁
  have hm₁ := b800062f4_mem_same h₁
  have hx16 : u.getReg .x16 = BitVec.ofNat 64 c := BitVec.eq_of_toNat_eq (by rw [hu.x16, hcn])
  have hx15 : u₁.getReg .x15 = BitVec.ofNat 64 c := (b800062f4_x15 h₁).trans hx16
  have ps₁ := hu.toPSt.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  by_cases hn : s.getReg .x12 = 0
  · have hn' : (s.getReg .x12).toNat = 0 := by rw [hn]; rfl
    refine ⟨u₁, hr₁, Or.inr {
      toPSt := ?_
      pc := b800062f4_pc_taken h₁ (by rw [hu.x8]; exact hn)
      le := hc
      x15 := hx15 }⟩
    rw [upto_pred s hc, stackPass_eq, hn']
    exact ps₁
  · have hnz : (s.getReg .x12).toNat ≠ 0 := fun h ↦ hn (BitVec.eq_of_toNat_eq h)
    have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 8 ≤ nx.toNat :=
      hP.range.resolve_left hnz
    have hPf := hP.fits
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800062fc_spec
      (b800062f4_pc_not_taken h₁ (by rw [hu.x8]; exact hn)) (by rv_eval [])
    have k₂ := b800062fc_keeps h₂
    have hm₂ := b800062fc_mem_same h₂
    refine ⟨u₂, hr₁.trans hr₂, Or.inl {
      toPSt := ps₁.same hpre hm₂ fun r hr ↦ k₂ r (mem_of_mem hr _)
      pc := b800062fc_pc h₂
      le := hc
      lt := by omega
      x15 := (k₂ .x15 (by decide)).trans hx15
      x16 := (b800062fc_x16 h₂).trans rfl
      x5 := by
        rw [b800062fc_x5 h₂, k₁ .x12 (by decide), hu.x12]
        simp only [heapEnd] at hPf
        addr_omega [hPr, hPf]
      x6 := by rw [b800062fc_x6 h₂, k₁ .x11 (by decide), hu.x11]; simp
      x7 := by rw [b800062fc_x7 h₂, k₁ .x18 (by decide), hu.x18]; simp
      x17 := h₂.reg_eq .x17 rfl (by rv_eval [k₁ .x14 (by decide), hu.x14, hx15, hcn]) }⟩

theorem pass {s : MachineState} (hpre : StackOffsetsPre s) {nx P : Word} (hP : BufOk s P nx)
    {c : Nat} {u : MachineState} (hu : IInv s u nx P c 0) :
    ∃ v, Reaches Image.code u v ∧ (PDone s v nx P c ∨ Dead Image.code v) :=
  Reaches.loop (code := Image.code) (fun v ↦ ∃ i, IInv s v nx P c i) (fun v ↦ (v.getReg .x5).toNat)
    _ (inner_body hpre hP) u ⟨0, hu⟩

theorem pdone {s : MachineState} (hpre : StackOffsetsPre s) {nx P : Word} {c : Nat}
    {u : MachineState} (hu : PDone s u nx P c) :
    ∃ v, Reaches Image.code u v ∧ ((c ≠ 0 ∧ OInv s v nx P (c - 1)) ∨ Last s v nx P) := by
  have hc := hu.le
  have hL : LL s < 2 ^ 64 := largest_lt s
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b800062ec_spec hu.pc (by rv_eval [])
  have k := b800062ec_keeps h
  have ps := hu.toPSt.same hpre (b800062ec_mem_same h) fun r hr ↦ k r (mem_of_mem hr _)
  by_cases h0 : c = 0
  · subst h0
    exact ⟨v, hr, Or.inr { toPSt := ps, pc := b800062ec_pc_taken h (by rw [hu.x15]; rfl) }⟩
  · refine ⟨v, hr, Or.inl ⟨h0, {
      toPSt := by rw [Nat.sub_add_cancel (by omega)]; exact ps
      pc := b800062ec_pc_not_taken h (by rw [hu.x15]; addr_omega [hL, hc, h0])
      le := by omega
      x16 := by rw [b800062ec_x16 h, hu.x15]; addr_omega [hL, hc, h0] }⟩⟩

theorem finish {s : MachineState} (hpre : StackOffsetsPre s) {nx P : Word} (hP : BufOk s P nx)
    {u : MachineState} (hu : Last s u nx P) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ StackOffsetsPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hPa := hP.align
  have hPf := hP.fits
  obtain ⟨hsp, sl1, sl2, sl3, sl4⟩ := hu.inv.saved
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006340_spec hu.pc (by rv_eval [])
  have k₁ := b80006340_keeps h₁
  have hm₁ := b80006340_mem_same h₁
  have hy : u₁.getReg .x13 = Model.satSubOne (u.getReg .x13) :=
    h₁.reg_eq .x13 rfl (by rv_eval []; exact sat_eq _)
  have hp := h₁.pc
  rv_eval [] at hp
  -- to `0x800063f8` with `a4` = `popc(!smear(y))`
  have hto : ∃ w, Reaches Image.code u w ∧ w.pc = 0x800063f8 ∧ (∀ a, w.getMem a = u.getMem a) ∧
      (∀ r ∈ ([.x2, .x8, .x9, .x10, .x11, .x18] ++ kept : List Reg), w.getReg r = u.getReg r) ∧
      w.getReg .x12 = 64 ∧
      w.getReg .x14 = popc (smear (Model.satSubOne (u.getReg .x13)) ^^^ 0xffffffffffffffff) := by
    rcases pc_cases hp with ⟨hpc, hC⟩ | ⟨hpc, -⟩
    · have hy0 : Model.satSubOne (u.getReg .x13) = 0 := (sat_eq _).symm.trans (beq_iff_eq.mp hC)
      refine ⟨u₁, hr₁, hpc, hm₁, fun r hr ↦ k₁ r (mem_of_mem hr _), b80006340_x12 h₁, ?_⟩
      rw [b80006340_x14 h₁, hy0]
      decide
    · obtain ⟨w, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006354_spec hpc (by rv_eval [])
      have k₂ := b80006354_keeps h₂
      refine ⟨w, hr₁.trans hr₂, b80006354_pc h₂,
        fun a ↦ (b80006354_mem_same h₂ a).trans (hm₁ a),
        fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _)),
        (k₂ .x12 (by decide)).trans (b80006340_x12 h₁), ?_⟩
      rw [x14_eq h₂, hy]
  obtain ⟨w, hrw, hpcw, hmw, hkw, hx12, hx14⟩ := hto
  have hspw : w.getReg .x2 = s.getReg .x2 - 64 := (hkw .x2 (by decide)).trans hsp
  have hx9 : w.getReg .x9 = s.getReg .x10 := (hkw .x9 (by decide)).trans hu.x9
  have inv := hu.inv.same hpre hmw (l := [.x2, .x8, .x9, .x10, .x11, .x18] ++ kept) hkw (by decide)
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b800063f8_spec hpcw (by
    rv_eval [hspw, hx9]
    and_intros <;> first
      | addr_omega [hb, hos]
      | valid_access hpre.stack.valid [hb]
      | valid_access (outValid hpre) [hb])
  have k := b800063f8_keeps ht
  have pc := b800063f8_pc ht
  have x2 := b800063f8_x2 ht
  have x8 := b800063f8_x8 ht
  have x9 := b800063f8_x9 ht
  have x18 := b800063f8_x18 ht
  have m₀ := b800063f8_m_x9_0 ht
  have m₁ := b800063f8_m_x9_8 ht
  have m₂ := b800063f8_m_x9_16 ht
  have m₃ := b800063f8_m_x9_24 ht
  have hm := b800063f8_frame ht (by rw [hx9]; addr_omega [hb])
  rw [hx9] at m₀ m₁ m₂ m₃ hm
  have hx10 : w.getReg .x10 = s.getReg .x12 := (hkw .x10 (by decide)).trans hu.x10
  have hx11 : w.getReg .x11 = P := (hkw .x11 (by decide)).trans hu.x11
  have hx8 : w.getReg .x8 = s.getReg .x12 := (hkw .x8 (by decide)).trans hu.x8
  rw [hx10] at m₀
  rw [hx11] at m₁
  rw [hx8] at m₂
  rw [hx12, hx14] at m₃
  rv_eval [hspw, hmw, sl1, sl2, sl3, sl4] at pc x2 x8 x9 x18
  have bf := ByteFrame.of_memFrame hm (by addr_omega [hb]) (by decide)
    (ht.unaligned (by rv_eval [hx9]; and_intros <;> addr_omega [hb]))
  have hnt : t.getMem nextAddr = nx := (hm _ (by addr_omega [hof.2, hb])).trans inv.next
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hbf := inv.frame bf (fun a ha ↦ Or.inl ha) hnt
  have hlo := hpre.heap.lo
  have hPlo := hP.lo
  have hbuf : t.readWords P (s.getReg .x12).toNat = (upto s (LL s) 0).1 := by
    rw [← hu.buf, readWords_eq_map, readWords_eq_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [hm _ (by
      have hPr := hP.range.resolve_left (by omega)
      addr_omega [hi, hPr, hPf, hof.1, hb]), hmw]
  refine ⟨t, hrw.trans hr, Or.inl ⟨pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 ((k .x19 (by decide)).trans (inv.kept .x19 (by decide))) fun r hr' ↦ ?_,
    { heap := ⟨by omega, by omega⟩
      mono := by omega
      vec := ⟨?_, ?_⟩
      len := by simp only [vecLen, m₂]
      offsets := by
        simp only [vecWords, vecPtr, vecLen]
        rw [m₁, m₂, hbuf, upto_zero]
        rfl
      log := by
        rw [m₃, log_eq, hu.x13, upto_zero]
        simp only [Model.stackOffsetsRust, Model.log2CeilRust, Model.sub_clz_eq_bitLength]
      fresh := ?_
      frame := hbf.mono fun a ha ↦ ?_ }⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k _ (by decide)).trans (inv.kept _ (by decide))
  · simp only [RawVecOk, Buf, vecPtr, vecCap, m₀, m₁]
    refine ⟨hPa, ?_⟩
    rcases hP.range with h0 | h0
    · exact Or.inl (by rw [h0])
    · exact Or.inr ⟨by omega, by rw [hn]; omega⟩
  · simp only [vecLen, vecCap, m₀, m₂, le_refl]
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

theorem fm_one (l : List Nat) (h : l.length = 1) : l.foldl max 0 = l.getD 0 0 := by
  match l, h with
  | [a], _ => simp

theorem prologue (hT : TryAllocZeroedSpec) {s : MachineState} (hpc : s.pc = 0x80006258)
    (hpre : StackOffsetsPre s) :
    ∃ u, Reaches Image.code s u ∧
      ((∃ nx P, BufOk s P nx ∧ OInv s u nx P (LL s)) ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006258_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80006258_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack64 hpre)
    (by rw [b80006258_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b80006258_m_x2_n8 h₁, b80006258_m_x2_n16 h₁, b80006258_m_x2_n24 h₁,
        b80006258_m_x2_n32 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    ((b80006258_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 64 := b80006258_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 56 := b80006258_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = stackLo s stackOffsetsStack := by
    simp only [stackLo, tryAllocStack, stackOffsetsStack, hsp₁]
    rw [Sym.sub_sub_lit]; rfl
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b80006258_x13 h₁]; decide
    size := by rw [b80006258_x14 h₁]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; exact hab, by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, hzero⟩ | hdead⟩ := hT.call hr₁ (b80006258_pc h₁) hpre₁
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
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006294_spec
    (by rw [hpc₂, returnAddress_eq, b80006258_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 56)) 0 with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b80006294_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b80006294_keeps h₃
  have hm₃ := b80006294_mem_same h₃
  have inv₃ := inv₂.same hpre hm₃ k₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  have hz := hzero (by rw [b80006258_x12 h₁]; decide) (by rw [hx10₁]; exact htag)
  rw [hx10₁, b80006258_x11 h₁] at hcap hbuf hz
  rw [b80006258_x14 h₁, b80006258_x13 h₁] at hbuf
  rw [b80006258_x14 h₁] at hz
  rv_eval [] at hcap hbuf hz
  obtain ⟨P, hP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 40) := ⟨_, rfl⟩
  rw [← hP] at hbuf hz
  simp only [NewBuf, hn₁] at hbuf
  have hBuf : BufOk s P (t₂.getMem nextAddr) := {
    align := hbuf.1
    range := by
      rcases hbuf.2 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    fits := hpost₂.heap.hi
    lo := by have := hpost₂.mono; rw [hn₁] at this; exact this }
  have hPb : P.toNat + 8 * (s.getReg .x12).toNat ≤ 2 ^ 64 := by
    rcases hBuf.range with h | h
    · rw [h]; have := P.isLt; omega
    · have := hBuf.fits; simp only [heapEnd] at this; omega
  have hz3 : t₃.readWords P (s.getReg .x12).toNat = List.replicate (s.getReg .x12).toNat 0 := by
    rw [readWords_eq_map]
    simp only [hm₃]
    rw [← readWords_eq_map]
    exact words_zero hBuf.align hPb hz
  have hreg₃ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18]) : t₃.getReg r = t₁.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have mid₃ : Mid s t₃ (t₂.getMem nextAddr) P := {
    x8 := by rw [hreg₃ .x8 (by decide), b80006258_x8 h₁]
    x9 := by rw [hreg₃ .x9 (by decide), b80006258_x9 h₁]
    x18 := by rw [hreg₃ .x18 (by decide), b80006258_x18 h₁]
    inv := inv₃
    cap := (hm₃ _).trans hcap
    ptr := (hm₃ _).trans hP.symm
    zero := hz3 }
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000629c_spec
    (b80006294_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)) (by rv_eval [])
  have k₄ := b8000629c_keeps h₄
  have mid₄ := mid₃.same hpre (b8000629c_mem_same h₄) fun r hr ↦ k₄ r (mem_of_mem hr _)
  have hx12₄ : t₄.getReg .x12 = s.getReg .x12 * 8 := by rw [b8000629c_x12 h₄, mid₃.x8]
  have hreach₄ := hr₂.trans (hr₃.trans hr₄)
  -- from `0x800062d8`
  have fin (u : MachineState) (hu : Reaches Image.code s u) (hd : MDone s u (t₂.getMem nextAddr) P) :
      ∃ v, Reaches Image.code s v ∧
        ((∃ nx P, BufOk s P nx ∧ OInv s v nx P (LL s)) ∨ Dead Image.code v) := by
    have hspu : u.getReg .x2 = s.getReg .x2 - 64 := hd.inv.saved.1
    obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b800062d8_spec hd.pc (by
      rv_eval [hspu]; and_intros <;> valid_access hst.valid [hb])
    have k := b800062d8_keeps h
    have hm := b800062d8_mem_same h
    refine ⟨v, hu.trans hr, Or.inl ⟨_, P, hBuf, {
      toRegs := hd.toRegs.step fun r hr' ↦ k r (mem_of_mem hr' _)
      inv := hd.inv.same hpre hm k
      x10 := by rw [b800062d8_x10 h, hspu]; rv_eval [hd.cap]
      x11 := by rw [b800062d8_x11 h, hspu]; rv_eval [hd.ptr]
      x12 := (k .x12 (by decide)).trans hd.x12
      x13 := by rw [b800062d8_x13 h, upto_top]; rfl
      x14 := b800062d8_x14 h
      buf := by
        rw [upto_top]
        have hz' := hd.zero
        rw [readWords_eq_map] at hz' ⊢
        simp only [hm]
        rw [hz', sizesAt_length]
        rfl
      pc := b800062d8_pc h
      le := le_refl _
      x16 := (congrArg BitVec.toNat (k .x16 (by decide))).trans hd.x16 }⟩⟩
  by_cases hn0 : s.getReg .x12 = 0
  · obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800062d4_spec
      (b8000629c_pc_taken h₄ (by rw [mid₃.x8]; exact hn0)) (by rv_eval [])
    have k₅ := b800062d4_keeps h₅
    have hn' : (s.getReg .x12).toNat = 0 := by rw [hn0]; rfl
    have hsz : sizesAt s = [] := List.eq_nil_of_length_eq_zero (by rw [sizesAt_length]; exact hn')
    exact fin t₅ (hreach₄.trans hr₅) {
      toMid := mid₄.same hpre (b800062d4_mem_same h₅) fun r hr ↦ k₅ r (mem_of_mem hr _)
      pc := b800062d4_pc h₅
      x12 := (k₅ .x12 (by decide)).trans hx12₄
      x16 := by rw [b800062d4_x16 h₅, hsz]; rfl }
  have hnz : (s.getReg .x12).toNat ≠ 0 := fun h ↦ hn0 (BitVec.eq_of_toNat_eq h)
  have hr := hpre.sizes.resolve_left hnz
  have hr1 := hr.1
  have hx18₄ : t₄.getReg .x18 = s.getReg .x11 := mid₄.x18
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800062a4_spec
    (b8000629c_pc_not_taken h₄ (by rw [mid₃.x8]; exact hn0)) (by
      rv_eval [hx18₄]
      exact Transcript.Region.valid hr (by addr_omega [hr1]) (by addr_omega [hr1, hnz]) hr.2)
  have k₅ := b800062a4_keeps h₅
  have hm₅ := b800062a4_mem_same h₅
  have mid₅ := mid₄.same hpre hm₅ fun r hr ↦ k₅ r (mem_of_mem hr _)
  have hv0 : (t₅.getReg .x16).toNat = (sizesAt s).getD 0 0 := by
    rw [b800062a4_x16 h₅, hx18₄, sizesAt_getD s (by omega)]
    have := size_eq hpre mid₄.inv (i := 0) (by omega)
    simp only [Nat.mul_zero, BitVec.add_zero] at this ⊢
    rw [this]
  have hx12₅ : t₅.getReg .x12 = s.getReg .x12 * 8 := (k₅ .x12 (by decide)).trans hx12₄
  by_cases hn1 : s.getReg .x12 = 1
  · have hn1' : (s.getReg .x12).toNat = 1 := by rw [hn1]; rfl
    exact fin t₅ (hreach₄.trans hr₅) {
      toMid := mid₅
      pc := b800062a4_pc_taken h₅ (by rw [mid₄.x8]; exact hn1)
      x12 := hx12₅
      x16 := by rw [hv0, fm_one _ (by rw [sizesAt_length]; exact hn1')] }
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800062b0_spec
    (b800062a4_pc_not_taken h₅ (by rw [mid₄.x8]; exact hn1)) (by rv_eval [])
  have k₆ := b800062b0_keeps h₆
  have hm₆ := b800062b0_mem_same h₆
  have hn1' : (s.getReg .x12).toNat ≠ 1 := fun h ↦ hn1 (BitVec.eq_of_toNat_eq h)
  obtain ⟨t, hr', ht⟩ := Reaches.loop (code := Image.code)
    (fun u ↦ ∃ j, MInv s u (t₂.getMem nextAddr) P j)
    (fun u ↦ (s.getReg .x11 + BitVec.ofNat 64 (8 * (s.getReg .x12).toNat)).toNat -
      (u.getReg .x10).toNat)
    (fun u ↦ MDone s u (t₂.getMem nextAddr) P) (max_body hpre) t₆ ⟨1, {
      toMid := mid₅.same hpre hm₆ fun r hr ↦ k₆ r (mem_of_mem hr _)
      pc := b800062b0_pc h₆
      pos := le_refl _
      lt := by omega
      x10 := by rw [b800062b0_x10 h₆, k₅ .x18 (by decide), hx18₄]; rfl
      x11 := by
        rw [b800062b0_x11 h₆, k₅ .x18 (by decide), hx18₄, hx12₅]; addr_omega [hr1]
      x12 := (k₆ .x12 (by decide)).trans hx12₅
      x16 := by
        rw [k₆ .x16 (by decide), hv0]
        have := fm_succ (sizesAt s) (j := 0) (by rw [sizesAt_length]; omega)
        simp only [List.take_zero, List.foldl_nil, Nat.zero_max, Nat.zero_add] at this
        exact this.symm }⟩
  exact fin t (hreach₄.trans (hr₅.trans (hr₆.trans hr'))) ht

/-- **`stack_offsets` meets its contract**, given `try_allocate_in`'s. -/
theorem stack_offsets_spec (hT : TryAllocZeroedSpec) : StackOffsetsSpec := by
  intro s hpc hpre
  obtain ⟨u, hr, ⟨nx, P, hP, hu⟩ | hd⟩ := prologue hT hpc hpre
  · have step (v : MachineState) (c : Nat) (hv : OInv s v nx P c) (w : MachineState)
        (hw : Reaches Image.code v w) (hpd : PDone s w nx P c) :
        (∃ t, Reaches Image.code v t ∧ (Last s t nx P ∨ Dead Image.code t)) ∨
          (∃ t, Reaches Image.code v t ∧ (∃ c, OInv s t nx P c) ∧
            (t.getReg .x16).toNat < (v.getReg .x16).toNat) := by
      obtain ⟨y, hy, ⟨hc0, hy'⟩ | hy'⟩ := pdone hpre hpd
      · refine Or.inr ⟨y, hw.trans hy, ⟨c - 1, hy'⟩, ?_⟩
        rw [hy'.x16, hv.x16]
        omega
      · exact Or.inl ⟨y, hw.trans hy, Or.inl hy'⟩
    obtain ⟨v, hr', hv⟩ := Reaches.loop (code := Image.code) (fun v ↦ ∃ c, OInv s v nx P c)
      (fun v ↦ (v.getReg .x16).toNat) (fun v ↦ Last s v nx P ∨ Dead Image.code v)
      (fun v ⟨c, hv⟩ ↦ by
        obtain ⟨w, hw, hw' | hw'⟩ := outer_head hpre hP hv
        · obtain ⟨x, hx, hx' | hd⟩ := pass hpre hP hw'
          · exact step v c hv x (hw.trans hx) hx'
          · exact Or.inl ⟨x, hw.trans hx, Or.inr hd⟩
        · exact step v c hv w hw hw') u ⟨_, hu⟩
    rcases hv with hl | hd
    · obtain ⟨t, ht, hres⟩ := finish hpre hP hl
      exact ⟨t, hr.trans (hr'.trans ht), hres⟩
    · exact ⟨v, hr.trans hr', Or.inr hd⟩
  · exact ⟨u, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Multilinear.StackOffsets
