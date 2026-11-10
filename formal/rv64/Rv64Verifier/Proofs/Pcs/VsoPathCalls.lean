import Rv64Verifier.Proofs.Pcs.VsoClimb
import Rv64Verifier.Proofs.Pcs.VsoPathBytes

/-!
# `verify_stacked_opening`'s Merkle checks: what a path writes, and its callees

`PW` is what the path loop writes: the climb's buffers and the callees' stacks (`CW`), the leaf
index's slot `S - 784`, `NEXT` and the heap allocated. `Safe` is what it never writes. The callees
of a path's leaf: `try_allocate_in` of a byte buffer at `S - 384`, `memcpy` and `keccak_hash` into
the node at `S - 160`, from any source the stack misses.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38

/-- What the path loop writes, the heap allocated from `lo` to `hi`. -/
def PW (s : MachineState) (lo hi : ℕ) (a : Word) : Prop :=
  CW s a ∨ Within a (s.getReg .x2 - 784) 8 ∨ Within a nextAddr 8 ∨ (lo ≤ a.toNat ∧ a.toNat < hi)

theorem PW.mono {s : MachineState} {lo lo' hi hi' : ℕ} (h1 : lo' ≤ lo) (h2 : hi ≤ hi') {a : Word}
    (h : PW s lo hi a) : PW s lo' hi' a := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))

theorem PW.of_cw {s : MachineState} {lo hi : ℕ} {a : Word} (h : CW s a) : PW s lo hi a := Or.inl h

theorem PW.of_stack {s : MachineState} {lo hi : ℕ} {a : Word}
    (h : Within a (s.getReg .x2 - 2464) 1424) : PW s lo hi a := Or.inl (Or.inl h)

theorem PW.of_next {s : MachineState} {lo hi : ℕ} {a : Word} (h : Within a nextAddr 8) :
    PW s lo hi a := Or.inr (Or.inr (Or.inl h))

theorem PW.of_heap {s : MachineState} {lo hi : ℕ} {a : Word} (h1 : lo ≤ a.toNat)
    (h2 : a.toNat < hi) : PW s lo hi a := Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))

/-- `n` bytes from `a` that the path loop does not write: below the heap's `lo` or above the heap,
off the stack and `NEXT`. -/
def Safe (s : MachineState) (lo : ℕ) (a : Word) (n : ℕ) : Prop :=
  (a.toNat + n ≤ lo ∨ heapEnd ≤ a.toNat) ∧ Apart a n (s.getReg .x2 - 2464) 2464 ∧
    Apart a n nextAddr 8

theorem Safe.misses {s : MachineState} {lo hi : ℕ} {a : Word} {n : ℕ} (hpre : VsoPre s)
    (h : Safe s lo a n) (hhi : hi ≤ heapEnd) : ∀ y, Within y a n → ¬ PW s lo hi y := by
  have hm := stack_mapped hpre
  obtain ⟨h1, h2, h3⟩ := h
  intro y hy hw
  rcases hw with (hw | hw | hw | hw) | hw | hw | ⟨hw1, hw2⟩
  · addr_omega [hy, hw, h2, hm]
  · addr_omega [hy, hw, h2, hm]
  · addr_omega [hy, hw, h2, hm]
  · addr_omega [hy, hw, h2, hm]
  · addr_omega [hy, hw, h2, hm]
  · addr_omega [hy, hw, h3]
  · rcases h1 with h1 | h1
    · addr_omega [hy, hw1, h1]
    · addr_omega [hy, hw2, h1, hhi]

theorem Safe.mono {s : MachineState} {lo lo' : ℕ} {a : Word} {n : ℕ} (h : Safe s lo a n)
    (hl : lo ≤ lo') : Safe s lo' a n := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by omega, h2, h3⟩

/-- The path loop writes no `.rodata`. -/
theorem PW.rodata {s : MachineState} {lo hi : ℕ} (hpre : VsoPre s) (hhi : hi ≤ heapEnd) :
    ∀ a, Within a rodataBase Rv64Verifier.rodataSize → ¬ PW s lo hi a := by
  have hm := stack_mapped hpre
  have hro := hpre.stack.rodata
  rw [stackLo_vso, vso_stack] at hro
  intro a ha hw
  rcases hw with (hw | hw | hw | hw) | hw | hw | ⟨hw1, hw2⟩
  · addr_omega [ha, hw, hro, hm]
  · addr_omega [ha, hw, hro, hm]
  · addr_omega [ha, hw, hro, hm]
  · addr_omega [ha, hw, hro, hm]
  · addr_omega [ha, hw, hro, hm]
  · addr_omega [ha, hw]
  · addr_omega [ha, hw2, hhi]

/-- `8 k` aligned bytes that a frame misses are kept. -/
theorem DFrame.bytesK {u v : MachineState} {X : Word → Prop} (hX : DFrame u v X) {a : Word}
    (ha : a.toNat % 8 = 0) (k : ℕ) (hk : a.toNat + 8 * k < 2 ^ 64)
    (hm : ∀ y, Within y a (8 * k) → ¬ X y) :
    Contracts.bytesAt v a (8 * k) = Contracts.bytesAt u a (8 * k) := by
  rw [bytesAt_dwordsV v ha k hk, bytesAt_dwordsV u ha k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact hX _ fun j hj hx ↦ hm _ (by addr_omega [hj, hi, hk, ha]) hx

/-! ## The callees -/

/-- `try_allocate_in(S - 384, a1, _, 1, 1)`: a byte buffer of `a1` bytes. -/
theorem callTryAlloc (hT : TryAllocZeroedSpec) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x800049ac) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 384) (hx13 : t.getReg .x13 = 1)
    (hx14 : t.getReg .x14 = 1) (hheap : HeapOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      (v.getMem (s.getReg .x2 - 384) = 0 → v.getMem (s.getReg .x2 - 376) = t.getReg .x11 ∧
        NewBuf t v (v.getMem (s.getReg .x2 - 368)) (t.getReg .x11).toNat 1) ∧
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
      show (1 : Word).toNat = 1 from rfl, Nat.mul_one] at h2
    exact ⟨h1, h2⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- `memcpy` between two ranges the stack misses. -/
theorem callMemcpyG (hM : Runtime.MemcpySpec 0x800126e4) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x800126e4) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hdst : Mapped (t.getReg .x10) (t.getReg .x12).toNat)
    (hsrc : Mapped (t.getReg .x11) (t.getReg .x12).toNat)
    (hap : Apart (t.getReg .x10) (t.getReg .x12).toNat (t.getReg .x11) (t.getReg .x12).toNat)
    (hds : Apart (t.getReg .x10) (t.getReg .x12).toNat (s.getReg .x2 - 2464) 2464)
    (hss : Apart (t.getReg .x11) (t.getReg .x12).toNat (s.getReg .x2 - 2464) 2464) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      Contracts.bytesAt v (t.getReg .x10) (t.getReg .x12).toNat =
        Contracts.bytesAt t (t.getReg .x11) (t.getReg .x12).toNat ∧
      DFrame t v fun a ↦ Within a (t.getReg .x10) (t.getReg .x12).toNat ∨
        Within a (s.getReg .x2 - 1056) 16)) := by
  have hm := stack_mapped hpre
  have hsl : stackLo t memcpyStack = s.getReg .x2 - 1056 := by
    simp only [stackLo, memcpyStack, hsp]; rv_eval []
  have hpreM : Runtime.MemcpyPre t := {
    dst := hdst
    src := hsrc
    apart := hap
    stack := (hpre.stack.sub 1040 hsp (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [hsl]; addr_omega [hds, hm]
    srcStack := by rw [hsl]; addr_omega [hss, hm] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hM.call (Reaches.refl t) hpc hpreM
  · have hf := DFrame.of_byteFrame hpost.frame
    rw [hsl] at hf
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.bytes, hf⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- `keccak_hash` into the node at `S - 160`, of data the stack misses. -/
theorem callKeccakG (hK : KeccakHashSpec) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x8000c8e0) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 160)
    (hdata : Mapped (t.getReg .x11) (t.getReg .x12).toNat)
    (hda : Apart (t.getReg .x11) (t.getReg .x12).toNat (s.getReg .x2 - 2464) 2464)
    (hrod : RodataOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      Contracts.bytesAt v (s.getReg .x2 - 160) 32 =
        Model.keccakHashRust (Contracts.bytesAt t (t.getReg .x11) (t.getReg .x12).toNat) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 160) 32 ∨ Within a (s.getReg .x2 - 2144) 1104)) := by
  have hm := stack_mapped hpre
  have hro := hpre.stack.rodata
  rw [stackLo_vso, vso_stack] at hro
  have hsl : stackLo t keccakHashStack = s.getReg .x2 - 2144 := by
    simp only [stackLo, keccakHashStack, keccakFStack, memStack, hsp, Nat.reduceAdd]; rv_eval []
  have hpreK : KeccakHashPre t := {
    out := by rw [hx10]; exact bytesValid_ram (by addr_omega [hm]) (by addr_omega [hm])
    outAligned := by rw [hx10]; addr_omega [hm]
    data := hdata
    stack := (hpre.stack.sub 1040 hsp (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    outStack := by rw [hx10, hsl]; addr_omega [hm]
    dataStack := by rw [hsl]; addr_omega [hda, hm]
    tables := keccakTables_of_rodata hrod
    tablesStack := by rw [hsl]; addr_omega [hro, hm] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hK.call (Reaches.refl t) hpc hpreK
  · have hb := hpost.value
    have hf := DFrame.of_two hpost.frame
    rw [hx10] at hb
    rw [hx10, hsl] at hf
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hb, hf⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

end Rv64Verifier.Proofs.Pcs.Vso
