import Rv64Verifier.Proofs.Bus.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Blocks.F85

/-!
# `verify_bus_balance::{closure#2}`, the `fingerprints` closure

```rust
let fingerprints = |pc: E, memory_count: E, bytecode_count: E| {
    vec![
        dot(&weights[..3], &[SEP_STATE, pc, gpow(0)]),
        dot(&weights[..6], &[SEP_MEM, memory_index, memory_count, memory[0], memory[1], memory[2]]),
        dot(&weights[..3], &[SEP_BYTECODE, bytecode_index, bytecode_count]) + bytecode_value,
    ]
};
```

compiled at `0x8001174c` (`Blocks/F85.lean`), with `S` the entry's `sp`: `0x8001174c` saves `ra`,
`s0`..`s6` in a 432-byte frame and allocates the 72-byte buffer (`s1`); `0x80011798`,
`0x80011800`, `0x80011808`..`0x8001181c` trap unless `weights` has six elements and `memory`
three; `0x800117ac`, `0x80011824`, `0x800118cc` lay out the three right-hand arrays at `S - 400`,
`S - 304`, `S - 136` and call `dot` into `S - 424`, `S - 328`, `S - 160`; `0x80011930` writes the
buffer (the last sum by XOR), the `Vec` (capacity and length `3`), restores and returns.

After the prologue, everything but `alloc` writes the stack below the saved registers
(`Fr`), so what the closure reads keeps its value until the end.
-/

namespace Rv64Verifier.Proofs.Bus.Fingerprints
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords Rv64Verifier.Bus
  Rv64Verifier.Blocks.F85 Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `u` agrees with `t` but on the stack below the saved registers and `NEXT`. -/
def Fr (S : Word) (t u : MachineState) : Prop :=
  ∀ a, ¬ Within a (S - 1552) 1488 → a ≠ nextAddr → u.getMem a = t.getMem a

theorem Fr.refl (S : Word) (t : MachineState) : Fr S t t := fun _ _ _ ↦ rfl

theorem Fr.step {S : Word} {t u v : MachineState} (h : Fr S t u)
    (h' : ∀ a, ¬ Within a (S - 1552) 1488 → a ≠ nextAddr → v.getMem a = u.getMem a) :
    Fr S t v :=
  fun a h1 h2 ↦ (h' a h1 h2).trans (h a h1 h2)

theorem bounds {s : MachineState} (h : FingerprintsPre s) :
    0x78000000 + 1552 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s fingerprintsStack).toNat = (s.getReg .x2).toNat - 1552 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  simp only [fingerprintsStack, dotStack, mulStack, heapEnd] at this ha ⊢
  rw [this.2.2.2] at ha
  omega

theorem trap {t : MachineState} (h : t.pc = 0x800119c8) : Dead Image.code t :=
  dead_of_fetch (by rw [h]; exact Option.isNone_iff_eq_none.mp (by decide +kernel))

theorem Fr.mem {S : Word} {t u v : MachineState} (h : Fr S t u) {lo : Word} {n : Nat}
    (hf : MemFrame u v lo n) (hsub : ∀ a, ¬ Within a (S - 1552) 1488 → ¬ Within a lo n) :
    Fr S t v :=
  h.step fun a h1 _ ↦ hf a (hsub a h1)

theorem Fr.same {S : Word} {t u v : MachineState} (h : Fr S t u)
    (hf : ∀ a, v.getMem a = u.getMem a) : Fr S t v :=
  h.step fun a _ _ ↦ hf a

/-- `u` agrees with `t` but below the frame (`S - 432`) and in `n` bytes from `lo`. -/
def Keep (S lo : Word) (n : Nat) (t u : MachineState) : Prop :=
  ∀ a, ¬ Within a (S - 1552) 1120 → ¬ Within a lo n → u.getMem a = t.getMem a

theorem Keep.refl (S lo : Word) (n : Nat) (t : MachineState) : Keep S lo n t t := fun _ _ _ ↦ rfl

theorem Keep.step {S lo : Word} {n : Nat} {t u v : MachineState} (h : Keep S lo n t u)
    (h' : ∀ a, ¬ Within a (S - 1552) 1120 → ¬ Within a lo n → v.getMem a = u.getMem a) :
    Keep S lo n t v :=
  fun a h1 h2 ↦ (h' a h1 h2).trans (h a h1 h2)

theorem Keep.eAt {S lo : Word} {n : Nat} {t u : MachineState} (h : Keep S lo n t u) {p : Word}
    (h1 : ∀ k < 24, ¬ Within (p + BitVec.ofNat 64 k) (S - 1552) 1120)
    (h2 : ∀ k < 24, ¬ Within (p + BitVec.ofNat 64 k) lo n) : eAt u p = eAt t p := by
  unfold Rv64Verifier.eAt
  have e0 := h p (by simpa using h1 0 (by decide)) (by simpa using h2 0 (by decide))
  rw [e0, h (p + 8) (h1 8 (by decide)) (h2 8 (by decide)),
    h (p + 16) (h1 16 (by decide)) (h2 16 (by decide))]

/-- The three dot products. -/
def dot₁ (s : MachineState) : E :=
  dotRust ((vecEs s (capWeights s)).take 3) [sepStateRust, eAt s (s.getReg .x12), gpowRust 0#64]

def dot₂ (s : MachineState) : E :=
  dotRust ((vecEs s (capWeights s)).take 6) [sepMemRust, eAt s (capMemoryIndex s),
    eAt s (s.getReg .x13), (vecEs s (capMemory s)).getD 0 0, (vecEs s (capMemory s)).getD 1 0,
    (vecEs s (capMemory s)).getD 2 0]

def dot₃ (s : MachineState) : E :=
  dotRust ((vecEs s (capWeights s)).take 3) [sepBytecodeRust, eAt s (capBytecodeIndex s),
    eAt s (s.getReg .x14)]

/-- After the allocation: the frame, the registers the closure keeps, the saved registers, what it
reads unchanged, and the buffer `P`. -/
structure Mid (s u : MachineState) (P : Word) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 432
  x8 : u.getReg .x8 = s.getReg .x10
  x18 : u.getReg .x18 = s.getReg .x11
  x21 : u.getReg .x21 = s.getReg .x13
  kept : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27], u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : u.getMem (s.getReg .x2 - 64) = s.getReg .x22
  mem : ∀ a, ¬ Within a (s.getReg .x2 - 1552) 1552 → a ≠ nextAddr → u.getMem a = s.getMem a
  next : u.getMem nextAddr = P + 72
  align : P.toNat % 8 = 0
  above : heapNext s ≤ P.toNat
  fits : P.toNat + 72 ≤ heapEnd

def midRegs : List Reg := [.x2, .x8, .x18, .x21, .x23, .x24, .x25, .x26, .x27]

/-- A step that writes the stack below the saved registers only. -/
theorem Mid.step {s u v : MachineState} {P : Word} (hpre : FingerprintsPre s) (h : Mid s u P)
    (hf : ∀ a, ¬ Within a (s.getReg .x2 - 1552) 1488 → v.getMem a = u.getMem a)
    (hr : ∀ r ∈ midRegs, v.getReg r = u.getReg r) : Mid s v P := by
  obtain ⟨hb1, -, -, hlo⟩ := bounds hpre
  have hnx8 := hpre.stack.next
  have slot (k : Nat) (h1 : 8 ≤ k) (h2 : k ≤ 64) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    hf _ (by addr_omega [hb1, h1, h2])
  exact {
    sp := (hr .x2 (by decide)).trans h.sp
    x8 := (hr .x8 (by decide)).trans h.x8
    x18 := (hr .x18 (by decide)).trans h.x18
    x21 := (hr .x21 (by decide)).trans h.x21
    kept := fun r hr' ↦ (hr r (mem_of_mem hr' _)).trans (h.kept r hr')
    ra := (slot 8 (by decide) (by decide)).trans h.ra
    s0 := (slot 16 (by decide) (by decide)).trans h.s0
    s1 := (slot 24 (by decide) (by decide)).trans h.s1
    s2 := (slot 32 (by decide) (by decide)).trans h.s2
    s3 := (slot 40 (by decide) (by decide)).trans h.s3
    s4 := (slot 48 (by decide) (by decide)).trans h.s4
    s5 := (slot 56 (by decide) (by decide)).trans h.s5
    s6 := (slot 64 (by decide) (by decide)).trans h.s6
    mem := fun a h1 h2 ↦ (hf a (by addr_omega [h1, hb1])).trans (h.mem a h1 h2)
    next := (hf _ (by addr_omega [hnx8, hlo, hb1])).trans h.next
    align := h.align
    above := h.above
    fits := h.fits }

theorem Mid.same {s u v : MachineState} {P : Word} (hpre : FingerprintsPre s) (h : Mid s u P)
    (hf : ∀ a, v.getMem a = u.getMem a) (hr : ∀ r ∈ midRegs, v.getReg r = u.getReg r) :
    Mid s v P :=
  h.step hpre (fun a _ ↦ hf a) hr

theorem Mid.eAt_eq {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (h : Mid s u P)
    {p : Word} (hp : p.toNat + 24 ≤ 0xc0000008) (h1 : Apart p 24 (s.getReg .x2 - 1552) 1552)
    (h2 : Apart p 24 nextAddr 8) : eAt u p = eAt s p := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  unfold Rv64Verifier.eAt
  rw [h.mem p (by addr_omega [h1, hp, hb1]) (by addr_omega [h2, hp]),
    h.mem (p + 8) (by addr_omega [h1, hp, hb1]) (by addr_omega [h2, hp]),
    h.mem (p + 16) (by addr_omega [h1, hp, hb1]) (by addr_omega [h2, hp])]

theorem Mid.rodata {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (h : Mid s u P) :
    RodataOk u := by
  obtain ⟨hb1, -, -, hlo⟩ := bounds hpre
  have hro := hpre.stack.rodata
  intro p hp
  have hw := within_of_mem_rodataWords hp
  rw [h.mem p.1 (by addr_omega [hw, hro, hlo, hb1]) (by addr_omega [hw])]
  exact hpre.rodata p hp

/-- A held word, unchanged. -/
theorem Mid.held {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (h : Mid s u P)
    {a : Word} {m : Nat} (hh : Held s fingerprintsStack a m) (hm : 8 ≤ m) (h8 : m % 8 = 0)
    {k : Nat} (hk : k + 8 ≤ m) :
    u.getMem (a + BitVec.ofNat 64 k) = s.getMem (a + BitVec.ofNat 64 k) := by
  obtain ⟨hb1, -, -, hlo⟩ := bounds hpre
  have f := hh.facts hm h8
  exact h.mem _ (by addr_omega [f, hk, hb1, hlo]) (by addr_omega [f, hk])

theorem Mid.heldE {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (h : Mid s u P)
    {a : Word} (hh : Held s fingerprintsStack a 24) : eAt u a = eAt s a := by
  obtain ⟨hb1, -, -, hlo⟩ := bounds hpre
  have f := hh.facts (by decide) (by decide)
  exact h.eAt_eq hpre (by addr_omega [f]) (by addr_omega [f, hb1, hlo]) (by addr_omega [f])

theorem Mid.take {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (h : Mid s u P)
    {a : Word} (hh : EVecHeld s fingerprintsStack a) {k : Nat} (hk : k ≤ (vecLen s a).toNat)
    (hk1 : 1 ≤ k) : eListAt u (vecPtr s a) k = (vecEs s a).take k := by
  obtain ⟨hb1, -, -, hlo⟩ := bounds hpre
  have f := hh.elems.facts (by omega) (by omega)
  rw [vecEs, eListAt_take s _ hk]
  exact eListAt_congr fun i hi ↦ h.eAt_eq hpre (by addr_omega [f, hi, hk])
    (by addr_omega [f, hi, hk, hb1, hlo]) (by addr_omega [f, hi, hk])

/-! ## The prologue and the allocation -/

theorem stageA (hA : AllocSpec) {s : MachineState} (hpc : s.pc = 0x8001174c)
    (hpre : FingerprintsPre s) :
    ∃ t, Reaches Image.code s t ∧ ((∃ P, Mid s t P ∧ t.pc = 0x80011798 ∧ t.getReg .x10 = P ∧
      t.getReg .x19 = s.getReg .x14 ∧ t.getReg .x20 = s.getReg .x12) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have hnx8 := hst.next
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8001174c_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb1, hlo])
  have hm₁ := b8001174c_frame h₁ (by addr_omega [hb1])
  have k₁ := b8001174c_keeps h₁
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx8, hlo, hb1])]
  have hpre₁ : AllocPre t₁ :=
    ⟨⟨hn₁ ▸ hpre.heap.lo, hn₁ ▸ hpre.heap.hi⟩, by rw [b8001174c_x10 h₁]; decide⟩
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hA.call hr₁ (b8001174c_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  obtain ⟨P, hP⟩ : ∃ P, t₂.getReg .x10 = P := ⟨_, rfl⟩
  have hP8 := hpost₂.aligned
  have hPa := hpost₂.above
  have hPn := hpost₂.next
  rw [hP, b8001174c_x10 h₁] at hP8
  rw [hP] at hPa hPn
  rw [b8001174c_x11 h₁] at hPn
  simp only [Sym.wordToNatLit] at hP8 hPn
  have hhi₂ := hpost₂.heap.hi
  rw [hPn] at hhi₂
  have hlo₁ := hpre.heap.lo
  rw [hn₁] at hPa
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011794_spec
    (by rw [hpc₂, returnAddress_eq, b8001174c_x1 h₁]; decide) trivial
  have k₃ := b80011794_keeps h₃
  have hm₃ := b80011794_mem_same h₃
  have hpc₃ := b80011794_pc_not_taken h₃ (by
    rw [hP]; intro h0; rw [h0] at hPa
    simp only [heapStart, heapNext] at hPa hlo₁; simp at hPa; omega)
  have reg (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : t₃.getReg r = t₁.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have mem₃ (a : Word) (ha : a ≠ nextAddr) : t₃.getMem a = t₁.getMem a := by
    rw [hm₃, hpost₂.mem a ha]
  refine ⟨t₃, hr₂.trans hr₃, Or.inl ⟨P, {
      sp := by rw [reg .x2 (by decide), b8001174c_x2 h₁]
      x8 := by rw [reg .x8 (by decide), b8001174c_x8 h₁]
      x18 := by rw [reg .x18 (by decide), b8001174c_x18 h₁]
      x21 := by rw [reg .x21 (by decide), b8001174c_x21 h₁]
      kept := fun r hr ↦ by rw [reg r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
      ra := by rw [mem₃ _ (by addr_omega [hnx8, hlo, hb1]), b8001174c_m_x2_n8 h₁]
      s0 := by rw [mem₃ _ (by addr_omega [hnx8, hlo, hb1]), b8001174c_m_x2_n16 h₁]
      s1 := by rw [mem₃ _ (by addr_omega [hnx8, hlo, hb1]), b8001174c_m_x2_n24 h₁]
      s2 := by rw [mem₃ _ (by addr_omega [hnx8, hlo, hb1]), b8001174c_m_x2_n32 h₁]
      s3 := by rw [mem₃ _ (by addr_omega [hnx8, hlo, hb1]), b8001174c_m_x2_n40 h₁]
      s4 := by rw [mem₃ _ (by addr_omega [hnx8, hlo, hb1]), b8001174c_m_x2_n48 h₁]
      s5 := by rw [mem₃ _ (by addr_omega [hnx8, hlo, hb1]), b8001174c_m_x2_n56 h₁]
      s6 := by rw [mem₃ _ (by addr_omega [hnx8, hlo, hb1]), b8001174c_m_x2_n64 h₁]
      mem := fun a h1 h2 ↦ by rw [mem₃ a h2, hm₁ a (by addr_omega [h1, hb1])]
      next := by
        rw [hm₃]
        apply BitVec.eq_of_toNat_eq
        simp only [heapNext] at hPn hhi₂
        rw [hPn, BitVec.toNat_add]
        simp only [Sym.wordToNatLit, heapEnd] at hhi₂ ⊢
        omega
      align := hP8
      above := hPa
      fits := by simpa [heapNext] using hhi₂ }, hpc₃, by rw [k₃ .x10 (by decide), hP],
      by rw [reg .x19 (by decide), b8001174c_x19 h₁],
      by rw [reg .x20 (by decide), b8001174c_x20 h₁]⟩⟩

/-- A call of `dot(&weights[..n], right)` from the frame: the result `r` and the array `q` bytes
below `S`, in the frame, apart. -/
theorem dotPre {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (hu : Mid s u P)
    {r q n : Nat} (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 r)
    (hx11 : u.getReg .x11 = vecPtr s (capWeights s)) (hx12 : u.getReg .x12 = BitVec.ofNat 64 n)
    (hx13 : u.getReg .x13 = s.getReg .x2 - BitVec.ofNat 64 q)
    (hx14 : u.getReg .x14 = BitVec.ofNat 64 n) (hn : n ≤ (vecLen s (capWeights s)).toNat)
    (hn1 : 1 ≤ n) (hn6 : n ≤ 6) (hr1 : 88 ≤ r) (hr2 : r ≤ 432) (hq1 : 64 + 24 * n ≤ q)
    (hq2 : q ≤ 432) (hr8 : r % 8 = 0) (hq8 : q % 8 = 0)
    (hrq : q + 24 ≤ r ∨ r + 24 * n ≤ q) :
    DotPre u := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have hro := hst.rodata
  have fWe := hpre.weights.elems.facts (by omega) (by omega)
  have hsl : stackLo u dotStack = s.getReg .x2 - 1552 := by
    simp only [stackLo, hu.sp, dotStack, mulStack, Nat.reduceAdd]; rv_eval []
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  exact {
    ret := by rw [hx10]; valid_sub hst.valid [hb1, hlo, hr1, hr2, hr8]
    left := by rw [hx11, hx12, hn']; valid_sub hpre.weights.elems.valid [fWe, hn]
    right := by rw [hx13, hx14, hn']; valid_sub hst.valid [hb1, hlo, hq1, hq2, hq8]
    stack := ⟨by rw [hsl]; valid_sub hst.valid [hb1, hlo], by rw [hu.sp]; addr_omega [hb1, hb3]⟩
    retLeft := by rw [hx10, hx11, hx12, hn']; addr_omega [fWe, hb1, hn, hlo, hr1, hr2]
    retRight := by rw [hx10, hx13, hx14, hn']; addr_omega [hb1, hrq, hr1, hr2, hq1, hq2]
    retStack := by rw [hx10, hsl]; addr_omega [hb1, hr1, hr2]
    leftStack := by rw [hx11, hx12, hn', hsl]; addr_omega [fWe, hb1, hn, hlo]
    rightStack := by rw [hx13, hx14, hn', hsl]; addr_omega [hb1, hq1, hq2]
    rodata := hu.rodata hpre
    retRodata := by rw [hx10]; addr_omega [hro, hb1, hlo, hr1, hr2]
    stackRodata := by rw [hsl]; addr_omega [hro, hb1, hlo] }

/-- `0x80011824`'s side conditions. -/
theorem obl₁₁ {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (hu : Mid s u P)
    (hx11 : u.getReg .x11 = capMemory s) (hm3 : 3 ≤ (vecLen s (capMemory s)).toNat) :
    Sym.Oblig.all u b80011824.obl := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have fE := hpre.env.facts (by decide) (by decide)
  have fMh := hpre.memory.header.facts (by decide) (by decide)
  have fMe := hpre.memory.elems.facts (by omega) (by omega)
  have fMI := hpre.memoryIndex.facts (by decide) (by decide)
  have fMC := hpre.memoryCount.facts (by decide) (by decide)
  have eMp : u.getMem (capMemory s + 8) = vecPtr s (capMemory s) :=
    hu.held hpre hpre.memory.header (by decide) (by decide) (k := 8) (by decide)
  have eMI : u.getMem (s.getReg .x11 + 8) = capMemoryIndex s :=
    hu.held hpre hpre.env (by decide) (by decide) (k := 8) (by decide)
  rv_eval [hu.sp, hx11, hu.x18, hu.x21, eMp, eMI]
  and_intros <;> first
    | valid_access hst.valid [hb1, hlo]
    | valid_access hpre.memory.elems.valid [fMe, hm3]
    | valid_access hpre.memoryIndex.valid [fMI]
    | valid_access hpre.memoryCount.valid [fMC]
    | valid_access hpre.memory.header.valid [fMh]
    | valid_access hpre.env.valid [fE]
    | addr_omega [fMe, fMI, fMC, fE, hb1, hm3, hlo]

/-! ## `dot(&weights[..3], &[SEP_STATE, pc, gpow(0)])` -/

theorem stageB (hDot : DotSpec) {s u : MachineState} {P : Word} (hpre : FingerprintsPre s)
    (hu : Mid s u P) (hpc : u.pc = 0x80011798) (hx10 : u.getReg .x10 = P)
    (hx19 : u.getReg .x19 = s.getReg .x14) (hx20 : u.getReg .x20 = s.getReg .x12) :
    ∃ t, Reaches Image.code u t ∧ ((Mid s t P ∧ t.pc = 0x80011800 ∧ t.getReg .x9 = P ∧
      t.getReg .x19 = s.getReg .x14 ∧ t.getReg .x20 = vecPtr s (capWeights s) ∧
      t.getReg .x22 = vecLen s (capWeights s) ∧ 3 ≤ (vecLen s (capWeights s)).toNat ∧
      eAt t (s.getReg .x2 - 424) = dot₁ s) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have hro := hst.rodata
  have fE := hpre.env.facts (by decide) (by decide)
  have fWh := hpre.weights.header.facts (by decide) (by decide)
  have fPC := hpre.pc.facts (by decide) (by decide)
  -- `0x80011798`: `weights` has three elements
  have eW : u.getMem (s.getReg .x11) = capWeights s := by
    simpa [capWeights] using hu.held hpre hpre.env (by decide) (by decide) (k := 0) (by decide)
  have eWl : u.getMem (capWeights s + 16) = vecLen s (capWeights s) :=
    hu.held hpre hpre.weights.header (by decide) (by decide) (k := 16) (by decide)
  have eWp : u.getMem (capWeights s + 8) = vecPtr s (capWeights s) :=
    hu.held hpre hpre.weights.header (by decide) (by decide) (k := 8) (by decide)
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80011798_spec hpc (by
    rv_eval [hu.x18, eW]
    and_intros
    · valid_access hpre.weights.header.valid [fWh]
    · valid_access hpre.env.valid [fE])
  have k₄ := b80011798_keeps h₄
  have hm₄ := b80011798_mem_same h₄
  by_cases hw3 : (vecLen s (capWeights s)).toNat ≤ 2
  · exact ⟨t₄, hr₄, Or.inr (trap (b80011798_pc_taken h₄ (by rw [hu.x18, eW, eWl]; exact hw3)))⟩
  have hpc₄ := b80011798_pc_not_taken h₄ (by
    rw [hu.x18, eW, eWl]; simp only [Sym.wordToNatLit]; omega)
  have m₄ := hu.same hpre hm₄ fun r hr ↦ k₄ r (mem_of_mem hr _)
  have hx10₄ : t₄.getReg .x10 = capWeights s := by rw [b80011798_x10 h₄, hu.x18, eW]
  have hx22₄ : t₄.getReg .x22 = vecLen s (capWeights s) := by
    rw [b80011798_x22 h₄, hu.x18, eW, eWl]
  have hx9₄ : t₄.getReg .x9 = P := by rw [b80011798_x9 h₄, hx10]
  have hx20₄ : t₄.getReg .x20 = s.getReg .x12 := (k₄ .x20 (by decide)).trans hx20
  have hx19₄ : t₄.getReg .x19 = s.getReg .x14 := (k₄ .x19 (by decide)).trans hx19
  have ePC (k : Nat) (hk : k + 8 ≤ 24) := m₄.held hpre hpre.pc (by decide) (by decide) hk
  have ePC0 := ePC 0 (by decide)
  have ePC8 := ePC 8 (by decide)
  have ePC16 := ePC 16 (by decide)
  rv_eval [] at ePC0 ePC8 ePC16
  -- `0x800117ac`: `[SEP_STATE, pc, gpow(0)]` at `S - 400`, `dot` into `S - 424`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800117ac_spec hpc₄ (by
    rv_eval [m₄.sp, hx10₄, hx20₄]
    and_intros <;> first
      | valid_access hst.valid [hb1, hlo]
      | valid_access hpre.weights.header.valid [fWh]
      | valid_access hpre.pc.valid [fPC]
      | addr_omega [fWh, fPC, hb1])
  have k₅ := b800117ac_keeps h₅
  have m₅ := m₄.step hpre (fun a ha ↦ b800117ac_frame h₅ (by rw [m₄.sp]; addr_omega [hb1]) a
    (by rw [m₄.sp]; addr_omega [ha, hb1])) fun r hr ↦ k₅ r (mem_of_mem hr _)
  have hx10₅ : t₅.getReg .x10 = s.getReg .x2 - 424 := by rw [b800117ac_x10 h₅, m₄.sp]; rv_eval []
  have hx11₅ : t₅.getReg .x11 = vecPtr s (capWeights s) := by
    rw [b800117ac_x11 h₅, hx10₄]
    exact m₄.held hpre hpre.weights.header (by decide) (by decide) (k := 8) (by decide)
  have hx13₅ : t₅.getReg .x13 = s.getReg .x2 - 400 := by rw [b800117ac_x13 h₅, m₄.sp]; rv_eval []
  have hx12₅ := b800117ac_x12 h₅
  have hx14₅ := b800117ac_x14 h₅
  have hx20₅ : t₅.getReg .x20 = vecPtr s (capWeights s) := by
    rw [b800117ac_x20 h₅, hx10₄]
    exact m₄.held hpre hpre.weights.header (by decide) (by decide) (k := 8) (by decide)
  have fWe := hpre.weights.elems.facts (by omega) (by omega)
  have hsl₅ : stackLo t₅ dotStack = s.getReg .x2 - 1552 := by
    simp only [stackLo, m₅.sp, dotStack, mulStack, Nat.reduceAdd]; rv_eval []
  have hpre₅ : DotPre t₅ := {
    ret := by rw [hx10₅]; valid_sub hst.valid [hb1, hlo]
    left := by rw [hx11₅, hx12₅]; valid_sub hpre.weights.elems.valid [fWe, hw3]
    right := by rw [hx13₅, hx14₅]; valid_sub hst.valid [hb1, hlo]
    stack := ⟨by rw [hsl₅]; valid_sub hst.valid [hb1, hlo], by rw [m₅.sp]; addr_omega [hb1, hb3]⟩
    retLeft := by rw [hx10₅, hx11₅, hx12₅]; addr_omega [fWe, hb1, hw3, hlo]
    retRight := by rw [hx10₅, hx13₅, hx14₅]; addr_omega [hb1]
    retStack := by rw [hx10₅, hsl₅]; addr_omega [hb1]
    leftStack := by rw [hx11₅, hx12₅, hsl₅]; addr_omega [fWe, hb1, hw3, hlo]
    rightStack := by rw [hx13₅, hx14₅, hsl₅]; addr_omega [hb1]
    rodata := m₅.rodata hpre
    retRodata := by rw [hx10₅]; addr_omega [hro, hb1, hlo]
    stackRodata := by rw [hsl₅]; addr_omega [hro, hb1, hlo] }
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hpost₆⟩ | hdead⟩ := hDot.call hr₅ (b800117ac_pc h₅) hpre₅
  swap
  · exact ⟨t₆, hr₄.trans hr₆, Or.inr hdead⟩
  have hf₆ := hpost₆.frame
  rw [hx10₅, hsl₅] at hf₆
  have m₆ := m₅.step hpre (fun a ha ↦ hf₆ a (by addr_omega [ha, hb1]) (by addr_omega [ha, hb1]))
    fun r hr ↦ hpres₆ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have d := hpost₆.value
  rw [hx10₅, hx11₅, hx12₅, hx13₅] at d
  change Rv64Verifier.eAt _ _ = dotRust (eListAt t₅ _ 3) (eListAt t₅ _ 3) at d
  rw [eListAt_three t₅ (s.getReg .x2 - 400), m₅.take hpre hpre.weights (by omega) (by decide)] at d
  rv_eval [] at d
  have m32 := b800117ac_m_x2_32 h₅
  have m40 := b800117ac_m_x2_40 h₅
  have m48 := b800117ac_m_x2_48 h₅
  have m56 := b800117ac_m_x2_56 h₅
  have m64 := b800117ac_m_x2_64 h₅
  have m72 := b800117ac_m_x2_72 h₅
  have m80 := b800117ac_m_x2_80 h₅
  have m88 := b800117ac_m_x2_88 h₅
  have m96 := b800117ac_m_x2_96 h₅
  rw [m₄.sp] at m32 m40 m48 m56 m64 m72 m80 m88 m96
  rw [hx20₄] at m56 m64 m72
  rv_eval [ePC0, ePC8, ePC16] at m32 m40 m48 m56 m64 m72 m80 m88 m96
  rw [eAt_const m32 (by rv_eval [m40]) (by rv_eval [m48]),
    eAt_const m80 (by rv_eval [m88]) (by rv_eval [m96]),
    eAt_congr (s := s) (b := s.getReg .x12) m56 (by rv_eval [m64]) (by rv_eval [m72])] at d
  refine ⟨t₆, hr₄.trans hr₆, Or.inl ⟨m₆, by rw [hpc₆, returnAddress_eq, b800117ac_x1 h₅]; decide,
    ?_, ?_, ?_, ?_, by omega, ?_⟩⟩
  · rw [hpres₆.reg .x9, k₅ .x9 (by decide), hx9₄]
  · rw [hpres₆.reg .x19, k₅ .x19 (by decide), hx19₄]
  · rw [hpres₆.reg .x20, hx20₅]
  · rw [hpres₆.reg .x22, k₅ .x22 (by decide), hx22₄]
  · rw [d, dot₁, sepStateRust_eNew, gpowRust_zero]

/-! ## The length checks -/

def c1Regs : List Reg :=
  [.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem stageC1 {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (hu : Mid s u P)
    (hpc : u.pc = 0x80011800) (hx22 : u.getReg .x22 = vecLen s (capWeights s)) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80011824 ∧ (∀ a, t.getMem a = u.getMem a) ∧
      (∀ r ∈ c1Regs, t.getReg r = u.getReg r) ∧ t.getReg .x10 = 2 ∧
      t.getReg .x11 = capMemory s ∧ 6 ≤ (vecLen s (capWeights s)).toNat ∧
      3 ≤ (vecLen s (capMemory s)).toNat) ∨ Dead Image.code t) := by
  have fE := hpre.env.facts (by decide) (by decide)
  have fMh := hpre.memory.header.facts (by decide) (by decide)
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80011800_spec hpc trivial
  by_cases hw6 : (vecLen s (capWeights s)).toNat ≤ 5
  · exact ⟨t₇, hr₇, Or.inr (trap (b80011800_pc_taken h₇ (by rw [hx22]; exact hw6)))⟩
  have hpc₇ := b80011800_pc_not_taken h₇ (by rw [hx22]; simp only [Sym.wordToNatLit]; omega)
  have k₇ := b80011800_keeps h₇
  have hm₇ := b80011800_mem_same h₇
  have eM : t₇.getMem (s.getReg .x11 + 16) = capMemory s := by
    rw [hm₇]; exact hu.held hpre hpre.env (by decide) (by decide) (k := 16) (by decide)
  have eMl : t₇.getMem (capMemory s + 16) = vecLen s (capMemory s) := by
    rw [hm₇]; exact hu.held hpre hpre.memory.header (by decide) (by decide) (k := 16) (by decide)
  have hx18₇ : t₇.getReg .x18 = s.getReg .x11 := (k₇ .x18 (by decide)).trans hu.x18
  obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80011808_spec hpc₇ (by
    rv_eval [hx18₇, eM]
    and_intros
    · valid_access hpre.memory.header.valid [fMh]
    · valid_access hpre.env.valid [fE])
  have hR₈ := hr₇.trans hr₈
  by_cases hm0 : vecLen s (capMemory s) = 0
  · exact ⟨t₈, hR₈, Or.inr (trap (b80011808_pc_taken h₈ (by rw [hx18₇, eM, eMl]; exact hm0)))⟩
  have hpc₈ := b80011808_pc_not_taken h₈ (by rw [hx18₇, eM, eMl]; exact hm0)
  have k₈ := b80011808_keeps h₈
  have hm₈ := b80011808_mem_same h₈
  have hx12₈ : t₈.getReg .x12 = vecLen s (capMemory s) := by
    rw [b80011808_x12 h₈, hx18₇, eM, eMl]
  have hx11₈ : t₈.getReg .x11 = capMemory s := by rw [b80011808_x11 h₈, hx18₇, eM]
  obtain ⟨t₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b80011814_spec hpc₈ trivial
  by_cases hm1 : vecLen s (capMemory s) = 1
  · exact ⟨t₉, hR₈.trans hr₉, Or.inr (trap (b80011814_pc_taken h₉ (by rw [hx12₈]; exact hm1)))⟩
  have hpc₉ := b80011814_pc_not_taken h₉ (by rw [hx12₈]; exact hm1)
  have k₉ := b80011814_keeps h₉
  have hm₉ := b80011814_mem_same h₉
  obtain ⟨t₁₀, hr₁₀, h₁₀⟩ := Sym.BlockSpec.reaches b8001181c_spec hpc₉ trivial
  have hx12₉ : t₉.getReg .x12 = vecLen s (capMemory s) := (k₉ .x12 (by decide)).trans hx12₈
  have hR₁₀ := hR₈.trans (hr₉.trans hr₁₀)
  by_cases hm2 : (vecLen s (capMemory s)).toNat ≤ 2
  · exact ⟨t₁₀, hR₁₀, Or.inr (trap (b8001181c_pc_taken h₁₀ (by rw [hx12₉]; exact hm2)))⟩
  have hpc₁₀ := b8001181c_pc_not_taken h₁₀ (by rw [hx12₉]; simp only [Sym.wordToNatLit]; omega)
  have k₁₀ := b8001181c_keeps h₁₀
  have hm₁₀ := b8001181c_mem_same h₁₀
  refine ⟨t₁₀, hR₁₀, Or.inl ⟨hpc₁₀, fun a ↦ by rw [hm₁₀, hm₉, hm₈, hm₇], fun r hr ↦ ?_,
    b8001181c_x10 h₁₀, by rw [k₁₀ .x11 (by decide), k₉ .x11 (by decide), hx11₈], by omega,
    by omega⟩⟩
  rw [k₁₀ r (mem_of_mem hr _), k₉ r (mem_of_mem hr _), k₈ r (mem_of_mem hr _),
    k₇ r (mem_of_mem hr _)]

/-! ## `dot(&weights[..6], &[SEP_MEM, memory_index, memory_count, memory[0..3]])` -/

theorem stageC2 (hDot : DotSpec) {s u : MachineState} {P : Word} (hpre : FingerprintsPre s)
    (hu : Mid s u P) (hpc : u.pc = 0x80011824) (hx9 : u.getReg .x9 = P) (hx10 : u.getReg .x10 = 2)
    (hx11 : u.getReg .x11 = capMemory s) (hx19 : u.getReg .x19 = s.getReg .x14)
    (hx20 : u.getReg .x20 = vecPtr s (capWeights s)) (hw6 : 6 ≤ (vecLen s (capWeights s)).toNat)
    (hm3 : 3 ≤ (vecLen s (capMemory s)).toNat) :
    ∃ t, Reaches Image.code u t ∧ ((Mid s t P ∧ t.pc = 0x800118cc ∧ t.getReg .x9 = P ∧
      t.getReg .x19 = s.getReg .x14 ∧ t.getReg .x20 = vecPtr s (capWeights s) ∧
      (∀ a, ¬ Within a (s.getReg .x2 - 1552) 1120 → ¬ Within a (s.getReg .x2 - 328) 264 →
        t.getMem a = u.getMem a) ∧
      eAt t (s.getReg .x2 - 328) = dot₂ s) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have hro := hst.rodata
  have fE := hpre.env.facts (by decide) (by decide)
  have fMh := hpre.memory.header.facts (by decide) (by decide)
  have fMe := hpre.memory.elems.facts (by omega) (by omega)
  have fWe := hpre.weights.elems.facts (by omega) (by omega)
  have fMI := hpre.memoryIndex.facts (by decide) (by decide)
  have fMC := hpre.memoryCount.facts (by decide) (by decide)
  have eMp : u.getMem (capMemory s + 8) = vecPtr s (capMemory s) :=
    hu.held hpre hpre.memory.header (by decide) (by decide) (k := 8) (by decide)
  have eMI : u.getMem (s.getReg .x11 + 8) = capMemoryIndex s :=
    hu.held hpre hpre.env (by decide) (by decide) (k := 8) (by decide)
  have rdM (k : Nat) (hk : k + 8 ≤ 72) :
      u.getMem (vecPtr s (capMemory s) + BitVec.ofNat 64 k) =
        s.getMem (vecPtr s (capMemory s) + BitVec.ofNat 64 k) :=
    hu.mem _ (by addr_omega [fMe, hb1, hm3, hk, hlo]) (by addr_omega [fMe, hm3, hk])
  have rdMI (k : Nat) (hk : k + 8 ≤ 24) := hu.held hpre hpre.memoryIndex (by decide) (by decide) hk
  have rdMC (k : Nat) (hk : k + 8 ≤ 24) := hu.held hpre hpre.memoryCount (by decide) (by decide) hk
  obtain ⟨t₁₁, hr₁₁, h₁₁⟩ := Sym.BlockSpec.reaches b80011824_spec hpc (obl₁₁ hpre hu hx11 hm3)
  have k₁₁ := b80011824_keeps h₁₁
  have hf₁₁ := b80011824_frame h₁₁ (by rw [hu.sp]; addr_omega [hb1])
  rw [hu.sp] at hf₁₁
  rv_eval [] at hf₁₁
  have m₁₁ := hu.step hpre (fun a ha ↦ hf₁₁ a (by addr_omega [ha, hb1]))
    fun r hr ↦ k₁₁ r (mem_of_mem hr _)
  have hx10₁₁ : t₁₁.getReg .x10 = s.getReg .x2 - 328 := by rw [b80011824_x10 h₁₁, hu.sp]; rv_eval []
  have hx11₁₁ : t₁₁.getReg .x11 = vecPtr s (capWeights s) := by rw [b80011824_x11 h₁₁, hx20]
  have hx13₁₁ : t₁₁.getReg .x13 = s.getReg .x2 - 304 := by rw [b80011824_x13 h₁₁, hu.sp]; rv_eval []
  have hx12₁₁ := b80011824_x12 h₁₁
  have hx14₁₁ := b80011824_x14 h₁₁
  have hsl : stackLo t₁₁ dotStack = s.getReg .x2 - 1552 := by
    simp only [stackLo, m₁₁.sp, dotStack, mulStack, Nat.reduceAdd]; rv_eval []
  have hpre₁₁ : DotPre t₁₁ := dotPre hpre m₁₁ (r := 328) (q := 304) (n := 6) hx10₁₁ hx11₁₁ hx12₁₁
    hx13₁₁ hx14₁₁ hw6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨t₁₂, hr₁₂, ⟨hpc₁₂, hpres₁₂, hpost₁₂⟩ | hdead⟩ :=
    hDot.call hr₁₁ (b80011824_pc h₁₁) hpre₁₁
  swap
  · exact ⟨t₁₂, hr₁₂, Or.inr hdead⟩
  have hf₁₂ := hpost₁₂.frame
  rw [hx10₁₁, hsl] at hf₁₂
  have m₁₂ := m₁₁.step hpre (fun a ha ↦ hf₁₂ a (by addr_omega [ha, hb1]) (by addr_omega [ha, hb1]))
    fun r hr ↦ hpres₁₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have d := hpost₁₂.value
  rw [hx10₁₁, hx11₁₁, hx12₁₁, hx13₁₁] at d
  change Rv64Verifier.eAt _ _ = dotRust (eListAt t₁₁ _ 6) (eListAt t₁₁ _ 6) at d
  rw [eListAt_six t₁₁ (s.getReg .x2 - 304), m₁₁.take hpre hpre.weights (by omega) (by decide)] at d
  rv_eval [] at d
  have m128 := b80011824_m_x2_128 h₁₁
  have m136 := b80011824_m_x2_136 h₁₁
  have m144 := b80011824_m_x2_144 h₁₁
  have m152 := b80011824_m_x2_152 h₁₁
  have m160 := b80011824_m_x2_160 h₁₁
  have m168 := b80011824_m_x2_168 h₁₁
  have m176 := b80011824_m_x2_176 h₁₁
  have m184 := b80011824_m_x2_184 h₁₁
  have m192 := b80011824_m_x2_192 h₁₁
  have m200 := b80011824_m_x2_200 h₁₁
  have m208 := b80011824_m_x2_208 h₁₁
  have m216 := b80011824_m_x2_216 h₁₁
  have m224 := b80011824_m_x2_224 h₁₁
  have m232 := b80011824_m_x2_232 h₁₁
  have m240 := b80011824_m_x2_240 h₁₁
  have m248 := b80011824_m_x2_248 h₁₁
  have m256 := b80011824_m_x2_256 h₁₁
  have m264 := b80011824_m_x2_264 h₁₁
  have i0 := rdMI 0 (by decide)
  have i8 := rdMI 8 (by decide)
  have i16 := rdMI 16 (by decide)
  have c0 := rdMC 0 (by decide)
  have c8 := rdMC 8 (by decide)
  have c16 := rdMC 16 (by decide)
  have e0 := rdM 0 (by decide)
  have e8 := rdM 8 (by decide)
  have e16 := rdM 16 (by decide)
  have e24 := rdM 24 (by decide)
  have e32 := rdM 32 (by decide)
  have e40 := rdM 40 (by decide)
  have e48 := rdM 48 (by decide)
  have e56 := rdM 56 (by decide)
  have e64 := rdM 64 (by decide)
  rv_eval [] at i0 i8 i16 c0 c8 c16 e0 e8 e16 e24 e32 e40 e48 e56 e64
  rw [hu.sp] at m128 m136 m144 m152 m160 m168 m176 m184 m192
  rw [hu.sp] at m200 m208 m216 m224 m232 m240 m248 m256 m264
  rv_eval [hx10, hu.x18, hu.x21, eMI, i0, i8, i16, c0, c8, c16] at m128 m136 m144 m152 m160 m168
  rv_eval [hu.x18, hu.x21, eMI, i0, i8, i16, c0, c8, c16] at m176 m184 m192
  rv_eval [hx11, eMp, e0, e8, e16, e24, e32, e40, e48] at m200 m208 m216 m224 m232 m240
  rv_eval [hx11, eMp, e48, e56, e64] at m248 m256 m264
  rw [eAt_const m128 (by rv_eval [m136]) (by rv_eval [m144]),
    eAt_congr (s := s) (b := capMemoryIndex s) m152 (by rv_eval [m160]) (by rv_eval [m168]),
    eAt_congr (s := s) (b := s.getReg .x13) m176 (by rv_eval [m184]) (by rv_eval [m192]),
    eAt_congr (s := s) (b := vecPtr s (capMemory s)) m200 (by rv_eval [m208]) (by rv_eval [m216]),
    eAt_congr (s := s) (b := vecPtr s (capMemory s) + 24) m224 (by rv_eval [m232])
      (by rv_eval [m240]),
    eAt_congr (s := s) (b := vecPtr s (capMemory s) + 48) m248 (by rv_eval [m256])
      (by rv_eval [m264])] at d
  have g (i : Nat) (hi : i < 3) : (vecEs s (capMemory s)).getD i 0 =
      Rv64Verifier.eAt s (vecPtr s (capMemory s) + BitVec.ofNat 64 (24 * i)) :=
    eListAt_getD s _ (by omega)
  have g0 := g 0 (by decide)
  have g1 := g 1 (by decide)
  have g2 := g 2 (by decide)
  rv_eval [Nat.reduceMul] at g0 g1 g2
  refine ⟨t₁₂, hr₁₂, Or.inl ⟨m₁₂, by rw [hpc₁₂, returnAddress_eq, b80011824_x1 h₁₁]; decide,
    ?_, ?_, ?_, fun a h1 h2 ↦ ?_, ?_⟩⟩
  · rw [hpres₁₂.reg .x9, k₁₁ .x9 (by decide), hx9]
  · rw [hpres₁₂.reg .x19, k₁₁ .x19 (by decide), hx19]
  · rw [hpres₁₂.reg .x20, k₁₁ .x20 (by decide), hx20]
  · rw [hf₁₂ a (by addr_omega [h2, hb1]) (by addr_omega [h1, hb1]),
      hf₁₁ a (by addr_omega [h2, hb1])]
  · rw [d, dot₂, g0, g1, g2, sepMemRust_eNew]

/-! ## `dot(&weights[..3], &[SEP_BYTECODE, bytecode_index, bytecode_count])` -/

theorem obl₁₃ {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (hu : Mid s u P)
    (hx19 : u.getReg .x19 = s.getReg .x14) : Sym.Oblig.all u b800118cc.obl := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have fE := hpre.env.facts (by decide) (by decide)
  have fBI := hpre.bytecodeIndex.facts (by decide) (by decide)
  have fBC := hpre.bytecodeCount.facts (by decide) (by decide)
  have eBI : u.getMem (s.getReg .x11 + 24) = capBytecodeIndex s :=
    hu.held hpre hpre.env (by decide) (by decide) (k := 24) (by decide)
  rv_eval [hu.sp, hu.x18, hx19, eBI]
  and_intros <;> first
    | valid_access hst.valid [hb1, hlo]
    | valid_access hpre.bytecodeIndex.valid [fBI]
    | valid_access hpre.bytecodeCount.valid [fBC]
    | valid_access hpre.env.valid [fE]
    | addr_omega [fBI, fBC, fE, hb1, hlo]

theorem stageD (hDot : DotSpec) {s u : MachineState} {P : Word} (hpre : FingerprintsPre s)
    (hu : Mid s u P) (hpc : u.pc = 0x800118cc) (hx9 : u.getReg .x9 = P)
    (hx19 : u.getReg .x19 = s.getReg .x14) (hx20 : u.getReg .x20 = vecPtr s (capWeights s))
    (hw3 : 3 ≤ (vecLen s (capWeights s)).toNat) :
    ∃ t, Reaches Image.code u t ∧ ((Mid s t P ∧ t.pc = 0x80011930 ∧ t.getReg .x9 = P ∧
      t.getReg .x19 = 3 ∧
      (∀ a, ¬ Within a (s.getReg .x2 - 1552) 1120 → ¬ Within a (s.getReg .x2 - 160) 96 →
        t.getMem a = u.getMem a) ∧
      eAt t (s.getReg .x2 - 160) = dot₃ s) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have eBI : u.getMem (s.getReg .x11 + 24) = capBytecodeIndex s :=
    hu.held hpre hpre.env (by decide) (by decide) (k := 24) (by decide)
  have rdBI (k : Nat) (hk : k + 8 ≤ 24) := hu.held hpre hpre.bytecodeIndex (by decide) (by decide) hk
  have rdBC (k : Nat) (hk : k + 8 ≤ 24) := hu.held hpre hpre.bytecodeCount (by decide) (by decide) hk
  obtain ⟨t₁₃, hr₁₃, h₁₃⟩ := Sym.BlockSpec.reaches b800118cc_spec hpc (obl₁₃ hpre hu hx19)
  have k₁₃ := b800118cc_keeps h₁₃
  have hf₁₃ := b800118cc_frame h₁₃ (by rw [hu.sp]; addr_omega [hb1])
  rw [hu.sp] at hf₁₃
  rv_eval [] at hf₁₃
  have m₁₃ := hu.step hpre (fun a ha ↦ hf₁₃ a (by addr_omega [ha, hb1]))
    fun r hr ↦ k₁₃ r (mem_of_mem hr _)
  have hx10₁₃ : t₁₃.getReg .x10 = s.getReg .x2 - 160 := by rw [b800118cc_x10 h₁₃, hu.sp]; rv_eval []
  have hx11₁₃ : t₁₃.getReg .x11 = vecPtr s (capWeights s) := by rw [b800118cc_x11 h₁₃, hx20]
  have hx13₁₃ : t₁₃.getReg .x13 = s.getReg .x2 - 136 := by rw [b800118cc_x13 h₁₃, hu.sp]; rv_eval []
  have hpre₁₃ : DotPre t₁₃ := dotPre hpre m₁₃ (r := 160) (q := 136) (n := 3) hx10₁₃ hx11₁₃
    (b800118cc_x12 h₁₃) hx13₁₃ (b800118cc_x14 h₁₃) hw3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t₁₄, hr₁₄, ⟨hpc₁₄, hpres₁₄, hpost₁₄⟩ | hdead⟩ :=
    hDot.call hr₁₃ (b800118cc_pc h₁₃) hpre₁₃
  swap
  · exact ⟨t₁₄, hr₁₄, Or.inr hdead⟩
  have hsl : stackLo t₁₃ dotStack = s.getReg .x2 - 1552 := by
    simp only [stackLo, m₁₃.sp, dotStack, mulStack, Nat.reduceAdd]; rv_eval []
  have hf₁₄ := hpost₁₄.frame
  rw [hx10₁₃, hsl] at hf₁₄
  have m₁₄ := m₁₃.step hpre (fun a ha ↦ hf₁₄ a (by addr_omega [ha, hb1]) (by addr_omega [ha, hb1]))
    fun r hr ↦ hpres₁₄ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have d := hpost₁₄.value
  rw [hx10₁₃, hx11₁₃, b800118cc_x12 h₁₃, hx13₁₃] at d
  change Rv64Verifier.eAt _ _ = dotRust (eListAt t₁₃ _ 3) (eListAt t₁₃ _ 3) at d
  rw [eListAt_three t₁₃ (s.getReg .x2 - 136), m₁₃.take hpre hpre.weights hw3 (by decide)] at d
  rv_eval [] at d
  have m296 := b800118cc_m_x2_296 h₁₃
  have m304 := b800118cc_m_x2_304 h₁₃
  have m312 := b800118cc_m_x2_312 h₁₃
  have m320 := b800118cc_m_x2_320 h₁₃
  have m328 := b800118cc_m_x2_328 h₁₃
  have m336 := b800118cc_m_x2_336 h₁₃
  have m344 := b800118cc_m_x2_344 h₁₃
  have m352 := b800118cc_m_x2_352 h₁₃
  have m360 := b800118cc_m_x2_360 h₁₃
  have i0 := rdBI 0 (by decide)
  have i8 := rdBI 8 (by decide)
  have i16 := rdBI 16 (by decide)
  have c0 := rdBC 0 (by decide)
  have c8 := rdBC 8 (by decide)
  have c16 := rdBC 16 (by decide)
  rv_eval [] at i0 i8 i16 c0 c8 c16
  rw [hu.sp] at m296 m304 m312 m320 m328 m336 m344 m352 m360
  rv_eval [hu.x18, hx19, eBI, i0, i8, i16] at m296 m304 m312 m320 m328 m336
  rv_eval [hx19, c0, c8, c16] at m344 m352 m360
  rw [eAt_const m296 (by rv_eval [m304]) (by rv_eval [m312]),
    eAt_congr (s := s) (b := capBytecodeIndex s) m320 (by rv_eval [m328]) (by rv_eval [m336]),
    eAt_congr (s := s) (b := s.getReg .x14) m344 (by rv_eval [m352]) (by rv_eval [m360])] at d
  refine ⟨t₁₄, hr₁₄, Or.inl ⟨m₁₄, by rw [hpc₁₄, returnAddress_eq, b800118cc_x1 h₁₃]; decide,
    ?_, ?_, fun a h1 h2 ↦ ?_, ?_⟩⟩
  · rw [hpres₁₄.reg .x9, k₁₃ .x9 (by decide), hx9]
  · rw [hpres₁₄.reg .x19, b800118cc_x19 h₁₃]
  · rw [hf₁₄ a (by addr_omega [h2, hb1]) (by addr_omega [h1, hb1]),
      hf₁₃ a (by addr_omega [h2, hb1])]
  · rw [d, dot₃, sepBytecodeRust_eNew]

/-! ## The epilogue -/

theorem fingerprintsRust_eq (s : MachineState) :
    fingerprintsRust (vecEs s (capWeights s)) (eAt s (capMemoryIndex s)) (vecEs s (capMemory s))
      (eAt s (capBytecodeIndex s)) (eAt s (capBytecodeValue s)) (eAt s (s.getReg .x12))
      (eAt s (s.getReg .x13)) (eAt s (s.getReg .x14)) =
    [dot₁ s, dot₂ s, dot₃ s + eAt s (capBytecodeValue s)] := rfl

theorem obl₁₅ {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (hu : Mid s u P)
    (hx9 : u.getReg .x9 = P) : Sym.Oblig.all u b80011930.obl := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have fE := hpre.env.facts (by decide) (by decide)
  have fBV := hpre.bytecodeValue.facts (by decide) (by decide)
  have fO := ValidMemRange.bounds hpre.out (by decide)
  have fOs := hpre.outStack
  have fOf := hpre.outFree
  have fP := hu.fits
  have fP0 := hu.above
  have fP8 := hu.align
  have hlo' := hpre.heap.lo
  have eBV : u.getMem (s.getReg .x11 + 32) = capBytecodeValue s :=
    hu.held hpre hpre.env (by decide) (by decide) (k := 32) (by decide)
  have hPv : ValidMemRange P 9 := heap_valid_range fP8
    (by simp only [heapNext, heapStart] at fP0 hlo' ⊢; omega)
    (by simp only [heapEnd] at fP ⊢; omega)
  rv_eval [hu.sp, hu.x18, hu.x8, hx9, eBV]
  and_intros <;> first
    | valid_access hst.valid [hb1, hlo]
    | valid_access hPv [fP8, fP]
    | valid_access hpre.bytecodeValue.valid [fBV]
    | valid_access hpre.env.valid [fE]
    | valid_access hpre.out [fO]
    | addr_omega [fP, fP0, hlo', hab, hb1, hlo]
    | addr_omega [fO, fOs, hb1, hlo]
    | addr_omega [fO, fOf, fP, fP0]

theorem stageE {s u : MachineState} {P : Word} (hpre : FingerprintsPre s) (hu : Mid s u P)
    (hpc : u.pc = 0x80011930) (hx9 : u.getReg .x9 = P) (hx19 : u.getReg .x19 = 3)
    (hd₁ : eAt u (s.getReg .x2 - 424) = dot₁ s) (hd₂ : eAt u (s.getReg .x2 - 328) = dot₂ s)
    (hd₃ : eAt u (s.getReg .x2 - 160) = dot₃ s) (hw6 : 6 ≤ (vecLen s (capWeights s)).toNat)
    (hm3 : 3 ≤ (vecLen s (capMemory s)).toNat) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      FingerprintsPost s t := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have fBV := hpre.bytecodeValue.facts (by decide) (by decide)
  have fO := ValidMemRange.bounds hpre.out (by decide)
  have fOs := hpre.outStack
  have fOf := hpre.outFree
  have fP := hu.fits
  have fP0 := hu.above
  have fP8 := hu.align
  have hlo' := hpre.heap.lo
  have hhi := hpre.heap.hi
  simp only [heapNext, heapStart, heapEnd] at fP fP0 hlo' hhi
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b80011930_spec hpc (obl₁₅ hpre hu hx9)
  have eBV : u.getMem (s.getReg .x11 + 32) = capBytecodeValue s :=
    hu.held hpre hpre.env (by decide) (by decide) (k := 32) (by decide)
  have rdBV (k : Nat) (hk : k + 8 ≤ 24) := hu.held hpre hpre.bytecodeValue (by decide) (by decide) hk
  have v0 := rdBV 0 (by decide)
  have v8 := rdBV 8 (by decide)
  have v16 := rdBV 16 (by decide)
  rv_eval [] at v0 v8 v16
  -- what the block writes
  have hfr (a : Word) (h1 : ¬ Within a (s.getReg .x10) 24)
      (h2 : a.toNat < P.toNat ∨ P.toNat + 72 ≤ a.toNat) :
      t.getMem a = u.getMem a :=
    h.frame a (by
      rv_eval [hu.x8, hx9]
      and_intros <;> first | addr_omega [h1, fO] | addr_omega [h2, fP])
  have hnext : t.getMem nextAddr = P + 72 :=
    (hfr _ (by addr_omega [fOf, fO]) (by addr_omega [fP])).trans hu.next
  have hn : heapNext t = P.toNat + 72 := by
    simp only [heapNext, hnext, BitVec.toNat_add, Sym.wordToNatLit]; omega
  have c0 := b80011930_m_x8_0 h
  have c8 := b80011930_m_x8_8 h
  have c16 := b80011930_m_x8_16 h
  rw [hu.x8, hx19] at c0 c16
  rw [hu.x8, hx9] at c8
  have e0 := b80011930_m_x9_0 h
  have e8 := b80011930_m_x9_8 h
  have e16 := b80011930_m_x9_16 h
  have e24 := b80011930_m_x9_24 h
  have e32 := b80011930_m_x9_32 h
  have e40 := b80011930_m_x9_40 h
  have e48 := b80011930_m_x9_48 h
  have e56 := b80011930_m_x9_56 h
  have e64 := b80011930_m_x9_64 h
  rw [hx9] at e0 e8 e16 e24 e32 e40 e48 e56 e64
  rv_eval [hu.sp, hu.x18, eBV, v0, v8, v16] at e0 e8 e16 e24 e32 e40 e48 e56 e64
  have hE₁ : eAt t P = dot₁ s := by
    rw [← hd₁]; exact eAt_congr e0 (by rv_eval [e8]) (by rv_eval [e16])
  have hE₂ : eAt t (P + 24) = dot₂ s := by
    rw [← hd₂]; exact eAt_congr e24 (by rv_eval [e32]) (by rv_eval [e40])
  have hE₃ : eAt t (P + 48) = dot₃ s + eAt s (capBytecodeValue s) := by
    apply eAt_eq_of_limbs
    rw [limbs_add, ← hd₃, limbs_eAt, limbs_eAt, e48]
    rv_eval [e56, e64]
  have pc := b80011930_pc h
  rw [hu.sp] at pc
  rv_eval [hu.ra] at pc
  have x2 := b80011930_x2 h
  rw [hu.sp] at x2
  rv_eval [] at x2
  have k := b80011930_keeps h
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm, ?_, {
    heap := ⟨by rw [hn]; simp only [heapStart]; omega, by rw [hn]; simp only [heapEnd]; omega⟩
    mono := by rw [hn]; simp only [heapNext]; omega
    vec := ⟨⟨by simp only [vecPtr, c8]; omega, Or.inr ⟨by simp only [vecPtr, c8, heapStart]; omega,
      by simp only [vecPtr, vecCap, c8, c0, hn]; simp only [Sym.wordToNatLit]; omega⟩⟩,
      by simp only [vecLen, vecCap, c0, c16, le_refl]⟩
    cap := c0
    len := c16
    elems := ?_
    weightsLen := hw6
    memoryLen := hm3
    fresh := ⟨by simp only [vecPtr, c8]; omega, Or.inr ⟨by simp only [vecPtr, c8, heapNext]; omega,
      by simp only [vecPtr, c8, hn]; omega⟩⟩
    frame := fun a ha ↦ ?_ }⟩
  · refine preserves_of x2 ?_ ?_ ?_ ?_ fun r hr' ↦ ?_
    · rw [b80011930_x8 h, hu.sp]; rv_eval [hu.s0]
    · rw [b80011930_x9 h, hu.sp]; rv_eval [hu.s1]
    · rw [b80011930_x18 h, hu.sp]; rv_eval [hu.s2]
    · rw [b80011930_x19 h, hu.sp]; rv_eval [hu.s3]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b80011930_x20 h, hu.sp]; rv_eval [hu.s4]
      · rw [b80011930_x21 h, hu.sp]; rv_eval [hu.s5]
      · rw [b80011930_x22 h, hu.sp]; rv_eval [hu.s6]
      all_goals exact (k _ (by decide)).trans (hu.kept _ (by decide))
  · rw [fingerprintsRust_eq, vecEs, vecPtr, vecLen, c8, c16]
    change eListAt t P 3 = _
    rw [eListAt_three, hE₁, hE₂, hE₃]
  · have h0 := ha 0 (by decide)
    simp only [BitVec.add_zero, FingerprintsW, Fresh, hn] at h0
    rw [hfr a (fun hw ↦ h0 (Or.inl hw)) (by
      by_contra hc
      exact h0 (Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext]; omega, by omega⟩))))]
    exact hu.mem a (fun hw ↦ h0 (Or.inr (Or.inl (by addr_omega [hw, hlo, hb1]))))
      (fun he ↦ h0 (Or.inr (Or.inr (Or.inl (by rw [he]; addr_omega [])))))

/-! ## The closure -/

/-- **The `fingerprints` closure meets its contract**, given `alloc`'s and `dot`'s. -/
theorem fingerprints_spec (hA : AllocSpec) (hDot : DotSpec) : FingerprintsSpec := by
  intro s hpc hpre
  obtain ⟨u₁, hr₁, ⟨P, m₁, pc₁, x10₁, x19₁, x20₁⟩ | hd⟩ := stageA hA hpc hpre
  swap
  · exact ⟨u₁, hr₁, Or.inr hd⟩
  obtain ⟨u₂, hr₂, ⟨m₂, pc₂, x9₂, x19₂, x20₂, x22₂, -, d₁₂⟩ | hd⟩ :=
    stageB hDot hpre m₁ pc₁ x10₁ x19₁ x20₁
  swap
  · exact ⟨u₂, hr₁.trans hr₂, Or.inr hd⟩
  obtain ⟨u₃, hr₃, ⟨pc₃, mem₃, reg₃, x10₃, x11₃, hw6, hm3⟩ | hd⟩ := stageC1 hpre m₂ pc₂ x22₂
  swap
  · exact ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  have m₃ := m₂.same hpre mem₃ fun r hr ↦ reg₃ r (mem_of_mem hr _)
  obtain ⟨u₄, hr₄, ⟨m₄, pc₄, x9₄, x19₄, x20₄, f₄, d₂₄⟩ | hd⟩ := stageC2 hDot hpre m₃ pc₃
    (by rw [reg₃ .x9 (by decide), x9₂]) x10₃ x11₃ (by rw [reg₃ .x19 (by decide), x19₂])
    (by rw [reg₃ .x20 (by decide), x20₂]) hw6 hm3
  swap
  · exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr hd⟩
  obtain ⟨u₅, hr₅, ⟨m₅, pc₅, x9₅, x19₅, f₅, d₃₅⟩ | hd⟩ :=
    stageD hDot hpre m₄ pc₄ x9₄ x19₄ x20₄ (by omega)
  swap
  · exact ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr hd⟩
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have d₁₅ : eAt u₅ (s.getReg .x2 - 424) = dot₁ s := by
    rw [Keep.eAt (S := s.getReg .x2) f₅ (fun k hk ↦ by addr_omega [hk, hb1])
        (fun k hk ↦ by addr_omega [hk, hb1]),
      Keep.eAt (S := s.getReg .x2) f₄ (fun k hk ↦ by addr_omega [hk, hb1])
        (fun k hk ↦ by addr_omega [hk, hb1])]
    unfold Rv64Verifier.eAt
    rw [mem₃, mem₃, mem₃]
    exact d₁₂
  have d₂₅ : eAt u₅ (s.getReg .x2 - 328) = dot₂ s := by
    rw [Keep.eAt (S := s.getReg .x2) f₅ (fun k hk ↦ by addr_omega [hk, hb1])
      (fun k hk ↦ by addr_omega [hk, hb1])]
    exact d₂₄
  obtain ⟨t, hr, ht⟩ := stageE hpre m₅ pc₅ x9₅ x19₅ d₁₅ d₂₅ d₃₅ hw6 hm3
  exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr)))), Or.inl ht⟩

end Rv64Verifier.Proofs.Bus.Fingerprints
