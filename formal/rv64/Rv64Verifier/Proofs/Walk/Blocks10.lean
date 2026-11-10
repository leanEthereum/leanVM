import Rv64Verifier.Proofs.Walk.AtR10
import Rv64Verifier.Proofs.Layout.Keep
import Rv64Verifier.Proofs.Layout.BusBridge
import Rv64Verifier.Proofs.Bus.Contracts

/-!
# `Vec<BusBlock>` in memory, and `extend_trusted`'s contract

A `BusBlock` is 48 bytes: its coordinates `Vec<Form>` at `+0`, `log_rows` at `+24`, `rows` at
`+32`, `owner` at `+40` (`blockOf`, the bus proofs' `blockAt`). `n` blocks in a buffer of `c` are
sound (`BlocksSound`) when the buffer is allocated and every block's coordinates are a sound
`Vec<Form>` whose deep footprint misses the buffer.

`ExtendBlocksSpec` restates the contract of `Vec<BusBlock>::extend_trusted` for `build_layout`'s
`{closure#2}` (at `0x80005f94`) in these terms; `ExtB10.lean` derives it from the proved one.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

/-- The `BusBlock` at `a`. -/
def blockOf (u : MachineState) (a : Word) : BusBlockRust :=
  ⟨(u.getMem (a + 24)).toNat, u.getMem (a + 32), formVecOf u a, (u.getMem (a + 40)).toNat⟩

/-- The `n` blocks from `p`. -/
def blocksAt (u : MachineState) (p : Word) (n : Nat) : List BusBlockRust :=
  (List.range n).map fun j ↦ blockOf u (p + BitVec.ofNat 64 (48 * j))

/-- The blocks of the `Vec<BusBlock>` at `a`. -/
def blocksOf (u : MachineState) (a : Word) : List BusBlockRust :=
  blocksAt u (vecPtr u a) (vecLen u a).toNat

/-- What the `n` blocks from `p` reach: their coordinates' deep footprints. -/
@[rv_addr] def blocksDeep (u : MachineState) (p : Word) (n : Nat) (x : Word) : Prop :=
  ∃ j < n, formVecDeep u (p + BitVec.ofNat 64 (48 * j)) x

/-- `n` sound blocks from `p`, in an allocated buffer of `c`, their coordinates missing it. -/
structure BlocksSound (u : MachineState) (p : Word) (c n : Nat) : Prop where
  buf : Buf u p (c * 48) 8
  le : n ≤ c
  elems : ∀ j < n, FormVecOk u (p + BitVec.ofNat 64 (48 * j))
  sep : ∀ x, blocksDeep u p n x → ¬ Within x p (48 * c)

/-- The `Vec<BusBlock>` at `a` is sound. -/
def BlocksOk (u : MachineState) (a : Word) : Prop :=
  BlocksSound u (vecPtr u a) (vecCap u a).toNat (vecLen u a).toNat

/-- Its buffer and what its blocks reach. -/
@[rv_addr] def blocksFoot (u : MachineState) (a : Word) (x : Word) : Prop :=
  Within x (vecPtr u a) (48 * (vecCap u a).toNat) ∨ blocksDeep u (vecPtr u a) (vecLen u a).toNat x

theorem blockOf_toSpec (u : MachineState) (a : Word) : (blockOf u a).toSpec = Bus.blockAt u a := by
  simp only [blockOf, BusBlockRust.toSpec, Bus.blockAt, formVecAt_eq]

theorem blocksOf_toSpec (u : MachineState) (a : Word) :
    (blocksOf u a).map BusBlockRust.toSpec = Bus.blocksAt u a := by
  simp only [blocksOf, blocksAt, Bus.blocksAt, List.map_map]
  exact List.map_congr_left fun j _ ↦ blockOf_toSpec u _

theorem BlocksSound.vecOk {u : MachineState} {a : Word}
    (h : BlocksSound u (vecPtr u a) (vecCap u a).toNat (vecLen u a).toNat) : VecOk u a 48 8 :=
  ⟨h.buf, h.le⟩

/-- The buffer is in the heap below `NEXT`. -/
theorem BlocksSound.bounds {u : MachineState} {p : Word} {c n : Nat} (h : BlocksSound u p c n) :
    p.toNat % 8 = 0 ∧ (c = 0 ∨ heapStart ≤ p.toNat ∧ p.toNat + 48 * c ≤ heapNext u) := by
  have hb := h.buf
  simp only [Buf] at hb
  refine ⟨hb.1, ?_⟩
  rcases hb.2 with h0 | h0
  · exact Or.inl (by omega)
  · exact Or.inr ⟨h0.1, by omega⟩

/-- Everything the blocks reach is in the heap below `NEXT`. -/
theorem BlocksSound.deep_below {u : MachineState} {p : Word} {c n : Nat} (h : BlocksSound u p c n)
    {x : Word} (hx : blocksDeep u p n x) : heapStart ≤ x.toNat ∧ x.toNat < heapNext u := by
  obtain ⟨j, hj, hx⟩ := hx
  exact (h.elems j hj).deep_below hx

/-- Blocks whose buffer and deep footprint a frame misses are kept. -/
theorem blocksAt_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    {c n : Nat} (hok : BlocksSound s p c n) (hb : ∀ x, Within x p (48 * n) → ¬ w x)
    (hd : ∀ x, blocksDeep s p n x → ¬ w x) (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    blocksAt t p n = blocksAt s p n ∧ BlocksSound t p c n ∧ blocksDeep t p n = blocksDeep s p n := by
  have hbd := hok.bounds
  have hle := hok.le
  have hhi := hheap.hi
  simp only [heapEnd, heapStart] at hbd hhi
  have g (j : Nat) (hj : j < n) (k : Nat) (hk : k + 8 ≤ 48) :
      t.getMem (p + BitVec.ofNat 64 (48 * j) + BitVec.ofNat 64 k) =
        s.getMem (p + BitVec.ofNat 64 (48 * j) + BitVec.ofNat 64 k) := by
    rcases hbd.2 with h0 | h0
    · omega
    · exact h.getMem_of (fun x hx ↦ hb x (by addr_omega [hx, h0, hj, hk, hle, hhi]))
        (by addr_omega [h0, hj, hk, hle, hhi])
  have hel (j : Nat) (hj : j < n) :=
    formVecOf_moved h (e := p + BitVec.ofNat 64 (48 * j)) (e' := p + BitVec.ofNat 64 (48 * j))
      (by simpa using g j hj 0 (by decide)) (g j hj 8 (by decide)) (g j hj 16 (by decide))
      (hok.elems j hj) (fun x hx ↦ hd x ⟨j, hj, hx⟩) hheap hmono
  have hdeep : blocksDeep t p n = blocksDeep s p n := by
    funext x
    apply propext
    simp only [blocksDeep]
    exact exists_congr fun j ↦ ⟨fun ⟨hj, hx⟩ ↦ ⟨hj, by rwa [(hel j hj).2.2] at hx⟩,
      fun ⟨hj, hx⟩ ↦ ⟨hj, by rwa [(hel j hj).2.2]⟩⟩
  refine ⟨?_, ⟨?_, hle, fun j hj ↦ (hel j hj).2.1, fun x hx ↦ ?_⟩, hdeep⟩
  · simp only [blocksAt]
    refine List.map_congr_left fun j hm ↦ ?_
    have hj := List.mem_range.mp hm
    have g24 : t.getMem (p + BitVec.ofNat 64 (48 * j) + 24) =
        s.getMem (p + BitVec.ofNat 64 (48 * j) + 24) := g j hj 24 (by decide)
    have g32 : t.getMem (p + BitVec.ofNat 64 (48 * j) + 32) =
        s.getMem (p + BitVec.ofNat 64 (48 * j) + 32) := g j hj 32 (by decide)
    have g40 : t.getMem (p + BitVec.ofNat 64 (48 * j) + 40) =
        s.getMem (p + BitVec.ofNat 64 (48 * j) + 40) := g j hj 40 (by decide)
    simp only [blockOf, (hel j hj).1, g24, g32, g40]
  · have hraw := hok.buf
    simp only [Buf] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hmono⟩⟩
  · rw [hdeep] at hx; exact hok.sep x hx

/-! ## `extend_trusted`, at `0x80005f94` -/

/-- Its 144-byte frame and `clone`'s stack below it (deeper than `reserve`'s). -/
@[rv_addr] def extendBlocksStack : Nat := 144 + cloneStack

/-- The iterator at `a1`: the slice of `Vec<Form>`s from `[a1]` to `[a1 + 8]`, then the closure's
captures, `&log_rows`, `&rows` and `&table`. -/
def itBegin (s : MachineState) : Word := s.getMem (s.getReg .x11)
def itLen (s : MachineState) : Nat :=
  ((s.getMem (s.getReg .x11 + 8)).toNat - (itBegin s).toNat) / 24
def itHeight (s : MachineState) : Word := s.getMem (s.getReg .x11 + 16)
def itRows (s : MachineState) : Word := s.getMem (s.getReg .x11 + 24)
def itTable (s : MachineState) : Word := s.getMem (s.getReg .x11 + 32)

/-- What the call may write: the `Vec`'s header and buffer. -/
@[rv_addr] def selfW (s : MachineState) (x : Word) : Prop :=
  Within x (s.getReg .x10) 24 ∨ Within x (vecPtr s (s.getReg .x10)) (48 * (vecCap s (s.getReg .x10)).toNat)

/-- `n` bytes read only by the call: valid, outside the free heap, apart from the stack and from
the `Vec`'s header and buffer. -/
structure ExtRO (s : MachineState) (a : Word) (n : Nat) : Prop where
  valid : ValidMemRange a ((n + 7) / 8)
  aligned : a.toNat % 8 = 0
  free : n = 0 ∨ Outside s a n
  stack : Apart a n (stackLo s extendBlocksStack) extendBlocksStack
  self : ∀ x, Within x a n → ¬ selfW s x

structure ExtendBlocksPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s extendBlocksStack
  self : ValidMemRange (s.getReg .x10) 3
  ok : BlocksOk s (s.getReg .x10)
  selfFree : Outside s (s.getReg .x10) 24
  selfStack : Apart (s.getReg .x10) 24 (stackLo s extendBlocksStack) extendBlocksStack
  header : ∀ x, Within x (s.getReg .x10) 24 → ¬ blocksFoot s (s.getReg .x10) x
  env : ExtRO s (s.getReg .x11) 40
  whole : (itBegin s).toNat ≤ (s.getMem (s.getReg .x11 + 8)).toNat ∧
    ((s.getMem (s.getReg .x11 + 8)).toNat - (itBegin s).toNat) % 24 = 0
  src : ExtRO s (itBegin s) (24 * itLen s)
  srcOk : ∀ i < itLen s, FormVecOk s (itBegin s + BitVec.ofNat 64 (24 * i))
  srcNe : ∀ i < itLen s, (vecLen s (itBegin s + BitVec.ofNat 64 (24 * i))).toNat ≠ 0
  srcDeep : ∀ i < itLen s, ∀ x, formVecDeep s (itBegin s + BitVec.ofNat 64 (24 * i)) x →
    ¬ selfW s x
  height : ExtRO s (itHeight s) 8
  rows : ExtRO s (itRows s) 8
  table : ExtRO s (itTable s + 72) 8

/-- The blocks of the slice's coordinates, each with the captured `log_rows`, `rows` and owner,
pushed on. -/
structure ExtendBlocksPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : blocksOf t (s.getReg .x10) = blocksOf s (s.getReg .x10) ++
    ((List.range (itLen s)).map fun i ↦ formVecOf s (itBegin s + BitVec.ofNat 64 (24 * i))).map
      fun c ↦ (⟨(s.getMem (itHeight s)).toNat, s.getMem (itRows s), c,
        (s.getMem (itTable s + 72)).toNat⟩ : BusBlockRust)
  ok : BlocksOk t (s.getReg .x10)
  foot : ∀ x, blocksFoot t (s.getReg .x10) x → blocksFoot s (s.getReg .x10) x ∨ Fresh s t x
  frame : DFrame s t fun a ↦ selfW s a ∨
    Within a (stackLo s extendBlocksStack) extendBlocksStack ∨ Within a nextAddr 8 ∨ Fresh s t a

def ExtendBlocksSpec : Prop := FunSpec Image.code 0x80005f94 ExtendBlocksPre ExtendBlocksPost

end Rv64Verifier.Proofs.Walk
