import Rv64Verifier.Proofs.Pcs.VsoBatch
import Rv64Verifier.Proofs.Pcs.VsoConfig
import Rv64Verifier.Proofs.Pcs.VsoContracts

/-!
# `verify_stacked_opening`: the configuration's checks and allocations

From `0x80009f08`: the `StackBasis` stored at `S - 728` (scales, then the claims' pointer and
length); `log_inv_rate - 1 > 3` returns `Err` (`0x8000a0b8`), and so does `log_n` outside
`[15, 28]`; `WHIR_QUERIES`' slice for the pair read (pointer to `S - 848`, length to `S - 800`, the
root to `S - 840`); `folds = [6]` at `S - 464` and `log_inv_rates = [r]` at `S - 384`, each in a new
8-byte buffer (`Alloced`, at the first `grow_one`).

What the configuration writes from the batched state on is `RW`: those slots, the `Vec` headers,
the callees' stacks, `NEXT` and the heap allocated since (`Since`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A run that ends in a dead end, or returns an `Err`. -/
def Fail (s v : MachineState) : Prop :=
  Dead Image.code v ∨ (v.pc = 0x8000a0bc ∧ v.getReg .x10 ≠ okTag ∧ ∃ nx, Inv s v nx)

/-- The `Vec` headers, the callees' stacks, `NEXT` and the heap from `lo` to `hi`. -/
def RWl (s : MachineState) (lo hi a : Word) : Prop :=
  Within a (s.getReg .x2 - 464) 104 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a nextAddr 8 ∨ (lo.toNat ≤ a.toNat ∧ a.toNat < hi.toNat)

/-- `RWl` and the slots stored once. -/
def RW (s : MachineState) (lo hi a : Word) : Prop :=
  Within a (s.getReg .x2 - 864) 32 ∨ Within a (s.getReg .x2 - 800) 8 ∨
    Within a (s.getReg .x2 - 728) 40 ∨ RWl s lo hi a

theorem RWl.mono {s : MachineState} {lo hi hi' a : Word} (hle : hi.toNat ≤ hi'.toNat)
    (h : RWl s lo hi a) : RWl s lo hi' a := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩))

theorem RW.mono {s : MachineState} {lo hi hi' a : Word} (hle : hi.toNat ≤ hi'.toNat)
    (h : RW s lo hi a) : RW s lo hi' a := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (h.mono hle)))

theorem sfacts {s : MachineState} (hpre : VsoPre s) :
    Apart (s.getReg .x2 - 2464) 2464 nextAddr 8 ∧
      Apart (s.getReg .x2 - 2464) 2464 rodataStart rodataSize := by
  have h1 := hpre.stack.next
  have h2 := hpre.stack.rodata
  have hb := bounds hpre
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
    stackLo] at h1 h2
  exact ⟨by addr_omega [h1, hb], by addr_omega [h2, hb]⟩

theorem in_stack {s : MachineState} (hpre : VsoPre s) {a : Word}
    (h : Within a (s.getReg .x2 - 2464) 2464) : Within a (stackLo s vsoStack) vsoStack := by
  have hb := bounds hpre
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack, stackLo]
  addr_omega [h, hb]

/-- A block's writes, each a doubleword. -/
theorem holds_dframe {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t) :
    DFrame s t fun a ↦ ∃ k ∈ x.writes, Within a (k.eval s) 8 :=
  fun a ha ↦ h.2.2.2 a fun k hk heq ↦ ha 0 (by decide)
    ⟨k, hk, by rw [add_ofNat_zero, heq]; exact ⟨Nat.le_refl _, by omega⟩⟩

/-- `Bump::alloc` writes `NEXT` alone. -/
theorem alloc_dframe {s t : MachineState} (h : ∀ a, a ≠ nextAddr → t.getMem a = s.getMem a) :
    DFrame s t (Within · nextAddr 8) :=
  fun a ha ↦ h a fun heq ↦ ha 0 (by decide) (by rw [add_ofNat_zero, heq]; exact ⟨Nat.le_refl _, by
    simp only [nextAddr]; decide⟩)

/-! ## From the batched state on -/

/-- From the batched state `b` on: memory changed only in `RW`, the registers the rest reads
kept. -/
structure Since (s b u : MachineState) (nxb : Word) : Prop where
  bat : Batched s b nxb
  fr : DFrame b u (RW s nxb (u.getMem nextAddr))
  heap : HeapOk u
  mono : nxb.toNat ≤ heapNext u
  sp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040
  x25 : u.getReg .x25 = s.getReg .x10 + 8
  x26 : u.getReg .x26 = s.getReg .x12
  x27 : u.getReg .x27 = s.getReg .x10

theorem Since.start {s b : MachineState} {nxb : Word} (hpre : VsoPre s) (h : Batched s b nxb) :
    Since s b b nxb where
  bat := h
  fr := DFrame.refl _ _
  heap := h.inv.heap hpre.heap
  mono := by simp only [heapNext, h.inv.next]; exact Nat.le_refl _
  sp := h.inv.sp
  x25 := h.x25
  x26 := h.x26
  x27 := h.x27

theorem Since.step {s b u v : MachineState} {nxb : Word} (h : Since s b u nxb) {X : Word → Prop}
    (hX : DFrame u v X) (hXs : ∀ a, X a → RW s nxb (v.getMem nextAddr) a) (hheap : HeapOk v)
    (hmono : heapNext u ≤ heapNext v)
    (hr : ∀ r ∈ [Reg.x2, .x25, .x26, .x27], v.getReg r = u.getReg r) : Since s b v nxb where
  bat := h.bat
  fr := (h.fr.mono fun _ ha ↦ RW.mono hmono ha).trans hX hXs
  heap := hheap
  mono := Nat.le_trans h.mono hmono
  sp := (hr _ (by decide)).trans h.sp
  x25 := (hr _ (by decide)).trans h.x25
  x26 := (hr _ (by decide)).trans h.x26
  x27 := (hr _ (by decide)).trans h.x27

/-- A block that leaves `NEXT` alone. -/
theorem Since.blk {s b u v : MachineState} {nxb : Word} (h : Since s b u nxb) {X : Word → Prop}
    (hX : DFrame u v X) (hXs : ∀ a, X a → RW s nxb (u.getMem nextAddr) a)
    (hn : v.getMem nextAddr = u.getMem nextAddr)
    (hr : ∀ r ∈ [Reg.x2, .x25, .x26, .x27], v.getReg r = u.getReg r) : Since s b v nxb :=
  h.step hX (fun a ha ↦ by rw [hn]; exact hXs a ha)
    ⟨by simp only [heapNext, hn]; exact h.heap.lo, by simp only [heapNext, hn]; exact h.heap.hi⟩
    (by simp only [heapNext, hn]; exact Nat.le_refl _) hr

theorem Since.same {s b u v : MachineState} {nxb : Word} (h : Since s b u nxb)
    (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x25, .x26, .x27], v.getReg r = u.getReg r) : Since s b v nxb :=
  h.blk (X := fun _ ↦ False) (DFrame.of_same hm _) (fun _ h ↦ h.elim) (hm _) hr

theorem Since.inv {s b u : MachineState} {nxb : Word} (hpre : VsoPre s) (h : Since s b u nxb) :
    Inv s u (u.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hm := h.bat.inv.mono
  have hhi := h.heap.hi
  refine Inv.step' hpre h.bat.inv h.fr (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl h.mono hhi
    (h.sp.trans h.bat.inv.sp.symm)
  · simp only [RW, RWl] at ha
    rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨Nat.le_trans hm ha.1, ha.2⟩))
  · simp only [RW, RWl] at ha
    rcases ha with ha | ha | ha | ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · addr_omega [ha.2, hb, hhi]

theorem Since.fail {s b u : MachineState} {nxb : Word} (hpre : VsoPre s) (h : Since s b u nxb)
    (hpc : u.pc = 0x8000a0bc) (hx : u.getReg .x10 ≠ okTag) : Fail s u :=
  Or.inr ⟨hpc, hx, _, h.inv hpre⟩

theorem Since.rodata {s b u : MachineState} {nxb : Word} (hpre : VsoPre s) (h : Since s b u nxb) :
    RodataOk u := by
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hst := hpre.stack
  exact (h.inv hpre).rodata hpre.rodata (fun a ha hr ↦ by
    have := hI.rodata; simp only [W] at ha; addr_omega [this, ha, hr, hS]) hst.rodata

/-- `RWl` misses the slots from `S - 864` to `S - 688`. -/
theorem RWl.miss {s : MachineState} {lo hi a : Word} (hpre : VsoPre s) (h : RWl s lo hi a)
    (hhi : hi.toNat ≤ heapEnd) : ¬ Within a (s.getReg .x2 - 864) 176 := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  rcases h with hw | hw | hw | hw
  · addr_omega [hw, hb]
  · addr_omega [hw, hb]
  · addr_omega [hw, hb, hnx]
  · addr_omega [hw.2, hb, hhi]

/-- A word a frame misses keeps its value. -/
theorem keepW {u v : MachineState} {X : Word → Prop} (hX : DFrame u v X) {lo : Word} {n : Nat}
    (hXs : ∀ a, X a → ¬ Within a lo n) (hlo : lo.toNat + n ≤ 2 ^ 64) {y : Word}
    (h1 : lo.toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ lo.toNat + n) : v.getMem y = u.getMem y :=
  hX y fun i hi hw ↦ hXs _ hw (by addr_omega [h1, h2, hi, hlo])

theorem RWl.rw {s : MachineState} {lo hi a : Word} (h : RWl s lo hi a) : RW s lo hi a :=
  Or.inr (Or.inr (Or.inr h))

theorem RW.next {s : MachineState} {lo hi a : Word} (h : Within a nextAddr 8) : RW s lo hi a :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem RW.heap {s : MachineState} {lo hi a : Word} (h : lo.toNat ≤ a.toNat ∧ a.toNat < hi.toNat) :
    RW s lo hi a :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem RW.hdr {s : MachineState} {lo hi a : Word} (h : Within a (s.getReg .x2 - 464) 104) :
    RW s lo hi a :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem RW.stk {s : MachineState} {lo hi a : Word} (h : Within a (s.getReg .x2 - 2464) 1424) :
    RW s lo hi a :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-! ## The stores kept -/

/-- The `StackBasis` at `S - 728`: the scales' `Vec` as at `S - 776` in `b`, the claims. -/
structure Basis (s b u : MachineState) : Prop where
  b0 : u.getMem (s.getReg .x2 - 728) = b.getMem (s.getReg .x2 - 776)
  b1 : u.getMem (s.getReg .x2 - 720) = b.getMem (s.getReg .x2 - 768)
  b2 : u.getMem (s.getReg .x2 - 712) = b.getMem (s.getReg .x2 - 760)
  b3 : u.getMem (s.getReg .x2 - 704) = s.getReg .x14
  b4 : u.getMem (s.getReg .x2 - 696) = s.getReg .x15

/-- The queries' slice and the root, then the `StackBasis`. -/
structure Kept (s b u : MachineState) (QP QL : Word) : Prop extends Basis s b u where
  qp : u.getMem (s.getReg .x2 - 848) = QP
  root : u.getMem (s.getReg .x2 - 840) = s.getReg .x11
  ql : u.getMem (s.getReg .x2 - 800) = QL

theorem Basis.step {s b u v : MachineState} (hpre : VsoPre s) (h : Basis s b u)
    {X : Word → Prop} (hX : DFrame u v X) (hXs : ∀ a, X a → ¬ Within a (s.getReg .x2 - 728) 40) :
    Basis s b v := by
  have hb := bounds hpre
  have k (y : Word) (h1 : (s.getReg .x2 - 728).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 728).toNat + 40) :=
    keepW hX hXs (by addr_omega [hb]) h1 h2
  exact ⟨by rw [k _ (by addr_omega [hb]) (by addr_omega [hb])]; exact h.b0,
    by rw [k _ (by addr_omega [hb]) (by addr_omega [hb])]; exact h.b1,
    by rw [k _ (by addr_omega [hb]) (by addr_omega [hb])]; exact h.b2,
    by rw [k _ (by addr_omega [hb]) (by addr_omega [hb])]; exact h.b3,
    by rw [k _ (by addr_omega [hb]) (by addr_omega [hb])]; exact h.b4⟩

theorem Kept.step {s b u v : MachineState} {QP QL : Word} (hpre : VsoPre s)
    (h : Kept s b u QP QL) {X : Word → Prop} (hX : DFrame u v X)
    (hXs : ∀ a, X a → ¬ Within a (s.getReg .x2 - 848) 160) : Kept s b v QP QL := by
  have hb := bounds hpre
  have k (y : Word) (h1 : (s.getReg .x2 - 848).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 848).toNat + 160) :=
    keepW hX hXs (by addr_omega [hb]) h1 h2
  exact { toBasis := h.toBasis.step hpre hX fun a ha hw ↦ hXs a ha (by addr_omega [hw, hb])
          qp := by rw [k _ (by addr_omega [hb]) (by addr_omega [hb])]; exact h.qp
          root := by rw [k _ (by addr_omega [hb]) (by addr_omega [hb])]; exact h.root
          ql := by rw [k _ (by addr_omega [hb]) (by addr_omega [hb])]; exact h.ql }

/-! ## The checks -/

/-- At `0x80009f48`: the `StackBasis` stored, the rate in `[1, 4]`, `log_n` in `[15, 28]`. -/
structure Checked (s b u : MachineState) (nxb : Word) : Prop extends Since s b u nxb,
    Basis s b u where
  pc : u.pc = 0x80009f48
  x8 : u.getReg .x8 = s.getReg .x11
  x11 : u.getReg .x11 = s.getReg .x12 - 15
  x21 : u.getReg .x21 = s.getReg .x13
  rate : 1 ≤ (s.getReg .x13).toNat ∧ (s.getReg .x13).toNat ≤ 4
  logN : 15 ≤ (s.getReg .x12).toNat ∧ (s.getReg .x12).toNat ≤ 28

theorem rate_bounds {x : Word} (h : (x - 1).toNat ≤ ((3 : Word)).toNat) :
    1 ≤ x.toNat ∧ x.toNat ≤ 4 := by
  rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
  · have : x = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
    subst this
    exact absurd h (by decide)
  · addr_omega [h, h0]

theorem checks {s b : MachineState} {nxb : Word} (hpre : VsoPre s) (h : Batched s b nxb) :
    ∃ v, Reaches Image.code b v ∧ (Fail s v ∨ Checked s b v nxb) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := h.inv.sp
  have h0 := Since.start hpre h
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009f08_spec h.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80009f08_keeps h₁
  have hm₁ := b80009f08_frame h₁ (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm₁
  rv_eval [] at hm₁
  have s₁ : Since s b t₁ nxb := h0.blk (DFrame.of_memFrame hm₁)
    (fun a ha ↦ Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))
    (hm₁ _ (by addr_omega [hb, hnx])) (fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _))
  by_cases hc : ((3 : Word)).toNat < (s.getReg .x13 - 1).toNat
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a0b8_spec
      (b80009f08_pc_taken h₁ (by rw [h.x21]; exact hc)) trivial
    have s₂ := s₁.same (b8000a0b8_mem_same h₂)
      (fun r hr ↦ b8000a0b8_keeps h₂ r (Runtime.mem_of_mem hr _))
    exact ⟨t₂, hr₁.trans hr₂, Or.inl (s₂.fail hpre (b8000a0b8_pc h₂)
      (by rw [b8000a0b8_x10 h₂]; decide))⟩
  have hrate := rate_bounds (Nat.le_of_not_lt hc)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009f34_spec
    (b80009f08_pc_not_taken h₁ (by rw [h.x21]; exact Nat.le_of_not_lt hc)) trivial
  have k₂ := b80009f34_keeps h₂
  have s₂ := s₁.same (b80009f34_mem_same h₂) (fun r hr ↦ k₂ r (Runtime.mem_of_mem hr _))
  by_cases hc₂ : (s.getReg .x12).toNat < ((15 : Word)).toNat
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (s₂.fail hpre
      (b80009f34_pc_taken h₂ (by rw [s₁.x26]; exact hc₂)) (by rw [b80009f34_x10 h₂]; decide))⟩
  have hn15 : 15 ≤ (s.getReg .x12).toNat := Nat.le_of_not_lt hc₂
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009f3c_spec
    (b80009f34_pc_not_taken h₂ (by rw [s₁.x26]; exact Nat.le_of_not_lt hc₂)) trivial
  have k₃ := b80009f3c_keeps h₃
  have s₃ := s₂.same (b80009f3c_mem_same h₃) (fun r hr ↦ k₃ r (Runtime.mem_of_mem hr _))
  by_cases hc₃ : ((13 : Word)).toNat < (s.getReg .x12 - 15).toNat
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl (s₃.fail hpre
      (b80009f3c_pc_taken h₃ (by rw [s₂.x26]; exact hc₃))
      (by rw [k₃ .x10 (by decide), b80009f34_x10 h₂]; decide))⟩
  have hn28 : (s.getReg .x12).toNat ≤ 28 := by
    have := Nat.le_of_not_lt hc₃
    addr_omega [this, hn15]
  have hm₃ (a : Word) : t₃.getMem a = t₁.getMem a := by
    rw [b80009f3c_mem_same h₃, b80009f34_mem_same h₂]
  have e0 := b80009f08_m_x2_312 h₁
  have e1 := b80009f08_m_x2_320 h₁
  have e2 := b80009f08_m_x2_328 h₁
  have e3 := b80009f08_m_x2_336 h₁
  have e4 := b80009f08_m_x2_344 h₁
  rw [hsp] at e0 e1 e2 e3 e4
  rv_eval [] at e0 e1 e2 e3 e4
  have hr13 (r : Reg) (hr : r ∈ [Reg.x8, .x21]) : t₃.getReg r = b.getReg r := by
    rw [k₃ r (Runtime.mem_of_mem hr _), k₂ r (Runtime.mem_of_mem hr _),
      k₁ r (Runtime.mem_of_mem hr _)]
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr {
    toSince := s₃
    b0 := by rw [hm₃, e0]
    b1 := by rw [hm₃, e1]
    b2 := by rw [hm₃, e2]
    b3 := by rw [hm₃, e3, h.x22]
    b4 := by rw [hm₃, e4, h.x20]
    pc := b80009f3c_pc_not_taken h₃ (by rw [s₂.x26]; exact Nat.le_of_not_lt hc₃)
    x8 := by rw [hr13 .x8 (by decide), h.x8]
    x11 := by rw [b80009f3c_x11 h₃, s₂.x26]
    x21 := by rw [hr13 .x21 (by decide), h.x21]
    rate := hrate
    logN := ⟨hn15, hn28⟩ }⟩


/-! ## The allocations -/

/-- `WHIR_QUERIES[r - 1][log_n - 15]`'s entry. -/
@[rv_addr] def qEntry (s : MachineState) : Word :=
  Model.Pcs.queriesEntry ((s.getReg .x13).toNat - 1) ((s.getReg .x12).toNat - 15)

/-- An entry of the table reads the same in every state that keeps `.rodata`. -/
theorem entry_const {r n : ℕ} (hr : r < 4) (hn : n < 14) {u v : MachineState} (hu : RodataOk u)
    (hv : RodataOk v) :
    v.getMem (Model.Pcs.queriesEntry r n) = u.getMem (Model.Pcs.queriesEntry r n) ∧
      v.getMem (Model.Pcs.queriesEntry r n + 8) = u.getMem (Model.Pcs.queriesEntry r n + 8) := by
  have hok := Model.Pcs.queriesEntryOk_all r hr n hn
  unfold Model.Pcs.queriesEntryOk at hok
  split at hok
  swap
  · cases hok
  rename_i p l hp hl
  exact ⟨(hv.word? hp).trans (hu.word? hp).symm, (hv.word? hl).trans (hu.word? hl).symm⟩

/-- At `0x8000d7bc`, called from `0x80009ff8`: `folds = [6]` at `S - 464` (buffer `P`) and
`log_inv_rates = [r]` at `S - 384` (buffer `Q`), the queries' slice at `S - 848`. -/
structure Alloced (s b u : MachineState) (nxb QP QL P Q : Word) : Prop extends Since s b u nxb,
    Kept s b u QP QL where
  pc : u.pc = 0x8000d7bc
  x1 : u.getReg .x1 = 0x80009ff8
  x8 : u.getReg .x8 = (s.getReg .x12 - 12) >>> 2
  x9 : (u.getReg .x9).toNat = (s.getReg .x13).toNat + 3
  x10 : u.getReg .x10 = s.getReg .x2 - 384
  rate : 1 ≤ (s.getReg .x13).toNat ∧ (s.getReg .x13).toNat ≤ 4
  logN : 15 ≤ (s.getReg .x12).toNat ∧ (s.getReg .x12).toNat ≤ 28
  hQ : ∀ t, RodataOk t → t.getMem (qEntry s) = QP ∧ t.getMem (qEntry s + 8) = QL
  f0 : u.getMem (s.getReg .x2 - 464) = 1
  f1 : u.getMem (s.getReg .x2 - 456) = P
  f2 : u.getMem (s.getReg .x2 - 448) = 1
  fP : u.getMem P = 6
  r0 : u.getMem (s.getReg .x2 - 384) = 1
  r1 : u.getMem (s.getReg .x2 - 376) = Q
  r2 : u.getMem (s.getReg .x2 - 368) = 1
  rQ : u.getMem Q = s.getReg .x13
  bufs : P.toNat % 8 = 0 ∧ Q.toNat % 8 = 0 ∧ nxb.toNat ≤ P.toNat ∧ P.toNat + 8 ≤ Q.toNat ∧
    Q.toNat + 8 = heapNext u

theorem allocs (hA : AllocSpec) {s b u : MachineState} {nxb : Word} (hpre : VsoPre s)
    (h : Checked s b u nxb) :
    ∃ v, Reaches Image.code u v ∧ (Fail s v ∨ ∃ QP QL P Q, Alloced s b v nxb QP QL P Q) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, hro⟩ := sfacts hpre
  have hsp := h.sp
  have hr := h.rate
  have hn := h.logN
  have hRo : Region 0xa0000000 0xf30 := ⟨Or.inr ⟨by decide, by decide⟩, by decide⟩
  have hE0 : s.getReg .x13 * 256 - s.getReg .x13 * 32 + 0xa0000948 + (s.getReg .x12 - 15) * 16
      - 224 = qEntry s := by addr_omega [hr, hn]
  have hE8 : s.getReg .x13 * 256 - s.getReg .x13 * 32 + 0xa0000948 + (s.getReg .x12 - 15) * 16
      - 216 = qEntry s + 8 := by addr_omega [hr, hn]
  have hlo := hpre.heap.lo
  have hmb := h.bat.inv.mono
  -- the queries' slice
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009f48_spec h.pc (by
    rv_eval [hsp, h.x21, h.x11]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRo (by addr_omega [hr, hn]) (by addr_omega [hr, hn])
          (by addr_omega [hr, hn])
      | addr_omega [hr, hn, hb, hro])
  have k₁ := b80009f48_keeps h₁
  have hm₁ := b80009f48_frame h₁ (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm₁
  rv_eval [] at hm₁
  have s₁ : Since s b t₁ nxb := h.toSince.blk (DFrame.of_memFrame hm₁)
    (fun a ha ↦ Or.inl (by addr_omega [ha, hb])) (hm₁ _ (by addr_omega [hb, hnx]))
    (fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _))
  have B₁ : Basis s b t₁ := h.toBasis.step hpre (DFrame.of_memFrame hm₁)
    fun a ha hw ↦ by addr_omega [ha, hw, hb]
  have q₁ : t₁.getMem (s.getReg .x2 - 848) = u.getMem (qEntry s) := by
    have e := b80009f48_m_x2_192 h₁
    rw [hsp, h.x21, h.x11, hE0] at e
    rv_eval [] at e
    exact e
  have x9₁ : t₁.getReg .x9 = u.getMem (qEntry s + 8) := by
    rw [b80009f48_x9 h₁, h.x21, h.x11, hE8]
  have hQ : ∀ t, RodataOk t → t.getMem (qEntry s) = u.getMem (qEntry s) ∧
      t.getMem (qEntry s + 8) = u.getMem (qEntry s + 8) := fun t ht ↦
    entry_const (by omega) (by omega) (h.toSince.rodata hpre) ht
  -- `alloc(8, 8)` for `folds`
  have hpre₁ : AllocPre t₁ := ⟨s₁.heap, by rw [b80009f48_x10 h₁]; decide⟩
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hA.call hr₁ (b80009f48_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inl (Or.inl hdead)⟩
  obtain ⟨P, hP⟩ : ∃ P, t₂.getReg .x10 = P := ⟨_, rfl⟩
  have hP8 := hpost₂.aligned
  have hPa := hpost₂.above
  have hPn := hpost₂.next
  rw [hP, b80009f48_x10 h₁] at hP8
  rw [hP] at hPa hPn
  rw [b80009f48_x11 h₁] at hPn
  simp only [Sym.wordToNatLit] at hP8 hPn
  have hPhi : P.toNat + 8 ≤ heapEnd := by have := hpost₂.heap.hi; omega
  have hmo₁ := s₁.mono
  have hPlo : nxb.toNat ≤ P.toNat := by omega
  have hPs : heapStart ≤ P.toNat := by simp only [heapNext] at hlo hmb hmo₁ hPa ⊢; omega
  have s₂ : Since s b t₂ nxb := s₁.step (alloc_dframe hpost₂.mem) (fun _ ha ↦ RW.next ha)
    hpost₂.heap (by omega)
    (fun r hr ↦ hpres₂ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _))
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009f84_spec
    (by rw [hpc₂, returnAddress_eq, b80009f48_x1 h₁]; decide) trivial
  have hpc₃ := b80009f84_pc_taken h₃ (by
    rw [hP]; intro h0; rw [h0] at hPs; simp only [heapStart] at hPs; simp at hPs)
  have k₃ := b80009f84_keeps h₃
  have s₃ := s₂.same (b80009f84_mem_same h₃) (fun r hr ↦ k₃ r (Runtime.mem_of_mem hr _))
  -- `folds`
  have hPr : Region P 8 := heap_region (by simp only [heapStart] at hPs; omega) hPhi hP8
  have x10₃ : t₃.getReg .x10 = P := by rw [k₃ .x10 (by decide), hP]
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := s₃.sp
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009f8c_spec hpc₃ (by
    rv_eval [sp₃, x10₃]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hPr (by addr_omega []) (by addr_omega []) (by addr_omega [hP8])
      | addr_omega [hb, hPhi])
  have k₄ := b80009f8c_keeps h₄
  have X₄ : DFrame t₃ t₄ fun a ↦ Within a (s.getReg .x2 - 464) 24 ∨ Within a P 8 ∨
      Within a (s.getReg .x2 - 840) 8 ∨ Within a (s.getReg .x2 - 800) 8 :=
    (holds_dframe h₄).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b80009f8c, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rv_eval [sp₃, x10₃] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))
      · exact Or.inr (Or.inr (Or.inr (by addr_omega [hw, hb])))
  have hn₂ : heapNext t₃ = P.toNat + 8 := by
    simp only [heapNext, b80009f84_mem_same h₃] at hPn ⊢; exact hPn
  have nx₄ : t₄.getMem nextAddr = t₃.getMem nextAddr := X₄ _ fun i hi hw ↦ by
    rcases hw with hw | hw | hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hPhi]
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hb, hnx]
  have s₄ : Since s b t₄ nxb := s₃.blk X₄ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact RW.hdr (by addr_omega [ha, hb])
      · exact RW.heap ⟨by addr_omega [ha, hPlo], by
          simp only [heapNext] at hn₂; addr_omega [ha, hn₂]⟩
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha))
    nx₄ (fun r hr ↦ k₄ r (Runtime.mem_of_mem hr _))
  -- `alloc(8, 8)` for `log_inv_rates`
  have hpre₄ : AllocPre t₄ := ⟨s₄.heap, by rw [b80009f8c_x10 h₄]; decide⟩
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hdead⟩ := hA.call hr₄ (b80009f8c_pc h₄) hpre₄
  swap
  · exact ⟨t₅, hr₂.trans (hr₃.trans hr₅), Or.inl (Or.inl hdead)⟩
  obtain ⟨Q, hQd⟩ : ∃ Q, t₅.getReg .x10 = Q := ⟨_, rfl⟩
  have hQ8 := hpost₅.aligned
  have hQa := hpost₅.above
  have hQn := hpost₅.next
  rw [hQd, b80009f8c_x10 h₄] at hQ8
  rw [hQd] at hQa hQn
  rw [b80009f8c_x11 h₄] at hQn
  simp only [Sym.wordToNatLit] at hQ8 hQn
  have hQhi : Q.toNat + 8 ≤ heapEnd := by have := hpost₅.heap.hi; omega
  have hn₄ : heapNext t₄ = P.toNat + 8 := by simp only [heapNext, nx₄] at hn₂ ⊢; exact hn₂
  have hPQ : P.toNat + 8 ≤ Q.toNat := by omega
  have s₅ : Since s b t₅ nxb := s₄.step (alloc_dframe hpost₅.mem) (fun _ ha ↦ RW.next ha)
    hpost₅.heap (by omega)
    (fun r hr ↦ hpres₅ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _))
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80009fc0_spec
    (by rw [hpc₅, returnAddress_eq, b80009f8c_x1 h₄]; decide) trivial
  have hpc₆ := b80009fc0_pc_taken h₆ (by
    rw [hQd]; intro h0; rw [h0] at hPQ; simp at hPQ)
  have k₆ := b80009fc0_keeps h₆
  have s₆ := s₅.same (b80009fc0_mem_same h₆) (fun r hr ↦ k₆ r (Runtime.mem_of_mem hr _))
  -- `log_inv_rates`
  have hQr : Region Q 8 := heap_region (by simp only [heapStart] at hPs; omega) hQhi hQ8
  have x10₆ : t₆.getReg .x10 = Q := by rw [k₆ .x10 (by decide), hQd]
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := s₆.sp
  have hreg₆ (r : Reg) (hr : r ∈ [Reg.x8, .x21, .x22]) : t₆.getReg r = t₄.getReg r := by
    rw [k₆ r (Runtime.mem_of_mem hr _),
      hpres₅ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _)]
  have x22₆ : t₆.getReg .x22 = P := by rw [hreg₆ .x22 (by decide), b80009f8c_x22 h₄, x10₃]
  have x21₆ : t₆.getReg .x21 = s.getReg .x13 := by
    rw [hreg₆ .x21 (by decide), k₄ .x21 (by decide), k₃ .x21 (by decide),
      hpres₂ .x21 (by simp only [calleeSaved]; decide), k₁ .x21 (by decide), h.x21]
  have x8₆ : t₆.getReg .x8 = 1 := by rw [hreg₆ .x8 (by decide), b80009f8c_x8 h₄]
  have P₆ : t₆.getMem P = 6 := by
    rw [b80009fc0_mem_same h₆, hpost₅.mem _ (by addr_omega [hPhi])]
    have e := b80009f8c_m_x10_0 h₄
    rw [x10₃] at e
    exact e
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80009fc8_spec hpc₆ (by
    rv_eval [sp₆, x10₆, x22₆]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hQr (by addr_omega []) (by addr_omega []) (by addr_omega [hQ8])
      | exact Region.valid hPr (by addr_omega []) (by addr_omega []) (by addr_omega [hP8])
      | addr_omega [hb, hQhi, hPQ])
  have k₇ := b80009fc8_keeps h₇
  have X₇ : DFrame t₆ t₇ fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨ Within a Q 8 :=
    (holds_dframe h₇).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b80009fc8, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rv_eval [sp₆, x10₆] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr hw
  have hn₅ : heapNext t₆ = Q.toNat + 8 := by
    simp only [heapNext, b80009fc0_mem_same h₆] at hQn ⊢; exact hQn
  have nx₇ : t₇.getMem nextAddr = t₆.getMem nextAddr := X₇ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hQhi]
  have s₇ : Since s b t₇ nxb := s₆.blk X₇ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact RW.hdr (by addr_omega [ha, hb])
      · exact RW.heap ⟨by addr_omega [ha, hPlo, hPQ], by
          simp only [heapNext] at hn₅; addr_omega [ha, hn₅]⟩)
    nx₇ (fun r hr ↦ k₇ r (Runtime.mem_of_mem hr _))
  -- what `t₄` holds, and `t₇`
  have F₄₇ : DFrame t₄ t₇ fun a ↦ Within a nextAddr 8 ∨ Within a (s.getReg .x2 - 384) 24 ∨
      Within a Q 8 :=
    (((alloc_dframe hpost₅.mem).trans (DFrame.of_same (b80009fc0_mem_same h₆) _) fun _ h ↦ h).mono
      fun _ ha ↦ Or.inl ha).trans X₇ fun _ ha ↦ Or.inr ha
  have w₄₇ (y : Word) (h1 : (s.getReg .x2 - 864).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 384).toNat) : t₇.getMem y = t₄.getMem y :=
    F₄₇ y fun i hi hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hw, hi, h1, h2, hb, hnx]
      · addr_omega [hw, hi, h1, h2, hb]
      · addr_omega [hw, hi, h1, h2, hb, hQhi]
  have F₁₄ : DFrame t₁ t₄ fun a ↦ Within a nextAddr 8 ∨ Within a (s.getReg .x2 - 464) 24 ∨
      Within a P 8 ∨ Within a (s.getReg .x2 - 840) 8 ∨ Within a (s.getReg .x2 - 800) 8 :=
    (((alloc_dframe hpost₂.mem).trans (DFrame.of_same (b80009f84_mem_same h₃) _) fun _ h ↦ h).mono
      fun _ ha ↦ Or.inl ha).trans X₄ fun _ ha ↦ Or.inr ha
  have K₇ : Kept s b t₇ (u.getMem (qEntry s)) (u.getMem (qEntry s + 8)) := by
    have B₄ : Basis s b t₄ := B₁.step hpre F₁₄ fun a ha hw ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · addr_omega [ha, hw, hb, hnx]
      · addr_omega [ha, hw, hb]
      · addr_omega [ha, hw, hb, hPhi]
      · addr_omega [ha, hw, hb]
      · addr_omega [ha, hw, hb]
    have B₇ : Basis s b t₇ := B₄.step hpre F₄₇ fun a ha hw ↦ by
      rcases ha with ha | ha | ha
      · addr_omega [ha, hw, hb, hnx]
      · addr_omega [ha, hw, hb]
      · addr_omega [ha, hw, hb, hQhi]
    have e200 := b80009f8c_m_x2_200 h₄
    have e240 := b80009f8c_m_x2_240 h₄
    rw [sp₃] at e200 e240
    rv_eval [] at e200 e240
    refine { toBasis := B₇, qp := ?_, root := ?_, ql := ?_ }
    · rw [w₄₇ _ (by addr_omega [hb]) (by addr_omega [hb]), F₁₄ _ fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw | hw
        · addr_omega [hw, hi, hb, hnx]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb, hPhi]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]]
      exact q₁
    · rw [w₄₇ _ (by addr_omega [hb]) (by addr_omega [hb]), e200, b80009f84_keeps h₃ .x8 (by decide),
        hpres₂ .x8 (by simp only [calleeSaved]; decide), k₁ .x8 (by decide), h.x8]
    · rw [w₄₇ _ (by addr_omega [hb]) (by addr_omega [hb]), e240, b80009f84_keeps h₃ .x9 (by decide),
        hpres₂ .x9 (by simp only [calleeSaved]; decide), x9₁]
  have f₄ (o : Nat) (ho : o + 8 ≤ 24) : t₇.getMem (s.getReg .x2 - 464 + BitVec.ofNat 64 o) =
      t₄.getMem (s.getReg .x2 - 464 + BitVec.ofNat 64 o) :=
    w₄₇ _ (by addr_omega [hb, ho]) (by addr_omega [hb, ho])
  have m592 := b80009f8c_m_x2_592 h₄
  have m584 := b80009f8c_m_x2_584 h₄
  have m576 := b80009f8c_m_x2_576 h₄
  rw [sp₃] at m592 m584 m576
  rv_eval [] at m592 m584 m576
  have m672 := b80009fc8_m_x2_672 h₇
  have m664 := b80009fc8_m_x2_664 h₇
  have m656 := b80009fc8_m_x2_656 h₇
  have mQ := b80009fc8_m_x10_0 h₇
  rw [sp₆] at m672 m664 m656
  rv_eval [x8₆, x10₆] at m672 m664 m656
  rw [x10₆, x21₆] at mQ
  have hn₇ : heapNext t₇ = Q.toNat + 8 := by simp only [heapNext, nx₇] at hn₅ ⊢; exact hn₅
  refine ⟨t₇, hr₂.trans (hr₃.trans (hr₅.trans (hr₆.trans hr₇))), Or.inr
    ⟨_, _, P, Q, {
      toSince := s₇
      toKept := K₇
      pc := b80009fc8_pc h₇
      x1 := b80009fc8_x1 h₇
      x8 := by rw [b80009fc8_x8 h₇, s₆.x26]
      x9 := by rw [b80009fc8_x9 h₇, x21₆, x22₆, P₆]; addr_omega [hr]
      x10 := by rw [b80009fc8_x10 h₇, sp₆]; rv_eval []
      rate := hr
      logN := hn
      hQ := hQ
      f0 := by have := f₄ 0 (by decide); simp only [add_ofNat_zero] at this; rw [this, m576]
      f1 := by have := f₄ 8 (by decide); rv_eval [] at this; rw [this, m584, x10₃]
      f2 := by have := f₄ 16 (by decide); rv_eval [] at this; rw [this, m592]
      fP := by
        rw [F₄₇ P fun i hi hw ↦ by
          rcases hw with hw | hw | hw
          · addr_omega [hw, hi, hPhi]
          · addr_omega [hw, hi, hb, hPhi]
          · addr_omega [hw, hi, hPQ]]
        have e := b80009f8c_m_x10_0 h₄
        rw [x10₃] at e
        exact e
      r0 := m656
      r1 := m664
      r2 := m672
      rQ := mQ
      bufs := ⟨hP8, hQ8, hPlo, hPQ, hn₇.symm⟩ }⟩⟩


/-! ## `Vec<K>`s of words -/

/-- Naturals as words. -/
def lw (l : List ℕ) : List Word := l.map (BitVec.ofNat 64)

/-- A `Vec` of the words `ws` at `A`, its buffer allocated from `lo` on. -/
structure WVec (u : MachineState) (A lo : Word) (ws : List Word) : Prop where
  vec : VecOk u A 8 8
  len : (vecLen u A).toNat = ws.length
  words : u.readWords (vecPtr u A) ws.length = ws
  lo : lo.toNat ≤ (vecPtr u A).toNat
  hi : (vecPtr u A).toNat + (vecCap u A).toNat * 8 ≤ heapNext u

theorem readWords_snoc (u : MachineState) (p : Word) (n : Nat) :
    u.readWords p (n + 1) = u.readWords p n ++ [u.getMem (p + BitVec.ofNat 64 (8 * n))] := by
  rw [readWords_eq_map, readWords_eq_map, List.range_succ, List.map_append]
  rfl

theorem readWords_get {u : MachineState} {p : Word} {n : Nat} {ws : List Word}
    (h : u.readWords p n = ws) {j : Nat} (hj : j < n) :
    u.getMem (p + BitVec.ofNat 64 (8 * j)) = ws.getD j 0 := by
  rw [← h, readWords_eq_map]
  simp [hj]

theorem DFrame.readWords' {u v : MachineState} {X : Word → Prop} (hX : DFrame u v X) {p : Word}
    {n : Nat} (hm : ∀ a, X a → ¬ Within a p (8 * n)) (hp : p.toNat + 8 * n ≤ 2 ^ 64) :
    v.readWords p n = u.readWords p n := by
  rw [readWords_eq_map, readWords_eq_map]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact hX _ fun j hj hw ↦ hm _ hw (by addr_omega [hj, hi, hp])

theorem WVec.keep {u v : MachineState} {A lo : Word} {ws : List Word} (h : WVec u A lo ws)
    {X : Word → Prop} (hX : DFrame u v X)
    (hm : ∀ a, X a → ¬ Within a A 24 ∧ ¬ Within a (vecPtr u A) ((vecCap u A).toNat * 8))
    (hA : A.toNat + 24 ≤ 2 ^ 64) (hmono : heapNext u ≤ heapNext v) : WVec v A lo ws := by
  have w (o : Nat) (ho : o + 8 ≤ 24) :
      v.getMem (A + BitVec.ofNat 64 o) = u.getMem (A + BitVec.ofNat 64 o) :=
    hX _ fun i hi hw ↦ (hm _ hw).1 (by addr_omega [hi, ho, hA])
  have e0 : vecCap v A = vecCap u A := by
    have := w 0 (by decide); simp only [add_ofNat_zero] at this; exact this
  have e1 : vecPtr v A = vecPtr u A := w 8 (by decide)
  have e2 : vecLen v A = vecLen u A := w 16 (by decide)
  have hbl := h.vec.len
  have hraw := h.vec.raw
  have hlen := h.len
  have hhi := h.hi
  have hN := (u.getMem nextAddr).isLt
  simp only [heapNext] at hhi hN hmono
  refine ⟨⟨?_, by rw [e0, e2]; exact hbl⟩, by rw [e2]; exact hlen, ?_, by rw [e1]; exact h.lo,
    by rw [e1, e0]; simp only [heapNext]; omega⟩
  · simp only [RawVecOk, Buf] at hraw ⊢
    rw [e0, e1]
    obtain ⟨h1, h2⟩ := hraw
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨h2.1, by simp only [heapNext] at h2 ⊢; omega⟩
  · rw [e1, DFrame.readWords' hX (fun a ha hw ↦ (hm a ha).2 (by
      simp only [Within] at hw ⊢; omega)) (by omega)]
    exact h.words

/-- One word pushed: the length at `A + 16`, the word at the end of the buffer. -/
theorem WVec.push {u v : MachineState} {A lo w : Word} {ws : List Word} (h : WVec u A lo ws)
    {X : Word → Prop} (hX : DFrame u v X)
    (hm : ∀ a, X a → Within a (A + 16) 8 ∨
      Within a (vecPtr u A + BitVec.ofNat 64 (8 * ws.length)) 8)
    (hlt : ws.length < (vecCap u A).toNat)
    (hl : v.getMem (A + 16) = BitVec.ofNat 64 (ws.length + 1))
    (hw : v.getMem (vecPtr u A + BitVec.ofNat 64 (8 * ws.length)) = w)
    (hA : heapEnd ≤ A.toNat) (hA' : A.toNat + 24 ≤ 2 ^ 64) (hmono : heapNext u ≤ heapNext v)
    (hend : heapNext u ≤ heapEnd) :
    WVec v A lo (ws ++ [w]) := by
  have hhi := h.hi
  have hN := (u.getMem nextAddr).isLt
  simp only [heapNext] at hhi hN hmono hend
  have w0 : v.getMem A = u.getMem A := hX _ fun i hi hx ↦ by
    rcases hm _ hx with hx | hx
    · addr_omega [hx, hi, hA']
    · addr_omega [hx, hi, hhi, hlt, hend, hA, hA']
  have w8 : v.getMem (A + 8) = u.getMem (A + 8) := hX _ fun i hi hx ↦ by
    rcases hm _ hx with hx | hx
    · addr_omega [hx, hi, hA']
    · addr_omega [hx, hi, hhi, hlt, hend, hA, hA']
  have e0 : vecCap v A = vecCap u A := w0
  have e1 : vecPtr v A = vecPtr u A := w8
  have hraw := h.vec.raw
  have hsmall : ws.length + 1 < 2 ^ 64 := by omega
  have hlv : (vecLen v A).toNat = ws.length + 1 := by
    simp only [vecLen]; rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  refine ⟨⟨?_, by rw [e0, hlv]; exact hlt⟩, by rw [hlv]; simp, ?_, by rw [e1]; exact h.lo,
    by rw [e1, e0]; simp only [heapNext]; omega⟩
  · simp only [RawVecOk, Buf] at hraw ⊢
    rw [e0, e1]
    obtain ⟨h1, h2⟩ := hraw
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨h2.1, by simp only [heapNext] at h2 ⊢; omega⟩
  · rw [List.length_append, List.length_singleton, e1, readWords_snoc, hw,
      DFrame.readWords' hX (fun a ha hx ↦ by
        rcases hm _ ha with ha | ha
        · addr_omega [hx, ha, hhi, hlt, hend, hA, hA']
        · addr_omega [hx, ha, hhi, hlt])
        (by omega), h.words]

/-- A `Vec` header's pointer and capacity, missed by a frame. -/
theorem hdr_keep {u v : MachineState} {X : Word → Prop} (hX : DFrame u v X) {A : Word}
    (hm : ∀ a, X a → ¬ Within a A 16) (hA : A.toNat + 16 ≤ 2 ^ 64) :
    vecPtr v A = vecPtr u A ∧ vecCap v A = vecCap u A := by
  refine ⟨hX _ fun i hi hx ↦ hm _ hx (by addr_omega [hi, hA]), ?_⟩
  have := hX A fun i hi hx ↦ hm _ hx (by addr_omega [hi, hA])
  exact this

theorem WVec.same {u v : MachineState} {A lo : Word} {ws : List Word} (h : WVec u A lo ws)
    (hm : ∀ a, v.getMem a = u.getMem a) (hA : A.toNat + 24 ≤ 2 ^ 64) : WVec v A lo ws :=
  h.keep (X := fun _ ↦ False) (DFrame.of_same hm _) (fun _ h ↦ h.elim) hA
    (by simp only [heapNext, hm]; exact Nat.le_refl _)

/-! ## `grow_one` -/

theorem grow8 (hG : GrowOneFreshSpec 0x8000d7bc 8 8) {s b u : MachineState}
    {nxb QP QL A B : Word} {ws ws' : List Word} (hpre : VsoPre s) (hS : Since s b u nxb)
    (hK : Kept s b u QP QL) (hpc : u.pc = 0x8000d7bc)
    (hAB : (A = s.getReg .x2 - 384 ∧ B = s.getReg .x2 - 464) ∨
      (A = s.getReg .x2 - 464 ∧ B = s.getReg .x2 - 384))
    (hx10 : u.getReg .x10 = A) (hv : WVec u A nxb ws) (hw : WVec u B nxb ws') :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ (v.pc = returnAddress u ∧ Preserves u v ∧
      Since s b v nxb ∧ Kept s b v QP QL ∧ WVec v A nxb ws ∧ WVec v B nxb ws' ∧
      (vecCap u A).toNat + 1 ≤ (vecCap v A).toNat ∧
      (vecPtr v B).toNat + (vecCap v B).toNat * 8 ≤ (vecPtr v A).toNat ∧
      vecPtr v B = vecPtr u B)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hS.sp
  have hA1 : (s.getReg .x2 - 464).toNat ≤ A.toNat ∧ A.toNat + 24 ≤ (s.getReg .x2 - 360).toNat ∧
      A.toNat % 8 = 0 := by
    rcases hAB with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact ⟨by addr_omega [hb], by addr_omega [hb], by addr_omega [hb]⟩
  have hB1 : (s.getReg .x2 - 464).toNat ≤ B.toNat ∧ B.toNat + 24 ≤ (s.getReg .x2 - 360).toNat := by
    rcases hAB with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨by addr_omega [hb], by addr_omega [hb]⟩
  have hAB' : Apart A 24 B 24 := by rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> addr_omega [hb]
  have hsl : stackLo u growOneStack = s.getReg .x2 - 1200 := by
    simp only [stackLo, growOneStack, hsp]; rv_eval []
  have hpreG : GrowOnePre 8 8 u := {
    heap := hS.heap
    self := by rw [hx10]; valid_sub hst.valid [hb, hA1]
    raw := by rw [hx10]; exact hv.vec.raw
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [hx10]; exact stack_outside hpre (by addr_omega [hA1, hb]) (by addr_omega [hA1, hb])
    selfStack := by rw [hx10, hsl]; addr_omega [hA1, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, hnew⟩ | hdead⟩ := hG.call (Reaches.refl u) hpc hpreG
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  have hfr := DFrame.of_byteFrame hpost.frame
  rw [hx10, hsl] at hfr
  rw [hx10] at hnew
  have hcap := hpost.cap
  have hraw' := hpost.raw
  have hbytes := hpost.bytes
  rw [hx10] at hcap hraw' hbytes
  have hhv := hpost.heap.hi
  have hmo := hpost.mono
  have hlo := hS.mono
  have hwhi := hw.hi
  have hreg (r : Reg) (hr : r ∈ [Reg.x2, .x25, .x26, .x27]) : v.getReg r = u.getReg r :=
    hpres r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _)
  have sv : Since s b v nxb := hS.step hfr (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact RW.hdr (by addr_omega [ha, hA1, hb])
      · exact RW.stk (by addr_omega [ha, hb])
      · exact RW.next ha
      · exact RW.heap ⟨Nat.le_trans hlo ha.1, ha.2⟩)
    hpost.heap hmo hreg
  have hmiss (a : Word) (ha : Within a A 16 ∨ Within a (s.getReg .x2 - 1200) 160 ∨
      Within a nextAddr 8 ∨ Fresh u v a) : ¬ Within a (s.getReg .x2 - 864) 176 := by
    rcases ha with ha | ha | ha | ha
    · addr_omega [ha, hA1, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · simp only [Fresh] at ha; addr_omega [ha.2, hb, hhv]
  have kv : Kept s b v QP QL := hK.step hpre hfr fun a ha hw ↦ hmiss a ha (by addr_omega [hw, hb])
  -- the header's length, kept
  have e2 : vecLen v A = vecLen u A := hfr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx | hx
    · addr_omega [hx, hi, hA1]
    · addr_omega [hx, hi, hA1, hb]
    · addr_omega [hx, hi, hA1, hb, hnx]
    · simp only [Fresh] at hx; addr_omega [hx.2, hi, hA1, hb, hhv]
  have hbl := hv.vec.len
  have hlen := hv.len
  have hcap0 : 0 < (vecCap v A).toNat * 8 := by omega
  have hnew' := hnew.2.resolve_left (by omega)
  have hal := hnew.1
  have hN := (u.getMem nextAddr).isLt
  have hvA : WVec v A nxb ws := {
    vec := ⟨hraw', by rw [e2]; omega⟩
    len := by rw [e2]; exact hlen
    words := by
      have hw8 := hv.vec.raw.1
      rw [readWords_eq_of_bytesAt (bytesAt_eq_iff.mpr fun i hi ↦ bytesAt_eq_iff.mp hbytes i
        (by omega)) hal hw8]
      exact hv.words
    lo := Nat.le_trans hlo hnew'.1
    hi := hnew'.2 }
  have hvB : WVec v B nxb ws' := hw.keep hfr (fun a ha ↦ by
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rcases ha with ha | ha | ha | ha
        · addr_omega [ha, hx, hAB']
        · addr_omega [ha, hx, hB1, hb]
        · addr_omega [ha, hx, hB1, hb, hnx]
        · simp only [Fresh] at ha; addr_omega [ha.2, hx, hB1, hb, hhv]
      · rcases ha with ha | ha | ha | ha
        · addr_omega [ha, hx, hA1, hwhi, hb, hhv, hmo]
        · addr_omega [ha, hx, hwhi, hb, hhv, hmo]
        · simp only [heapNext] at hwhi hhv hmo; addr_omega [ha, hx, hwhi, hhv, hmo, hnx, hb]
        · simp only [Fresh] at ha; addr_omega [ha.1, hx, hwhi])
    (by addr_omega [hB1, hb]) hmo
  have e1 : vecPtr v B = vecPtr u B := by
    have := hfr (B + 8) fun i hi hx ↦ by
      rcases hx with hx | hx | hx | hx
      · addr_omega [hx, hi, hAB', hB1]
      · addr_omega [hx, hi, hB1, hb]
      · addr_omega [hx, hi, hB1, hb, hnx]
      · simp only [Fresh] at hx; addr_omega [hx.2, hi, hB1, hb, hhv]
    exact this
  have e0 : vecCap v B = vecCap u B := by
    have := hfr B fun i hi hx ↦ by
      rcases hx with hx | hx | hx | hx
      · addr_omega [hx, hi, hAB', hB1]
      · addr_omega [hx, hi, hB1, hb]
      · addr_omega [hx, hi, hB1, hb, hnx]
      · simp only [Fresh] at hx; addr_omega [hx.2, hi, hB1, hb, hhv]
    exact this
  refine ⟨v, hr, Or.inr ⟨hpc', hpres, sv, kv, hvA, hvB, hcap, ?_, e1⟩⟩
  rw [e0, e1]
  simp only [heapNext] at hwhi hnew'
  omega


/-! ## The ladder -/

/-- `(log_n - 12) / 4`, the ladder loop's count. -/
@[rv_addr] def K0 (s : MachineState) : ℕ := ((s.getReg .x12).toNat - 12) / 4

/-- What the checks established, of `s` alone. -/
structure Cfg (s : MachineState) (QP QL : Word) : Prop where
  rate : 1 ≤ (s.getReg .x13).toNat ∧ (s.getReg .x13).toNat ≤ 4
  logN : 15 ≤ (s.getReg .x12).toNat ∧ (s.getReg .x12).toNat ≤ 28
  hQ : ∀ t, RodataOk t → t.getMem (qEntry s) = QP ∧ t.getMem (qEntry s + 8) = QL

/-- Both ladders `k` steps in, `folds` at `S - 464` and `log_inv_rates` at `S - 384`, their
buffers apart. -/
structure Ladders (s u : MachineState) (nxb : Word) (k : ℕ) : Prop where
  folds : WVec u (s.getReg .x2 - 464) nxb (lw (Model.Pcs.ladderFolds k))
  rates : WVec u (s.getReg .x2 - 384) nxb (lw (Model.Pcs.ladderRates (s.getReg .x13).toNat k))
  apart : Apart (vecPtr u (s.getReg .x2 - 464)) ((vecCap u (s.getReg .x2 - 464)).toNat * 8)
    (vecPtr u (s.getReg .x2 - 384)) ((vecCap u (s.getReg .x2 - 384)).toNat * 8)

/-- At `0x8000a060`, iteration `i` of the ladder's loop next. -/
structure Lad (s b u : MachineState) (nxb QP QL : Word) (i : ℕ) : Prop extends Since s b u nxb,
    Kept s b u QP QL, Ladders s u nxb (i + 1) where
  pc : u.pc = 0x8000a060
  lt : i < K0 s
  x8 : u.getReg .x8 = BitVec.ofNat 64 (i + 2)
  x9 : u.getReg .x9 = vecPtr u (s.getReg .x2 - 464)
  x18 : u.getReg .x18 = BitVec.ofNat 64 (K0 s + 2)
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 384)
  x20 : u.getReg .x20 = 4
  x21 : u.getReg .x21 = BitVec.ofNat 64 (8 * i)
  x22 : u.getReg .x22 = 0 - BitVec.ofNat 64 (K0 s)
  x23 : u.getReg .x23 = 2

/-- At `0x8000a0fc`, the ladders done. -/
structure LadEnd (s b u : MachineState) (nxb QP QL : Word) : Prop extends Since s b u nxb,
    Kept s b u QP QL, Ladders s u nxb (K0 s + 1) where
  pc : u.pc = 0x8000a0fc
  x9 : u.getReg .x9 = vecPtr u (s.getReg .x2 - 464)
  x18 : u.getReg .x18 = BitVec.ofNat 64 (K0 s + 2)

theorem x8_eq {s : MachineState} (hn : 15 ≤ (s.getReg .x12).toNat ∧ (s.getReg .x12).toNat ≤ 28) :
    (s.getReg .x12 - 12) >>> 2 = BitVec.ofNat 64 (K0 s) := by
  apply BitVec.eq_of_toNat_eq
  have e : (s.getReg .x12 - 12).toNat = (s.getReg .x12).toNat - 12 := by addr_omega [hn]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e, BitVec.toNat_ofNat, K0]
  simp only [Nat.reducePow]
  omega

theorem WVec.one {u : MachineState} {A lo p w : Word} (hc : vecCap u A = 1) (hp : vecPtr u A = p)
    (hl : vecLen u A = 1) (hw : u.getMem p = w) (h8 : p.toNat % 8 = 0) (hlo : lo.toNat ≤ p.toNat)
    (hs : heapStart ≤ p.toNat) (hhi : p.toNat + 8 ≤ heapNext u) : WVec u A lo [w] where
  vec := ⟨by simp only [RawVecOk, Buf, hc, hp]; exact ⟨h8, Or.inr ⟨hs, by simpa using hhi⟩⟩,
    by rw [hc, hl]⟩
  len := by rw [hl]; rfl
  words := by rw [hp, readWords_eq_map]; simp [hw]
  lo := by rw [hp]; exact hlo
  hi := by rw [hp, hc]; simpa using hhi

theorem ofNat_toNat' (x : Word) : BitVec.ofNat 64 x.toNat = x := by simp

theorem pushes (hG : GrowOneFreshSpec 0x8000d7bc 8 8) {s b u : MachineState}
    {nxb QP QL P Q : Word} (hpre : VsoPre s) (h : Alloced s b u nxb QP QL P Q) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ Lad s b v nxb QP QL 0 ∨
      (K0 s = 0 ∧ LadEnd s b v nxb QP QL)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := h.sp
  have hr := h.rate
  have hn := h.logN
  obtain ⟨hP8, hQ8, hPlo, hPQ, hQn⟩ := h.bufs
  have hlo := hpre.heap.lo
  have hmb := h.bat.inv.mono
  have hmo := h.mono
  have hs : heapStart ≤ nxb.toNat := by simp only [heapNext] at hlo hmb; omega
  have hR0 : WVec u (s.getReg .x2 - 384) nxb (lw (Model.Pcs.ladderRates (s.getReg .x13).toNat 0)) := by
    have e : lw (Model.Pcs.ladderRates (s.getReg .x13).toNat 0) = [s.getReg .x13] := by
      simp [lw, Model.Pcs.ladderRates]
    rw [e]
    exact WVec.one h.r0 (by simp only [vecPtr]; rv_eval []; exact h.r1)
      (by simp only [vecLen]; rv_eval []; exact h.r2) h.rQ hQ8 (by omega) (by omega) (by omega)
  have hF0 : WVec u (s.getReg .x2 - 464) nxb (lw (Model.Pcs.ladderFolds 0)) := by
    have e : lw (Model.Pcs.ladderFolds 0) = [6] := by simp [lw, Model.Pcs.ladderFolds]
    rw [e]
    exact WVec.one h.f0 (by simp only [vecPtr]; rv_eval []; exact h.f1)
      (by simp only [vecLen]; rv_eval []; exact h.f2) h.fP hP8 hPlo (by omega)
      (by simp only [heapNext] at hQn ⊢; omega)
  -- `log_inv_rates.push(r + 3)`
  obtain ⟨v₁, hr₁, hv₁⟩ := grow8 hG hpre h.toSince h.toKept h.pc (Or.inl ⟨rfl, rfl⟩) h.x10 hR0 hF0
  rcases hv₁ with hd | ⟨hpc₁, hpres₁, S₁, K₁, R₁, F₁, hcap₁, hap₁, -⟩
  · exact ⟨v₁, hr₁, Or.inl hd⟩
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := S₁.sp
  obtain ⟨R, hR⟩ : ∃ R, vecPtr v₁ (s.getReg .x2 - 384) = R := ⟨_, rfl⟩
  have hR' : v₁.getMem (s.getReg .x2 - 376) = R := by rw [← hR]; simp only [vecPtr]; rv_eval []
  have hRhi := R₁.hi
  have hRlo := R₁.lo
  have hR8 := R₁.vec.raw.1
  rw [hR] at hRhi hRlo hR8
  have hv₁hi := S₁.heap.hi
  have hRlen : (lw (Model.Pcs.ladderRates (s.getReg .x13).toNat 0)).length = 1 := by
    simp [lw, Model.Pcs.ladderRates]
  have hRr : Region R ((vecCap v₁ (s.getReg .x2 - 384)).toNat * 8) :=
    heap_region (by simp only [heapStart] at hs; omega) (by simp only [heapNext] at hRhi hv₁hi ⊢; omega) hR8
  have hc0 : (vecCap u (s.getReg .x2 - 384)).toNat = 1 := by simp only [vecCap, h.r0]; rfl
  have x9₁ : (v₁.getReg .x9).toNat = (s.getReg .x13).toNat + 3 := by
    rw [hpres₁ .x9 (by simp only [calleeSaved]; decide)]; exact h.x9
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009ff8_spec
    (by rw [hpc₁, returnAddress_eq, h.x1]; decide) (by
      rv_eval [sp₁, hR']
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hRr (by addr_omega [hRhi, hv₁hi])
            (by addr_omega [hcap₁, hc0, hRhi, hv₁hi]) (by addr_omega [hR8, hRhi, hv₁hi])
        | addr_omega [hb, hRhi, hv₁hi])
  have k₂ := b80009ff8_keeps h₂
  have X₂ : DFrame v₁ v₂ fun a ↦ Within a (s.getReg .x2 - 368) 8 ∨ Within a (R + 8) 8 :=
    (holds_dframe h₂).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b80009ff8, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp₁, hR'] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr hw
  have nx₂ : v₂.getMem nextAddr = v₁.getMem nextAddr := X₂ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hRhi, hv₁hi, hcap₁, hc0, hnx]
  have S₂ : Since s b v₂ nxb := S₁.blk X₂ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact RW.hdr (by addr_omega [ha, hb])
      · exact RW.heap ⟨by addr_omega [ha, hRlo, hRhi, hv₁hi], by
          addr_omega [ha, hRhi, hcap₁, hc0, hv₁hi]⟩)
    nx₂ (fun r hr ↦ k₂ r (Runtime.mem_of_mem hr _))
  have K₂ : Kept s b v₂ QP QL := K₁.step hpre X₂ fun a ha hw ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hw, hb]
    · addr_omega [ha, hw, hb, hRhi, hv₁hi, hcap₁, hc0]
  have hn₂ : heapNext v₁ ≤ heapNext v₂ := by simp only [heapNext, nx₂]; exact Nat.le_refl _
  have R₂ : WVec v₂ (s.getReg .x2 - 384) nxb
      (lw (Model.Pcs.ladderRates (s.getReg .x13).toNat 1)) := by
    have e : lw (Model.Pcs.ladderRates (s.getReg .x13).toNat 1) =
        lw (Model.Pcs.ladderRates (s.getReg .x13).toNat 0) ++ [v₁.getReg .x9] := by
      rw [show v₁.getReg .x9 = BitVec.ofNat 64 ((s.getReg .x13).toNat + 3 * (0 + 1)) from
        BitVec.eq_of_toNat_eq (by rw [x9₁, BitVec.toNat_ofNat]; omega)]
      simp [lw, Model.Pcs.ladderRates]
    rw [e]
    refine R₁.push X₂ (fun a ha ↦ ?_) (by rw [hRlen]; omega) ?_ ?_
      (by addr_omega [hb]) (by addr_omega [hb]) hn₂ hv₁hi
    · rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (by rw [hRlen, hR]; addr_omega [ha, hRhi, hv₁hi])
    · rw [hRlen]
      have := b80009ff8_m_x2_672 h₂
      rw [sp₁] at this
      rv_eval [] at this
      rv_eval [this]
      rfl
    · rw [hRlen, hR]
      have := b80009ff8_m1 h₂
      rw [sp₁] at this
      rv_eval [hR'] at this
      exact this
  have hF2 := F₁.hi
  rw [hR] at hap₁
  have hdR₂ := hdr_keep X₂ (A := s.getReg .x2 - 384) (fun a ha hx ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hx, hb]
    · addr_omega [ha, hx, hb, hRhi, hv₁hi, hcap₁, hc0]) (by addr_omega [hb])
  have F₂ : WVec v₂ (s.getReg .x2 - 464) nxb (lw (Model.Pcs.ladderFolds 0)) :=
    F₁.keep X₂ (fun a ha ↦ by
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩ <;> rcases ha with ha | ha
      · addr_omega [ha, hx, hb]
      · addr_omega [ha, hx, hb, hRhi, hv₁hi, hcap₁, hc0]
      · addr_omega [ha, hx, hb, hF2, hv₁hi]
      · addr_omega [ha, hx, hap₁, hRhi, hv₁hi])
      (by addr_omega [hb]) hn₂
  -- `folds.push(4)`
  have sp₂ : v₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := S₂.sp
  obtain ⟨v₃, hr₃, hv₃⟩ := grow8 hG hpre S₂ K₂ (b80009ff8_pc h₂) (Or.inr ⟨rfl, rfl⟩)
    (by rw [b80009ff8_x10 h₂, sp₁]; rv_eval []) F₂ R₂
  rcases hv₃ with hd | ⟨hpc₃, hpres₃, S₃, K₃, F₃, R₃, hcap₃, hap₃, hRe₃⟩
  · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  have sp₃ : v₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := S₃.sp
  obtain ⟨Fp, hFp⟩ : ∃ F, vecPtr v₃ (s.getReg .x2 - 464) = F := ⟨_, rfl⟩
  have hF' : v₃.getMem (s.getReg .x2 - 456) = Fp := by rw [← hFp]; simp only [vecPtr]; rv_eval []
  have hFhi := F₃.hi
  have hFlo := F₃.lo
  have hF8 := F₃.vec.raw.1
  have hv₃hi := S₃.heap.hi
  rw [hFp] at hFhi hFlo hF8 hap₃
  have hFl2 := F₂.vec.len
  have hFn2 := F₂.len
  have hFlen : (lw (Model.Pcs.ladderFolds 0)).length = 1 := by simp [lw, Model.Pcs.ladderFolds]
  rw [hFlen] at hFn2
  have hFr : Region Fp ((vecCap v₃ (s.getReg .x2 - 464)).toNat * 8) :=
    heap_region (by simp only [heapStart] at hs; omega) (by simp only [heapNext] at hFhi hv₃hi ⊢; omega) hF8
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a014_spec
    (by rw [hpc₃, returnAddress_eq, b80009ff8_x1 h₂]; decide) (by
      rv_eval [sp₃, hF']
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hFr (by addr_omega [hFhi, hv₃hi])
            (by addr_omega [hcap₃, hFl2, hFn2, hFhi, hv₃hi]) (by addr_omega [hF8, hFhi, hv₃hi])
        | addr_omega [hb, hFhi, hv₃hi])
  have k₄ := b8000a014_keeps h₄
  have X₄ : DFrame v₃ v₄ fun a ↦ Within a (s.getReg .x2 - 448) 8 ∨ Within a (Fp + 8) 8 :=
    (holds_dframe h₄).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a014, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp₃, hF'] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr hw
  have nx₄ : v₄.getMem nextAddr = v₃.getMem nextAddr := X₄ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hFhi, hv₃hi, hcap₃, hFl2, hFn2, hnx]
  have S₄ : Since s b v₄ nxb := S₃.blk X₄ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact RW.hdr (by addr_omega [ha, hb])
      · exact RW.heap ⟨by addr_omega [ha, hFlo, hFhi, hv₃hi], by
          addr_omega [ha, hFhi, hcap₃, hFl2, hFn2, hv₃hi]⟩)
    nx₄ (fun r hr ↦ k₄ r (Runtime.mem_of_mem hr _))
  have K₄ : Kept s b v₄ QP QL := K₃.step hpre X₄ fun a ha hw ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hw, hb]
    · addr_omega [ha, hw, hb, hFhi, hv₃hi, hcap₃, hFl2, hFn2]
  have hn₄ : heapNext v₃ ≤ heapNext v₄ := by simp only [heapNext, nx₄]; exact Nat.le_refl _
  have x18₃ : v₃.getReg .x18 = 2 := by
    rw [hpres₃ .x18 (by simp only [calleeSaved]; decide), b80009ff8_x18 h₂]
  have F₄ : WVec v₄ (s.getReg .x2 - 464) nxb (lw (Model.Pcs.ladderFolds 1)) := by
    have e : lw (Model.Pcs.ladderFolds 1) = lw (Model.Pcs.ladderFolds 0) ++ [4] := by
      simp [lw, Model.Pcs.ladderFolds]
    rw [e]
    refine F₃.push X₄ (fun a ha ↦ ?_) (by rw [hFlen]; omega) ?_ ?_
      (by addr_omega [hb]) (by addr_omega [hb]) hn₄ hv₃hi
    · rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (by rw [hFlen, hFp]; addr_omega [ha, hFhi, hv₃hi])
    · rw [hFlen]
      have := b8000a014_m_x2_592 h₄
      rw [sp₃, x18₃] at this
      rv_eval [] at this
      rv_eval [this]
      rfl
    · rw [hFlen, hFp]
      have := b8000a014_m1 h₄
      rw [sp₃] at this
      rv_eval [hF'] at this
      exact this
  have hR3hi := R₃.hi
  have R₄ : WVec v₄ (s.getReg .x2 - 384) nxb (lw (Model.Pcs.ladderRates (s.getReg .x13).toNat 1)) :=
    R₃.keep X₄ (fun a ha ↦ by
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩ <;> rcases ha with ha | ha
      · addr_omega [ha, hx, hb]
      · addr_omega [ha, hx, hb, hFhi, hv₃hi, hcap₃, hFl2, hFn2]
      · addr_omega [ha, hx, hb, hR3hi, hv₃hi]
      · addr_omega [ha, hx, hap₃, hFhi, hv₃hi])
      (by addr_omega [hb]) hn₄
  have hdF := hdr_keep X₄ (A := s.getReg .x2 - 464) (fun a ha hx ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hx, hb]
    · addr_omega [ha, hx, hb, hFhi, hv₃hi, hcap₃, hFl2, hFn2]) (by addr_omega [hb])
  have hdR := hdr_keep X₄ (A := s.getReg .x2 - 384) (fun a ha hx ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hx, hb]
    · addr_omega [ha, hx, hb, hFhi, hv₃hi, hcap₃, hFl2, hFn2]) (by addr_omega [hb])
  have L₄ : Ladders s v₄ nxb 1 := ⟨F₄, R₄, by
    rw [hdF.1, hdF.2, hdR.1, hdR.2, hFp]; simp only [Apart]; omega⟩
  have x8₃ : v₃.getReg .x8 = BitVec.ofNat 64 (K0 s) := by
    rw [hpres₃ .x8 (by simp only [calleeSaved]; decide), k₂ .x8 (by decide),
      hpres₁ .x8 (by simp only [calleeSaved]; decide), h.x8]
    exact x8_eq hn
  have hK0 : K0 s ≤ 4 := by simp only [K0]; omega
  have x9₄ : v₄.getReg .x9 = vecPtr v₄ (s.getReg .x2 - 464) := by
    rw [b8000a014_x9 h₄, sp₃, hdF.1, hFp]; rv_eval [hF']
  by_cases hk : K0 s = 0
  · refine ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨hk, {
      toSince := S₄
      toKept := K₄
      toLadders := by rw [hk]; exact L₄
      pc := b8000a014_pc_taken h₄ (by rw [x8₃, hk]; rfl)
      x9 := x9₄
      x18 := by rw [k₄ .x18 (by decide), x18₃, hk]; rfl }⟩)⟩
  obtain ⟨v₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000a028_spec
    (b8000a014_pc_not_taken h₄ (by
      rw [x8₃]; intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat] at this
      simp at this; omega)) trivial
  have k₅ := b8000a028_keeps h₅
  have hm₅ := b8000a028_mem_same h₅
  have x8₄ : v₄.getReg .x8 = BitVec.ofNat 64 (K0 s) := by rw [b8000a014_keeps h₄ .x8 (by decide), x8₃]
  refine ⟨v₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inl {
    toSince := S₄.same hm₅ (fun r hr ↦ k₅ r (Runtime.mem_of_mem hr _))
    toKept := K₄.step hpre (DFrame.of_same hm₅ (fun _ ↦ False)) fun _ h ↦ h.elim
    toLadders := ⟨L₄.folds.same hm₅ (by addr_omega [hb]), L₄.rates.same hm₅ (by addr_omega [hb]),
      by simp only [vecPtr, vecCap, hm₅]; exact L₄.apart⟩
    pc := b8000a028_pc h₅
    lt := by omega
    x8 := b8000a028_x8 h₅
    x9 := by rw [k₅ .x9 (by decide), x9₄]; simp only [vecPtr, hm₅]
    x18 := by
      rw [b8000a028_x18 h₅, x8₄]; addr_omega [hK0]
    x19 := by
      have e : vecPtr v₅ (s.getReg .x2 - 384) = R := by
        rw [show vecPtr v₅ (s.getReg .x2 - 384) = vecPtr v₄ (s.getReg .x2 - 384) by
          simp only [vecPtr, hm₅], hdR.1, hRe₃, hdR₂.1, hR]
      rw [e, k₅ .x19 (by decide), k₄ .x19 (by decide),
        hpres₃ .x19 (by simp only [calleeSaved]; decide), b80009ff8_x19 h₂, sp₁]
      rv_eval [hR']
    x20 := by rw [k₅ .x20 (by decide), b8000a014_x20 h₄]
    x21 := b8000a028_x21 h₅
    x22 := by rw [b8000a028_x22 h₅, x8₄]
    x23 := b8000a028_x23 h₅ })⟩


/-! ## The ladder's loop -/

theorem lwF_len (k : ℕ) : (lw (Model.Pcs.ladderFolds k)).length = k + 1 := by
  simp [lw, Model.Pcs.ladderFolds]

theorem lwR_len (r k : ℕ) : (lw (Model.Pcs.ladderRates r k)).length = k + 1 := by
  simp [lw, Model.Pcs.ladderRates]

theorem lwF_succ (k : ℕ) : lw (Model.Pcs.ladderFolds (k + 1)) = lw (Model.Pcs.ladderFolds k) ++ [4] := by
  rw [← Model.Pcs.ladderFolds_succ]; simp [lw]

theorem lwR_succ (r k : ℕ) : lw (Model.Pcs.ladderRates r (k + 1)) =
    lw (Model.Pcs.ladderRates r k) ++ [BitVec.ofNat 64 (r + 3 * (k + 1))] := by
  rw [← Model.Pcs.ladderRates_succ]; simp [lw]

theorem lwF_last (k : ℕ) : (lw (Model.Pcs.ladderFolds (k + 1))).getD (k + 1) 0 = 4 := by
  rw [lwF_succ, List.getD_append_right _ _ _ _ (by rw [lwF_len])]
  simp [lwF_len]

theorem lwR_last (r k : ℕ) : (lw (Model.Pcs.ladderRates r (k + 1))).getD (k + 1) 0 =
    BitVec.ofNat 64 (r + 3 * (k + 1)) := by
  rw [lwR_succ, List.getD_append_right _ _ _ _ (by rw [lwR_len])]
  simp [lwR_len]

theorem Ladders.same {s u v : MachineState} {nxb : Word} {k : ℕ} (hpre : VsoPre s)
    (h : Ladders s u nxb k) (hm : ∀ a, v.getMem a = u.getMem a) : Ladders s v nxb k := by
  have hb := bounds hpre
  exact ⟨h.folds.same hm (by addr_omega [hb]), h.rates.same hm (by addr_omega [hb]),
    by simp only [vecPtr, vecCap, hm]; exact h.apart⟩

/-- At `0x8000a088`, iteration `i`'s values read, room for one more rate. -/
structure AtA088 (s b u : MachineState) (nxb QP QL : Word) (i : ℕ) : Prop extends Since s b u nxb,
    Kept s b u QP QL, Ladders s u nxb (i + 1) where
  pc : u.pc = 0x8000a088
  lt : i < K0 s
  x8 : u.getReg .x8 = BitVec.ofNat 64 (i + 2)
  x9 : u.getReg .x9 = BitVec.ofNat 64 ((s.getReg .x13).toNat + 3 * (i + 1))
  x18 : u.getReg .x18 = BitVec.ofNat 64 (K0 s + 2)
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 384)
  x20 : u.getReg .x20 = 4
  x21 : u.getReg .x21 = BitVec.ofNat 64 (8 * i)
  x22 : u.getReg .x22 = 0 - BitVec.ofNat 64 (K0 s)
  x23 : u.getReg .x23 = 2
  x24 : u.getReg .x24 = 4
  room : i + 2 < (vecCap u (s.getReg .x2 - 384)).toNat

theorem lad_read (hG : GrowOneFreshSpec 0x8000d7bc 8 8) {s b u : MachineState}
    {nxb QP QL : Word} {i : ℕ} (hpre : VsoPre s) (hc : Cfg s QP QL)
    (h : Lad s b u nxb QP QL i) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ AtA088 s b v nxb QP QL i) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.sp
  have hr := hc.rate
  have hn := hc.logN
  have hF := h.folds
  have hR := h.rates
  have hFn := hF.len
  have hRn := hR.len
  rw [lwF_len] at hFn
  rw [lwR_len] at hRn
  have hFc := hF.vec.len
  have hRc := hR.vec.len
  have hFhi := hF.hi
  have hRhi := hR.hi
  have hF8 := hF.vec.raw.1
  have hR8 := hR.vec.raw.1
  have hhi := h.heap.hi
  have hlo := hpre.heap.lo
  have hmb := h.bat.inv.mono
  have hs : heapStart ≤ nxb.toNat := by simp only [heapNext] at hlo hmb; omega
  have hFlo := hF.lo
  have hRlo := hR.lo
  have hFr : Region (vecPtr u (s.getReg .x2 - 464)) ((vecCap u (s.getReg .x2 - 464)).toNat * 8) :=
    heap_region (by simp only [heapStart] at hs; omega) (by simp only [heapNext] at hFhi hhi ⊢; omega) hF8
  have hRr : Region (vecPtr u (s.getReg .x2 - 384)) ((vecCap u (s.getReg .x2 - 384)).toNat * 8) :=
    heap_region (by simp only [heapStart] at hs; omega) (by simp only [heapNext] at hRhi hhi ⊢; omega) hR8
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a060_spec h.pc (by
    rv_eval [hsp, h.x9, h.x19, h.x21]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hFr (by addr_omega [hFhi, hhi, hFc, hFn])
          (by addr_omega [hFhi, hhi, hFc, hFn]) (by addr_omega [hF8, hFhi, hhi, hFc, hFn])
      | exact Region.valid hRr (by addr_omega [hRhi, hhi, hRc, hRn])
          (by addr_omega [hRhi, hhi, hRc, hRn]) (by addr_omega [hR8, hRhi, hhi, hRc, hRn]))
  have k₁ := b8000a060_keeps h₁
  have hm₁ := b8000a060_mem_same h₁
  have v9 : t₁.getReg .x9 = BitVec.ofNat 64 ((s.getReg .x13).toNat + 3 * (i + 1)) := by
    rw [b8000a060_x9 h₁, h.x19, h.x21,
      show vecPtr u (s.getReg .x2 - 384) + BitVec.ofNat 64 (8 * i) + 8 =
        vecPtr u (s.getReg .x2 - 384) + BitVec.ofNat 64 (8 * (i + 1)) by
          addr_omega [hRhi, hhi, hRc, hRn],
      readWords_get hR.words (by rw [lwR_len]; omega), lwR_last]
  have v24 : t₁.getReg .x24 = 4 := by
    rw [b8000a060_x24 h₁, h.x9, h.x21,
      show vecPtr u (s.getReg .x2 - 464) + BitVec.ofNat 64 (8 * i) + 8 =
        vecPtr u (s.getReg .x2 - 464) + BitVec.ofNat 64 (8 * (i + 1)) by
          addr_omega [hFhi, hhi, hFc, hFn],
      readWords_get hF.words (by rw [lwF_len]; omega), lwF_last]
  have S₁ := h.toSince.same hm₁ (fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _))
  have K₁ := h.toKept.step hpre (DFrame.of_same hm₁ (fun _ ↦ False)) fun _ h ↦ h.elim
  have L₁ := h.toLadders.same hpre hm₁
  have hp (A : Word) : vecPtr t₁ A = vecPtr u A := by simp only [vecPtr, hm₁]
  have hcp (A : Word) : vecCap t₁ A = vecCap u A := by simp only [vecCap, hm₁]
  by_cases hroom : i + 2 < (vecCap u (s.getReg .x2 - 384)).toNat
  · refine ⟨t₁, hr₁, Or.inr {
      toSince := S₁
      toKept := K₁
      toLadders := L₁
      pc := b8000a060_pc_taken h₁ (by
        rw [h.x8, hsp]; rv_eval []; intro h0
        have := congrArg BitVec.toNat h0
        have e : (vecCap u (s.getReg .x2 - 384)).toNat = (u.getMem (s.getReg .x2 - 384)).toNat := rfl
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        omega)
      lt := h.lt
      x8 := by rw [k₁ .x8 (by decide), h.x8]
      x9 := v9
      x18 := by rw [k₁ .x18 (by decide), h.x18]
      x19 := by rw [k₁ .x19 (by decide), h.x19, hp]
      x20 := by rw [k₁ .x20 (by decide), h.x20]
      x21 := by rw [k₁ .x21 (by decide), h.x21]
      x22 := by rw [k₁ .x22 (by decide), h.x22]
      x23 := by rw [k₁ .x23 (by decide), h.x23]
      x24 := v24
      room := by rw [hcp]; exact hroom }⟩
  have heq : (vecCap u (s.getReg .x2 - 384)).toNat = i + 2 := by omega
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a078_spec
    (b8000a060_pc_not_taken h₁ (by
      rw [h.x8, hsp]; rv_eval []
      apply BitVec.eq_of_toNat_eq
      have e : (vecCap u (s.getReg .x2 - 384)).toNat = (u.getMem (s.getReg .x2 - 384)).toNat := rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega)) trivial
  have k₂ := b8000a078_keeps h₂
  have hm₂ := b8000a078_mem_same h₂
  have S₂ := S₁.same hm₂ (fun r hr ↦ k₂ r (Runtime.mem_of_mem hr _))
  have K₂ := K₁.step hpre (DFrame.of_same hm₂ (fun _ ↦ False)) fun _ h ↦ h.elim
  have L₂ := L₁.same hpre hm₂
  obtain ⟨t₃, hr₃, hv₃⟩ := grow8 hG hpre S₂ K₂ (b8000a078_pc h₂) (Or.inl ⟨rfl, rfl⟩)
    (by rw [b8000a078_x10 h₂, S₁.sp]; rv_eval []) L₂.rates L₂.folds
  rcases hv₃ with hd | ⟨hpc₃, hpres₃, S₃, K₃, R₃, F₃, hcap₃, hap₃, -⟩
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a084_spec
    (by rw [hpc₃, returnAddress_eq, b8000a078_x1 h₂]; decide) (by
      rv_eval [S₃.sp]
      valid_access hst.valid [hb])
  have k₄ := b8000a084_keeps h₄
  have hm₄ := b8000a084_mem_same h₄
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x18, .x20, .x21, .x22, .x23]) :
      t₄.getReg r = u.getReg r := by
    rw [k₄ r (Runtime.mem_of_mem hr _),
      hpres₃ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _),
      k₂ r (Runtime.mem_of_mem hr _), k₁ r (Runtime.mem_of_mem hr _)]
  have hcap₂ : (vecCap t₂ (s.getReg .x2 - 384)).toNat = i + 2 := by
    rw [show vecCap t₂ (s.getReg .x2 - 384) = vecCap u (s.getReg .x2 - 384) from
      (hm₂ _).trans (hm₁ _)]
    exact heq
  refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr {
    toSince := S₃.same hm₄ (fun r hr ↦ k₄ r (Runtime.mem_of_mem hr _))
    toKept := K₃.step hpre (DFrame.of_same hm₄ (fun _ ↦ False)) fun _ h ↦ h.elim
    toLadders := Ladders.same hpre ⟨F₃, R₃, by simp only [Apart]; omega⟩ hm₄
    pc := b8000a084_pc h₄
    lt := h.lt
    x8 := by rw [hreg .x8 (by decide), h.x8]
    x9 := by
      rw [k₄ .x9 (by decide), hpres₃ .x9 (by simp only [calleeSaved]; decide),
        k₂ .x9 (by decide), v9]
    x18 := by rw [hreg .x18 (by decide), h.x18]
    x19 := by rw [b8000a084_x19 h₄, S₃.sp]; simp only [vecPtr, hm₄]; rv_eval []
    x20 := by rw [hreg .x20 (by decide), h.x20]
    x21 := by rw [hreg .x21 (by decide), h.x21]
    x22 := by rw [hreg .x22 (by decide), h.x22]
    x23 := by rw [hreg .x23 (by decide), h.x23]
    x24 := by
      rw [k₄ .x24 (by decide), hpres₃ .x24 (by simp only [calleeSaved]; decide),
        k₂ .x24 (by decide), v24]
    room := by
      rw [show vecCap t₄ (s.getReg .x2 - 384) = vecCap t₃ (s.getReg .x2 - 384) from hm₄ _]
      omega }⟩


/-- At `0x8000a040`, iteration `i`'s rate pushed, room for one more fold. -/
structure AtA040 (s b u : MachineState) (nxb QP QL : Word) (i : ℕ) : Prop extends Since s b u nxb,
    Kept s b u QP QL where
  folds : WVec u (s.getReg .x2 - 464) nxb (lw (Model.Pcs.ladderFolds (i + 1)))
  rates : WVec u (s.getReg .x2 - 384) nxb (lw (Model.Pcs.ladderRates (s.getReg .x13).toNat (i + 2)))
  apart : Apart (vecPtr u (s.getReg .x2 - 464)) ((vecCap u (s.getReg .x2 - 464)).toNat * 8)
    (vecPtr u (s.getReg .x2 - 384)) ((vecCap u (s.getReg .x2 - 384)).toNat * 8)
  pc : u.pc = 0x8000a040
  lt : i < K0 s
  x18 : u.getReg .x18 = BitVec.ofNat 64 (K0 s + 2)
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 384)
  x20 : u.getReg .x20 = 4
  x21 : u.getReg .x21 = BitVec.ofNat 64 (8 * i)
  x22 : u.getReg .x22 = 0 - BitVec.ofNat 64 (K0 s)
  x23 : u.getReg .x23 = 2
  x24 : u.getReg .x24 = BitVec.ofNat 64 (i + 3)
  room : i + 2 < (vecCap u (s.getReg .x2 - 464)).toNat

theorem lad_rate (hG : GrowOneFreshSpec 0x8000d7bc 8 8) {s b u : MachineState}
    {nxb QP QL : Word} {i : ℕ} (hpre : VsoPre s) (hc : Cfg s QP QL)
    (h : AtA088 s b u nxb QP QL i) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ AtA040 s b v nxb QP QL i) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := h.sp
  have hr := hc.rate
  have hn := hc.logN
  have hK0 : K0 s ≤ 4 := by simp only [K0]; omega
  have hlt := h.lt
  have hF := h.folds
  have hR := h.rates
  have hFn := hF.len
  have hRn := hR.len
  rw [lwF_len] at hFn
  rw [lwR_len] at hRn
  have hFc := hF.vec.len
  have hRc := h.room
  have hFhi := hF.hi
  have hRhi := hR.hi
  have hR8 := hR.vec.raw.1
  have hhi := h.heap.hi
  have hlo := hpre.heap.lo
  have hmb := h.bat.inv.mono
  have hs : heapStart ≤ nxb.toNat := by simp only [heapNext] at hlo hmb; omega
  have hRlo := hR.lo
  have hap := h.apart
  have hRr : Region (vecPtr u (s.getReg .x2 - 384)) ((vecCap u (s.getReg .x2 - 384)).toNat * 8) :=
    heap_region (by simp only [heapStart] at hs; omega) (by simp only [heapNext] at hRhi hhi ⊢; omega) hR8
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a088_spec h.pc (by
    rv_eval [hsp, h.x19, h.x21]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRr (by addr_omega [hRhi, hhi, hRc])
          (by addr_omega [hRhi, hhi, hRc]) (by addr_omega [hR8, hRhi, hhi, hRc])
      | addr_omega [hb, hRhi, hhi, hRc])
  have k₁ := b8000a088_keeps h₁
  have X₁ : DFrame u t₁ fun a ↦ Within a (s.getReg .x2 - 368) 8 ∨
      Within a (vecPtr u (s.getReg .x2 - 384) + BitVec.ofNat 64 (8 * (i + 2))) 8 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a088, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [hsp, h.x19, h.x21] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr (by addr_omega [hw, hRhi, hhi, hRc])
  have nx₁ : t₁.getMem nextAddr = u.getMem nextAddr := X₁ _ fun i' hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hRhi, hhi, hRc, hnx]
  have S₁ : Since s b t₁ nxb := h.toSince.blk X₁ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact RW.hdr (by addr_omega [ha, hb])
      · exact RW.heap ⟨by addr_omega [ha, hRlo, hRhi, hhi, hRc], by
          addr_omega [ha, hRhi, hhi, hRc]⟩)
    nx₁ (fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _))
  have K₁ : Kept s b t₁ QP QL := h.toKept.step hpre X₁ fun a ha hw ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hw, hb]
    · addr_omega [ha, hw, hb, hRhi, hhi, hRc]
  have hn₁ : heapNext u ≤ heapNext t₁ := by simp only [heapNext, nx₁]; exact Nat.le_refl _
  have R₁ : WVec t₁ (s.getReg .x2 - 384) nxb
      (lw (Model.Pcs.ladderRates (s.getReg .x13).toNat (i + 2))) := by
    rw [lwR_succ]
    refine hR.push X₁ (fun a ha ↦ ?_) (by rw [lwR_len]; omega) ?_ ?_
      (by addr_omega [hb]) (by addr_omega [hb]) hn₁ hhi
    · rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (by rw [lwR_len]; exact ha)
    · rw [lwR_len]
      have := b8000a088_m_x2_672 h₁
      rw [hsp, h.x8] at this
      rv_eval [] at this
      rv_eval [this]
      addr_omega [hlt, hK0]
    · rw [lwR_len]
      have := b8000a088_m1 h₁
      rw [h.x19, h.x21, h.x9, h.x24] at this
      rw [show vecPtr u (s.getReg .x2 - 384) + BitVec.ofNat 64 (8 * (i + 1 + 1)) =
          vecPtr u (s.getReg .x2 - 384) + BitVec.ofNat 64 (8 * i) + 16 by
        addr_omega [hRhi, hhi, hRc], this]
      addr_omega [hr, hlt, hK0]
  have hFhi' := hF.hi
  have F₁ : WVec t₁ (s.getReg .x2 - 464) nxb (lw (Model.Pcs.ladderFolds (i + 1))) :=
    hF.keep X₁ (fun a ha ↦ by
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩ <;> rcases ha with ha | ha
      · addr_omega [ha, hx, hb]
      · addr_omega [ha, hx, hb, hRhi, hhi, hRc]
      · addr_omega [ha, hx, hb, hFhi', hhi]
      · simp only [Apart] at hap
        rcases hap with h0 | h0 | h0 | h0
        · addr_omega [hx, h0]
        · addr_omega [h0, hRc]
        · addr_omega [ha, hx, h0, hRhi, hhi, hRc]
        · addr_omega [ha, hx, h0, hRhi, hhi, hRc])
      (by addr_omega [hb]) hn₁
  have hdF := hdr_keep X₁ (A := s.getReg .x2 - 464) (fun a ha hx ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hx, hb]
    · addr_omega [ha, hx, hb, hRhi, hhi, hRc]) (by addr_omega [hb])
  have hdR := hdr_keep X₁ (A := s.getReg .x2 - 384) (fun a ha hx ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hx, hb]
    · addr_omega [ha, hx, hb, hRhi, hhi, hRc]) (by addr_omega [hb])
  have ap₁ : Apart (vecPtr t₁ (s.getReg .x2 - 464)) ((vecCap t₁ (s.getReg .x2 - 464)).toNat * 8)
      (vecPtr t₁ (s.getReg .x2 - 384)) ((vecCap t₁ (s.getReg .x2 - 384)).toNat * 8) := by
    rw [hdF.1, hdF.2, hdR.1, hdR.2]; exact hap
  have x24₁ : t₁.getReg .x24 = BitVec.ofNat 64 (i + 3) := by
    rw [b8000a088_x24 h₁, h.x8]; addr_omega [hlt, hK0]
  have hcF : (vecCap t₁ (s.getReg .x2 - 464)).toNat = (vecCap u (s.getReg .x2 - 464)).toNat := by
    rw [hdF.2]
  by_cases hroom : i + 2 < (vecCap u (s.getReg .x2 - 464)).toNat
  · refine ⟨t₁, hr₁, Or.inr {
      toSince := S₁
      toKept := K₁
      folds := F₁
      rates := R₁
      apart := ap₁
      pc := b8000a088_pc_taken h₁ (by
        rw [h.x8, hsp]; rv_eval []; intro h0
        have := congrArg BitVec.toNat h0
        have e : (vecCap u (s.getReg .x2 - 464)).toNat = (u.getMem (s.getReg .x2 - 464)).toNat := rfl
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        omega)
      lt := hlt
      x18 := by rw [k₁ .x18 (by decide), h.x18]
      x19 := by rw [k₁ .x19 (by decide), h.x19, hdR.1]
      x20 := by rw [k₁ .x20 (by decide), h.x20]
      x21 := by rw [k₁ .x21 (by decide), h.x21]
      x22 := by rw [k₁ .x22 (by decide), h.x22]
      x23 := by rw [k₁ .x23 (by decide), h.x23]
      x24 := x24₁
      room := by rw [hcF]; exact hroom }⟩
  have heq : (vecCap u (s.getReg .x2 - 464)).toNat = i + 2 := by omega
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a0a8_spec
    (b8000a088_pc_not_taken h₁ (by
      rw [h.x8, hsp]; rv_eval []
      apply BitVec.eq_of_toNat_eq
      have e : (vecCap u (s.getReg .x2 - 464)).toNat = (u.getMem (s.getReg .x2 - 464)).toNat := rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega)) trivial
  have k₂ := b8000a0a8_keeps h₂
  have hm₂ := b8000a0a8_mem_same h₂
  have S₂ := S₁.same hm₂ (fun r hr ↦ k₂ r (Runtime.mem_of_mem hr _))
  have K₂ := K₁.step hpre (DFrame.of_same hm₂ (fun _ ↦ False)) fun _ h ↦ h.elim
  obtain ⟨t₃, hr₃, hv₃⟩ := grow8 hG hpre S₂ K₂ (b8000a0a8_pc h₂) (Or.inr ⟨rfl, rfl⟩)
    (by rw [b8000a0a8_x10 h₂, S₁.sp]; rv_eval []) (F₁.same hm₂ (by addr_omega [hb]))
    (R₁.same hm₂ (by addr_omega [hb]))
  rcases hv₃ with hd | ⟨hpc₃, hpres₃, S₃, K₃, F₃, R₃, hcap₃, hap₃, hRe₃⟩
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a0b4_spec
    (by rw [hpc₃, returnAddress_eq, b8000a0a8_x1 h₂]; decide) trivial
  have k₄ := b8000a0b4_keeps h₄
  have hm₄ := b8000a0b4_mem_same h₄
  have hreg (r : Reg) (hr : r ∈ [Reg.x18, .x19, .x20, .x21, .x22, .x23, .x24]) :
      t₄.getReg r = t₁.getReg r := by
    rw [k₄ r (Runtime.mem_of_mem hr _),
      hpres₃ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _),
      k₂ r (Runtime.mem_of_mem hr _)]
  have hcap₂ : (vecCap t₂ (s.getReg .x2 - 464)).toNat = i + 2 := by
    rw [show vecCap t₂ (s.getReg .x2 - 464) = vecCap t₁ (s.getReg .x2 - 464) from hm₂ _, hcF]
    exact heq
  have hp4 (A : Word) : vecPtr t₄ A = vecPtr t₃ A := hm₄ _
  have hc4 (A : Word) : vecCap t₄ A = vecCap t₃ A := hm₄ _
  refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr {
    toSince := S₃.same hm₄ (fun r hr ↦ k₄ r (Runtime.mem_of_mem hr _))
    toKept := K₃.step hpre (DFrame.of_same hm₄ (fun _ ↦ False)) fun _ h ↦ h.elim
    folds := F₃.same hm₄ (by addr_omega [hb])
    rates := R₃.same hm₄ (by addr_omega [hb])
    apart := by rw [hp4, hp4, hc4, hc4]; simp only [Apart]; omega
    pc := b8000a0b4_pc h₄
    lt := hlt
    x18 := by rw [hreg .x18 (by decide), k₁ .x18 (by decide), h.x18]
    x19 := by
      rw [hreg .x19 (by decide), k₁ .x19 (by decide), h.x19, hp4, hRe₃,
        show vecPtr t₂ (s.getReg .x2 - 384) = vecPtr t₁ (s.getReg .x2 - 384) from hm₂ _, hdR.1]
    x20 := by rw [hreg .x20 (by decide), k₁ .x20 (by decide), h.x20]
    x21 := by rw [hreg .x21 (by decide), k₁ .x21 (by decide), h.x21]
    x22 := by rw [hreg .x22 (by decide), k₁ .x22 (by decide), h.x22]
    x23 := by rw [hreg .x23 (by decide), k₁ .x23 (by decide), h.x23]
    x24 := by rw [hreg .x24 (by decide), x24₁]
    room := by rw [hc4]; omega }⟩

theorem neg_add_two : ∀ k < 5, ∀ j < 9,
    ((0 - BitVec.ofNat 64 k) + BitVec.ofNat 64 j = 2 ↔ j = k + 2) := by
  decide +kernel

theorem lad_fold {s b u : MachineState} {nxb QP QL : Word} {i : ℕ} (hpre : VsoPre s)
    (hc : Cfg s QP QL) (h : AtA040 s b u nxb QP QL i) :
    ∃ v, Reaches Image.code u v ∧ ((i + 1 < K0 s ∧ Lad s b v nxb QP QL (i + 1)) ∨
      (i + 1 = K0 s ∧ LadEnd s b v nxb QP QL)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := h.sp
  have hn := hc.logN
  have hK0 : K0 s ≤ 4 := by simp only [K0]; omega
  have hlt := h.lt
  have hF := h.folds
  have hR := h.rates
  have hFn := hF.len
  rw [lwF_len] at hFn
  have hFc := h.room
  have hFhi := hF.hi
  have hRhi := hR.hi
  have hF8 := hF.vec.raw.1
  have hhi := h.heap.hi
  have hlo := hpre.heap.lo
  have hmb := h.bat.inv.mono
  have hs : heapStart ≤ nxb.toNat := by simp only [heapNext] at hlo hmb; omega
  have hFlo := hF.lo
  have hap := h.apart
  have hFr : Region (vecPtr u (s.getReg .x2 - 464)) ((vecCap u (s.getReg .x2 - 464)).toNat * 8) :=
    heap_region (by simp only [heapStart] at hs; omega) (by simp only [heapNext] at hFhi hhi ⊢; omega) hF8
  have hF' : u.getMem (s.getReg .x2 - 456) = vecPtr u (s.getReg .x2 - 464) := by
    simp only [vecPtr]; rv_eval []
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a040_spec h.pc (by
    rv_eval [hsp, h.x21, hF']
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hFr (by addr_omega [hFhi, hhi, hFc])
          (by addr_omega [hFhi, hhi, hFc]) (by addr_omega [hF8, hFhi, hhi, hFc])
      | addr_omega [hb, hFhi, hhi, hFc])
  have k₁ := b8000a040_keeps h₁
  have X₁ : DFrame u t₁ fun a ↦ Within a (s.getReg .x2 - 448) 8 ∨
      Within a (vecPtr u (s.getReg .x2 - 464) + BitVec.ofNat 64 (8 * (i + 2))) 8 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a040, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [hsp, h.x21, hF'] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr (by addr_omega [hw, hFhi, hhi, hFc])
  have nx₁ : t₁.getMem nextAddr = u.getMem nextAddr := X₁ _ fun i' hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hFhi, hhi, hFc, hnx]
  have S₁ : Since s b t₁ nxb := h.toSince.blk X₁ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact RW.hdr (by addr_omega [ha, hb])
      · exact RW.heap ⟨by addr_omega [ha, hFlo, hFhi, hhi, hFc], by
          addr_omega [ha, hFhi, hhi, hFc]⟩)
    nx₁ (fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _))
  have K₁ : Kept s b t₁ QP QL := h.toKept.step hpre X₁ fun a ha hw ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hw, hb]
    · addr_omega [ha, hw, hb, hFhi, hhi, hFc]
  have hn₁ : heapNext u ≤ heapNext t₁ := by simp only [heapNext, nx₁]; exact Nat.le_refl _
  have F₁ : WVec t₁ (s.getReg .x2 - 464) nxb (lw (Model.Pcs.ladderFolds (i + 2))) := by
    rw [lwF_succ]
    refine hF.push X₁ (fun a ha ↦ ?_) (by rw [lwF_len]; omega) ?_ ?_
      (by addr_omega [hb]) (by addr_omega [hb]) hn₁ hhi
    · rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (by rw [lwF_len]; exact ha)
    · rw [lwF_len]
      have := b8000a040_m_x2_592 h₁
      rw [hsp, h.x24] at this
      rv_eval [] at this
      rv_eval [this]
    · rw [lwF_len]
      have := b8000a040_m1 h₁
      rw [hsp, h.x21, h.x20] at this
      rv_eval [hF'] at this
      rw [show vecPtr u (s.getReg .x2 - 464) + BitVec.ofNat 64 (8 * (i + 1 + 1)) =
          vecPtr u (s.getReg .x2 - 464) + BitVec.ofNat 64 (8 * i) + 16 by
        addr_omega [hFhi, hhi, hFc], this]
  have R₁ : WVec t₁ (s.getReg .x2 - 384) nxb
      (lw (Model.Pcs.ladderRates (s.getReg .x13).toNat (i + 2))) :=
    hR.keep X₁ (fun a ha ↦ by
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩ <;> rcases ha with ha | ha
      · addr_omega [ha, hx, hb]
      · addr_omega [ha, hx, hb, hFhi, hhi, hFc]
      · addr_omega [ha, hx, hb, hRhi, hhi]
      · simp only [Apart] at hap
        rcases hap with h0 | h0 | h0 | h0
        · addr_omega [h0, hFc]
        · addr_omega [hx, h0]
        · addr_omega [ha, hx, h0, hFhi, hhi, hFc]
        · addr_omega [ha, hx, h0, hFhi, hhi, hFc])
      (by addr_omega [hb]) hn₁
  have hdF := hdr_keep X₁ (A := s.getReg .x2 - 464) (fun a ha hx ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hx, hb]
    · addr_omega [ha, hx, hb, hFhi, hhi, hFc]) (by addr_omega [hb])
  have hdR := hdr_keep X₁ (A := s.getReg .x2 - 384) (fun a ha hx ↦ by
    rcases ha with ha | ha
    · addr_omega [ha, hx, hb]
    · addr_omega [ha, hx, hb, hFhi, hhi, hFc]) (by addr_omega [hb])
  have L₁ : Ladders s t₁ nxb (i + 2) := ⟨F₁, R₁, by rw [hdF.1, hdF.2, hdR.1, hdR.2]; exact hap⟩
  have x9₁ : t₁.getReg .x9 = vecPtr t₁ (s.getReg .x2 - 464) := by
    rw [b8000a040_x9 h₁, hsp, hdF.1]; rv_eval [hF']
  have x24 := h.x24
  have hiff := neg_add_two (K0 s) (by omega) (i + 3) (by omega)
  by_cases hk : i + 1 = K0 s
  · refine ⟨t₁, hr₁, Or.inr ⟨hk, {
      toSince := S₁
      toKept := K₁
      toLadders := by rw [← hk]; exact L₁
      pc := b8000a040_pc_taken h₁ (by rw [h.x22, h.x24, h.x23]; exact hiff.mpr (by omega))
      x9 := x9₁
      x18 := by rw [k₁ .x18 (by decide), h.x18] }⟩⟩
  refine ⟨t₁, hr₁, Or.inl ⟨by omega, {
    toSince := S₁
    toKept := K₁
    toLadders := L₁
    pc := b8000a040_pc_not_taken h₁ (by
      rw [h.x22, h.x24, h.x23]; intro h0; exact hk (by have := hiff.mp h0; omega))
    lt := by omega
    x8 := by rw [b8000a040_x8 h₁, h.x24]
    x9 := x9₁
    x18 := by rw [k₁ .x18 (by decide), h.x18]
    x19 := by rw [k₁ .x19 (by decide), h.x19, hdR.1]
    x20 := by rw [k₁ .x20 (by decide), h.x20]
    x21 := by rw [b8000a040_x21 h₁, h.x21]; addr_omega [hlt, hK0]
    x22 := by rw [k₁ .x22 (by decide), h.x22]
    x23 := by rw [k₁ .x23 (by decide), h.x23] }⟩⟩

theorem ladder_loop (hG : GrowOneFreshSpec 0x8000d7bc 8 8) {s b : MachineState}
    {nxb QP QL : Word} (hpre : VsoPre s) (hc : Cfg s QP QL) :
    ∀ (n i : ℕ) (u : MachineState), i + n = K0 s → Lad s b u nxb QP QL i →
      ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ LadEnd s b v nxb QP QL)
  | 0, i, u, hn, h => absurd h.lt (by omega)
  | n + 1, i, u, hn, h => by
    obtain ⟨v₁, hr₁, hv₁⟩ := lad_read hG hpre hc h
    rcases hv₁ with hd | hv₁
    · exact ⟨v₁, hr₁, Or.inl hd⟩
    obtain ⟨v₂, hr₂, hv₂⟩ := lad_rate hG hpre hc hv₁
    rcases hv₂ with hd | hv₂
    · exact ⟨v₂, hr₁.trans hr₂, Or.inl hd⟩
    obtain ⟨v₃, hr₃, hv₃⟩ := lad_fold hpre hc hv₂
    rcases hv₃ with ⟨_, hv₃⟩ | ⟨_, hv₃⟩
    · obtain ⟨w, hw, hw'⟩ := ladder_loop hG hpre hc n (i + 1) v₃ (by omega) hv₃
      exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans hw)), hw'⟩
    · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr hv₃⟩

end Rv64Verifier.Proofs.Pcs.Vso
