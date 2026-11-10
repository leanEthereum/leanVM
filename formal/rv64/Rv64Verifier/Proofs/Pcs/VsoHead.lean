import Rv64Verifier.Proofs.Pcs.VsoBase

/-!
# `verify_stacked_opening`: the claims' values, the scales, the target

```rust
let values: Vec<E> = claims.iter().map(|claim| claim.value).collect();
let scales = powers(transcript.sample(), claims.len());
let target = dot(&scales, &values);
```

`0x80009db8` calls `try_allocate_in(S - 384, n, 0, 8, 24)`, `0x80009e24` traps on `Err`,
`0x80009e30` makes the `Vec` at `S - 384` and calls `reserve(S - 384, n)`, which has room;
`0x80009e54` takes the buffer `VP` (`s7`) and skips the copy for no claims; the loop at
`0x80009e8c` copies claim `j`'s value (at `+64`) to `VP + 24 j`. `0x80009eb0` calls `duplex` on the
sponge, `0x80009ec0` copies the first three lanes to `S - 384` and calls
`powers(S - 776, S - 384, n)`, `0x80009eec` calls `dot(S - 752, scales, values)`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The number of claims. -/
@[rv_addr] def ncl (s : MachineState) : Nat := (s.getReg .x15).toNat

/-- Claim `j`'s address. -/
@[rv_addr] def claimAddr (s : MachineState) (j : Nat) : Word :=
  s.getReg .x14 + BitVec.ofNat 64 (88 * j)

/-- The claims' values. -/
def valuesOf (s : MachineState) : List E :=
  (claimsAt s (s.getReg .x14) (ncl s)).map (·.value)

theorem trap : Image.code.fetch 0x8000bfd4 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- The registers the function keeps from its arguments. -/
structure Args (s u : MachineState) : Prop where
  x8 : u.getReg .x8 = s.getReg .x11
  x20 : u.getReg .x20 = s.getReg .x15
  x21 : u.getReg .x21 = s.getReg .x13
  x22 : u.getReg .x22 = s.getReg .x14
  x26 : u.getReg .x26 = s.getReg .x12
  x27 : u.getReg .x27 = s.getReg .x10

theorem Args.of_eq {s u v : MachineState} (h : Args s u)
    (hr : ∀ r ∈ [Reg.x8, .x20, .x21, .x22, .x26, .x27], v.getReg r = u.getReg r) : Args s v where
  x8 := (hr _ (by decide)).trans h.x8
  x20 := (hr _ (by decide)).trans h.x20
  x21 := (hr _ (by decide)).trans h.x21
  x22 := (hr _ (by decide)).trans h.x22
  x26 := (hr _ (by decide)).trans h.x26
  x27 := (hr _ (by decide)).trans h.x27

/-- The values' buffer `VP`, of `n` elements, allocated below `nx`. -/
structure VBuf (s : MachineState) (VP nx : Word) : Prop where
  align : VP.toNat % 8 = 0
  range : ncl s = 0 ∨ (heapNext s ≤ VP.toNat ∧ VP.toNat + 24 * ncl s ≤ nx.toNat)

/-- At `0x80009e54`, the empty `Vec` at `S - 384` with room for every value. -/
structure Reserved (s u : MachineState) (nx VP : Word) : Prop extends Args s u where
  inv : Inv0 s u nx
  pc : u.pc = 0x80009e54
  ptr : u.getMem (s.getReg .x2 - 376) = VP
  len : u.getMem (s.getReg .x2 - 368) = 0
  buf : VBuf s VP nx

theorem setup (hT : TryAllocZeroedSpec) {s : MachineState} (hpc : s.pc = 0x80009db8)
    (hpre : VsoPre s) :
    ∃ u, Reaches Image.code s u ∧ (Dead Image.code u ∨ ∃ nx VP, Reserved s u nx VP) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009db8_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80009db8_keeps h₁
  have hm₁ := b80009db8_frame h₁ (by omega)
  have inv₁ : Inv0 s t₁ (s.getMem nextAddr) := {
    sp := b80009db8_x2 h₁
    slots := by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b80009db8_m_x2_n8 h₁, b80009db8_m_x2_n16 h₁, b80009db8_m_x2_n24 h₁,
        b80009db8_m_x2_n32 h₁, b80009db8_m_x2_n40 h₁, b80009db8_m_x2_n48 h₁,
        b80009db8_m_x2_n56 h₁, b80009db8_m_x2_n64 h₁, b80009db8_m_x2_n72 h₁,
        b80009db8_m_x2_n80 h₁, b80009db8_m_x2_n88 h₁, b80009db8_m_x2_n96 h₁,
        b80009db8_m_x2_n104 h₁⟩
    kept := fun _ hr ↦ by cases hr
    mem := (DFrame.of_memFrame hm₁).mono fun a ha ↦ Or.inr (Or.inl (by
      simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
        shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack, stackLo]
      addr_omega [ha, hb]))
    next := hm₁ _ (by addr_omega [hb, hnx8])
    mono := Nat.le_refl _
    fits := hheap.hi }
  have args₁ : Args s t₁ := ⟨b80009db8_x8 h₁, b80009db8_x20 h₁, b80009db8_x21 h₁,
    b80009db8_x22 h₁, b80009db8_x26 h₁, b80009db8_x27 h₁⟩
  -- `try_allocate_in`
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := inv₁.sp
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 384 := b80009db8_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = s.getReg .x2 - 1088 := by
    simp only [stackLo, tryAllocStack, hsp₁]; rv_eval []
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b80009db8_x13 h₁]; decide
    size := by rw [b80009db8_x14 h₁]; decide
    stack := hst.sub 1040 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b80009db8_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have hfit₂ := hpost₂.heap.hi
  have inv₂ : Inv0 s t₂ (t₂.getMem nextAddr) := Inv.step' hpre inv₁ (DFrame.of_byteFrame hfr₂)
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact frame_wr hpre (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl (by
          simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack,
            nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack,
            keccakFStack, memStack, stackLo]
          addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨hn₁ ▸ ha.1, ha.2⟩)))
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx8]
      · simp only [Fresh] at ha; addr_omega [ha, hb, hab, hfit₂])
    rfl (by have := hpost₂.mono; simp only [heapNext] at this hn₁ ⊢; omega) hfit₂
    (hpres₂.reg .x2)
  have args₂ : Args s t₂ := args₁.of_eq fun r hr ↦ hpres₂ r (by
    simp only [calleeSaved]; exact Runtime.mem_of_mem hr _)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := inv₂.sp
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009e24_spec
    (by rw [hpc₂, returnAddress_eq, b80009db8_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 384)) 0 with htag | htag
  swap
  · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009e2c_spec
      (b80009e24_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)) trivial
    exact ⟨t₄, hr₂.trans (hr₃.trans hr₄), Or.inl (dead_of_fetch (by rw [b80009e2c_pc h₄]; exact trap))⟩
  have k₃ := b80009e24_keeps h₃
  have hm₃ := b80009e24_mem_same h₃
  have inv₃ := inv₂.same' hm₃ (k₃ .x2 (by decide))
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁, b80009db8_x11 h₁, b80009db8_x14 h₁, b80009db8_x13 h₁] at hbuf
  rw [hx10₁, b80009db8_x11 h₁] at hcap
  rv_eval [] at hbuf hcap
  obtain ⟨VP, hVP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 368) := ⟨_, rfl⟩
  rw [← hVP] at hbuf
  have hBuf : VBuf s VP (t₂.getMem nextAddr) := {
    align := hbuf.1
    range := by
      rcases hbuf.2 with h | h
      · exact Or.inl (by simp only [ncl]; omega)
      · exact Or.inr ⟨hn₁ ▸ h.1, by simp only [ncl, heapNext] at h ⊢; omega⟩ }
  -- the `Vec`, and `reserve` with room
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := inv₃.sp
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009e30_spec
    (b80009e24_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b80009e30_keeps h₄
  have hm₄ := b80009e30_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rw [hsp₃] at hm₄
  rv_eval [] at hm₄
  have inv₄ : Inv0 s t₄ (t₂.getMem nextAddr) := Inv.step' hpre inv₃ (DFrame.of_memFrame hm₄)
    (fun a ha ↦ frame_wr hpre (by addr_omega [ha, hb]))
    (fun a ha ↦ by addr_omega [ha, hb])
    ((hm₄ _ (by addr_omega [hb, hnx8])).trans inv₃.next) (Nat.le_refl _) inv₃.fits
    (k₄ .x2 (by decide))
  have v₀ := b80009e30_m_x2_656 h₄
  have v₁ := b80009e30_m_x2_664 h₄
  have v₂ := b80009e30_m_x2_672 h₄
  rw [hsp₃] at v₀ v₁ v₂
  rv_eval [hm₃] at v₀ v₁ v₂
  obtain ⟨t₅, hr₅, hpc₅, hpres₅, -, hm₅⟩ := MultilinearWords.reserve_fast (b80009e30_pc h₄)
    (by rw [b80009e30_x10 h₄, hsp₃]; rv_eval []; valid_sub hst.valid [hb]) (by
      rw [b80009e30_x10 h₄, b80009e30_x11 h₄, hsp₃]
      rv_eval [v₀, v₂, k₃ .x20 (by decide), args₂.x20, hcap]
      simp)
  have inv₅ := inv₄.same' hm₅ (hpres₅.reg .x2)
  refine ⟨t₅, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr ⟨_, VP, {
    toArgs := args₂.of_eq fun r hr ↦ by
      rw [hpres₅ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _),
        k₄ r (Runtime.mem_of_mem hr _), k₃ r (Runtime.mem_of_mem hr _)]
    inv := inv₅
    pc := by rw [hpc₅, returnAddress_eq, b80009e30_x1 h₄]; decide
    ptr := by rw [hm₅, v₁, hVP]
    len := by rw [hm₅, v₂]
    buf := hBuf }⟩⟩

/-! ## The values -/

/-- A word of a region read, apart from the transcript's mutable part, keeps its value. -/
theorem Inv.keep {s u : MachineState} {nx : Word} {w : Word → Prop} (h : InvW w s u nx) {a : Word}
    {n : Nat} (hs : Src s vsoStack a n) (hw : ∀ z, Within z a n → ¬ w z) {x : Word}
    (h1 : a.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ a.toNat + n) : u.getMem x = s.getMem x := by
  rcases hs.bound with h0 | h0
  · omega
  · exact DFrame.word h.mem (fun y hy ↦ hs.miss hw h.fits y (by addr_omega [hy, h1, h2, h0]))
      (by addr_omega [h1, h2, h0])

theorem claims_region {s : MachineState} (hpre : VsoPre s) (hn : 0 < ncl s) :
    Region (s.getReg .x14) (88 * ncl s) :=
  hpre.claims.region.resolve_left (by simp only [ncl] at hn; omega)

/-- At `0x80009e8c`, claim `j`'s value next, those before it copied. -/
structure Copying (s u : MachineState) (nx VP : Word) (j : Nat) : Prop extends Args s u where
  inv : Inv0 s u nx
  pc : u.pc = 0x80009e8c
  lt : j < ncl s
  x10 : u.getReg .x10 = claimAddr s j + 64
  x11 : u.getReg .x11 = VP + BitVec.ofNat 64 (24 * j)
  x12 : u.getReg .x12 = VP + BitVec.ofNat 64 (24 * ncl s)
  x23 : u.getReg .x23 = VP
  x24 : u.getReg .x24 = s.getReg .x15
  buf : VBuf s VP nx
  vals : ∀ i < j, eAt u (VP + BitVec.ofNat 64 (24 * i)) = eAt s (claimAddr s i + 64)

/-- At `0x80009eb0`, every value copied. -/
structure Copied (s u : MachineState) (nx VP : Word) : Prop extends Args s u where
  inv : Inv0 s u nx
  pc : u.pc = 0x80009eb0
  x23 : u.getReg .x23 = VP
  x24 : u.getReg .x24 = s.getReg .x15
  buf : VBuf s VP nx
  vals : ∀ i < ncl s, eAt u (VP + BitVec.ofNat 64 (24 * i)) = eAt s (claimAddr s i + 64)

theorem copy_step {s u : MachineState} {nx VP : Word} {j : Nat} (hpre : VsoPre s)
    (h : Copying s u nx VP j) :
    ∃ v, Reaches Image.code u v ∧
      ((j + 1 < ncl s ∧ Copying s v nx VP (j + 1)) ∨ (j + 1 = ncl s ∧ Copied s v nx VP)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hk := h.lt
  have hCr := claims_region hpre (by omega)
  have hC := Region.bounds hCr
  have hPa := h.buf.align
  have hPr := h.buf.range.resolve_left (by omega)
  have hfit := h.inv.fits
  have hlo := hpre.heap.lo
  have hHr := heap_region (a := VP) (n := 24 * ncl s) (by simp only [heapStart] at hlo; omega)
    (by omega) hPa
  have hO := hpre.claims.free
  simp only [Outside] at hO
  simp only [ncl] at hk hPr hHr hCr hO hC
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80009e8c_spec h.pc (by
    rv_eval [h.x10, h.x11]
    simp only [claimAddr]
    and_intros <;> first
      | exact Region.valid hCr (by addr_omega [hC, hk]) (by addr_omega [hC, hk])
          (by addr_omega [hC, hk])
      | exact Region.valid hHr (by addr_omega [hPr, hk, hfit]) (by addr_omega [hPr, hk, hfit])
          (by addr_omega [hPa, hPr, hk, hfit])
      | (rcases hO.1 with hO1 | hO1 <;> addr_omega [hC, hk, hPr, hfit, hO1]))
  have k₁ := b80009e8c_keeps ht
  have hm := b80009e8c_frame ht (by rw [h.x11]; addr_omega [hPr, hk, hfit])
  rw [h.x11] at hm
  have inv : Inv0 s t nx := Inv.step' (nx' := nx) hpre h.inv (DFrame.of_memFrame hm)
    (fun a ha ↦ Or.inr (Or.inr (Or.inr (by addr_omega [ha, hPr, hk, hfit]))))
    (fun a ha ↦ by addr_omega [ha, hPr, hk, hfit, hab, hb])
    ((hm _ (by addr_omega [hPr, hk, hfit])).trans h.inv.next) (Nat.le_refl _) hfit
    (k₁ .x2 (by decide))
  have hc (o : Nat) (ho : o + 8 ≤ 24) : u.getMem (claimAddr s j + 64 + BitVec.ofNat 64 o) =
      s.getMem (claimAddr s j + 64 + BitVec.ofNat 64 o) :=
    Inv.keep h.inv hpre.claims (fun _ _ h ↦ h) (by simp only [claimAddr]; addr_omega [hC, hk, ho])
      (by simp only [claimAddr]; addr_omega [hC, hk, ho])
  have hnew : eAt t (VP + BitVec.ofNat 64 (24 * j)) = eAt s (claimAddr s j + 64) := by
    have m0 := b80009e8c_m_x11_0 ht
    have m1 := b80009e8c_m_x11_8 ht
    have m2 := b80009e8c_m_x11_16 ht
    rw [h.x11, h.x10] at m0 m1 m2
    have c0 := hc 0 (by decide)
    have c1 := hc 8 (by decide)
    have c2 := hc 16 (by decide)
    rv_eval [] at m0 m1 m2 c0 c1 c2
    unfold eAt
    rv_eval [m0, m1, m2, c0, c1, c2]
  have hvals (i : Nat) (hi : i < j + 1) :
      eAt t (VP + BitVec.ofNat 64 (24 * i)) = eAt s (claimAddr s i + 64) := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hm.eAt (p := VP + BitVec.ofNat 64 (24 * i)) (by addr_omega [hi, hk, hPr, hfit])
        (by addr_omega [hi, hk, hPr, hfit])]
      exact h.vals i hi
    · exact hnew
  have args := h.toArgs.of_eq fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _)
  have x10 : t.getReg .x10 = claimAddr s (j + 1) + 64 := by
    rw [b80009e8c_x10 ht, h.x10]; simp only [claimAddr]; addr_omega [hC, hk]
  have x11 : t.getReg .x11 = VP + BitVec.ofNat 64 (24 * (j + 1)) := by
    rw [b80009e8c_x11 ht, h.x11]; addr_omega [hPr, hk, hfit]
  by_cases hj : j + 1 < ncl s
  · refine ⟨t, hr, Or.inl ⟨hj, {
      toArgs := args
      inv := inv
      lt := hj
      x10 := x10
      x11 := x11
      x12 := by rw [k₁ .x12 (by decide), h.x12]
      x23 := by rw [k₁ .x23 (by decide), h.x23]
      x24 := by rw [k₁ .x24 (by decide), h.x24]
      buf := h.buf
      vals := hvals
      pc := b80009e8c_pc_taken ht (by
        rw [h.x11, h.x12]
        simp only [ncl] at hj
        addr_omega [hPr, hk, hfit, hj]) }⟩⟩
  · have hj' : j + 1 = ncl s := by simp only [ncl] at hj ⊢; omega
    refine ⟨t, hr, Or.inr ⟨hj', {
      toArgs := args
      inv := inv
      x23 := by rw [k₁ .x23 (by decide), h.x23]
      x24 := by rw [k₁ .x24 (by decide), h.x24]
      buf := h.buf
      vals := fun i hi ↦ hvals i (by omega)
      pc := b80009e8c_pc_not_taken ht (by
        rw [h.x11, h.x12, ← hj']
        addr_omega [hPr, hk, hfit]) }⟩⟩

theorem copy_loop {s : MachineState} {nx VP : Word} (hpre : VsoPre s) :
    ∀ (k j : Nat) (u : MachineState), j + k = ncl s → Copying s u nx VP j →
      ∃ v, Reaches Image.code u v ∧ Copied s v nx VP
  | 0, j, u, hk, h => absurd h.lt (by omega)
  | k + 1, j, u, hk, h => by
    obtain ⟨v, huv, hv⟩ := copy_step hpre h
    rcases hv with ⟨_, hv⟩ | ⟨_, hv⟩
    · obtain ⟨w, hvw, hw⟩ := copy_loop hpre k (j + 1) v (by omega) hv
      exact ⟨w, huv.trans hvw, hw⟩
    · exact ⟨v, huv, hv⟩

/-- **The values**: from `0x80009e54`, every claim's value copied to the buffer. -/
theorem copy {s u : MachineState} {nx VP : Word} (hpre : VsoPre s) (h : Reserved s u nx VP) :
    ∃ v, Reaches Image.code u v ∧ Copied s v nx VP := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.inv.sp
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80009e54_spec h.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80009e54_keeps ht
  have hm := b80009e54_mem_same ht
  have inv := h.inv.same' hm (k₁ .x2 (by decide))
  have args := h.toArgs.of_eq fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _)
  have x23 : t.getReg .x23 = VP := by rw [b80009e54_x23 ht, hsp]; rv_eval [h.ptr]
  have x24 : t.getReg .x24 = 0 := by rw [b80009e54_x24 ht, hsp]; rv_eval [h.len]
  by_cases h0 : s.getReg .x15 = 0
  · have hn0 : ncl s = 0 := by simp only [ncl, h0]; rfl
    exact ⟨t, hr, {
      toArgs := args
      inv := inv
      x23 := x23
      buf := h.buf
      x24 := by rw [x24, h0]
      vals := fun i hi ↦ by omega
      pc := b80009e54_pc_taken ht (by rw [h.x20]; exact h0) }⟩
  have hn0 : 0 < ncl s := by
    simp only [ncl]
    rcases Nat.eq_zero_or_pos (s.getReg .x15).toNat with h' | h'
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h')) h0
    · exact h'
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009e60_spec
    (b80009e54_pc_not_taken ht (by rw [h.x20]; exact h0)) trivial
  have k₂ := b80009e60_keeps h₂
  have hm₂ := b80009e60_mem_same h₂
  have hPr := h.buf.range.resolve_left (by omega)
  have hfit := h.inv.fits
  simp only [ncl] at hPr
  obtain ⟨v, hv, hvv⟩ := copy_loop hpre (ncl s) 0 t₂ (by omega) {
    toArgs := args.of_eq fun r hr ↦ k₂ r (Runtime.mem_of_mem hr _)
    inv := inv.same' hm₂ (k₂ .x2 (by decide))
    pc := b80009e60_pc h₂
    lt := hn0
    x10 := by rw [b80009e60_x10 h₂, args.x22]; simp [claimAddr]
    x11 := by rw [b80009e60_x11 h₂, x23, x24]; simp
    x12 := by
      rw [b80009e60_x12 h₂, x23, x24, k₁ .x20 (by decide), h.x20]
      simp only [ncl]
      rv_eval []
      addr_omega [hPr, hfit]
    x23 := by rw [k₂ .x23 (by decide), x23]
    x24 := by rw [b80009e60_x24 h₂, x24, k₁ .x20 (by decide), h.x20]; simp
    buf := h.buf
    vals := fun i hi ↦ by omega }
  exact ⟨v, hr.trans (hr₂.trans hv), hvv⟩

end Rv64Verifier.Proofs.Pcs.Vso
