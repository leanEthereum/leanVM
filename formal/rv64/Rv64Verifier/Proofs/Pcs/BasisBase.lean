import Rv64Verifier.Proofs.Pcs.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.EqEval
import Rv64Verifier.Blocks.F55

/-!
# `<StackBasis>::evaluate`

```rust
fn evaluate(&self, point: &[E]) -> E {
    let weights: Vec<E> = self.claims.iter().map(|claim| claim.weight.evaluate(point)).collect();
    dot(&self.scales, &weights)
}
```

compiled at `0x8000d0a4` (`Blocks/F55.lean`), with `S` the entry's `sp`, `n` the number of claims:
`0x8000d0a4` saves `ra`, `s0`..`s10` in a 192-byte frame and calls
`try_allocate_in(S - 120, n, 0, 8, 24)`; `0x8000d10c` traps on `Err`; `0x8000d114` makes the
`Vec` at `S - 192` and calls `reserve(S - 192, n)`, which has room; `0x8000d138` takes the buffer
`WP` (`s6`) and goes to the end for no claims. The loop at `0x8000d1ac`, `s4` walking the claims,
`s9` the weights, dispatches on the claim's tag: `Eq` at `0x8000d164` (`eq_eval` into `S - 168`),
`Ring` at `0x8000d1cc` (`RingWeight::evaluate` into `S - 168`), `PlacedRing` at `0x8000d1e8`
(`eq_above` into `S - 144`, the bound check at `0x8000d204`, `RingWeight::evaluate` into `S - 120`
on the point's first `variables` coordinates, `mul` into `S - 168`); `0x8000d180` pushes the
weight. `0x8000d238` restores the registers and tail-calls `dot(out, scales, weights)`.
-/

namespace Rv64Verifier.Proofs.Pcs.Basis
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F55
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Names -/

/-- The claims' pointer and count, the point. -/
@[rv_addr] def clp (s : MachineState) : Word := s.getMem (s.getReg .x11 + 24)
@[rv_addr] def ncl (s : MachineState) : Nat := (s.getMem (s.getReg .x11 + 32)).toNat
def ptl (s : MachineState) : List E := eListAt s (s.getReg .x12) (s.getReg .x13).toNat

/-- Claim `l`. -/
@[rv_addr] def claimAddr (s : MachineState) (l : Nat) : Word := clp s + BitVec.ofNat 64 (88 * l)

/-- Claim `l`'s weight, which the mirror evaluates at the point. -/
def weightOf (s : MachineState) (l : Nat) : Option E :=
  (stackClaimAt s (claimAddr s l)).weight.evaluate (ptl s)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19),
  (48, .x20), (56, .x21), (64, .x22), (72, .x23), (80, .x24), (88, .x25), (96, .x26)]

/-- Nothing besides the stack, `NEXT` and the heap is written before `dot`'s tail call. -/
abbrev Inv (s u : MachineState) (nx : Word) : Prop :=
  PInv s u 192 basisStack slots [.x27] (fun _ ↦ False) nx

theorem bounds {s : MachineState} (h : BasisPre s) :
    0x78000000 + 1392 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  simp only [basisStack, ringEvalStack, mulStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem Inv.step' {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : BasisPre s) (h : Inv s u nx) (hX : DFrame u v X)
    (hXsub : ∀ a, X a → Wr s basisStack (fun _ ↦ False) nx' a)
    (hXslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 96) 96)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) (hk : v.getReg .x27 = u.getReg .x27) : Inv s v nx' :=
  h.step 96 (by decide) (by have := bounds hpre; omega) hX hXsub hXslot hnx hle hend hsp
    (fun r hr ↦ by simp only [List.mem_singleton] at hr; subst hr; exact hk)

/-- A region read is never written. -/
theorem Inv.src {s u : MachineState} {nx : Word} (h : Inv s u nx) {a : Word} {n : Nat}
    (hs : Src s basisStack a n) : ∀ x, Within x a n → ¬ Wr s basisStack (fun _ ↦ False) nx x :=
  hs.miss (fun _ _ h ↦ h) h.fits

theorem Inv.rodata' {s u : MachineState} {nx : Word} (hpre : BasisPre s) (h : Inv s u nx) :
    RodataOk u :=
  h.rodata hpre.rodata (fun _ h ↦ h.elim) hpre.stack.rodata

theorem trap : Image.code.fetch 0x8000d288 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-! ## The loop's invariant -/

/-- Registers through the loop. -/
structure Regs (s u : MachineState) (WP : Word) (k : Nat) : Prop where
  x8 : u.getReg .x8 = s.getReg .x11
  x9 : u.getReg .x9 = s.getReg .x10
  x18 : u.getReg .x18 = s.getReg .x13
  x19 : u.getReg .x19 = s.getReg .x12
  x20 : u.getReg .x20 = claimAddr s k
  x21 : u.getReg .x21 = BitVec.ofNat 64 (ncl s - k)
  x22 : u.getReg .x22 = WP
  x23 : u.getReg .x23 = BitVec.ofNat 64 k
  x24 : u.getReg .x24 = 0x8000000000000000
  x25 : u.getReg .x25 = WP + BitVec.ofNat 64 (24 * k)
  x26 : u.getReg .x26 = 1

/-- The weights' buffer `WP`, of `n` elements, below `nx`. -/
structure BufOk (s : MachineState) (WP nx : Word) : Prop where
  align : WP.toNat % 8 = 0
  range : ncl s = 0 ∨ (heapNext s ≤ WP.toNat ∧ WP.toNat + 24 * ncl s ≤ nx.toNat)

/-- At `pc`, claim `k` next, the weights before it pushed. -/
structure Head (s u : MachineState) (nx WP : Word) (k : Nat) (pc : Word) : Prop
    extends Regs s u WP k where
  inv : Inv s u nx
  pc : u.pc = pc
  lt : k < ncl s
  buf : BufOk s WP nx
  ws : ∀ l < k, weightOf s l = some (eAt u (WP + BitVec.ofNat 64 (24 * l)))

/-- At `0x8000d180`, claim `k`'s weight at `S - 168`. -/
structure Got (s u : MachineState) (nx WP : Word) (k : Nat) : Prop extends Head s u nx WP k 0x8000d180 where
  w : weightOf s k = some (eAt u (s.getReg .x2 - 168))

/-- At `0x8000d238`, every weight pushed. -/
structure End (s u : MachineState) (nx WP : Word) : Prop where
  inv : Inv s u nx
  pc : u.pc = 0x8000d238
  x8 : u.getReg .x8 = s.getReg .x11
  x9 : u.getReg .x9 = s.getReg .x10
  x22 : u.getReg .x22 = WP
  x23 : u.getReg .x23 = BitVec.ofNat 64 (ncl s)
  buf : BufOk s WP nx
  ws : ∀ l < ncl s, weightOf s l = some (eAt u (WP + BitVec.ofNat 64 (24 * l)))

/-! ## The prologue, the allocation and the `Vec` -/

theorem setup (hT : TryAllocZeroedSpec) {s : MachineState} (hpc : s.pc = 0x8000d0a4)
    (hpre : BasisPre s) :
    ∃ u, Reaches Image.code s u ∧ (Dead Image.code u ∨
      ∃ nx WP, End s u nx WP ∨ Head s u nx WP 0 0x8000d1ac) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hheap := hpre.heap
  have hSB := hpre.self.stack
  have hBr := hpre.self.region.resolve_left (by decide)
  have hBb := Region.bounds hBr
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d0a4_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hBr (by addr_omega [hBb]) (by addr_omega [hBb]) (by addr_omega [hBb])
      | addr_omega [hBb, hb, hSB])
  have k₁ := b8000d0a4_keeps h₁
  have hm₁ := b8000d0a4_frame h₁ (by omega)
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := {
    sp := b8000d0a4_x2 h₁
    slots := by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000d0a4_m_x2_n8 h₁, b8000d0a4_m_x2_n16 h₁, b8000d0a4_m_x2_n24 h₁,
        b8000d0a4_m_x2_n32 h₁, b8000d0a4_m_x2_n40 h₁, b8000d0a4_m_x2_n48 h₁,
        b8000d0a4_m_x2_n56 h₁, b8000d0a4_m_x2_n64 h₁, b8000d0a4_m_x2_n72 h₁,
        b8000d0a4_m_x2_n80 h₁, b8000d0a4_m_x2_n88 h₁, b8000d0a4_m_x2_n96 h₁⟩
    kept := fun r hr ↦ by simp only [List.mem_singleton] at hr; subst hr; exact k₁ _ (by decide)
    mem := (DFrame.of_memFrame hm₁).mono fun a ha ↦
      Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
    next := hm₁ _ (by addr_omega [hb, hnx8])
    mono := Nat.le_refl _
    fits := hheap.hi }
  -- `try_allocate_in`
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₁.sp
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 120 := b8000d0a4_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = s.getReg .x2 - 240 := by
    simp only [stackLo, tryAllocStack, hsp₁]; rv_eval []
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b8000d0a4_x13 h₁]; decide
    size := by rw [b8000d0a4_x14 h₁]; decide
    stack := hst.sub 192 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b8000d0a4_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have hfit₂ := hpost₂.heap.hi
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := Inv.step' hpre inv₁ (DFrame.of_byteFrame hfr₂)
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨hn₁ ▸ ha.1, ha.2⟩)))
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx8]
      · simp only [Fresh] at ha; addr_omega [ha, hb, hab, hfit₂])
    rfl (by have := hpost₂.mono; simp only [heapNext] at this hn₁ ⊢; omega) hfit₂
    (hpres₂.reg .x2) (hpres₂.reg .x27)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₂.sp
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d10c_spec
    (by rw [hpc₂, returnAddress_eq, b8000d0a4_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 120)) 0 with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inl (dead_of_fetch ?_)⟩
    rw [b8000d10c_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)]
    exact trap
  have k₃ := b8000d10c_keeps h₃
  have hm₃ := b8000d10c_mem_same h₃
  have inv₃ := inv₂.same hm₃ (k₃ .x2 (by decide)) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact k₃ _ (by decide))
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁, b8000d0a4_x11 h₁, b8000d0a4_x14 h₁, b8000d0a4_x13 h₁] at hbuf
  rw [hx10₁, b8000d0a4_x11 h₁] at hcap
  rv_eval [] at hbuf hcap
  obtain ⟨WP, hWP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 104) := ⟨_, rfl⟩
  rw [← hWP] at hbuf
  have hBuf : BufOk s WP (t₂.getMem nextAddr) := {
    align := hbuf.1
    range := by
      rcases hbuf.2 with h | h
      · exact Or.inl (by simp only [ncl]; omega)
      · exact Or.inr ⟨hn₁ ▸ h.1, by simp only [ncl, heapNext] at h ⊢; omega⟩ }
  -- the `Vec`, and `reserve` with room
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₃.sp
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000d114_spec
    (b8000d10c_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000d114_keeps h₄
  have hm₄ := b8000d114_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rw [hsp₃] at hm₄
  rv_eval [] at hm₄
  have inv₄ := Inv.step' hpre inv₃ (DFrame.of_memFrame hm₄)
    (fun a ha ↦ Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb])))
    (fun a ha ↦ by addr_omega [ha, hb])
    ((hm₄ _ (by addr_omega [hb, hnx8])).trans inv₃.next) (Nat.le_refl _) inv₃.fits
    (k₄ .x2 (by decide)) (k₄ .x27 (by decide))
  have v₀ := b8000d114_m_x2_0 h₄
  have v₁ := b8000d114_m_x2_8 h₄
  have v₂ := b8000d114_m_x2_16 h₄
  rw [hsp₃] at v₀ v₁ v₂
  rv_eval [hm₃] at v₀ v₁ v₂
  have hn : t₁.getReg .x21 = s.getMem (s.getReg .x11 + 32) := b8000d0a4_x21 h₁
  obtain ⟨t₅, hr₅, hpc₅, hpres₅, -, hm₅⟩ := MultilinearWords.reserve_fast (b8000d114_pc h₄)
    (by rw [b8000d114_x10 h₄, hsp₃]; rv_eval []; valid_sub hst.valid [hb]) (by
      rw [b8000d114_x10 h₄, b8000d114_x11 h₄, hsp₃]
      rv_eval [v₀, v₂, k₃ .x21 (by decide), hpres₂.reg .x21, hn, hcap]
      simp)
  have inv₅ := inv₄.same hm₅ (hpres₅.reg .x2) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact hpres₅.reg .x27)
  -- the buffer and the count
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₅.sp
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000d138_spec
    (by rw [hpc₅, returnAddress_eq, b8000d114_x1 h₄]; decide) (by
      rv_eval [hsp₅]
      and_intros <;> valid_access hst.valid [hb])
  have k₆ := b8000d138_keeps h₆
  have hm₆ := b8000d138_mem_same h₆
  have inv₆ := inv₅.same hm₆ (k₆ .x2 (by decide)) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact k₆ _ (by decide))
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21]) :
      t₆.getReg r = t₁.getReg r := by
    rw [k₆ r (Runtime.mem_of_mem hr _), hpres₅ r (by unfold calleeSaved; exact Runtime.mem_of_mem hr _),
      k₄ r (Runtime.mem_of_mem hr _), k₃ r (Runtime.mem_of_mem hr _),
      hpres₂ r (by unfold calleeSaved; exact Runtime.mem_of_mem hr _)]
  have hx22 : t₆.getReg .x22 = WP := by rw [b8000d138_x22 h₆, hsp₅, hm₅]; rv_eval [v₁, hWP]
  have hx23 : t₆.getReg .x23 = 0 := by rw [b8000d138_x23 h₆, hsp₅, hm₅]; rv_eval [v₂]
  have hx21 : t₆.getReg .x21 = s.getMem (s.getReg .x11 + 32) := by
    rw [hreg .x21 (by decide), hn]
  have hx21₅ : t₅.getReg .x21 = s.getMem (s.getReg .x11 + 32) := by
    rw [hpres₅.reg .x21, k₄ .x21 (by decide), k₃ .x21 (by decide), hpres₂.reg .x21, hn]
  have hr₆' := hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))
  by_cases h0 : s.getMem (s.getReg .x11 + 32) = 0
  · have hn0 : ncl s = 0 := by simp only [ncl, h0]; rfl
    refine ⟨t₆, hr₆', Or.inr ⟨_, WP, Or.inl {
      inv := inv₆
      pc := b8000d138_pc_taken h₆ (by rw [hx21₅]; exact h0)
      x8 := by rw [hreg .x8 (by decide), b8000d0a4_x8 h₁]
      x9 := by rw [hreg .x9 (by decide), b8000d0a4_x9 h₁]
      x22 := hx22
      x23 := by rw [hx23, hn0]; rfl
      buf := hBuf
      ws := fun l hl ↦ by omega }⟩⟩
  have hn0 : 0 < ncl s := by
    simp only [ncl]
    rcases Nat.eq_zero_or_pos (s.getMem (s.getReg .x11 + 32)).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
    · exact h
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000d144_spec
    (b8000d138_pc_not_taken h₆ (by rw [hx21₅]; exact h0)) trivial
  have k₇ := b8000d144_keeps h₇
  refine ⟨t₇, hr₆'.trans hr₇, Or.inr ⟨_, WP, Or.inr {
    x8 := by rw [k₇ .x8 (by decide), hreg .x8 (by decide), b8000d0a4_x8 h₁]
    x9 := by rw [k₇ .x9 (by decide), hreg .x9 (by decide), b8000d0a4_x9 h₁]
    x18 := by rw [k₇ .x18 (by decide), hreg .x18 (by decide), b8000d0a4_x18 h₁]
    x19 := by rw [k₇ .x19 (by decide), hreg .x19 (by decide), b8000d0a4_x19 h₁]
    x20 := by rw [k₇ .x20 (by decide), hreg .x20 (by decide), b8000d0a4_x20 h₁]; simp [claimAddr, clp]
    x21 := by rw [k₇ .x21 (by decide), hx21]; simp [ncl]
    x22 := by rw [k₇ .x22 (by decide), hx22]
    x23 := by rw [k₇ .x23 (by decide), hx23]; rfl
    x24 := b8000d144_x24 h₇
    x25 := by rw [b8000d144_x25 h₇, hx22, hx23]; simp
    x26 := b8000d144_x26 h₇
    inv := inv₆.same (b8000d144_mem_same h₇) (k₇ .x2 (by decide)) (fun r hr ↦ by
      simp only [List.mem_singleton] at hr; subst hr; exact k₇ _ (by decide))
    pc := b8000d144_pc h₇
    lt := hn0
    buf := hBuf
    ws := fun l hl ↦ by omega }⟩⟩

end Rv64Verifier.Proofs.Pcs.Basis
