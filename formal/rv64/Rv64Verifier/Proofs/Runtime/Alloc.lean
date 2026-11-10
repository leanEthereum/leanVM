import Rv64Verifier.Proofs.Runtime.Contracts
import Rv64Verifier.Blocks.F2

/-!
# `Bump::alloc`

```rust
let start = NEXT.next_multiple_of(layout.align());
match start.checked_add(layout.size()) {
    Some(end) if end <= HEAP_END => { NEXT = end; start as *mut u8 }
    _ => halt(ABORT),
}
```

compiled at `0x80000284` (`Blocks/F2.lean`): `0x80000284` rounds `NEXT` up (`remu`, then
`align - rem` masked to zero when `rem = 0`) and adds the size, branching to the halt on a carry;
`0x800002ac` branches to it past `HEAP_END`; `0x800002b4` stores `NEXT` and returns; `0x800002bc`
sets `a0 = 2`, `t0 = 0` and reaches the `HALT` call at `0x800002c4`, a dead end (`dead_of_halt`).
-/

namespace Rv64Verifier.Runtime
open RiscvZkvm.Rv64 Rv64Verifier.Blocks.F2
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Halting -/

theorem halt_step_none {code : Code} {t : MachineState} (h : Halting code t) :
    step code t = none := by
  obtain ⟨hf, ht0⟩ := h
  have hx5 : ({ t with code := code.baseMap } : MachineState).getReg .x5 = 0 := ht0
  simp only [step, hf]
  simp only [RiscvZkvm.Rv64.step, Code.baseMap, hf]
  simp [hx5]

/-- The `HALT` call with a verdict other than `1` is a dead end. -/
theorem dead_of_halt {code : Code} {t : MachineState} (hf : code.fetch t.pc = some (.base .ECALL))
    (h5 : t.getReg .x5 = 0) (h10 : t.getReg .x10 ≠ 1) : Dead code t :=
  ⟨halt_step_none ⟨hf, h5⟩, fun _ ↦ h10⟩

/-! ## Rounding up -/

/-- The compiled `next_multiple_of`: `n` plus `align - n % align`, masked to zero when the
remainder is zero. -/
theorem nextMultiple {n al p : Word} (h0 : 0 < al.toNat)
    (hp : p = ((if (rv64_remu n al).ult 1 = true then 1 else 0) - 1 &&& al - rv64_remu n al) + n)
    (hn : n.toNat + al.toNat < 2 ^ 64) :
    p.toNat % al.toNat = 0 ∧ n.toNat ≤ p.toNat ∧ p.toNat < n.toNat + al.toNat := by
  have hne : (al == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h] at h0; simp at h0
  have hr : (rv64_remu n al).toNat = n.toNat % al.toNat := by
    rw [rv64_remu, hne]
    simp [BitVec.toNat_umod]
  have hlt := Nat.mod_lt n.toNat h0
  have hdiv := Nat.mod_add_div n.toNat al.toNat
  generalize n.toNat % al.toNat = r at hr hlt hdiv
  generalize n.toNat / al.toNat = q at hdiv
  have h1 : (1 : Word).toNat = 1 := rfl
  have hpn : p.toNat = n.toNat + (if r = 0 then 0 else al.toNat - r) := by
    subst hp
    by_cases hz : r = 0
    · have hu : (rv64_remu n al).ult 1 = true := by
        simp only [BitVec.ult, hr, hz, h1]; decide
      have hm : ∀ x : Word, ((if true = true then (1 : Word) else 0) - 1 &&& x) = 0 := by
        intro x; simp
      rw [hu, hm, BitVec.toNat_add]
      simp [hz, n.isLt]
    · have hu : (rv64_remu n al).ult 1 = false := by
        simp only [BitVec.ult, hr, h1, decide_eq_false_iff_not]; omega
      have hm : ∀ x : Word, ((if false = true then (1 : Word) else 0) - 1 &&& x) = x := by
        intro x
        rw [show ((if false = true then (1 : Word) else 0) - 1) = BitVec.allOnes 64 from rfl,
          BitVec.allOnes_and]
      rw [hu, hm, BitVec.toNat_add, BitVec.toNat_sub, hr]; simp only [hz, ↓reduceIte]
      omega
  rw [hpn]
  by_cases hz : r = 0
  · simp only [hz, ↓reduceIte]
    refine ⟨?_, by omega, by omega⟩
    rw [show n.toNat + 0 = al.toNat * q by omega]
    exact Nat.mul_mod_right _ _
  · simp only [hz, ↓reduceIte]
    refine ⟨?_, by omega, by omega⟩
    rw [show n.toNat + (al.toNat - r) = al.toNat * (q + 1) by rw [Nat.mul_add]; omega]
    exact Nat.mul_mod_right _ _

/-! ## `alloc` -/

theorem halt_fetch : Image.code.fetch 0x800002c4 = some (.base .ECALL) := by rfl

/-- From `0x800002bc`: `a0 = 2`, then the `HALT` call. -/
theorem abort {t : MachineState} (hpc : t.pc = 0x800002bc) :
    ∃ u, Reaches Image.code t u ∧ Dead Image.code u := by
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b800002bc_spec hpc trivial
  exact ⟨u, hr, dead_of_halt (by rw [b800002bc_pc h]; exact halt_fetch) (b800002bc_x5 h)
    (by rw [b800002bc_x10 h]; decide)⟩

/-- **`alloc` meets its contract.** -/
theorem alloc_spec : AllocSpec := by
  intro s hpc hpre
  have hN := hpre.heap
  have hal := hpre.align
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80000284_spec hpc trivial
  have k₁ := b80000284_keeps h₁
  have h10 := h₁.reg .x10 rfl
  have h11 := h₁.reg .x11 rfl
  have hpc₁ := h₁.pc
  have h12 := b80000284_x12 h₁
  rv_eval [] at h10 h11 hpc₁
  rw [← h10] at h11 hpc₁
  have hlo := hN.lo
  have hhi := hN.hi
  simp only [heapNext, heapStart, heapEnd, nextAddr] at hlo hhi
  have hp := nextMultiple hal.1 h10 (by omega)
  have hm₁ := b80000284_mem_same h₁
  -- `p + size` wraps: the halt
  by_cases hc : (t₁.getReg .x10 + s.getReg .x11).ult (t₁.getReg .x10) = true
  · simp only [hc, ↓reduceIte] at hpc₁
    obtain ⟨u, hru, hd⟩ := abort hpc₁
    exact ⟨u, hr₁.trans hru, Or.inr hd⟩
  simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc₁
  simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hc
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800002ac_spec hpc₁ trivial
  have k₂ := b800002ac_keeps h₂
  have hend : t₁.getReg .x11 = t₁.getReg .x10 + s.getReg .x11 := h11
  -- past `HEAP_END`: the halt
  by_cases hc' : 0x78000000 < (t₁.getReg .x11).toNat
  · obtain ⟨u, hru, hd⟩ := abort (b800002ac_pc_taken h₂ hc')
    exact ⟨u, hr₁.trans (hr₂.trans hru), Or.inr hd⟩
  have hpc₂ := b800002ac_pc_not_taken h₂ (by simpa using hc')
  have h12₂ : t₂.getReg .x12 = 0xa0001284 := (k₂ .x12 (by decide)).trans h12
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800002b4_spec hpc₂ (by
    rv_eval [h12₂]
    decide)
  have hm₃ := b800002b4_m_x12_n852 h₃
  rw [h12₂, k₂ .x11 (by decide), hend] at hm₃
  have hm₂ := b800002ac_mem_same h₂
  have k₃ := b800002b4_keeps h₃
  have hsz : (t₁.getReg .x10 + s.getReg .x11).toNat = (t₁.getReg .x10).toNat + (s.getReg .x11).toNat := by
    rw [BitVec.toNat_add]
    have := BitVec.toNat_add (t₁.getReg .x10) (s.getReg .x11)
    omega
  have hx10 : t₃.getReg .x10 = t₁.getReg .x10 := by
    rw [k₃ .x10 (by decide), k₂ .x10 (by decide)]
  have hend' : (t₁.getReg .x10).toNat + (s.getReg .x11).toNat ≤ 0x78000000 := by
    rw [← hsz, ← hend]; simpa using hc'
  have hnext : (t₃.getMem 0xa0000f30).toNat = (t₃.getReg .x10).toNat + (s.getReg .x11).toNat := by
    rw [show (0xa0000f30 : Word) = 0xa0001284 - 852 from rfl, hm₃, hsz, hx10]
  rw [← hx10] at hp hend'
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨?_, ?_, ?_⟩⟩
  · rw [b800002b4_pc h₃, k₂ .x1 (by decide), k₁ .x1 (by decide)]; rfl
  · intro r hr
    rw [k₃ r (mem_of_calleeSaved hr _), k₂ r (mem_of_calleeSaved hr _),
      k₁ r (mem_of_calleeSaved hr _)]
  · refine ⟨hp.1, hp.2.1, hnext, ⟨?_, ?_⟩, fun a ha ↦ ?_⟩
    · simp only [heapNext, heapStart, nextAddr, hnext]; omega
    · simp only [heapNext, heapEnd, nextAddr, hnext]; omega
    · rw [h₃.frame a (by rv_eval [h12₂]; exact ha), hm₂, hm₁]

end Rv64Verifier.Runtime
