import Rv64Verifier.Proofs.Walk.Blk12

/-!
# `walk`: `block_kappas` (R12), the map loop

From `f₀` at `0x8000328c`: `x14` walks `blocks` (`G`), `x13` the new buffer `BK`, each round
storing `kappas[blocks[j]]` (`x10` = `kappas`' buffer `Kp`), `x15` counting down from `101`.
`mapLoop` reaches `0x800032b8` with the `101` words of `BK` stored, nothing else written.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem blk_165_length : (blk 165).length = 101 := by decide

theorem blk_165_lt : ∀ i < 101, (blk 165).getD i 0 < 165 := by decide

/-- The registers the loop leaves. -/
def mapRegs : List Reg := [.x2, .x9, .x10, .x11, .x18, .x23, .x24, .x25, .x26]

/-- At `0x8000328c`, `j` words stored. -/
structure Map12 (f₀ u : MachineState) (G BK : Word) (j : Nat) : Prop where
  pc : u.pc = 0x8000328c
  lt : j < 101
  x12 : u.getReg .x12 = BitVec.ofNat 64 j
  x13 : u.getReg .x13 = BK + BitVec.ofNat 64 (8 * j)
  x14 : u.getReg .x14 = G + BitVec.ofNat 64 (8 * j)
  x15 : u.getReg .x15 = BitVec.ofNat 64 (101 - j)
  regs : ∀ r ∈ mapRegs, u.getReg r = f₀.getReg r
  fr : Layout.DFrame f₀ u fun a ↦ Within a BK (8 * j)
  vals : ∀ i < j, u.getMem (BK + BitVec.ofNat 64 (8 * i)) =
    f₀.getMem (f₀.getReg .x10 + BitVec.ofNat 64 (8 * (blk 165).getD i 0))

section
variable {f₀ : MachineState} {G BK : Word} (hG : G.toNat % 8 = 0) (hBK : BK.toNat % 8 = 0)
    (hK : (f₀.getReg .x10).toNat % 8 = 0) (hG1 : 0x20000000 ≤ G.toNat)
    (hK1 : 0x20000000 ≤ (f₀.getReg .x10).toNat) (hGB : G.toNat + 808 ≤ BK.toNat)
    (hKB : (f₀.getReg .x10).toNat + 8 * 165 ≤ BK.toNat) (hB2 : BK.toNat + 808 ≤ 0x78000000)
    (x24 : f₀.getReg .x24 = 165)
    (gv : ∀ i < 101, f₀.getMem (G + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 ((blk 165).getD i 0))
include hG hBK hK hG1 hK1 hGB hKB hB2 x24 gv

set_option maxRecDepth 8192 in
/-- One round. -/
theorem mapBody {u : MachineState} {j : Nat} (h : Map12 f₀ u G BK j) :
    ∃ t, Reaches Image.code u t ∧ (∀ r ∈ mapRegs, t.getReg r = f₀.getReg r) ∧
      Layout.DFrame f₀ t (fun a ↦ Within a BK (8 * (j + 1))) ∧
      (∀ i < j + 1, t.getMem (BK + BitVec.ofNat 64 (8 * i)) =
        f₀.getMem (f₀.getReg .x10 + BitVec.ofNat 64 (8 * (blk 165).getD i 0))) ∧
      t.getReg .x12 = BitVec.ofNat 64 (j + 1) ∧
      ((j + 1 < 101 ∧ t.pc = 0x8000328c ∧ t.getReg .x13 = BK + BitVec.ofNat 64 (8 * (j + 1)) ∧
        t.getReg .x14 = G + BitVec.ofNat 64 (8 * (j + 1)) ∧
        t.getReg .x15 = BitVec.ofNat 64 (101 - (j + 1))) ∨ (j + 1 = 101 ∧ t.pc = 0x800032b8)) := by
  have hj := h.lt
  have x10 : u.getReg .x10 = f₀.getReg .x10 := h.regs .x10 (by decide)
  have x24u : u.getReg .x24 = 165 := (h.regs .x24 (by decide)).trans x24
  have hbl := blk_165_lt j hj
  have gj : u.getMem (G + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 ((blk 165).getD j 0) := by
    rw [h.fr.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; addr_omega [hx, hw, hGB, hj, hG1, hB2])
      (by addr_omega [hG1, hGB, hB2, hj])]
    exact gv j hj
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000328c_spec h.pc (by
    rv_eval [h.x14]; simp only [Sym.validAccess_eight]; addr_omega [hG, hG1, hGB, hB2, hj])
  have h165 : (165 : Word).toNat = 165 := rfl
  have pc₁ := b8000328c_pc_not_taken h₁ (by
    rw [h.x14, gj, x24u, BitVec.toNat_ofNat, h165]; omega)
  have m₁ := b8000328c_mem_same h₁
  have k₁ := b8000328c_keeps h₁
  have x16₁ : u₁.getReg .x16 = BitVec.ofNat 64 ((blk 165).getD j 0) := by
    rw [b8000328c_x16 h₁, h.x14, gj]
  have x13₁ : u₁.getReg .x13 = BK + BitVec.ofNat 64 (8 * j) := by
    rw [k₁ .x13 (by decide)]; exact h.x13
  have x10₁ : u₁.getReg .x10 = f₀.getReg .x10 := by rw [k₁ .x10 (by decide)]; exact x10
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003294_spec pc₁ (by
    rv_eval [x13₁, x10₁, x16₁, ofNat_mul8]; simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hBK, hK, hK1, hKB, hB2, hj, hbl, hG1, hGB])
  have fr₂ := (b80003294_frame h₂ (by rw [x13₁]; addr_omega [hG1, hGB, hB2, hj])).dframe
  rw [x13₁] at fr₂
  have k₂ := b80003294_keeps h₂
  have st : u₂.getMem (BK + BitVec.ofNat 64 (8 * j)) =
      f₀.getMem (f₀.getReg .x10 + BitVec.ofNat 64 (8 * (blk 165).getD j 0)) := by
    have := b80003294_m_x13_0 h₂
    rw [x13₁, x10₁, x16₁, ofNat_mul8, m₁] at this
    rw [this, h.fr.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; addr_omega [hx, hw, hKB, hj, hbl, hK1, hB2])
      (by addr_omega [hK1, hKB, hB2, hbl])]
  refine ⟨u₂, hr₁.trans hr₂, fun r hr ↦ ?_, ?_, fun i hi ↦ ?_, ?_, ?_⟩
  · rw [← h.regs r hr, k₂ r (by revert r hr; decide), k₁ r (by revert r hr; decide)]
  · intro a ha hw8
    rw [fr₂ a (fun x hx h' ↦ ha x hx (by simp only [Within] at h' ⊢; addr_omega [h', hG1, hGB, hB2, hj]))
      hw8, m₁, h.fr a (fun x hx h' ↦ ha x hx (by simp only [Within] at h' ⊢; omega)) hw8]
  · by_cases hij : i < j
    · rw [fr₂.getMem_of (fun x hx hw ↦ by
          simp only [Within] at hx hw; addr_omega [hx, hw, hij, hG1, hGB, hB2, hj])
        (by addr_omega [hij, hG1, hGB, hB2, hj]), m₁]
      exact h.vals i hij
    · have : i = j := by omega
      subst this; exact st
  · rw [b80003294_x12 h₂, k₁ .x12 (by decide), h.x12, ofNat_succ']
  · have x15₁ : u₁.getReg .x15 = BitVec.ofNat 64 (101 - j) := by rw [k₁ .x15 (by decide)]; exact h.x15
    have e15 : BitVec.ofNat 64 (101 - j) - 1 = BitVec.ofNat 64 (101 - (j + 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have : (1 : Word).toNat = 1 := rfl
      omega
    by_cases hj1 : j + 1 < 101
    · refine Or.inl ⟨hj1, b80003294_pc_taken h₂ (by
        rw [x15₁, e15]; intro he; have := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat] at this; have h0 : (0 : Word).toNat = 0 := rfl; omega), ?_, ?_, ?_⟩
      · rw [b80003294_x13 h₂, x13₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hG1, hGB, hB2, hj]
      · rw [b80003294_x14 h₂, k₁ .x14 (by decide), h.x14]; apply BitVec.eq_of_toNat_eq
        addr_omega [hG1, hGB, hB2, hj]
      · rw [b80003294_x15 h₂, x15₁, e15]
    · refine Or.inr ⟨by omega, b80003294_pc_not_taken h₂ (by
        rw [x15₁, e15, show 101 - (j + 1) = 0 by omega]; rfl)⟩

theorem mapLoop : ∀ d j u, 100 - j = d → Map12 f₀ u G BK j → ∃ t, Reaches Image.code u t ∧
      t.pc = 0x800032b8 ∧ (∀ r ∈ mapRegs, t.getReg r = f₀.getReg r) ∧
      t.getReg .x12 = 101 ∧ Layout.DFrame f₀ t (fun a ↦ Within a BK 808) ∧
      ∀ i < 101, t.getMem (BK + BitVec.ofNat 64 (8 * i)) =
        f₀.getMem (f₀.getReg .x10 + BitVec.ofNat 64 (8 * (blk 165).getD i 0)) := by
  intro d
  induction d with
  | zero =>
    intro j u hd h
    obtain ⟨t, hr, rg, fr, vals, x12, ⟨hj1, -⟩ | ⟨hj1, pct⟩⟩ :=
      mapBody hG hBK hK hG1 hK1 hGB hKB hB2 x24 gv h
    · omega
    · rw [hj1] at fr vals x12
      exact ⟨t, hr, pct, rg, x12, fr, vals⟩
  | succ d ih =>
    intro j u hd h
    obtain ⟨t, hr, rg, fr, vals, x12, ⟨hj1, pct, x13, x14, x15⟩ | ⟨hj1, -⟩⟩ :=
      mapBody hG hBK hK hG1 hK1 hGB hKB hB2 x24 gv h
    · obtain ⟨t', hr', ht'⟩ := ih (j + 1) t (by omega) ⟨pct, hj1, x12, x13, x14, x15, rg, fr, vals⟩
      exact ⟨t', hr.trans hr', ht'⟩
    · omega

end

end Rv64Verifier.Proofs.Walk
