import Rv64Verifier.Proofs.Walk.Sc13

/-!
# `walk`: `placements` (R13), the loop at `0x80003394`

From `f₀`: column `c` in `x10`, `x25` walking `kappas` (`Kp`), `x20` walking `offsets` (`OF`),
`x13` the placements' buffer `PL` (24 bytes each, from `+16`). `plSel` picks the placement (a
`q_keccak` slot, an output lane's `None`, or the column's offset), `plBody` stores it.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Blocks.F4 Rv64Verifier.Model
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem pf_off (K : List Nat) {c : Nat} (h : c < 73 ∨ c = 87 ∨ 138 ≤ c) :
    pf K c = some ⟨K.getD c 0, (ofl K).getD c 0⟩ := by
  unfold pf slotOf
  rcases h with h | h | h
  · simp [h]; omega
  · subst h; simp
  · simp only [show ¬ c < 73 by omega, show ¬ c - 73 < 14 by omega,
      show ¬ (15 ≤ c - 73 ∧ c - 73 < 40) by omega, show ¬ (113 ≤ c ∧ c < 138) by omega, ↓reduceIte]

theorem pf_slot (K : List Nat) {c : Nat} (h : 73 ≤ c ∧ c ≤ 86 ∨ 88 ≤ c ∧ c ≤ 112) :
    pf K c = some ⟨K.getD c 0, (ofl K).getD 5 0 +
      (BitVec.ofNat 64 (if c ≤ 86 then c - 23 else c - 88) <<< (K.getD c 0 % 64))⟩ := by
  unfold pf slotOf
  rcases h with h | h
  · simp only [show ¬ c < 73 by omega, show c - 73 < 14 by omega, show c ≤ 86 by omega, ↓reduceIte,
      show 50 + (c - 73) = c - 23 by omega]
  · simp only [show ¬ c < 73 by omega, show ¬ c - 73 < 14 by omega,
      show 15 ≤ c - 73 by omega, show c - 73 < 40 by omega, show ¬ c ≤ 86 by omega, and_self,
      ↓reduceIte, show c - 73 - 15 = c - 88 by omega]

theorem pf_none (K : List Nat) {c : Nat} (h : 113 ≤ c ∧ c < 138) : pf K c = none := by
  unfold pf slotOf
  simp only [show ¬ c < 73 by omega, show ¬ c - 73 < 14 by omega,
    show ¬ (15 ≤ c - 73 ∧ c - 73 < 40) by omega, h, and_self, ↓reduceIte]

/-- The registers the selection leaves. -/
def selRegs : List Reg :=
  [.x2, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
    .x25, .x26, .x27]

theorem b800033c4_x16 {s t : MachineState} (h : b800033c4.Holds s t) :
    t.getReg .x16 = (s.getReg .x16 <<< ((s.getReg .x15).toNat % 64)) + s.getReg .x19 :=
  h.reg_eq .x16 rfl (by rv_eval [])

/-- The column's offset: `x16 = [x20]`, `x17 = 1`. -/
theorem selOff {w : MachineState} (hpc : w.pc = 0x8000339c)
    (hv : Sym.validAccess 8 (w.getReg .x20) = true) :
    ∃ v, Reaches Image.code w v ∧ v.pc = 0x800033d0 ∧ (∀ a, v.getMem a = w.getMem a) ∧
      (∀ r ∈ selRegs, v.getReg r = w.getReg r) ∧ v.getReg .x16 = w.getMem (w.getReg .x20) ∧
      v.getReg .x17 = 1 := by
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000339c_spec hpc (by rv_eval []; exact hv)
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800033cc_spec (b8000339c_pc h₁) (by rv_eval [])
  refine ⟨v₂, hr₁.trans hr₂, b800033cc_pc h₂, fun a ↦ by
    rw [b800033cc_mem_same h₂, b8000339c_mem_same h₁], fun r hr ↦ by
    rw [b800033cc_keeps h₂ r (by revert r hr; decide), b8000339c_keeps h₁ r (by revert r hr; decide)],
    by rw [b800033cc_keeps h₂ .x16 (by decide), b8000339c_x16 h₁], b800033cc_x17 h₂⟩

/-- A `q_keccak` slot: `x16 = (x16 << x15) + x19`, `x17 = 1`. -/
theorem selSlot {w : MachineState} (hpc : w.pc = 0x800033c4) :
    ∃ v, Reaches Image.code w v ∧ v.pc = 0x800033d0 ∧ (∀ a, v.getMem a = w.getMem a) ∧
      (∀ r ∈ selRegs, v.getReg r = w.getReg r) ∧
      v.getReg .x16 = (w.getReg .x16 <<< ((w.getReg .x15).toNat % 64)) + w.getReg .x19 ∧
      v.getReg .x17 = 1 := by
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800033c4_spec hpc (by rv_eval [])
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800033cc_spec (b800033c4_pc h₁) (by rv_eval [])
  refine ⟨v₂, hr₁.trans hr₂, b800033cc_pc h₂, fun a ↦ by
    rw [b800033cc_mem_same h₂, b800033c4_mem_same h₁], fun r hr ↦ by
    rw [b800033cc_keeps h₂ r (by revert r hr; decide), b800033c4_keeps h₁ r (by revert r hr; decide)],
    by rw [b800033cc_keeps h₂ .x16 (by decide), b800033c4_x16 h₁], b800033cc_x17 h₂⟩

/-- The registers the loop leaves. -/
def plRegs : List Reg :=
  [.x2, .x8, .x9, .x11, .x12, .x14, .x18, .x19, .x21, .x22, .x23, .x24, .x26, .x27]

/-- At `0x80003394`, `c` placements stored. -/
structure Pl13 (f₀ u : MachineState) (PL OF Kp : Word) (K : List Nat) (c : Nat) : Prop where
  pc : u.pc = 0x80003394
  lt : c < 165
  x10 : u.getReg .x10 = BitVec.ofNat 64 c
  x13 : u.getReg .x13 = PL + BitVec.ofNat 64 (24 * c + 16)
  x20 : u.getReg .x20 = OF + BitVec.ofNat 64 (8 * c)
  x25 : u.getReg .x25 = Kp + BitVec.ofNat 64 (8 * c)
  regs : ∀ r ∈ plRegs, u.getReg r = f₀.getReg r
  fr : Layout.DFrame f₀ u fun a ↦ Within a PL (24 * c)
  vals : ∀ i < c, PcsContracts.placementAt u (PL + BitVec.ofNat 64 (24 * i)) = pf K i

theorem ofNat_subk {c m : Nat} (h : m ≤ c) (hc : c < 2 ^ 63) :
    BitVec.ofNat 64 c - BitVec.ofNat 64 m = BitVec.ofNat 64 (c - m) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

section
variable {f₀ : MachineState} {PL OF Kp : Word} {K : List Nat}
  (hP : PL.toNat % 8 = 0) (hO : OF.toNat % 8 = 0) (hKp : Kp.toNat % 8 = 0)
  (hK1 : 0x20000000 ≤ Kp.toNat) (hO1 : 0x20000000 ≤ OF.toNat)
  (hKP : Kp.toNat + 1320 ≤ PL.toNat) (hOP : OF.toNat + 1320 ≤ PL.toNat)
  (hP2 : PL.toNat + 3960 ≤ 0x78000000) (kle : ∀ i, K.getD i 0 ≤ 38)
  (kv : ∀ i < 165, f₀.getMem (Kp + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 (K.getD i 0))
  (ov : ∀ i < 165, f₀.getMem (OF + BitVec.ofNat 64 (8 * i)) = (ofl K).getD i 0)
  (x11 : f₀.getReg .x11 = 73) (x12 : f₀.getReg .x12 = 86) (x14 : f₀.getReg .x14 = 25)
  (x27 : f₀.getReg .x27 = 24) (x19 : f₀.getReg .x19 = (ofl K).getD 5 0)
  (x24 : f₀.getReg .x24 = 165)

include hO hKp hK1 hO1 hKP hOP hP2 kle kv ov x11 x12 x14 x27 x19 in
set_option maxRecDepth 8192 in
/-- Column `c`'s placement into `x17` (tag), `x15` (`kappas[c]`) and `x16` (index). -/
theorem plSel {u : MachineState} {c : Nat} (h : Pl13 f₀ u PL OF Kp K c) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x800033d0 ∧ (∀ a, v.getMem a = u.getMem a) ∧
      (∀ r ∈ selRegs, r ≠ .x15 → v.getReg r = u.getReg r) ∧
      v.getReg .x15 = BitVec.ofNat 64 (K.getD c 0) ∧
      ((pf K c = none ∧ v.getReg .x17 = 0) ∨
        (pf K c = some ⟨K.getD c 0, v.getReg .x16⟩ ∧ v.getReg .x17 = 1)) := by
  have hc := h.lt
  have hkc := kle c
  have rg (r : Reg) (hr : r ∈ plRegs) : u.getReg r = f₀.getReg r := h.regs r hr
  have mk : u.getMem (Kp + BitVec.ofNat 64 (8 * c)) = BitVec.ofNat 64 (K.getD c 0) := by
    rw [h.fr.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; addr_omega [hx, hw, hKP, hc, hK1, hP2])
      (by addr_omega [hK1, hKP, hP2, hc])]
    exact kv c hc
  have mo : u.getMem (OF + BitVec.ofNat 64 (8 * c)) = (ofl K).getD c 0 := by
    rw [h.fr.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; addr_omega [hx, hw, hOP, hc, hO1, hP2])
      (by addr_omega [hO1, hOP, hP2, hc])]
    exact ov c hc
  have hcN : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat]; omega
  have hkN : (BitVec.ofNat 64 (K.getD c 0)).toNat = K.getD c 0 := by
    rw [BitVec.toNat_ofNat]; omega
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003394_spec h.pc (by
    rv_eval [h.x25]; simp only [Sym.validAccess_eight]; addr_omega [hKp, hK1, hKP, hP2, hc])
  have m₁ := b80003394_mem_same h₁
  have k₁ := b80003394_keeps h₁
  have x15₁ : u₁.getReg .x15 = BitVec.ofNat 64 (K.getD c 0) := by rw [b80003394_x15 h₁, h.x25, mk]
  have x10₁ : u₁.getReg .x10 = BitVec.ofNat 64 c := by rw [k₁ .x10 (by decide)]; exact h.x10
  have x20₁ : u₁.getReg .x20 = OF + BitVec.ofNat 64 (8 * c) := by rw [k₁ .x20 (by decide)]; exact h.x20
  have x19₁ : u₁.getReg .x19 = (ofl K).getD 5 0 := by
    rw [k₁ .x19 (by decide), rg .x19 (by decide)]; exact x19
  -- the shared tails
  have off : ∀ w, Reaches Image.code u w → w.pc = 0x8000339c → (∀ a, w.getMem a = u.getMem a) →
      (∀ r ∈ selRegs, r ≠ .x15 → w.getReg r = u.getReg r) → w.getReg .x15 = u₁.getReg .x15 →
      pf K c = some ⟨K.getD c 0, (ofl K).getD c 0⟩ →
      ∃ v, Reaches Image.code u v ∧ v.pc = 0x800033d0 ∧ (∀ a, v.getMem a = u.getMem a) ∧
        (∀ r ∈ selRegs, r ≠ .x15 → v.getReg r = u.getReg r) ∧
        v.getReg .x15 = BitVec.ofNat 64 (K.getD c 0) ∧
        ((pf K c = none ∧ v.getReg .x17 = 0) ∨
          (pf K c = some ⟨K.getD c 0, v.getReg .x16⟩ ∧ v.getReg .x17 = 1)) := by
    intro w hrw hpw mw rw x15w hpf
    have x20w : w.getReg .x20 = OF + BitVec.ofNat 64 (8 * c) := by
      rw [rw .x20 (by decide) (by decide)]; exact h.x20
    obtain ⟨v, hrv, pcv, mv, rv, x16v, x17v⟩ := selOff hpw (by
      rw [x20w, Sym.validAccess_eight]; addr_omega [hO, hO1, hOP, hP2, hc])
    refine ⟨v, hrw.trans hrv, pcv, fun a ↦ by rw [mv, mw], fun r hr hr15 ↦ by rw [rv r hr, rw r hr hr15],
      by rw [rv .x15 (by decide), x15w, x15₁], Or.inr ⟨?_, x17v⟩⟩
    rw [hpf, x16v, x20w, mw, mo]
  have slot : ∀ w, Reaches Image.code u w → w.pc = 0x800033c4 → (∀ a, w.getMem a = u.getMem a) →
      (∀ r ∈ selRegs, r ≠ .x15 → w.getReg r = u.getReg r) → w.getReg .x15 = u₁.getReg .x15 →
      w.getReg .x16 = BitVec.ofNat 64 (if c ≤ 86 then c - 23 else c - 88) →
      (73 ≤ c ∧ c ≤ 86 ∨ 88 ≤ c ∧ c ≤ 112) →
      ∃ v, Reaches Image.code u v ∧ v.pc = 0x800033d0 ∧ (∀ a, v.getMem a = u.getMem a) ∧
        (∀ r ∈ selRegs, r ≠ .x15 → v.getReg r = u.getReg r) ∧
        v.getReg .x15 = BitVec.ofNat 64 (K.getD c 0) ∧
        ((pf K c = none ∧ v.getReg .x17 = 0) ∨
          (pf K c = some ⟨K.getD c 0, v.getReg .x16⟩ ∧ v.getReg .x17 = 1)) := by
    intro w hrw hpw mw rw x15w x16w hcr
    obtain ⟨v, hrv, pcv, mv, rv, x16v, x17v⟩ := selSlot hpw
    refine ⟨v, hrw.trans hrv, pcv, fun a ↦ by rw [mv, mw], fun r hr hr15 ↦ by rw [rv r hr, rw r hr hr15],
      by rw [rv .x15 (by decide), x15w, x15₁], Or.inr ⟨?_, x17v⟩⟩
    rw [pf_slot K hcr, x16v, x16w, x15w, x15₁, hkN, rw .x19 (by decide) (by decide), ← k₁ .x19 (by decide),
      x19₁, BitVec.add_comm]
  have rg₁ : ∀ r ∈ selRegs, r ≠ .x15 → u₁.getReg r = u.getReg r := fun r hr hr15 ↦
    k₁ r (by revert r hr15 hr; decide)
  have h73 : (73 : Word).toNat = 73 := rfl
  have x11u : u.getReg .x11 = 73 := by rw [rg .x11 (by decide)]; exact x11
  have x12₁ : u₁.getReg .x12 = 86 := by rw [k₁ .x12 (by decide), rg .x12 (by decide)]; exact x12
  by_cases hA : c < 73
  · exact off u₁ hr₁ (b80003394_pc_not_taken h₁ (by rw [h.x10, x11u, hcN, h73]; exact hA)) m₁ rg₁ rfl
      (pf_off K (Or.inl hA))
  have pc₁ := b80003394_pc_taken h₁ (by rw [h.x10, x11u, hcN, h73]; omega)
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800033a4_spec pc₁ (by rv_eval [])
  have m₂ (a : Word) : u₂.getMem a = u.getMem a := by rw [b800033a4_mem_same h₂, m₁]
  have k₂ := b800033a4_keeps h₂
  have rg₂ : ∀ r ∈ selRegs, r ≠ .x15 → u₂.getReg r = u.getReg r := fun r hr hr15 ↦ by
    rw [k₂ r (by revert r hr15 hr; decide), rg₁ r hr hr15]
  have x10₂ : u₂.getReg .x10 = BitVec.ofNat 64 c := by rw [rg₂ .x10 (by decide) (by decide)]; exact h.x10
  have x15₂ : u₂.getReg .x15 = u₁.getReg .x15 := k₂ .x15 (by decide)
  have h86 : (86 : Word).toNat = 86 := rfl
  by_cases hB : c ≤ 86
  · have pc₂ := b800033a4_pc_taken h₂ (by rw [x10₁, x12₁, hcN, h86]; exact hB)
    obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800033c0_spec pc₂ (by rv_eval [])
    have k₃ := b800033c0_keeps h₃
    exact slot u₃ (hr₁.trans (hr₂.trans hr₃)) (b800033c0_pc h₃)
      (fun a ↦ by rw [b800033c0_mem_same h₃, m₂])
      (fun r hr hr15 ↦ by rw [k₃ r (by revert r hr15 hr; decide), rg₂ r hr hr15])
      (by rw [k₃ .x15 (by decide), x15₂])
      (by rw [b800033c0_x16 h₃, x10₂]; simp only [hB, ↓reduceIte]
          rw [show (23 : Word) = BitVec.ofNat 64 23 from rfl, ofNat_subk (by omega) (by omega)])
      (Or.inl ⟨by omega, hB⟩)
  have pc₂ := b800033a4_pc_not_taken h₂ (by rw [x10₁, x12₁, hcN, h86]; omega)
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800033a8_spec pc₂ (by rv_eval [])
  have m₃ (a : Word) : u₃.getMem a = u.getMem a := by rw [b800033a8_mem_same h₃, m₂]
  have k₃ := b800033a8_keeps h₃
  have rg₃ : ∀ r ∈ selRegs, r ≠ .x15 → u₃.getReg r = u.getReg r := fun r hr hr15 ↦ by
    rw [k₃ r (by revert r hr15 hr; decide), rg₂ r hr hr15]
  have x27₂ : u₂.getReg .x27 = 24 := by
    rw [rg₂ .x27 (by decide) (by decide), rg .x27 (by decide)]; exact x27
  have e88 : (u₂.getReg .x10 - 88).toNat = (2 ^ 64 - 88 + c) % 2 ^ 64 := by
    rw [x10₂, BitVec.toNat_sub, hcN]; rfl
  have h24 : (24 : Word).toNat = 24 := rfl
  have x15₃ : u₃.getReg .x15 = u₁.getReg .x15 := by rw [k₃ .x15 (by decide), x15₂]
  by_cases hC : 88 ≤ c ∧ c ≤ 112
  · have pc₃ := b800033a8_pc_taken h₃ (by rw [e88, x27₂, h24]; omega)
    exact slot u₃ (hr₁.trans (hr₂.trans hr₃)) pc₃ m₃ rg₃ x15₃
      (by rw [b800033a8_x16 h₃, x10₂]; simp only [hB, ↓reduceIte]
          rw [show (88 : Word) = BitVec.ofNat 64 88 from rfl, ofNat_subk (by omega) (by omega)])
      (Or.inr hC)
  have pc₃ := b800033a8_pc_not_taken h₃ (by rw [e88, x27₂, h24]; omega)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800033b0_spec pc₃ (by rv_eval [])
  have m₄ (a : Word) : u₄.getMem a = u.getMem a := by rw [b800033b0_mem_same h₄, m₃]
  have k₄ := b800033b0_keeps h₄
  have rg₄ : ∀ r ∈ selRegs, r ≠ .x15 → u₄.getReg r = u.getReg r := fun r hr hr15 ↦ by
    rw [k₄ r (by revert r hr15 hr; decide), rg₃ r hr hr15]
  have x15₄ : u₄.getReg .x15 = u₁.getReg .x15 := by rw [k₄ .x15 (by decide), x15₃]
  have x14₃ : u₃.getReg .x14 = 25 := by
    rw [rg₃ .x14 (by decide) (by decide), rg .x14 (by decide)]; exact x14
  have e113 : (u₃.getReg .x10 - 113).toNat = (2 ^ 64 - 113 + c) % 2 ^ 64 := by
    rw [rg₃ .x10 (by decide) (by decide), h.x10, BitVec.toNat_sub, hcN]; rfl
  have h25 : (25 : Word).toNat = 25 := rfl
  by_cases hD : 113 ≤ c ∧ c < 138
  · have pc₄ := b800033b0_pc_not_taken h₄ (by rw [e113, x14₃, h25]; omega)
    obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800033b8_spec pc₄ (by rv_eval [])
    have k₅ := b800033b8_keeps h₅
    exact ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), b800033b8_pc h₅,
      fun a ↦ by rw [b800033b8_mem_same h₅, m₄],
      fun r hr hr15 ↦ by rw [k₅ r (by revert r hr15 hr; decide), rg₄ r hr hr15],
      by rw [k₅ .x15 (by decide), x15₄, x15₁], Or.inl ⟨pf_none K hD, b800033b8_x17 h₅⟩⟩
  · have pc₄ := b800033b0_pc_taken h₄ (by rw [e113, x14₃, h25]; omega)
    exact off u₄ (hr₁.trans (hr₂.trans (hr₃.trans hr₄))) pc₄ m₄ rg₄ x15₄ (pf_off K (by omega))

theorem placementAt_congr {u v : MachineState} {a : Word} (h0 : v.getMem a = u.getMem a)
    (h8 : v.getMem (a + 8) = u.getMem (a + 8)) (h16 : v.getMem (a + 16) = u.getMem (a + 16)) :
    PcsContracts.placementAt v a = PcsContracts.placementAt u a := by
  simp only [PcsContracts.placementAt, h0, h8, h16]

include hP hO hKp hK1 hO1 hKP hOP hP2 kle kv ov x11 x12 x14 x27 x19 x24 in
set_option maxRecDepth 8192 in
/-- One round. -/
theorem plBody {u : MachineState} {c : Nat} (h : Pl13 f₀ u PL OF Kp K c) :
    ∃ t, Reaches Image.code u t ∧ (∀ r ∈ plRegs, t.getReg r = f₀.getReg r) ∧
      Layout.DFrame f₀ t (fun a ↦ Within a PL (24 * (c + 1))) ∧
      (∀ i < c + 1, PcsContracts.placementAt t (PL + BitVec.ofNat 64 (24 * i)) = pf K i) ∧
      ((c + 1 < 165 ∧ t.pc = 0x80003394 ∧ t.getReg .x10 = BitVec.ofNat 64 (c + 1) ∧
        t.getReg .x13 = PL + BitVec.ofNat 64 (24 * (c + 1) + 16) ∧
        t.getReg .x20 = OF + BitVec.ofNat 64 (8 * (c + 1)) ∧
        t.getReg .x25 = Kp + BitVec.ofNat 64 (8 * (c + 1))) ∨ (c + 1 = 165 ∧ t.pc = 0x800033f0)) := by
  have hc := h.lt
  have hkc := kle c
  obtain ⟨v, hrv, pcv, mv, rv, x15v, tag⟩ := plSel hO hKp hK1 hO1 hKP hOP hP2 kle kv ov x11 x12 x14 x27 x19 h
  have x13v : v.getReg .x13 = PL + BitVec.ofNat 64 (24 * c + 16) := by
    rw [rv .x13 (by decide) (by decide)]; exact h.x13
  obtain ⟨t, hrt, ht⟩ := Sym.BlockSpec.reaches b800033d0_spec pcv (by
    rv_eval [x13v]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hP, hK1, hKP, hP2, hc])
  have fr := (b800033d0_frame ht (by rw [x13v]; constructor <;> addr_omega [hK1, hKP, hP2, hc])).dframe
  have ea : v.getReg .x13 - 16 = PL + BitVec.ofNat 64 (24 * c) := by
    rw [x13v]; apply BitVec.eq_of_toNat_eq; addr_omega [hK1, hKP, hP2, hc]
  have e8 : v.getReg .x13 - 8 = PL + BitVec.ofNat 64 (24 * c) + 8 := by
    rw [x13v]; apply BitVec.eq_of_toNat_eq; addr_omega [hK1, hKP, hP2, hc]
  have e16 : v.getReg .x13 = PL + BitVec.ofNat 64 (24 * c) + 16 := by
    rw [x13v]; apply BitVec.eq_of_toNat_eq; addr_omega [hK1, hKP, hP2, hc]
  rw [ea] at fr
  have kt := b800033d0_keeps ht
  have hkN : (BitVec.ofNat 64 (K.getD c 0)).toNat = K.getD c 0 := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨t, hrv.trans hrt, fun r hr ↦ ?_, ?_, fun i hi ↦ ?_, ?_⟩
  · rw [kt r (by revert r hr; decide), rv r (by revert r hr; decide) (by revert r hr; decide),
      h.regs r hr]
  · intro a ha hw8
    rw [fr a (fun x hx h' ↦ ha x hx (by simp only [Within] at h' ⊢; addr_omega [h', hK1, hKP, hP2, hc]))
      hw8, mv, h.fr a (fun x hx h' ↦ ha x hx (by simp only [Within] at h' ⊢; omega)) hw8]
  · by_cases hic : i < c
    · have g (o : Nat) (ho : o + 8 ≤ 24) :
          t.getMem (PL + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 o) =
            u.getMem (PL + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 o) := by
        rw [fr.getMem_of (fun x hx hw ↦ by
            simp only [Within] at hx hw; addr_omega [hx, hw, hic, ho, hK1, hKP, hP2, hc])
          (by addr_omega [hic, ho, hK1, hKP, hP2, hc]), mv]
      rw [placementAt_congr (by simpa using g 0 (by decide)) (g 8 (by decide)) (g 16 (by decide))]
      exact h.vals i hic
    · have : i = c := by omega
      subst this
      have w0 := b800033d0_m_x13_n16 ht
      have w8 := b800033d0_m_x13_n8 ht
      have w16 := b800033d0_m_x13_0 ht
      rw [ea] at w0
      rw [e8, x15v] at w8
      rw [e16] at w16
      simp only [PcsContracts.placementAt, w0, w8, w16, hkN]
      rcases tag with ⟨hn, h17⟩ | ⟨hs, h17⟩
      · rw [h17, hn]; rfl
      · rw [h17, hs]; rfl
  · have x10v : v.getReg .x10 = BitVec.ofNat 64 c := by rw [rv .x10 (by decide) (by decide)]; exact h.x10
    have x24v : v.getReg .x24 = 165 := by
      rw [rv .x24 (by decide) (by decide), h.regs .x24 (by decide)]; exact x24
    have e1 : BitVec.ofNat 64 c + 1 = BitVec.ofNat 64 (c + 1) := ofNat_succ' c
    by_cases hc1 : c + 1 < 165
    · refine Or.inl ⟨hc1, b800033d0_pc_taken ht (by
        rw [x24v, x10v, e1]; intro he; have := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat] at this; have : (165 : Word).toNat = 165 := rfl; omega), ?_, ?_, ?_, ?_⟩
      · rw [b800033d0_x10 ht, x10v, e1]
      · rw [b800033d0_x13 ht, x13v]; apply BitVec.eq_of_toNat_eq; addr_omega [hK1, hKP, hP2, hc]
      · rw [b800033d0_x20 ht, rv .x20 (by decide) (by decide), h.x20]; apply BitVec.eq_of_toNat_eq
        addr_omega [hO1, hOP, hP2, hc]
      · rw [b800033d0_x25 ht, rv .x25 (by decide) (by decide), h.x25]; apply BitVec.eq_of_toNat_eq
        addr_omega [hK1, hKP, hP2, hc]
    · refine Or.inr ⟨by omega, b800033d0_pc_not_taken ht (by
        rw [x24v, x10v, e1, show c + 1 = 165 by omega]; rfl)⟩

include hP hO hKp hK1 hO1 hKP hOP hP2 kle kv ov x11 x12 x14 x27 x19 x24 in
theorem plLoop : ∀ d c u, 164 - c = d → Pl13 f₀ u PL OF Kp K c → ∃ t, Reaches Image.code u t ∧
    t.pc = 0x800033f0 ∧ (∀ r ∈ plRegs, t.getReg r = f₀.getReg r) ∧
    Layout.DFrame f₀ t (fun a ↦ Within a PL (24 * 165)) ∧
    ∀ i < 165, PcsContracts.placementAt t (PL + BitVec.ofNat 64 (24 * i)) = pf K i := by
  intro d
  induction d with
  | zero =>
    intro c u hd h
    obtain ⟨t, hr, rg, fr, vals, ⟨hc1, -⟩ | ⟨hc1, pct⟩⟩ :=
      plBody hP hO hKp hK1 hO1 hKP hOP hP2 kle kv ov x11 x12 x14 x27 x19 x24 h
    · omega
    · rw [hc1] at fr vals; exact ⟨t, hr, pct, rg, fr, vals⟩
  | succ d ih =>
    intro c u hd h
    obtain ⟨t, hr, rg, fr, vals, ⟨hc1, pct, x10, x13, x20, x25⟩ | ⟨hc1, -⟩⟩ :=
      plBody hP hO hKp hK1 hO1 hKP hOP hP2 kle kv ov x11 x12 x14 x27 x19 x24 h
    · obtain ⟨t', hr', ht'⟩ := ih (c + 1) t (by omega) ⟨pct, hc1, x10, x13, x20, x25, rg, fr, vals⟩
      exact ⟨t', hr.trans hr', ht'⟩
    · omega

end

end Rv64Verifier.Proofs.Walk
