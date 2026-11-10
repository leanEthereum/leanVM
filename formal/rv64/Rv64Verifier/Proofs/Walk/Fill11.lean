import Rv64Verifier.Proofs.Walk.Tmp11

/-!
# `walk`: `vec![h; w]`'s fill loop (R11)

From `f₀` at `0x80003168`, `x11` walking `T` up to `x12 = T + 8 w - 8`, each round storing `x21`:
`fillLoop` reaches `0x800031a4` with the `w` words of `T` all `x21`, nothing else written.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The registers the loop leaves. -/
def fillRegs : List Reg := [.x2, .x8, .x9, .x10, .x12, .x19, .x20, .x21, .x22, .x24, .x25, .x27]

/-- At `0x80003168`, `m` words stored. -/
structure Fill11 (f₀ u : MachineState) (T : Word) (w m : Nat) : Prop where
  pc : u.pc = 0x80003168
  le : m + 2 ≤ w
  x11 : u.getReg .x11 = T + BitVec.ofNat 64 (8 * m)
  regs : ∀ r ∈ fillRegs, u.getReg r = f₀.getReg r
  fr : Layout.DFrame f₀ u fun a ↦ Within a T (8 * m)
  vals : ∀ j < m, u.getMem (T + BitVec.ofNat 64 (8 * j)) = f₀.getReg .x21

theorem fillLoop {f₀ : MachineState} {T : Word} {w : Nat} (hT : T.toNat % 8 = 0)
    (hT1 : 0x20000000 ≤ T.toNat) (hT2 : T.toNat + 8 * w ≤ 0x78000000)
    (x12 : f₀.getReg .x12 = T + BitVec.ofNat 64 (8 * w) - 8) :
    ∀ d m u, w - 2 - m = d → Fill11 f₀ u T w m → ∃ t, Reaches Image.code u t ∧
      t.pc = 0x800031a4 ∧ (∀ r ∈ ([.x2, .x8, .x9, .x10, .x12, .x19, .x20, .x21, .x22, .x25, .x27] :
        List Reg), t.getReg r = f₀.getReg r) ∧
      t.getReg .x24 = f₀.getReg .x24 + f₀.getReg .x10 ∧
      Layout.DFrame f₀ t (fun a ↦ Within a T (8 * w)) ∧
      ∀ j < w, t.getMem (T + BitVec.ofNat 64 (8 * j)) = f₀.getReg .x21 := by
  intro d
  induction d with
  | zero =>
    intro m u hd h
    have hm : m + 2 = w := by have := h.le; omega
    obtain ⟨v, hrv, hv⟩ := Sym.BlockSpec.reaches b80003168_spec h.pc (by
      rv_eval [h.x11]; simp only [Sym.validAccess_eight]; addr_omega [hT, hT1, hT2, hm])
    have kv := b80003168_keeps hv
    have x11v : v.getReg .x11 = T + BitVec.ofNat 64 (8 * (m + 1)) := by
      rw [b80003168_x11 hv, h.x11]; apply BitVec.eq_of_toNat_eq; addr_omega [hT1, hT2, hm]
    have pcv := b80003168_pc_not_taken hv (by
      rw [h.x11, h.regs .x12 (by decide), x12]; apply BitVec.eq_of_toNat_eq
      addr_omega [hT1, hT2, hm])
    have frv := (b80003168_frame hv (by rw [h.x11]; addr_omega [hT1, hT2, hm])).dframe
    have wv := b80003168_m_x11_0 hv
    rw [h.x11, h.regs .x21 (by decide)] at wv
    rw [h.x11] at frv
    obtain ⟨t, hrt, ht⟩ := Sym.BlockSpec.reaches b80003174_spec pcv (by
      rv_eval [x11v]; simp only [Sym.validAccess_eight]; addr_omega [hT, hT1, hT2, hm])
    have frt := (b80003174_frame ht (by rw [x11v]; addr_omega [hT1, hT2, hm])).dframe
    have wt := b80003174_m_x11_0 ht
    rw [x11v, kv .x21 (by decide), h.regs .x21 (by decide)] at wt
    rw [x11v] at frt
    have kt := b80003174_keeps ht
    refine ⟨t, hrv.trans hrt, b80003174_pc ht, fun r hr ↦ ?_, ?_, ?_, fun j hj ↦ ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [kt _ (by decide), kv _ (by decide), h.regs _ (by decide)]
    · rw [b80003174_x24 ht, kv .x24 (by decide), kv .x10 (by decide), h.regs .x24 (by decide),
        h.regs .x10 (by decide)]
    · refine ((h.fr.union frv).union frt).mono fun a ha ↦ ?_
      simp only [Within] at ha ⊢
      rcases ha with (ha | ha) | ha <;> addr_omega [ha, hT1, hT2, hm]
    · have ap (x : Word) (hx : Within x (T + BitVec.ofNat 64 (8 * j)) 8) (n : Nat) (hn : n ≠ j)
          (hn2 : n < w) : ¬ Within x (T + BitVec.ofNat 64 (8 * n)) 8 := by
        simp only [Within] at hx ⊢; addr_omega [hx, hT1, hT2, hn, hn2, hj]
      by_cases h1 : j = m + 1
      · subst h1; exact wt
      rw [frt _ (fun x hx ↦ ap x hx (m + 1) (Ne.symm h1) (by omega)) (by addr_omega [hT1, hT2, hj])]
      by_cases h2 : j = m
      · subst h2; exact wv
      rw [frv _ (fun x hx ↦ ap x hx m (Ne.symm h2) (by omega)) (by addr_omega [hT1, hT2, hj])]
      exact h.vals j (by omega)
  | succ d ih =>
    intro m u hd h
    have hm : m + 3 ≤ w := by have := h.le; omega
    obtain ⟨v, hrv, hv⟩ := Sym.BlockSpec.reaches b80003168_spec h.pc (by
      rv_eval [h.x11]; simp only [Sym.validAccess_eight]; addr_omega [hT, hT1, hT2, hm])
    have kv := b80003168_keeps hv
    have x11v : v.getReg .x11 = T + BitVec.ofNat 64 (8 * (m + 1)) := by
      rw [b80003168_x11 hv, h.x11]; apply BitVec.eq_of_toNat_eq; addr_omega [hT1, hT2, hm]
    have pcv := b80003168_pc_taken hv (by
      rw [h.x11, h.regs .x12 (by decide), x12]; intro he
      have := congrArg BitVec.toNat he
      addr_omega [this, hT1, hT2, hm])
    have frv := (b80003168_frame hv (by rw [h.x11]; addr_omega [hT1, hT2, hm])).dframe
    have wv := b80003168_m_x11_0 hv
    rw [h.x11, h.regs .x21 (by decide)] at wv
    rw [h.x11] at frv
    obtain ⟨t, hrt, ht⟩ := ih (m + 1) v (by omega) {
      pc := pcv
      le := by omega
      x11 := x11v
      regs := fun r hr ↦ by
        simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [kv _ (by decide), h.regs _ (by decide)]
      fr := (h.fr.union frv).mono fun a ha ↦ by
        simp only [Within] at ha ⊢
        rcases ha with ha | ha <;> addr_omega [ha, hT1, hT2, hm]
      vals := fun j hj ↦ by
        by_cases h2 : j = m
        · subst h2; exact wv
        rw [frv _ (fun x hx ↦ by simp only [Within] at hx ⊢; addr_omega [hx, hT1, hT2, h2, hj, hm])
          (by addr_omega [hT1, hT2, hj, hm])]
        exact h.vals j (by omega) }
    exact ⟨t, hrv.trans hrt, ht⟩

end Rv64Verifier.Proofs.Walk
