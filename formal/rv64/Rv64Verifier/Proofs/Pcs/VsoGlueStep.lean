import Rv64Verifier.Proofs.Pcs.VsoGlueQueries

/-!
# `verify_stacked_opening`'s final level: a glued claim, added

`0x8000baf8` stores the claim's value at `S - 208` and calls `mul(S - 256, scalar, value)`;
`0x8000bb20` adds the product to the weight at `S - 184` and goes on to the next claim
(`0x8000bb58`) or, past the last, to `0x8000bfe0`, which reloads the tail folds' pointer and length
for the terminal check at `0x8000bfe8` (`TC`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The loop's writes are what the mirror's transcript does not hold. -/
theorem GLW.ns {s : MachineState} (hpre : VsoPre s) {lo : ℕ} {hi a : Word} (hlo : heapNext s ≤ lo)
    (hhi : hi.toNat ≤ heapEnd) (h : GLW s lo hi a) : NS s a := by
  have hb := bounds hpre
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))

/-- The claims' end, and claim `j`'s successor. -/
theorem claim_next {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}
    (h : VsoFinalIn OA s x u Wl residual) {j : ℕ} (hj : j < (vecLen u (s.getReg .x2 - 664)).toNat) :
    (gAddr u s j + 88 = vecPtr u (s.getReg .x2 - 664) + vecLen u (s.getReg .x2 - 664) * 88 ↔
      j + 1 = (vecLen u (s.getReg .x2 - 664)).toNat) ∧
    gAddr u s (j + 1) = gAddr u s j + 88 := by
  obtain ⟨h8, hl, hb⟩ := h.gbuf
  have hhu := h.heap.hi
  simp only [heapEnd] at hhu
  rcases hb with h0 | h0
  · omega
  have hp := (vecPtr u (s.getReg .x2 - 664)).isLt
  have e1 : (gAddr u s j + 88).toNat = (vecPtr u (s.getReg .x2 - 664)).toNat + 88 * (j + 1) := by
    simp only [gAddr]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [show (88 : Word).toNat = 88 from rfl]
    rw [Nat.mod_eq_of_lt (a := 88 * j) (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    ring
  have e2 : (vecPtr u (s.getReg .x2 - 664) + vecLen u (s.getReg .x2 - 664) * 88).toNat =
      (vecPtr u (s.getReg .x2 - 664)).toNat + 88 * (vecLen u (s.getReg .x2 - 664)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_mul]
    simp only [show (88 : Word).toNat = 88 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    ring
  have e3 : (gAddr u s (j + 1)).toNat = (vecPtr u (s.getReg .x2 - 664)).toNat + 88 * (j + 1) := by
    simp only [gAddr]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 88 * (j + 1)) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨fun he ↦ ?_, fun he ↦ ?_⟩, BitVec.eq_of_toNat_eq (by rw [e3, e1])⟩
  · have := congrArg BitVec.toNat he
    rw [e1, e2] at this
    omega
  · exact BitVec.eq_of_toNat_eq (by rw [e1, e2, he])

/-- After `0x8000bb20`: the weight `acc'` at `S - 184`, and the next claim or the exit. -/
theorem claimAdd (hM : MulSpec) {OA : MachineState → Word → Model.TState → Prop} {s : MachineState}
    {x : LCtx} {u v w : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E}
    {rt w0 : E} {j : ℕ} {a : Word} {acc val : E} (hpre : VsoPre s)
    (h : GV OA s x u v w Wl residual tf rt w0 j a acc val) :
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ ∃ acc',
      gluedFold (Wl.glued.take (j + 1)) (Wl.folds ++ tf) w0 = some acc' ∧
      eAt w' (s.getReg .x2 - 184) = acc' ∧ GS s v w' ∧
      w'.getMem (s.getReg .x2 - 880) =
        vecPtr u (s.getReg .x2 - 664) + vecLen u (s.getReg .x2 - 664) * 88 ∧
      (j + 1 < (vecLen u (s.getReg .x2 - 664)).toNat ∧ w'.pc = 0x8000bb58 ∧
          w'.getReg .x8 = gAddr u s (j + 1) ∨
        j + 1 = (vecLen u (s.getReg .x2 - 664)).toNat ∧ w'.pc = 0x8000bfe0)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.gs.sp
  have fin := h.tb.toTI.fin
  -- `0x8000baf8`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000baf8_spec h.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000baf8_keeps h₁
  have F₁ : DFrame w t₁ fun y ↦ Within y (s.getReg .x2 - 208) 24 := by
    have := DFrame.of_memFrame (b8000baf8_frame h₁ (by rw [hsp]; addr_omega [hb]))
    rw [hsp] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  obtain ⟨G₁, -⟩ := h.gs.stepS hpre F₁ (fun y hy ↦ Or.inr (Or.inr (Or.inr (Or.inl (by
    addr_omega [hy, hb]))))) (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₁.sp
  have hval : eAt t₁ (s.getReg .x2 - 208) = val := by
    rw [← h.value]
    have m0 := b8000baf8_m_x2_832 h₁
    have m1 := b8000baf8_m_x2_840 h₁
    have m2 := b8000baf8_m_x2_848 h₁
    rw [hsp] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    simp only [eAt]
    rv_eval [m0, m1, m2]
  have hsc : eAt t₁ (s.getReg .x2 - 232) = eAt u (a + 56) := by
    rw [← h.scalar]
    exact F₁.eAt fun i hi hw ↦ by addr_omega [hw, hi, hb]
  -- `mul(S - 256, scalar, value)`
  obtain ⟨t₂, r₂, hd | ⟨hpc₂, hpres₂, F₂, hprod⟩⟩ := callMul (o := s.getReg .x2 - 256)
    (a := s.getReg .x2 - 232) (b := s.getReg .x2 - 208) hM hpre G₁.inv (b8000baf8_pc h₁)
    (by rw [b8000baf8_x10 h₁, hsp]; rv_eval []) (by rw [b8000baf8_x11 h₁, hsp]; rv_eval [])
    (by rw [b8000baf8_x12 h₁, hsp]; rv_eval [])
    ⟨by addr_omega [hb], by addr_omega [hb], by addr_omega [hb]⟩
    ⟨by addr_omega [hb], by addr_omega [hb], by addr_omega [hb]⟩
    ⟨by addr_omega [hb], by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb]) (by addr_omega [hb])
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
  obtain ⟨G₂, -⟩ := G₁.stepS hpre F₂ (fun y hy ↦ by
    rcases hy with hy | hy
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [hy, hb]))))) (hpres₂ .x2 (by decide))
  rw [hsc, hval] at hprod
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₂.sp
  have kw₂ : eAt t₂ (s.getReg .x2 - 184) = acc := by
    rw [← h.wt, F₂.eAt fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb]]
    exact F₁.eAt fun i hi hw ↦ by addr_omega [hw, hi, hb]
  -- `0x8000bb20`: the weight
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000bb20_spec
    (by rw [hpc₂, returnAddress_eq, b8000baf8_x1 h₁]; decide) (by
      rv_eval [sp₂]; and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000bb20_keeps h₃
  have F₃ : DFrame t₂ t₃ fun y ↦ Within y (s.getReg .x2 - 184) 24 := by
    have := DFrame.of_memFrame (b8000bb20_frame h₃ (by rw [sp₂]; addr_omega [hb]))
    rw [sp₂] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  obtain ⟨G₃, -⟩ := G₂.stepS hpre F₃ (fun y hy ↦ Or.inr (Or.inr (Or.inr (Or.inl (by
    addr_omega [hy, hb]))))) (k₃ .x2 (by decide))
  have hw₃ : eAt t₃ (s.getReg .x2 - 184) = acc + eAt u (a + 56) * val := by
    rw [← kw₂, ← hprod, add_comm]
    apply eAt_eq_of_limbs
    rw [limbs_add, limbs_eAt, limbs_eAt]
    have m0 := b8000bb20_m_x2_856 h₃
    have m1 := b8000bb20_m_x2_864 h₃
    have m2 := b8000bb20_m_x2_872 h₃
    rw [sp₂] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rv_eval [m0, m1, m2]
  -- the model: one more claim
  have hfold : gluedFold (Wl.glued.take (j + 1)) (Wl.folds ++ tf) w0 =
      some (acc + eAt u (a + 56) * val) := by
    rw [fin.take_succ h.jlt, gluedFold_snoc, h.fold, h.addr]
    obtain ⟨xs, hx, hev⟩ := h.eval
    simp only [gluedAt] at hx hev
    simp only [Option.bind_eq_bind, Option.bind_some, gluedAt, hx, hev]
    rfl
  have h880 : t₃.getMem (s.getReg .x2 - 880) =
      vecPtr u (s.getReg .x2 - 664) + vecLen u (s.getReg .x2 - 664) * 88 := by
    rw [F₃ _ fun i hi hw ↦ by addr_omega [hw, hi, hb],
      F₂ _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb],
      F₁ _ fun i hi hw ↦ by addr_omega [hw, hi, hb]]
    exact h.m880
  have x8₃ : t₃.getReg .x8 = gAddr u s j + 88 := by
    rw [k₃ .x8 (by decide), hpres₂ .x8 (by decide), b8000baf8_x8 h₁, hsp, h.addr]
    have := h.m872
    rv_eval [] at this ⊢
    rw [this]
  have e160 : t₂.getMem (t₂.getReg .x2 + 160) =
      vecPtr u (s.getReg .x2 - 664) + vecLen u (s.getReg .x2 - 664) * 88 := by
    rw [sp₂, show s.getReg .x2 - BitVec.ofNat 64 1040 + 160 = s.getReg .x2 - 880 by addr_omega [hb],
      F₂ _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb],
      F₁ _ fun i hi hw ↦ by addr_omega [hw, hi, hb]]
    exact h.m880
  have x8₂ : t₂.getReg .x8 = gAddr u s j + 88 := by rw [← x8₃, k₃ .x8 (by decide)]
  obtain ⟨hend, hnext⟩ := claim_next fin h.jlt
  refine ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr ⟨_, hfold, hw₃, G₃, h880, ?_⟩⟩
  by_cases hl : j + 1 = (vecLen u (s.getReg .x2 - 664)).toNat
  · exact Or.inr ⟨hl, b8000bb20_pc_taken h₃ (by rw [x8₂, e160]; exact hend.2 hl)⟩
  · refine Or.inl ⟨by have := h.jlt; omega, b8000bb20_pc_not_taken h₃ (by
      rw [x8₂, e160]; exact fun he ↦ hl (hend.1 he)), by rw [x8₃, hnext]⟩

end Rv64Verifier.Proofs.Pcs.Vso
