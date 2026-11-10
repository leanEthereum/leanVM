import Rv64Verifier.Proofs.Bus.VbbGkrEqs

/-!
# `verify_bus_balance`: an iteration's sumcheck

`count = (1 << step) + 1` (`4 >> (layer & 1)` plus one, `b8000677c_x19'`, `b8000677c_x13'`),
`sumcheck` on the claim at `S - 152` and `equalities`, into `S - 608` (`Err` to `0x80007100`,
`err7100`); the point `x` kept in `s10`/`s0`/`s5`, the claim in `s7`, `S - 1208`, `S - 1216`; to
the first `next_scalars`' entry (`AtNs`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem and_one_toNat (x : Word) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]
  exact Nat.and_one_is_mod _

theorem b8000677c_x19' {s t : MachineState} (h : b8000677c.Holds s t) {n : Nat}
    (hn : (s.getReg .x25).toNat = n) : t.getReg .x19 = BitVec.ofNat 64 (2 ^ stepOf n) :=
  h.reg_eq .x19 rfl (by
    rv_eval []
    rw [and_one_toNat, hn]
    unfold stepOf
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h0 <;> simp only [h0] <;> decide)

theorem b8000677c_x13' {s t : MachineState} (h : b8000677c.Holds s t) {n : Nat}
    (hn : (s.getReg .x25).toNat = n) : t.getReg .x13 = BitVec.ofNat 64 (2 ^ stepOf n + 1) :=
  h.reg_eq .x13 rfl (by
    rv_eval []
    rw [and_one_toNat, hn]
    unfold stepOf
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h0 <;> simp only [h0] <;> decide)

theorem stepOf_le (n : Nat) : 1 ≤ stepOf n ∧ stepOf n ≤ 2 := by
  unfold stepOf; split <;> omega

/-- The `Err` exit through `0x80007100` (`s2` reloaded) of a run the mirror fails. -/
theorem err7100 {bev : MachineState → Word → List E → Option E} {s u : MachineState} {k : Start}
    (hpre : BusBalancePre s) (h : Inv s u) (hk : Kept s u k) (hpc : u.pc = 0x80007100)
    (hnone : ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) :
    ∃ t, Reaches Image.code u t ∧ Done bev s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := h.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007100_spec hpc (by
    rv_eval [sp]
    valid_access hval [hb1])
  have m₁ := b80007100_mem_same h₁
  obtain ⟨t, hrt, hd⟩ := errDone (bev := bev) hpre (h.same m₁ (b80007100_keeps h₁ .x2 (by decide)))
    (by
      rw [b80007100_x18 h₁, sp, show s.getReg .x2 - 1344 + 32 = s.getReg .x2 - 1312 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      exact hk.out) (b80007100_pc h₁) hnone
  exact ⟨t, hr₁.trans hrt, hd⟩

/-- At the first `next_scalars`' entry: `x` in `s10`/`s0`/`s5`, the claim `cl`. -/
structure AtNs (s u w : MachineState) (k : Start) (cnt : E) (P : Word) (n : ℕ) (comb : E)
    (x : List E) (cl : E) : Prop where
  ctx : Ctx s w k cnt P
  regs : ∀ r ∈ ([.x9, .x20, .x24, .x25] : List Reg), w.getReg r = u.getReg r
  x19 : w.getReg .x19 = BitVec.ofNat 64 (2 ^ stepOf n)
  x22 : (w.getReg .x22).toNat = n % 2
  x1 : w.getReg .x1 = 0x800067dc
  x10 : w.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608
  x11 : w.getReg .x11 = s.getReg .x12
  x12 : w.getReg .x12 = BitVec.ofNat 64 (2 ^ stepOf n)
  combAt : eAt w (s.getReg .x2 - BitVec.ofNat 64 128) = comb
  valuesPtr : w.getMem (s.getReg .x2 - 1280) = P
  xv : NewVecR u w (w.getReg .x26) (w.getReg .x8) (w.getReg .x21) x
  claimAt : eOf3 (w.getReg .x23) (w.getMem (s.getReg .x2 - 1208)) (w.getMem (s.getReg .x2 - 1216)) = cl
  step : StepR s u w (Scratch s)

theorem optEListAt_same {v w : MachineState} (hm : ∀ a, w.getMem a = v.getMem a) (p : Word)
    (n : Nat) : optEListAt w p n = optEListAt v p n := by
  simp only [optEListAt, optEAt, Rv64Verifier.eAt, hm]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
