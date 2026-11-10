import Rv64Verifier.Proofs.Pcs.RingSwitchCtx

/-!
# `ring_switch`: the coefficient loop's states

`CS pc k j a` is the stage loop at `pc` (`0x800098d4` before stage `j`, `0x800098c4` after it),
the accumulator holding `cacc ch k a`; `CPush` is `0x8000982c`, coefficient `k` done; `CDone` is
`0x8000994c`, all 64 pushed. Words the loop never writes are read off the base `B1` (`keepF`,
`keepS`, `keepH`).
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Frames of calls -/

theorem dframe_of_two {u v : MachineState} {W₁ W₂ : Word → Prop}
    (h : ∀ a, ¬ W₁ a → ¬ W₂ a → v.getMem a = u.getMem a) : DFrame u v fun a ↦ W₁ a ∨ W₂ a := by
  intro a ha
  have h0 := ha 0 (by decide)
  rw [add_ofNat_zero] at h0
  exact h a (fun h' ↦ h0 (Or.inl h')) fun h' ↦ h0 (Or.inr h')

theorem dframe_of_three {u v : MachineState} {W₁ W₂ W₃ : Word → Prop}
    (h : ∀ a, ¬ W₁ a → ¬ W₂ a → ¬ W₃ a → v.getMem a = u.getMem a) :
    DFrame u v fun a ↦ W₁ a ∨ W₂ a ∨ W₃ a := by
  intro a ha
  have h0 := ha 0 (by decide)
  rw [add_ofNat_zero] at h0
  exact h a (fun h' ↦ h0 (Or.inl h')) (fun h' ↦ h0 (Or.inr (Or.inl h')))
    fun h' ↦ h0 (Or.inr (Or.inr h'))

/-! ## Words the coefficient loop never writes -/

section
variable {s B1 u : MachineState} {C chP nx : Word} {ch : List E}

/-- A word of the frame below the scratch. -/
theorem keepF (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch) (h : Ph B1 u (w1 s C) nx)
    {a : Word} (h1 : (s.getReg .x2).toNat - 464 ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 312 ∨
      (s.getReg .x2).toNat - 104 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat) :
    u.getMem a = B1.getMem a := by
  have hb := bounds hpre
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  have hsp := hctx.sp
  have hfit := h.fits
  refine DFrame.word h.mem (fun x hx hW ↦ ?_) (by addr_omega [h2, hb])
  rcases hW with (hW | hW) | hW | hW | hW
  · addr_omega [hW, hx, h1, h2, hb]
  · addr_omega [hW, hx, h1, hC, hH, hb]
  · simp only [stackLo, hsp] at hW; addr_omega [hW, hx, h1, h2, hb]
  · addr_omega [hW, hx, h1, hb]
  · addr_omega [hW.2, hx, h1, hfit, hb]

/-- A heap word below `C`. -/
theorem keepH (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch) (h : Ph B1 u (w1 s C) nx)
    {a : Word} (h1 : a.toNat + 8 ≤ C.toNat) : u.getMem a = B1.getMem a := by
  have hb := bounds hpre
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  have hsp := hctx.sp
  refine DFrame.word h.mem (fun x hx hW ↦ ?_) (by addr_omega [h1, hC, hH])
  rcases hW with (hW | hW) | hW | hW | hW
  · addr_omega [hW, hx, h1, hC, hH, hb]
  · addr_omega [hW, hx, h1, hC, hH]
  · simp only [stackLo, hsp] at hW; addr_omega [hW, hx, h1, hC, hH, hb]
  · addr_omega [hW, hx, h1, hC, hH]
  · addr_omega [hW.1, hx, h1, hC]

/-- Challenge `j`. -/
theorem keepCh (hpre : RingSwitchPre s) (hctx : Ctx s B1 C chP ch) (h : Ph B1 u (w1 s C) nx)
    {j : Nat} (hj : j < 6) : eAt u (chP + BitVec.ofNat 64 (24 * j)) = ch.getD j 0 := by
  have hcC := hctx.chC
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  have e : ch.getD j 0 = eAt B1 (chP + BitVec.ofNat 64 (24 * j)) := by
    rw [← hctx.chs, List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hj), eListAt_getElem]
  rw [e]
  unfold eAt
  rw [keepH hpre hctx h (by addr_omega [hj, hcC, hC, hH]),
    keepH hpre hctx h (by addr_omega [hj, hcC, hC, hH]),
    keepH hpre hctx h (by addr_omega [hj, hcC, hC, hH])]

end

/-! ## Words and numbers -/

theorem shifts_of {u : MachineState} {S : Word} (h0 : u.getMem (S - 192) = 32)
    (h1 : u.getMem (S - 184) = 16) (h2 : u.getMem (S - 176) = 8) (h3 : u.getMem (S - 168) = 4)
    (h4 : u.getMem (S - 160) = 2) (h5 : u.getMem (S - 152) = 1) :
    ∀ i < 6, u.getMem (S - 192 + BitVec.ofNat 64 (8 * i)) = shiftW i := by
  intro i hi
  interval_cases i <;> simp only [Nat.reduceMul] <;> rv_eval [] <;>
    simp only [shiftW, ringMapShiftsRust, List.getD_cons_zero, List.getD_cons_succ] <;> assumption

theorem and_toNat (j k : ℕ) (hj : j < 6) (hk : k < 64) :
    (shiftW j &&& BitVec.ofNat 64 k).toNat = k &&& ringMapShiftsRust.getD j 0 := by
  rw [BitVec.toNat_and, shift_toNat j hj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.land_comm]

theorem remu_toNat (j k : ℕ) (hj : j < 6) (hk : k < 64) :
    (rv64_remu (BitVec.ofNat 64 k) (shiftW j)).toNat = k % ringMapShiftsRust.getD j 0 := by
  have hp := shift_pos j hj
  have hne : (shiftW j == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0
    have := congrArg BitVec.toNat h0
    rw [shift_toNat j hj, show (0#64).toNat = 0 from rfl] at this; omega
  rw [rv64_remu, hne]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_umod, BitVec.toNat_ofNat,
    shift_toNat j hj]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

/-! ## The states -/

/-- The stage loop at `pc`, position `j`, the accumulator after `a` stages. -/
structure CS (s B1 u : MachineState) (C chP : Word) (ch : List E) (nx pc : Word) (k j a : Nat) :
    Prop extends CRegs s u C where
  ph : Ph B1 u (w1 s C) nx
  pc : u.pc = pc
  lt : k < 64
  ltj : j < 6
  x22 : u.getReg .x22 = BitVec.ofNat 64 k
  x26 : u.getReg .x26 = BitVec.ofNat 64 k
  x8 : u.getReg .x8 = s.getReg .x2 - 192 + BitVec.ofNat 64 (8 * j)
  x21 : u.getReg .x21 = BitVec.ofNat 64 (6 - j)
  x25 : u.getReg .x25 = chP + BitVec.ofNat 64 (24 * j)
  acc : eAt u (s.getReg .x2 - 312) = cacc ch k a
  shifts : ∀ i < 6, u.getMem (s.getReg .x2 - 192 + BitVec.ofNat 64 (8 * i)) = shiftW i
  buf : ∀ l < k, eAt u (C + BitVec.ofNat 64 (24 * l)) = cacc ch l 6

/-- At `0x8000982c`: coefficient `k` done. -/
structure CPush (s B1 u : MachineState) (C : Word) (ch : List E) (nx : Word) (k : Nat) : Prop
    extends CRegs s u C where
  ph : Ph B1 u (w1 s C) nx
  pc : u.pc = 0x8000982c
  lt : k < 64
  x22 : u.getReg .x22 = BitVec.ofNat 64 k
  x26 : u.getReg .x26 = BitVec.ofNat 64 k
  acc : eAt u (s.getReg .x2 - 312) = cacc ch k 6
  buf : ∀ l < k, eAt u (C + BitVec.ofNat 64 (24 * l)) = cacc ch l 6

/-- At `0x8000994c`: the 64 coefficients pushed. -/
structure CDone (s B1 u : MachineState) (C : Word) (ch : List E) (nx : Word) : Prop where
  ph : Ph B1 u (w1 s C) nx
  pc : u.pc = 0x8000994c
  x22 : u.getReg .x22 = 64
  x23 : u.getReg .x23 = s.getReg .x11
  buf : ∀ l < 64, eAt u (C + BitVec.ofNat 64 (24 * l)) = cacc ch l 6

end Rv64Verifier.Proofs.Pcs.RingSwitch
