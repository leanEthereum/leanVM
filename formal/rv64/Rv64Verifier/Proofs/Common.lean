import Rv64Verifier.Sym.Facts
import Rv64Verifier.Repr

/-!
# What every function proof uses

Besides `Sym/Facts.lean` (byte ranges, memory frames, the generated blocks' lemmas, `rv_eval`,
`addr_omega`):

* riscv-zkvm's `ValidMemRange` read as an interval (`ValidMemRange.bounds`, `.access`, `.sub`)
  and `valid_access` for a side condition `validAccess 8 x`.
* The stack below `sp` (`stackLo`, `StackOk`).
* `E` values in memory (`MemFrame.eAt`, `limbs_add`, `limbs_one`, `eAt_eq_of_limbs`,
  `eAt_congr`).
* Calls that never return (`FunSpec.call_dead`), traps (`dead_of_fetch`), the callee-saved
  registers (`Preserves.reg`, `preserves_of`), branches (`ite_bne_of_eq`, `ite_bne_of_ne`).
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64 LeanVM.Parameters CompPoly.Extension

theorem validAccess_of_dword {a : Word} (h : isValidDwordAccess a = true) :
    Sym.validAccess 8 a = true :=
  h

/-- A nonempty valid range lies in the machine's memory, aligned. -/
theorem ValidMemRange.bounds {a : Word} {n : Nat} (h : ValidMemRange a n) (hn : 0 < n) :
    0x20 ≤ a.toNat ∧ a.toNat % 8 = 0 ∧ a.toNat + 8 * n ≤ 0xc0000008 := by
  have h0 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h 0 hn))
  simp only [Nat.mul_zero, BitVec.add_zero] at h0
  refine ⟨by omega, h0.2, Classical.byContradiction fun hc ↦ ?_⟩
  have hi := (Sym.validAccess_eight _).mp
    (validAccess_of_dword (h ((0xc0000008 - a.toNat) / 8) (by omega)))
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at hi
  omega

/-- Every aligned doubleword of a valid range is a valid access. -/
theorem ValidMemRange.access {a : Word} {n : Nat} (h : ValidMemRange a n) {x : Word}
    (h1 : a.toNat ≤ x.toNat) (h2 : x.toNat < a.toNat + 8 * n) (h3 : x.toNat % 8 = a.toNat % 8) :
    Sym.validAccess 8 x = true := by
  have hx : x = a + BitVec.ofNat 64 (8 * ((x.toNat - a.toNat) / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := x.isLt
    omega
  rw [hx]
  exact h _ (by omega)

/-- A valid range's aligned subrange is valid. -/
theorem ValidMemRange.sub {a b : Word} {n m : Nat} (h : ValidMemRange a n)
    (h1 : a.toNat ≤ b.toNat) (h2 : b.toNat + 8 * m ≤ a.toNat + 8 * n)
    (h3 : b.toNat % 8 = a.toNat % 8) :
    ValidMemRange b m := by
  intro i hi
  have hb := ValidMemRange.bounds h (by omega)
  refine ValidMemRange.access h ?_ ?_ ?_ <;> rw [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

/-! ## The stack -/

/-- The lowest of the `n` bytes below `sp`. -/
@[rv_addr] def stackLo (s : MachineState) (n : Nat) : Word := s.getReg .x2 - BitVec.ofNat 64 n

/-- The `n` bytes below `sp` are valid memory, and `sp` is 16-aligned. -/
structure StackOk (s : MachineState) (n : Nat) : Prop where
  valid : ValidMemRange (stackLo s n) (n / 8)
  aligned : (s.getReg .x2).toNat % 16 = 0

/-- `sp` as a number, for `omega`. -/
theorem StackOk.bounds {s : MachineState} {n : Nat} (h : StackOk s n) (hn : 8 ≤ n)
    (h8 : n % 8 = 0) :
    0x20 + n ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (stackLo s n).toNat = (s.getReg .x2).toNat - n := by
  have hb := ValidMemRange.bounds h.valid (by omega)
  have ha := h.aligned
  simp only [stackLo, BitVec.toNat_sub, BitVec.toNat_ofNat] at hb ⊢
  have := (s.getReg .x2).isLt
  omega

/-- `valid_access h [f₁, ..]`: a doubleword access inside the valid range `h`, its bounds by
`addr_omega [f₁, ..]`. -/
macro "valid_access " h:term:max " [" ts:term,* "]" : tactic =>
  `(tactic| (refine ValidMemRange.access $h ?_ ?_ ?_ <;> addr_omega [$ts,*]))

/-- `valid_sub h [f₁, ..]`: an aligned part of the valid range `h` is valid, its bounds by
`addr_omega [f₁, ..]`. -/
macro "valid_sub " h:term:max " [" ts:term,* "]" : tactic =>
  `(tactic| (refine ValidMemRange.sub $h ?_ ?_ ?_ <;> addr_omega [$ts,*]))

/-! ## `E` in memory -/

/-- An `E` outside a frame's range is unchanged. -/
theorem MemFrame.eAt {s t : MachineState} {lo : Word} {n : Nat} (h : MemFrame s t lo n) {p : Word}
    (hp : Apart p 24 lo n) (hw : p.toNat + 24 ≤ 2 ^ 64) : eAt t p = eAt s p := by
  unfold Rv64Verifier.eAt
  rw [h p (by addr_omega [hp, hw]), h (p + 8) (by addr_omega [hp, hw]),
    h (p + 16) (by addr_omega [hp, hw])]

theorem coeffNat_add (x y : E) (i : Nat) :
    Ext.coeffNat (x + y) i = Ext.coeffNat x i + Ext.coeffNat y i := by
  unfold Ext.coeffNat
  split
  · exact Ext.coeff_add x y _
  · simp

theorem limbs_add (x y : E) : Model.limbs (x + y) =
    ((Model.limbs x).1 ^^^ (Model.limbs y).1, (Model.limbs x).2.1 ^^^ (Model.limbs y).2.1,
      (Model.limbs x).2.2 ^^^ (Model.limbs y).2.2) := by
  simp only [Model.limbs, coeffNat_add, Model.toBitVec_add]

theorem limbs_one : Model.limbs (1 : E) = (1, 0, 0) := by
  decide +kernel

theorem eAt_eq_of_limbs {t : MachineState} {a : Word} {x : E}
    (h : (t.getMem a, t.getMem (a + 8), t.getMem (a + 16)) = Model.limbs x) : eAt t a = x :=
  eq_of_limbs (by rw [limbs_eAt, h])

/-- Two `E`s whose limbs agree are equal. -/
theorem eAt_congr {s t : MachineState} {a b : Word} (h0 : t.getMem a = s.getMem b)
    (h1 : t.getMem (a + 8) = s.getMem (b + 8)) (h2 : t.getMem (a + 16) = s.getMem (b + 16)) :
    eAt t a = eAt s b := by
  simp only [eAt, h0, h1, h2]

/-! ## Calls and the frame -/

/-- A call to a function that never returns reaches a dead end. -/
theorem FunSpec.call_dead {code : Code} {entry : Word} {pre : MachineState → Prop}
    (h : FunSpec code entry pre fun _ _ ↦ False) {c c' : MachineState} (hjump : Reaches code c c')
    (hpc : c'.pc = entry) (hpre : pre c') : ∃ t, Reaches code c t ∧ Dead code t := by
  obtain ⟨t, ht, ⟨-, -, hf⟩ | hd⟩ := h.call hjump hpc hpre
  · exact hf.elim
  · exact ⟨t, ht, hd⟩

/-- A word that does not decode (`unimp`) traps: a dead end. -/
theorem dead_of_fetch {code : Code} {t : MachineState} (h : code.fetch t.pc = none) :
    Dead code t := by
  refine ⟨by simp [step, h], fun hh ↦ ?_⟩
  rw [Halting, h] at hh
  cases hh.1

theorem Preserves.reg {s t : MachineState} (h : Preserves s t) (r : Reg)
    (hr : r ∈ calleeSaved := by decide) : t.getReg r = s.getReg r :=
  h r hr

/-- `Preserves` from each callee-saved register. -/
theorem preserves_of {s t : MachineState} (h2 : t.getReg .x2 = s.getReg .x2)
    (h8 : t.getReg .x8 = s.getReg .x8) (h9 : t.getReg .x9 = s.getReg .x9)
    (h18 : t.getReg .x18 = s.getReg .x18) (h19 : t.getReg .x19 = s.getReg .x19)
    (hrest : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
      t.getReg r = s.getReg r) :
    Preserves s t := by
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr | hr | hr | hr | hr | hr | hr | hr <;>
    first | assumption | exact hrest _ (by simp [hr])

/-- A branch on `a != b` whose operands are equal falls through. -/
theorem ite_bne_of_eq {a b x y : Word} (h : a = b) : (if (a != b) = true then x else y) = y := by
  simp [h]

/-- A branch on `a != b` whose operands differ is taken. -/
theorem ite_bne_of_ne {a b x y : Word} (h : a ≠ b) : (if (a != b) = true then x else y) = x := by
  simp [h]

theorem returnAddress_eq (s : MachineState) :
    returnAddress s = s.getReg .x1 &&& 0xfffffffffffffffe := rfl

end Rv64Verifier
