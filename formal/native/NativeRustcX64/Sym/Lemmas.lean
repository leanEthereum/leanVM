module

public import NativeRustcX64.Sym.Exec

/-!
# Registers and flags of symbolic states

How `Sym.Match` follows the register and flag updates of the symbolic executor and of Kraken:
Kraken's reads and writes of registers of each width (`get_low`, `set_low`), writing a 64-bit
register (`Match.set64`), setting the flags (`Match.setFlags`); and the widths' reads and writes
(`low_ext`, `low_W64`).
-/

namespace NativeRustcX64.Sym

public section

/-! ## Conditionals -/

theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  simp [h]

theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by
  simp [h]

/-! ## Widths -/

@[simp] theorem low_W64 (x : BitVec 64) : low .W64 x = x := BitVec.setWidth_eq x

@[simp] theorem ext_W64 (v : BitVec 64) : ext .W64 v = v := BitVec.setWidth_eq v

theorem bits_le (w : Width) : w.bits ≤ 64 := by
  cases w <;> decide

theorem bits_eq (w : Width) : w.bits = 8 * w.bytes := by
  cases w <;> rfl

theorem bytes_le (w : Width) : w.bytes ≤ 8 := by
  cases w <;> decide

theorem bytes_pos (w : Width) : 0 < w.bytes := by
  cases w <;> decide

@[simp] theorem low_ext (w : Width) (v : w.type) : low w (ext w v) = v := by
  unfold low ext
  rw [BitVec.setWidth_setWidth_of_le _ (bits_le w), BitVec.setWidth_eq]

theorem toNat_ext (w : Width) (v : w.type) : (ext w v).toNat = v.toNat := by
  unfold ext
  rw [BitVec.toNat_setWidth]
  have := v.isLt
  have : 2 ^ w.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (bits_le w)
  omega

theorem toNat_low (w : Width) (x : BitVec 64) : (low w x).toNat = x.toNat % 2 ^ w.bits :=
  BitVec.toNat_setWidth _ _

theorem take_eq_low (w : Width) (x : BitVec 64) : x.take w.bits = low w x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_low]
  simp [BitVec.take]

@[simp] theorem low_zero (w : Width) : low w (BitVec.ofNat 64 0) = 0#w.bits := by
  cases w <;> rfl

@[simp] theorem low_one (w : Width) : low w (BitVec.ofNat 64 1) = 1#w.bits := by
  cases w <;> rfl

/-! ## Kraken's registers -/

theorem get64_set64_self (regs : Reg64s) (r : Reg64) (v : BitVec 64) :
    (regs.set64 r v).get64 r = v := by
  cases r <;> rfl

theorem get64_set64_ne (regs : Reg64s) {r r' : Reg64} (v : BitVec 64) (h : r ≠ r') :
    (regs.set64 r v).get64 r' = regs.get64 r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

/-- A register of width `w` reads the low `w` bits of its 64-bit register. -/
theorem get_low (regs : Reg64s) (r : Reg64) (w : Width) :
    regs.get (.low r w) = low w (regs.get64 r) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_low]
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

/-! ## Symbolic registers -/

theorem allRegs_idx (r : Reg64) : allRegs[r.idx]? = some r := by
  cases r <;> rfl

theorem Reg64.idx_inj {r r' : Reg64} (h : r.idx = r'.idx) : r = r' := by
  have h1 := allRegs_idx r
  rw [h, allRegs_idx r'] at h1
  exact (Option.some.inj h1).symm

theorem SState.reg_setReg (S : SState) (r r' : Reg64) (v : Option Sym) {u : Sym}
    (h : (S.setReg r v).reg r' = some u) :
    (r = r' ∧ v = some u) ∨ (r ≠ r' ∧ S.reg r' = some u) := by
  unfold SState.reg SState.setReg at h
  rw [List.getElem?_set] at h
  by_cases hr : r = r'
  · subst hr
    left
    refine ⟨rfl, ?_⟩
    split at h
    · split at h
      · exact h
      · simp at h
    · exact absurd rfl ‹¬_›
  · right
    refine ⟨hr, ?_⟩
    split at h
    · exact absurd (Reg64.idx_inj ‹_›) hr
    · exact h

/-! ## `Match` and registers, flags -/

variable [Labels] {env : Env} {S : SState} {m : MachineData}

theorem Match.set64 (hm : Match env S m) (r : Reg64) {v : Option Sym} {x : BitVec 64}
    (hv : ∀ u, v = some u → u.eval env = x) :
    Match env (S.setReg r v) { m with regs := m.regs.set64 r x } := by
  refine ⟨fun r' u h => ?_, hm.flags, hm.regions, hm.mem, hm.labels, hm.bounds, hm.aliases,
    hm.outside, hm.known, hm.roRegions⟩
  rcases S.reg_setReg r r' v h with ⟨rfl, hu⟩ | ⟨hne, hu⟩
  · show (m.regs.set64 r x).get64 r = _
    rw [get64_set64_self, hv u hu]
  · show (m.regs.set64 r x).get64 r' = _
    rw [get64_set64_ne _ _ hne]
    exact hm.regs r' u hu

theorem Match.setFlags (hm : Match env S m) (f : SFlags) {st : StatusFlags}
    (hf : FlagsOk env f st) : Match env (S.setFlags f) { m with status := st } :=
  ⟨hm.regs, hf, hm.regions, hm.mem, hm.labels, hm.bounds, hm.aliases, hm.outside, hm.known,
    hm.roRegions⟩

theorem flagsOk_unknown (st : StatusFlags) : FlagsOk env unknownFlags st :=
  ⟨nofun, nofun, nofun, nofun⟩

theorem Match.getR (hm : Match env S m) {w : Width} {r : Reg w} {u : Sym}
    (h : S.getR r = some u) : m.regs.get r = low w (u.eval env) := by
  cases r with
  | low r w => rw [get_low, hm.regs r u h]
  | _ => cases h

end

end NativeRustcX64.Sym
