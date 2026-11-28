module

public import NativeRustcArm.Sym.Exec

/-!
# Registers and flags of symbolic states

How `Sym.Match` follows the register and flag updates of the symbolic executor and of Kraken:
reading a register operand (`Match.getZr`, `Match.getSp`), writing one (`Match.setZr`,
`Match.setSp`), setting the flags (`Match.setFlags`); and the widths' reads and writes
(`low_ext`, `low_W64`).
-/

namespace NativeRustcArm.Sym

public section

/-! ## Conditionals -/

theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  simp [h]

theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by
  simp [h]

/-! ## Widths -/

@[simp] theorem low_W64 (x : BitVec 64) : low .W64 x = x := BitVec.extractLsb'_eq_self

@[simp] theorem ext_W64 (v : BitVec 64) : ext .W64 v = v := rfl

theorem ext_W32 (v : BitVec 32) : ext .W32 v = v.setWidth 64 := rfl

theorem low_W32 (x : BitVec 64) : low .W32 x = x.setWidth 32 := by
  simp [low, BitVec.take, BitVec.setWidth_eq_extractLsb']

@[simp] theorem low_ext (w : RegWidth) (v : w.type) : low w (ext w v) = v := by
  cases w
  · show low .W32 (v.setWidth 64) = v
    rw [low_W32, BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact BitVec.setWidth_eq v
  · exact low_W64 v

theorem ext_low_W64 (x : BitVec 64) : ext .W64 (low .W64 x) = x := low_W64 x

/-! ## Kraken's registers -/

theorem getXReg_setXReg_self (regs : Reg64s) (r : XReg) (v : BitVec 64) :
    (regs.setXReg r v).getXReg r = UInt64.ofBitVec v := by
  cases r <;> rfl

theorem getXReg_setXReg_ne (regs : Reg64s) {r r' : XReg} (v : BitVec 64) (h : r ≠ r') :
    (regs.setXReg r v).getXReg r' = regs.getXReg r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

theorem SP_setXReg (regs : Reg64s) (r : XReg) (v : BitVec 64) : (regs.setXReg r v).SP = regs.SP := by
  cases r <;> rfl

theorem getXReg_setSP (regs : Reg64s) (r : XReg) (v : UInt64) :
    ({ regs with SP := v } : Reg64s).getXReg r = regs.getXReg r := by
  cases r <;> rfl

/-! ## Symbolic registers -/

theorem allXRegs_idx (r : XReg) : allXRegs[r.idx]? = some r := by
  cases r <;> rfl

theorem XReg.idx_inj {r r' : XReg} (h : r.idx = r'.idx) : r = r' := by
  have h1 := allXRegs_idx r
  rw [h, allXRegs_idx r'] at h1
  exact (Option.some.inj h1).symm

theorem SState.reg_setReg (S : SState) (r r' : XReg) (v : Option Sym) {u : Sym}
    (h : (S.setReg r v).reg r' = some u) : (r = r' ∧ v = some u) ∨ (r ≠ r' ∧ S.reg r' = some u) := by
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
    · exact absurd (XReg.idx_inj ‹_›) hr
    · exact h

/-! ## `Match` and registers -/

variable [Labels] {env : Env} {S : SState} {m : MachineData}

theorem Match.setX (hm : Match env S m) (r : XReg) {v : Option Sym} {x : BitVec 64}
    (hv : ∀ u, v = some u → u.eval env = x) :
    Match env (S.setReg r v) { m with regs := m.regs.setXReg r x } := by
  refine ⟨fun r' u h => ?_, ?_, hm.flags, hm.regions, hm.mem, hm.labels, hm.bounds, hm.aliases, hm.outside⟩
  · rcases S.reg_setReg r r' v h with ⟨rfl, hu⟩ | ⟨hne, hu⟩
    · show ((m.regs.setXReg r x).getXReg r).toBitVec = _
      rw [getXReg_setXReg_self, hv u hu]
    · show ((m.regs.setXReg r x).getXReg r').toBitVec = _
      rw [getXReg_setXReg_ne _ _ hne]
      exact hm.regs r' u hu
  · show (m.regs.setXReg r x).SP.toBitVec = _
    rw [SP_setXReg]
    exact hm.sp

theorem Match.setZr (hm : Match env S m) {w : RegWidth} (r : RegOrZr w) {u : Sym} {x : w.type}
    (hv : u.eval env = ext w x) :
    Match env (S.setZr r u) { m with regs := m.regs.setRegOrZr r x } := by
  obtain ⟨b, w⟩ := r
  cases b with
  | XZR => cases w <;> exact hm
  | reg x' => cases w <;> exact hm.setX x' (fun _ h => (Option.some.inj h) ▸ hv)

theorem Match.setSp (hm : Match env S m) {w : RegWidth} (r : RegOrSp w) {u : Sym} {x : w.type}
    (hv : u.eval env = ext w x) :
    Match env (S.setSp r u) { m with regs := m.regs.setRegOrSp r x } := by
  obtain ⟨b, w⟩ := r
  cases b with
  | SP =>
    have h : Match env { S with sp := u }
        { m with regs := { m.regs with SP := UInt64.ofBitVec (ext w x) } } :=
      ⟨fun r v h => by
          show (({ m.regs with SP := _ } : Reg64s).getXReg r).toBitVec = _
          rw [getXReg_setSP]
          exact hm.regs r v h,
        by
          show (UInt64.ofBitVec (ext w x)).toBitVec = _
          rw [hv],
        hm.flags, hm.regions, hm.mem, hm.labels, hm.bounds, hm.aliases, hm.outside⟩
    cases w <;> exact h
  | reg x' => cases w <;> exact hm.setX x' (fun _ h => (Option.some.inj h) ▸ hv)

theorem Match.getZr64 (hm : Match env S m) {r : XRegOrXzr} {u : Sym} (h : S.getZr64 r = some u) :
    m.regs.getRegOrZr64 r = u.eval env := by
  cases r with
  | XZR =>
    cases h
    rfl
  | reg x => exact hm.regs x u h

theorem Match.getSp64 (hm : Match env S m) {r : XRegOrSp} {u : Sym} (h : S.getSp64 r = some u) :
    m.regs.getRegOrSp64 r = u.eval env := by
  cases r with
  | SP =>
    cases h
    exact hm.sp
  | reg x => exact hm.regs x u h

theorem Match.getZr (hm : Match env S m) {w : RegWidth} {r : RegOrZr w} {u : Sym}
    (h : S.getZr r = some u) : m.regs.getRegOrZr r = low w (u.eval env) := by
  show (m.regs.getRegOrZr64 r.base).take w.bits = _
  rw [hm.getZr64 h]
  rfl

theorem Match.getSp (hm : Match env S m) {w : RegWidth} {r : RegOrSp w} {u : Sym}
    (h : S.getSp r = some u) : m.regs.getRegOrSp r = low w (u.eval env) := by
  show (m.regs.getRegOrSp64 r.base).take w.bits = _
  rw [hm.getSp64 h]
  rfl

/-! ## `Match` and flags -/

theorem Match.setFlags (hm : Match env S m) (f : SFlags) {st : StatusFlags} (hf : f.eval env = st) :
    Match env (S.setFlags f) { m with status := st } :=
  ⟨hm.regs, hm.sp, fun g h => by cases h; exact hf.symm, hm.regions, hm.mem, hm.labels, hm.bounds, hm.aliases, hm.outside⟩

theorem Match.flagsEq (hm : Match env S m) {f : SFlags} (h : S.flags = some f) :
    m.status = f.eval env := hm.flags f h

end

end NativeRustcArm.Sym
