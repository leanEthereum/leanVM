module

public import NativeRustcVmArm.Ring.Target.Calls

/-!
# `ring_target`: the descriptions between the calls after the images loop

The table's entries in terms of the model (`tv_f`, `tv_z`, `tv_p`, `tv_t`, `tv_m`), the results of
the calls as the steps state them (`hrZ`, `hrP`, `hrT`, `hrM`), and the descriptions `K<k>`: what
holds after block `k` (before its call) in callee-saved registers, frame words and `f`'s words.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- `f`'s words. -/
def fD : List (Sym × Nat) :=
  [(.load 1 0 8, 0), (.load 1 8 8, 1), (.load 1 16 8, 2), (.load 1 24 8, 3), (.load 1 32 8, 4),
    (.load 1 40 8, 5), (.load 1 48 8, 6), (.load 1 56 8, 7), (.load 1 64 8, 8), (.load 1 72 8, 9),
    (.load 1 80 8, 10), (.load 1 88 8, 11), (.load 1 96 8, 12), (.load 1 104 8, 13),
    (.load 1 112 8, 14), (.load 1 120 8, 15)]

/-- `f`'s words and its address in X21. -/
def bD : List (Sym × Nat) := (.reg .X21, fPtr) :: fD

/-- An element stored high limb first at frame byte `off`. -/
def fr (off i : Nat) : List (Sym × Nat) := [(.load 0 off 8, i + 1), (.load 0 (off + 8) 8, i)]

/-- An element in two registers. -/
def r2 (a b : XReg) (i : Nat) : List (Sym × Nat) := [(.reg a, i), (.reg b, i + 1)]

/-- `f_p` and `T_p` in the frame, `p = 7 … 3`. -/
def FT7 : List (Sym × Nat) := fr 192 (fI 7) ++ fr 176 (tI 7)
def FT6 : List (Sym × Nat) := fr 160 (fI 6) ++ fr 144 (tI 6)
def FT5 : List (Sym × Nat) := fr 128 (fI 5) ++ fr 112 (tI 5)
def FT4 : List (Sym × Nat) := fr 96 (fI 4) ++ fr 80 (tI 4)
def FT3 : List (Sym × Nat) := fr 64 (fI 3) ++ fr 32 (tI 3)
def FTs : List (Sym × Nat) := FT3 ++ FT4 ++ FT5 ++ FT6 ++ FT7

/-- `f_0` at frame byte `48`. -/
def f0D : List (Sym × Nat) := [(.load 0 48 8, 0), (.load 0 56 8, 1)]

/-- Before `b4`. -/
def D4 : List (Sym × Nat) := (.lit 2, gI) :: (.lit 0, gI + 1) :: bD

def K5 : List (Sym × Nat) := r2 .X19 .X20 (zI 7) ++ fr 192 (fI 7) ++ bD
def K7 : List (Sym × Nat) := FT7 ++ bD
def K8 : List (Sym × Nat) := r2 .X19 .X20 (zI 6) ++ fr 160 (fI 6) ++ FT7 ++ bD
def K10 : List (Sym × Nat) := FT6 ++ FT7 ++ bD
def K11 : List (Sym × Nat) := r2 .X19 .X20 (zI 5) ++ fr 128 (fI 5) ++ FT6 ++ FT7 ++ bD
def K13 : List (Sym × Nat) := FT5 ++ FT6 ++ FT7 ++ bD
def K14 : List (Sym × Nat) := r2 .X19 .X20 (zI 4) ++ fr 96 (fI 4) ++ FT5 ++ FT6 ++ FT7 ++ bD
def K16 : List (Sym × Nat) := FT4 ++ FT5 ++ FT6 ++ FT7 ++ bD
def K17 : List (Sym × Nat) := r2 .X20 .X22 (zI 3) ++ fr 64 (fI 3) ++ FT4 ++ FT5 ++ FT6 ++ FT7 ++ bD
def K19 : List (Sym × Nat) := FTs ++ bD
def K20 : List (Sym × Nat) := r2 .X20 .X22 (zI 2) ++ r2 .X24 .X25 (fI 2) ++ FTs ++ bD
def K22 : List (Sym × Nat) := r2 .X24 .X25 (fI 2) ++ r2 .X27 .X28 (tI 2) ++ FTs ++ bD
def K23 : List (Sym × Nat) := r2 .X20 .X22 (zI 1) ++ r2 .X23 .X26 (fI 1) ++ K22
def K25 : List (Sym × Nat) := r2 .X19 .X29 (tI 1) ++ r2 .X23 .X26 (fI 1) ++ K22
def K26 : List (Sym × Nat) := fr 16 (zI 0) ++ f0D ++ K22
/-- The products from `M_1`, without X21. -/
def Ms27 : List (Sym × Nat) :=
  [(.load 0 8 8, mI 1), (.reg .X26, mI 1 + 1)] ++ fr 16 (zI 0) ++ f0D ++ FTs ++ fD
def Ms28 : List (Sym × Nat) := r2 .X19 .X24 (mI 2) ++ Ms27
def Ms29 : List (Sym × Nat) := r2 .X25 .X27 (mI 3) ++ Ms28
def Ms30 : List (Sym × Nat) := r2 .X28 .X29 (mI 4) ++ Ms29
def K31 : List (Sym × Nat) := r2 .X21 .X20 (mI 5) ++ Ms30
def K32 : List (Sym × Nat) := r2 .X22 .X23 (mI 6) ++ K31
/-- The sum `M_1 + … + M_7`'s limbs. -/
def sD : List (Sym × Nat) := [(.reg .X20, sI), (.reg .X19, sI + 1)]

end

public section

variable {m0 : MachineData}

/-! ## The table -/

theorem tv_f {p : Nat} (hp : p < 8) :
    (⟨tv m0 (fI p), tv m0 (fI p + 1)⟩ : EW) = (fl m0).getD p 0 := by
  have e0 : tv m0 (fI p) = ((fl m0).getD p 0).c0 := by
    unfold tv fI
    rw [ite_eq_left (by omega), show 2 * p / 2 = p by omega, show 2 * p % 2 = 0 by omega]
    rfl
  have e1 : tv m0 (fI p + 1) = ((fl m0).getD p 0).c1 := by
    unfold tv fI
    rw [ite_eq_left (by omega), show (2 * p + 1) / 2 = p by omega, show (2 * p + 1) % 2 = 1 by omega]
    rfl
  rw [e0, e1]

theorem tv_z {p : Nat} (hp : p < 8) : (⟨tv m0 (zI p), tv m0 (zI p + 1)⟩ : EW) = zV p := by
  have e0 : tv m0 (zI p) = (zV p).c0 := by
    unfold tv zI
    rw [ite_eq_right (by omega), ite_eq_left (by omega), show 7 - (16 + 2 * (7 - p) - 16) / 2 = p by omega,
      show (16 + 2 * (7 - p)) % 2 = 0 by omega]
    rfl
  have e1 : tv m0 (zI p + 1) = (zV p).c1 := by
    unfold tv zI
    rw [ite_eq_right (by omega), ite_eq_left (by omega),
      show 7 - (16 + 2 * (7 - p) + 1 - 16) / 2 = p by omega,
      show (16 + 2 * (7 - p) + 1) % 2 = 1 by omega]
    rfl
  rw [e0, e1]

theorem tv_p {p : Nat} (hp : p < 8) : (⟨tv m0 (pI p), tv m0 (pI p + 1)⟩ : EW) = pV m0 p := by
  have e0 : tv m0 (pI p) = (pV m0 p).c0 := by
    unfold tv pI
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show 7 - (32 + 2 * (7 - p) - 32) / 2 = p by omega, show (32 + 2 * (7 - p)) % 2 = 0 by omega]
    rfl
  have e1 : tv m0 (pI p + 1) = (pV m0 p).c1 := by
    unfold tv pI
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show 7 - (32 + 2 * (7 - p) + 1 - 32) / 2 = p by omega,
      show (32 + 2 * (7 - p) + 1) % 2 = 1 by omega]
    rfl
  rw [e0, e1]

theorem tv_t {p : Nat} (hp : p < 8) : (⟨tv m0 (tI p), tv m0 (tI p + 1)⟩ : EW) = tV m0 p := by
  have e0 : tv m0 (tI p) = (tV m0 p).c0 := by
    unfold tv tI
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show 7 - (48 + 2 * (7 - p) - 48) / 2 = p by omega, show (48 + 2 * (7 - p)) % 2 = 0 by omega]
    rfl
  have e1 : tv m0 (tI p + 1) = (tV m0 p).c1 := by
    unfold tv tI
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show 7 - (48 + 2 * (7 - p) + 1 - 48) / 2 = p by omega,
      show (48 + 2 * (7 - p) + 1) % 2 = 1 by omega]
    rfl
  rw [e0, e1]

theorem tv_m {p : Nat} (hp : p < 8) : (⟨tv m0 (mI p), tv m0 (mI p + 1)⟩ : EW) = mV m0 p := by
  have e0 : tv m0 (mI p) = (mV m0 p).c0 := by
    unfold tv mI
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega), show 7 - (64 + 2 * (7 - p) - 64) / 2 = p by omega,
      show (64 + 2 * (7 - p)) % 2 = 0 by omega]
    rfl
  have e1 : tv m0 (mI p + 1) = (mV m0 p).c1 := by
    unfold tv mI
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega), show 7 - (64 + 2 * (7 - p) + 1 - 64) / 2 = p by omega,
      show (64 + 2 * (7 - p) + 1) % 2 = 1 by omega]
    rfl
  rw [e0, e1]

theorem tv_g : (⟨tv m0 gI, tv m0 (gI + 1)⟩ : EW) = gen := rfl

theorem tv_s : (⟨tv m0 sI, tv m0 (sI + 1)⟩ : EW) = sV m0 := rfl

theorem tv_fPtr : tv m0 fPtr = UInt64.ofBitVec (fA m0) := rfl

/-! ## The calls' results -/

theorem zV_succ {p : Nat} (hp : p < 7) : EW.sqIter 8 (zV (p + 1)) = zV p := by
  unfold zV
  rw [show 8 - p = (8 - (p + 1)) + 1 by omega]
  rfl

theorem hrZ7 : EW.sqIter 8 ⟨tv m0 gI, tv m0 (gI + 1)⟩ = ⟨tv m0 (zI 7), tv m0 (zI 7 + 1)⟩ := by
  rw [tv_g, tv_z (by decide)]
  rfl

theorem hrZ (p : Nat) (hp : p < 7) :
    EW.sqIter 8 ⟨tv m0 (zI (p + 1)), tv m0 (zI (p + 1) + 1)⟩ = ⟨tv m0 (zI p), tv m0 (zI p + 1)⟩ := by
  rw [tv_z (by omega), tv_z (by omega), zV_succ hp]

theorem hrP (p : Nat) (hp : p < 8) :
    polyEval (imgs m0) ⟨tv m0 (zI p), tv m0 (zI p + 1)⟩ = ⟨tv m0 (pI p), tv m0 (pI p + 1)⟩ := by
  rw [tv_z hp, tv_p hp]
  rfl

theorem hrT (p : Nat) (hp : p < 8) :
    EW.sqIter (8 * p) ⟨tv m0 (pI p), tv m0 (pI p + 1)⟩ = ⟨tv m0 (tI p), tv m0 (tI p + 1)⟩ := by
  rw [tv_p hp, tv_t hp]
  rfl

theorem hrM (p : Nat) (hp : p < 8) :
    EW.mul ⟨tv m0 (fI p), tv m0 (fI p + 1)⟩ ⟨tv m0 (tI p), tv m0 (tI p + 1)⟩ =
      ⟨tv m0 (mI p), tv m0 (mI p + 1)⟩ := by
  rw [tv_f hp, tv_t hp, tv_m hp]
  rfl

theorem nilE : ∀ p ∈ ([] : List (Sym × Nat)), ∃ r, p.1 = .reg r ∧ calleeSaved r = true :=
  fun _ h ↦ nomatch h

theorem nilH [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {Q : MachineData → Prop} :
    ∀ st, Q st → Holds rs V [] st := fun _ _ _ h ↦ nomatch h

/-! ## The state's facts -/

section
variable [Labels] {D : List (Sym × Nat)} {m : MachineData}

/-- `f`'s address, a location of every state after the loop. -/
theorem St.ptr (hst : St m0 D m) : St m0 ((.ptr 1 0, fPtr) :: D) m := by
  refine ⟨hst.fr, fun p hp ↦ ?_, hst.copy⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · show UInt64.ofBitVec (Sym.eval (Env.ofMachine m (rsT m0)) (.ptr 1 0)) = tv m0 fPtr
    rw [tv_fPtr]
    simp [Sym.eval]
  · exact hst.hd p hp

/-- A register the description holds. -/
theorem Holds.reg (hH : Holds (rsT m0) (tv m0) D m) {r : XReg} {n : Nat}
    (h : D.contains (.reg r, n) = true) : m.regs.getXReg r = tv m0 n :=
  hH _ (List.contains_iff_mem.mp h)

theorem St.mid (hst : St m0 D m) (h : P m0) (hx : D.contains (.reg .X21, fPtr) = true) :
    Match (Env.ofMachine m (rsT m0)) midT m :=
  matchT hst.fr (x21_of fun p hp ↦ by
    rw [List.mem_singleton] at hp
    subst hp
    exact hst.hd _ (List.contains_iff_mem.mp hx)) h

end

end

end NativeRustcVmArm.Ring.Target
