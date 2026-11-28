module

public import NativeRustcVmX64.Ring.Target.Basic

/-!
# `ring_target`: the table and the sum (x86-64)

`tab`: the table of the values the code computes (`f`'s elements, the points, `P_p`, `T_p`,
`M_p`), which meets `Good`. `final`: the products the code sums, `M_0` last, are `ringTarget`.
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- **The table.** -/
def tab (m0 : MachineData) (i : Nat) : EW :=
  if i < 8 then fE m0 i
  else if i ≤ 16 then zz (i - 8)
  else if i < 20 then 0
  else if i < 28 then polyEval (imgs m0) (zz (8 - (i - 20)))
  else if i < 30 then 0
  else if i < 38 then EW.sqIter (8 * (i - 30)) (polyEval (imgs m0) (zz (8 - (i - 30))))
  else if i < 40 then 0
  else if i < 48 then
    fE m0 (i - 40) * EW.sqIter (8 * (i - 40)) (polyEval (imgs m0) (zz (8 - (i - 40))))
  else 0

/-- The products' sums the code keeps, limb `0` and `1`. -/
def X0 (E : Nat → EW) : BitVec 64 :=
  (((((c0 (E 47) ^^^ c0 (E 46)) ^^^ c0 (E 45)) ^^^ c0 (E 44)) ^^^ c0 (E 43)) ^^^ c0 (E 42)) ^^^
    c0 (E 41)
def X1 (E : Nat → EW) : BitVec 64 :=
  (((((c1 (E 47) ^^^ c1 (E 46)) ^^^ c1 (E 45)) ^^^ c1 (E 44)) ^^^ c1 (E 43)) ^^^ c1 (E 42)) ^^^
    c1 (E 41)

end

public section

variable {m0 : MachineData}

theorem tab_good : Good m0 (tab m0) where
  f p hp := by unfold tab; rw [ite_eq_left hp]
  z1 := rfl
  z n h1 h2 := by
    unfold tab
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show 9 + n - 8 = (8 + n - 8) + 1 by omega]
    rfl
  pv p hp := by
    unfold tab
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), show 20 + p - 20 = p by omega,
      show 16 - p - 8 = 8 - p by omega]
  tv p hp := by
    unfold tab
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), show 30 + p - 30 = p by omega,
      show 20 + p - 20 = p by omega]
  mv p hp := by
    unfold tab
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_left hp, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), show 40 + p - 40 = p by omega,
      show 30 + p - 30 = p by omega]

variable {E : Nat → EW}

theorem good_zz (hG : Good m0 E) : ∀ n, 1 ≤ n → n ≤ 8 → E (8 + n) = zz n
  | 0, h, _ => absurd h (by decide)
  | 1, _, _ => hG.z1
  | n + 2, _, h => by
    rw [show 8 + (n + 2) = 9 + (n + 1) by omega, hG.z (n + 1) (by omega) (by omega),
      show 8 + (n + 1) = 8 + (n + 1) from rfl, good_zz hG (n + 1) (by omega) (by omega)]
    rfl

theorem fl_getD {p : Nat} (hp : p < 8) : (fl m0).getD p 0 = fE m0 p := by
  unfold fl arr
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_eq_getElem (by rw [NativeRustcVm.length_ewsOf]; exact hp),
    NativeRustcVm.getElem_ewsOf]
  rfl

theorem good_term (hG : Good m0 E) {p : Nat} (hp : p < 8) :
    E (40 + p) = tTerm (imgs m0) (fl m0) p := by
  unfold tTerm
  rw [hG.mv p hp, hG.tv p hp, hG.pv p hp, hG.f p hp, fl_getD hp,
    show 16 - p = 8 + (8 - p) by omega, good_zz hG (8 - p) (by omega) (by omega)]

/-- **The sum**: the code's `M_0 + (M_7 + … + M_1)` is `ringTarget`. -/
theorem final (hG : Good m0 E) :
    ewArg (c0 (E 40) ^^^ X0 E) (c1 (E 40) ^^^ X1 E) = ringTarget (sl m0) (fl m0) (gl m0) := by
  rw [ringTarget_eq]
  show _ = 0 + tTerm (imgs m0) (fl m0) 7 + tTerm (imgs m0) (fl m0) 6 + tTerm (imgs m0) (fl m0) 5 +
    tTerm (imgs m0) (fl m0) 4 + tTerm (imgs m0) (fl m0) 3 + tTerm (imgs m0) (fl m0) 2 +
    tTerm (imgs m0) (fl m0) 1 + tTerm (imgs m0) (fl m0) 0
  rw [← good_term hG (p := 7) (by decide), ← good_term hG (p := 6) (by decide),
    ← good_term hG (p := 5) (by decide), ← good_term hG (p := 4) (by decide),
    ← good_term hG (p := 3) (by decide), ← good_term hG (p := 2) (by decide),
    ← good_term hG (p := 1) (by decide), ← good_term hG (p := 0) (by decide)]
  simp only [ewArg, X0, X1, c0, c1, EW.add_def]
  congr 1
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor]
    rw [show (0 : EW).c0.toBitVec = 0#64 from rfl, BitVec.zero_xor]
    ac_rfl
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor]
    rw [show (0 : EW).c1.toBitVec = 0#64 from rfl, BitVec.zero_xor]
    ac_rfl

end

end NativeRustcVmX64.Ring.Target
