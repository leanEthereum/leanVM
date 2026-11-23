module

public import NativeRustcVmArm.Ring.Coeff.Basic

/-!
# `ring_coefficients`: the loop's model state

`rc m0 (p + 1)` is `coeffStep` of `rc m0 p` and `f_p`: the coefficients so far and the products
of the turn (`rc_succ_fst`), `G`'s Frobenius images (`gG_succ`); the sizes.
-/

namespace NativeRustcVmArm.Ring.Coeff

open NativeVm.Model NativeRustcVm.Ring

public section

variable {m0 : MachineData}

theorem fl_length : (fl m0).length = 8 := NativeRustcVm.length_ewsOf ..

theorem gl_size : (gl m0).toArray.size = 8 := by simp [gl]

theorem fl_getElem {p : Nat} (hp : p < (fl m0).length) : (fl m0)[p] = fE m0 p :=
  NativeRustcVm.getElem_ewsOf ..

theorem rc_succ {p : Nat} (hp : p < 8) : rc m0 (p + 1) = coeffStep (rc m0 p) (fE m0 p) := by
  unfold rc
  rw [rcAt_succ _ _ (by rw [fl_length]; exact hp), fl_getElem]

theorem rc_size2 {p : Nat} (hp : p ≤ 8) : (rc m0 p).2.size = 8 := by
  unfold rc
  rw [rcAt_size2 _ _ _ (by rw [fl_length]; exact hp), gl_size]

theorem rc_size1 {p : Nat} (hp : p ≤ 8) : (rc m0 p).1.size = 8 * p := by
  unfold rc
  rw [rcAt_size1 _ _ _ (by rw [fl_length]; exact hp), gl_size]

theorem rc_length1 {p : Nat} (hp : p ≤ 8) : (rc m0 p).1.toList.length = 8 * p := by
  rw [Array.length_toList, rc_size1 hp]

theorem prods_length (p b : Nat) : (prods m0 p b).length = b := by simp [prods]

theorem prods_succ (p b : Nat) : prods m0 p (b + 1) = prods m0 p b ++ [fE m0 p * gG m0 p b] := by
  simp [prods, List.range_succ]

theorem rc_succ_fst {p : Nat} (hp : p < 8) :
    (rc m0 (p + 1)).1.toList = (rc m0 p).1.toList ++ prods m0 p 8 := by
  rw [rc_succ hp]
  simp only [coeffStep, Array.toList_append, Array.toList_map]
  congr 1
  apply List.ext_getElem (by simp [prods, rc_size2 (m0 := m0) (p := p) (by omega)])
  intro i h1 h2
  simp only [List.getElem_map, prods, List.getElem_range, gG, Array.getElem_toList]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [rc_size2 (by omega)]; simpa [prods] using h2)]
  rfl

theorem gG_succ {p b : Nat} (hp : p < 8) (hb : b < 8) :
    gG m0 (p + 1) b = frobenius8 (gG m0 p b) 1 := by
  unfold gG
  rw [rc_succ hp]
  simp only [coeffStep]
  have hs := rc_size2 (m0 := m0) (p := p) (by omega)
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem (by rw [hs]; exact hb)]
  rfl

theorem gG_zero {b : Nat} (hb : b < 8) :
    gG m0 0 b = NativeRustcVm.ewOf m0.dmem (gA m0 + BitVec.ofNat 64 (16 * b)) := by
  unfold gG rc
  rw [rcAt_zero]
  simp only
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, gl,
    List.getElem?_eq_getElem (by rw [NativeRustcVm.length_ewsOf]; exact hb),
    NativeRustcVm.getElem_ewsOf]
  rfl

end

end NativeRustcVmArm.Ring.Coeff
