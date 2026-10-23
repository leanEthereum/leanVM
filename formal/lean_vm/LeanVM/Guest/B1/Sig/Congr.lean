/-
  LeanVM.Guest.B1.Sig.Congr

  A codeword's statements read a chain's step addresses at its three steps only.
-/

module

public import LeanVM.Guest.B1.Sig.Template

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {w : Wots} {adr' : Nat → V} (hadr : ∀ s < 3, w.adr s = adr' s)
include hadr

theorem cStep_congr {i s b : Nat} {v o0 o1 : V} (hs : s < 3) :
    cStep w i s b v o0 o1 = cStep { w with adr := adr' } i s b v o0 o1 := by
  simp only [cStep, hadr s hs]

theorem cSteps_congr {i : Nat} {t0 t1 : V} :
    ∀ (m s b : Nat) (v : V), s + m ≤ 2 → cSteps w i t0 t1 m s b v = cSteps { w with adr := adr' } i t0 t1 m s b v
  | 0, s, b, v, h => cStep_congr hadr (by omega)
  | m + 1, s, b, v, h => by
      simp only [cSteps]
      rw [cStep_congr hadr (by omega), cSteps_congr m (s + 1) _ _ (by omega)]

theorem cWalk_congr {i d b : Nat} {t0 t1 : V} (hd : d < 4) :
    cWalk w i d b t0 t1 = cWalk { w with adr := adr' } i d b t0 t1 := by
  simp only [cWalk]
  split
  · rfl
  · rw [cSteps_congr hadr _ _ _ _ (by omega)]

theorem cWalks_congr {tips : Nat → V × V} {first k : Nat} {fresh : Bool} :
    ∀ (m r b : Nat), cWalks w tips first k fresh m r b = cWalks { w with adr := adr' } tips first k fresh m r b
  | 0, _, _ => rfl
  | m + 1, r, b => by
      simp only [cWalks]
      rw [cWalk_congr hadr (Nat.mod_lt _ (by norm_num)), cWalks_congr m (r + 1)]

theorem cArm_congr {tips : Nat → V × V} {power : Nat → V} {prodIn encIn prodOut encOut : V} {first n k : Nat}
    {fold fresh : Bool} {b : Nat} :
    cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b =
      cArm { w with adr := adr' } tips power prodIn encIn prodOut encOut first n k fold fresh b := by
  simp only [cArm]
  rw [cWalks_congr hadr]

theorem cArms_congr {tips : Nat → V × V} {power : Nat → V} {prodIn encIn prodOut encOut : V} {first n : Nat}
    {fold : Bool} : ∀ (m k b : Nat), cArms w tips power prodIn encIn prodOut encOut first n fold m k b =
      cArms { w with adr := adr' } tips power prodIn encIn prodOut encOut first n fold m k b
  | 0, _, _ => rfl
  | m + 1, k, b => by
      simp only [cArms]
      rw [cArm_congr hadr, cArms_congr m (k + 1)]

theorem cGroup_congr {power : Nat → V} {prodIn encIn : V} {first n : Nat} {fold : Bool} {b : Nat} :
    cGroup w power prodIn encIn first n fold b = cGroup { w with adr := adr' } power prodIn encIn first n fold b := by
  simp only [cGroup]
  rw [cArms_congr hadr]

theorem cGroups_congr {power : Nat → V} : ∀ (m p : Nat) (prod enc : V) (b : Nat),
    cGroups w power m p prod enc b = cGroups { w with adr := adr' } power m p prod enc b
  | 0, _, _, _, _ => rfl
  | m + 1, p, prod, enc, b => by
      simp only [cGroups]
      rw [cGroup_congr hadr, cGroups_congr m (p + 1)]

theorem cCodeword_congr {power : Nat → V} {G : Nat} {target : E} {d0 : V} {b : Nat} :
    cCodeword w power G target d0 b = cCodeword { w with adr := adr' } power G target d0 b := by
  simp only [cCodeword]
  rw [cGroups_congr hadr, cGroup_congr hadr]

end
end LeanVM.Guest.B1.Sig
