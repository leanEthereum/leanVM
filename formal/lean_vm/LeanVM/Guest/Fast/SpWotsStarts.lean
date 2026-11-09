module

public import LeanVM.Guest.B1.Sig.SpWotsLayout

/-!
# `sp_wots`' chain starts, one pass over a group's arms

`spStartAt K i` (`B1/Sig/SpWotsLayout.lean`) is where chain `i`'s start is hinted when group
`i / 3` takes arm `K (i / 3)`: arm `k`'s start at its base `spArmB … k`, a recursion over the arms
before it. `spArmsStarts` walks a group's arms once, from arm `k` at base `b`, and lists each arm's
starts (`spArmStarts`); `spArmsStarts_getElem`: its `j`-th entry is arm `k + j`'s, at its base;
`spStartAt_eq_getD`: chain `i`'s start is entry `K (i / 3)`, row `i % 3`, of its group's list from
arm `0`. The kernel evaluates the lists, one pass a group (`Fast/SpWotsTablesCheck.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-- Arm `k`'s starts, its base `b`, in group `p` from the state `st` (`spStartAt`). -/
def spArmStarts (p : Nat) (st : V × V × Nat) (k b : Nat) : List V :=
  (List.range (spN p)).map fun r => armStart spW (spSlot (p == 0) st.2.2) (p == 0) k b r

/-- Arms `k ..< k + m`' starts of group `p` from the state `st`, from base `b`. -/
def spArmsStarts (p : Nat) (st : V × V × Nat) : Nat → Nat → Nat → List (List V)
  | 0, _, _ => []
  | m + 1, k, b =>
      let a := spArmK (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k b
      spArmStarts p st k b :: spArmsStarts p st m (k + 1) (if k = 0 then a.2 + 2 else a.2)

theorem spArmsStarts_length (p : Nat) (st : V × V × Nat) :
    ∀ m k b, (spArmsStarts p st m k b).length = m
  | 0, _, _ => rfl
  | m + 1, k, b => by
      simp [spArmsStarts, spArmsStarts_length p st m]

theorem spArmsStarts_getD (p : Nat) (st : V × V × Nat) :
    ∀ m k b j, j < m →
      (spArmsStarts p st m k b).getD j [] =
        spArmStarts p st (k + j) (spArmBase (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k j b)
  | 0, _, _, j, hj => absurd hj (by omega)
  | m + 1, k, b, 0, _ => by simp [spArmsStarts, spArmBase, armBase]
  | m + 1, k, b, j + 1, hj => by
      simp only [spArmsStarts, List.getD_cons_succ]
      rw [spArmsStarts_getD p st m (k + 1) _ j (by omega)]
      simp only [spArmBase, armBase, spArmK, show k + 1 + j = k + (j + 1) by omega]

/-- **Chain `i`'s start**, off its group's list of arms' starts: entry `K (i / 3)`, row `i % 3`. -/
theorem spStartAt_eq_getD (K : Nat → Nat) (i : Nat) (hK : K (i / 3) < 4 ^ spN (i / 3))
    (hr : i % 3 < spN (i / 3)) :
    spStartAt K i =
      ((spArmsStarts (i / 3) (spState (i / 3)) (4 ^ spN (i / 3)) 0
        (spL (i / 3 == 0) (spState (i / 3)).2.2 + 6)).getD (K (i / 3)) []).getD (i % 3) (.n 0) := by
  rw [spArmsStarts_getD _ _ _ _ _ _ hK, Nat.zero_add, ← spArmB_eq]
  simp [spArmStarts, spStartAt, List.getD_eq_getElem?_getD, hr]

end
end LeanVM.Guest.Fast
