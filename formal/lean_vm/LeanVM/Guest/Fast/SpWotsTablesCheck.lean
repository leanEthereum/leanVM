module

public import LeanVM.Guest.Fast.SpWotsStarts
public import LeanVM.Guest.Fast.SpWotsTables
public import LeanVM.Guest.Fast.Numbers
import Mathlib.Tactic.IntervalCases

/-!
# `sp_wots`' chain starts are the literal tables', by evaluation

* `spState_eq`: group `p`'s running product's and encoding's cells and its base (`spState`,
  `B1/Sig/SpWotsLayout.lean`) are the recorded `spStates`, the kernel evaluating one group's arms
  at a time (`spState (p + 1)` from `spStates`' entry `p`);
* `spGroupStarts`: group `p`'s arms' starts (`spArmsStarts`, `Fast/SpWotsStarts.lean`, one pass
  over its arms), in the guest's numbering (`spRen`), are its selector cell plus the literal
  table's (`spSel`, `spTabOf`, `Fast/SpWotsTables.lean`);
* `spSel_eq`: the selectors are the groups' bases, renumbered.

The checks over all groups are one kernel evaluation per group (`interval_cases`), so the kernel's
cache holds one group at a time. It imports the templates and the tables alone
(`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1.Sig

public section

/-- Group `p`'s running product's and encoding's cells and its base, `p < 22`. -/
def spStates : List (V × V × Nat) :=
  [(.n 0, .n 0, 16), (.n 66, .n 67, 1046), (.n 1091, .n 1092, 2134), (.n 2179, .n 2180, 3222),
    (.n 3267, .n 3268, 4310), (.n 4355, .n 4356, 5398), (.n 5443, .n 5444, 6486),
    (.n 6531, .n 6532, 7574), (.n 7619, .n 7620, 8662), (.n 8707, .n 8708, 9750),
    (.n 9795, .n 9796, 10838), (.n 10883, .n 10884, 11926), (.n 11971, .n 11972, 13014),
    (.n 13059, .n 13060, 14102), (.n 14147, .n 14148, 15190), (.n 15235, .n 15236, 16278),
    (.n 16323, .n 16324, 17366), (.n 17411, .n 17412, 18454), (.n 18499, .n 18500, 19542),
    (.n 19587, .n 19588, 20630), (.n 20675, .n 20676, 21718), (.n 21763, .n 21764, 22806)]

/-- `spState`'s step from each recorded group gives the next. -/
private theorem spStates_step : ∀ p < 21,
    (let st := spStates.getD p default
     ((.n (spProd (p == 0) 3 st.2.2), .n (spEnc (p == 0) 3 st.2.2),
       (spGroupT (3 * p) 3 (p == 0) st.1 st.2.1 st.2.2).2) : V × V × Nat)) =
      spStates.getD (p + 1) default := by
  intro p hp
  interval_cases p <;> decide +kernel

/-- **Group `p`'s state is the recorded one.** -/
theorem spState_eq : ∀ p < 22, spState p = spStates.getD p default
  | 0, _ => rfl
  | p + 1, hp => by rw [spState, spState_eq p (by omega)]; exact spStates_step p (by omega)

/-- **The selectors are the groups' bases**, renumbered. -/
theorem spSel_eq : ∀ p < 22, spSel.getD p 0 = spR (spState p).2.2 := by
  intro p hp
  rw [spState_eq p hp]
  revert p
  decide +kernel

/-- **Group `p`'s arms' starts**, renumbered: its selector plus its table's. -/
theorem spGroupStarts (p : Nat) (hp : p < 22) :
    (spArmsStarts p (spState p) (4 ^ spN p) 0 (spL (p == 0) (spState p).2.2 + 6)).map (·.map spRen) =
      (List.range (4 ^ spN p)).map fun k ↦ (List.range (spN p)).map fun r ↦
        V.n (spSel.getD p 0 + offAt (spTabOf p) r k) := by
  rw [spState_eq p hp]
  interval_cases p <;> decide +kernel

end
end LeanVM.Guest.Fast
