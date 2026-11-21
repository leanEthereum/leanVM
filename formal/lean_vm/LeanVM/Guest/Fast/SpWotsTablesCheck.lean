module

public import LeanVM.Guest.Fast.SpWotsStarts
public import LeanVM.Guest.Fast.SpWotsTables
public import LeanVM.Guest.Fast.Numbers

/-!
# `sp_wots`' chain starts are the literal tables', by evaluation

* `spState_p`: group `p`'s running product's and encoding's cells and its base (`spState`,
  `B1/Sig/SpWotsLayout.lean`), the kernel evaluating one group's arms at a time (`spState (p + 1)`
  from `spState p`);
* `spGroupStarts_p`: group `p`'s `64` arms' starts (`spArmsStarts`, `Fast/SpWotsStarts.lean`, one
  pass over its arms), in the guest's numbering (`spRen`), are its base plus the literal table's
  (`spBase`, `spOff`, `Fast/SpWotsTables.lean`);
* combined: `spGroupStarts`.

It imports the templates and the tables alone (`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Core LeanVM.Guest.B1.Sig

public section

theorem spState_0 : spState 0 = (V.n 0, V.n 0, 126) := rfl

theorem spState_1 : spState 1 = (V.n 171, V.n 172, 1145) := by decide +kernel

theorem spState_2 : spState 2 = (V.n 1190, V.n 1191, 2227) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, spState, spState_1]
  decide +kernel

theorem spState_3 : spState 3 = (V.n 2272, V.n 2273, 3309) := by
  rw [show (3 : Nat) = 2 + 1 from rfl, spState, spState_2]
  decide +kernel

theorem spState_4 : spState 4 = (V.n 3354, V.n 3355, 4391) := by
  rw [show (4 : Nat) = 3 + 1 from rfl, spState, spState_3]
  decide +kernel

theorem spState_5 : spState 5 = (V.n 4436, V.n 4437, 5473) := by
  rw [show (5 : Nat) = 4 + 1 from rfl, spState, spState_4]
  decide +kernel

theorem spState_6 : spState 6 = (V.n 5518, V.n 5519, 6555) := by
  rw [show (6 : Nat) = 5 + 1 from rfl, spState, spState_5]
  decide +kernel

theorem spState_7 : spState 7 = (V.n 6600, V.n 6601, 7637) := by
  rw [show (7 : Nat) = 6 + 1 from rfl, spState, spState_6]
  decide +kernel

theorem spState_8 : spState 8 = (V.n 7682, V.n 7683, 8719) := by
  rw [show (8 : Nat) = 7 + 1 from rfl, spState, spState_7]
  decide +kernel

theorem spState_9 : spState 9 = (V.n 8764, V.n 8765, 9801) := by
  rw [show (9 : Nat) = 8 + 1 from rfl, spState, spState_8]
  decide +kernel

theorem spState_10 : spState 10 = (V.n 9846, V.n 9847, 10883) := by
  rw [show (10 : Nat) = 9 + 1 from rfl, spState, spState_9]
  decide +kernel

theorem spState_11 : spState 11 = (V.n 10928, V.n 10929, 11965) := by
  rw [show (11 : Nat) = 10 + 1 from rfl, spState, spState_10]
  decide +kernel

theorem spState_12 : spState 12 = (V.n 12010, V.n 12011, 13047) := by
  rw [show (12 : Nat) = 11 + 1 from rfl, spState, spState_11]
  decide +kernel

theorem spState_13 : spState 13 = (V.n 13092, V.n 13093, 14129) := by
  rw [show (13 : Nat) = 12 + 1 from rfl, spState, spState_12]
  decide +kernel

theorem spState_14 : spState 14 = (V.n 14174, V.n 14175, 15211) := by
  rw [show (14 : Nat) = 13 + 1 from rfl, spState, spState_13]
  decide +kernel

theorem spState_15 : spState 15 = (V.n 15256, V.n 15257, 16293) := by
  rw [show (15 : Nat) = 14 + 1 from rfl, spState, spState_14]
  decide +kernel

theorem spState_16 : spState 16 = (V.n 16338, V.n 16339, 17375) := by
  rw [show (16 : Nat) = 15 + 1 from rfl, spState, spState_15]
  decide +kernel

theorem spState_17 : spState 17 = (V.n 17420, V.n 17421, 18457) := by
  rw [show (17 : Nat) = 16 + 1 from rfl, spState, spState_16]
  decide +kernel

theorem spState_18 : spState 18 = (V.n 18502, V.n 18503, 19539) := by
  rw [show (18 : Nat) = 17 + 1 from rfl, spState, spState_17]
  decide +kernel

theorem spState_19 : spState 19 = (V.n 19584, V.n 19585, 20621) := by
  rw [show (19 : Nat) = 18 + 1 from rfl, spState, spState_18]
  decide +kernel

theorem spState_20 : spState 20 = (V.n 20666, V.n 20667, 21703) := by
  rw [show (20 : Nat) = 19 + 1 from rfl, spState, spState_19]
  decide +kernel

theorem spState_21 : spState 21 = (V.n 21748, V.n 21749, 22785) := by
  rw [show (21 : Nat) = 20 + 1 from rfl, spState, spState_20]
  decide +kernel

/-- Group `0`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_0 :
    (spArmsStarts 0 (V.n 0, V.n 0, 126) 64 0 (126 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 0)).map fun r ↦
        V.n (spBase.getD 0 0 + spOff 0 r k) := by
  decide +kernel

/-- Group `1`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_1 :
    (spArmsStarts 1 (V.n 171, V.n 172, 1145) 64 0 (1145 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 1)).map fun r ↦
        V.n (spBase.getD 1 0 + spOff 1 r k) := by
  decide +kernel

/-- Group `2`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_2 :
    (spArmsStarts 2 (V.n 1190, V.n 1191, 2227) 64 0 (2227 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 2)).map fun r ↦
        V.n (spBase.getD 2 0 + spOff 2 r k) := by
  decide +kernel

/-- Group `3`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_3 :
    (spArmsStarts 3 (V.n 2272, V.n 2273, 3309) 64 0 (3309 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 3)).map fun r ↦
        V.n (spBase.getD 3 0 + spOff 3 r k) := by
  decide +kernel

/-- Group `4`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_4 :
    (spArmsStarts 4 (V.n 3354, V.n 3355, 4391) 64 0 (4391 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 4)).map fun r ↦
        V.n (spBase.getD 4 0 + spOff 4 r k) := by
  decide +kernel

/-- Group `5`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_5 :
    (spArmsStarts 5 (V.n 4436, V.n 4437, 5473) 64 0 (5473 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 5)).map fun r ↦
        V.n (spBase.getD 5 0 + spOff 5 r k) := by
  decide +kernel

/-- Group `6`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_6 :
    (spArmsStarts 6 (V.n 5518, V.n 5519, 6555) 64 0 (6555 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 6)).map fun r ↦
        V.n (spBase.getD 6 0 + spOff 6 r k) := by
  decide +kernel

/-- Group `7`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_7 :
    (spArmsStarts 7 (V.n 6600, V.n 6601, 7637) 64 0 (7637 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 7)).map fun r ↦
        V.n (spBase.getD 7 0 + spOff 7 r k) := by
  decide +kernel

/-- Group `8`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_8 :
    (spArmsStarts 8 (V.n 7682, V.n 7683, 8719) 64 0 (8719 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 8)).map fun r ↦
        V.n (spBase.getD 8 0 + spOff 8 r k) := by
  decide +kernel

/-- Group `9`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_9 :
    (spArmsStarts 9 (V.n 8764, V.n 8765, 9801) 64 0 (9801 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 9)).map fun r ↦
        V.n (spBase.getD 9 0 + spOff 9 r k) := by
  decide +kernel

/-- Group `10`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_10 :
    (spArmsStarts 10 (V.n 9846, V.n 9847, 10883) 64 0 (10883 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 10)).map fun r ↦
        V.n (spBase.getD 10 0 + spOff 10 r k) := by
  decide +kernel

/-- Group `11`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_11 :
    (spArmsStarts 11 (V.n 10928, V.n 10929, 11965) 64 0 (11965 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 11)).map fun r ↦
        V.n (spBase.getD 11 0 + spOff 11 r k) := by
  decide +kernel

/-- Group `12`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_12 :
    (spArmsStarts 12 (V.n 12010, V.n 12011, 13047) 64 0 (13047 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 12)).map fun r ↦
        V.n (spBase.getD 12 0 + spOff 12 r k) := by
  decide +kernel

/-- Group `13`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_13 :
    (spArmsStarts 13 (V.n 13092, V.n 13093, 14129) 64 0 (14129 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 13)).map fun r ↦
        V.n (spBase.getD 13 0 + spOff 13 r k) := by
  decide +kernel

/-- Group `14`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_14 :
    (spArmsStarts 14 (V.n 14174, V.n 14175, 15211) 64 0 (15211 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 14)).map fun r ↦
        V.n (spBase.getD 14 0 + spOff 14 r k) := by
  decide +kernel

/-- Group `15`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_15 :
    (spArmsStarts 15 (V.n 15256, V.n 15257, 16293) 64 0 (16293 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 15)).map fun r ↦
        V.n (spBase.getD 15 0 + spOff 15 r k) := by
  decide +kernel

/-- Group `16`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_16 :
    (spArmsStarts 16 (V.n 16338, V.n 16339, 17375) 64 0 (17375 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 16)).map fun r ↦
        V.n (spBase.getD 16 0 + spOff 16 r k) := by
  decide +kernel

/-- Group `17`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_17 :
    (spArmsStarts 17 (V.n 17420, V.n 17421, 18457) 64 0 (18457 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 17)).map fun r ↦
        V.n (spBase.getD 17 0 + spOff 17 r k) := by
  decide +kernel

/-- Group `18`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_18 :
    (spArmsStarts 18 (V.n 18502, V.n 18503, 19539) 64 0 (19539 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 18)).map fun r ↦
        V.n (spBase.getD 18 0 + spOff 18 r k) := by
  decide +kernel

/-- Group `19`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_19 :
    (spArmsStarts 19 (V.n 19584, V.n 19585, 20621) 64 0 (20621 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 19)).map fun r ↦
        V.n (spBase.getD 19 0 + spOff 19 r k) := by
  decide +kernel

/-- Group `20`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_20 :
    (spArmsStarts 20 (V.n 20666, V.n 20667, 21703) 64 0 (21703 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 20)).map fun r ↦
        V.n (spBase.getD 20 0 + spOff 20 r k) := by
  decide +kernel

/-- Group `21`'s arms' starts, renumbered: its base plus the table's. -/
theorem spGroupStarts_21 :
    (spArmsStarts 21 (V.n 21748, V.n 21749, 22785) 64 0 (22785 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN 21)).map fun r ↦
        V.n (spBase.getD 21 0 + spOff 21 r k) := by
  decide +kernel

/-- **Group `p`'s arms' starts**, renumbered: its base plus its table's. -/
theorem spGroupStarts (p : Nat) (hp : p < 22) :
    (spArmsStarts p (spState p) 64 0 ((spState p).2.2 + 6)).map (·.map spRen) =
      (List.range 64).map fun k ↦ (List.range (spN p)).map fun r ↦
        V.n (spBase.getD p 0 + spOff p r k) := by
  interval_cases p
  · rw [spState_0]; exact spGroupStarts_0
  · rw [spState_1]; exact spGroupStarts_1
  · rw [spState_2]; exact spGroupStarts_2
  · rw [spState_3]; exact spGroupStarts_3
  · rw [spState_4]; exact spGroupStarts_4
  · rw [spState_5]; exact spGroupStarts_5
  · rw [spState_6]; exact spGroupStarts_6
  · rw [spState_7]; exact spGroupStarts_7
  · rw [spState_8]; exact spGroupStarts_8
  · rw [spState_9]; exact spGroupStarts_9
  · rw [spState_10]; exact spGroupStarts_10
  · rw [spState_11]; exact spGroupStarts_11
  · rw [spState_12]; exact spGroupStarts_12
  · rw [spState_13]; exact spGroupStarts_13
  · rw [spState_14]; exact spGroupStarts_14
  · rw [spState_15]; exact spGroupStarts_15
  · rw [spState_16]; exact spGroupStarts_16
  · rw [spState_17]; exact spGroupStarts_17
  · rw [spState_18]; exact spGroupStarts_18
  · rw [spState_19]; exact spGroupStarts_19
  · rw [spState_20]; exact spGroupStarts_20
  · rw [spState_21]; exact spGroupStarts_21

end
end LeanVM.Guest.Fast
