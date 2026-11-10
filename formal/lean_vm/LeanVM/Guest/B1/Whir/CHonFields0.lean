/-
  LeanVM.Guest.B1.Whir.CHonFields0

  Small facts the honest data's fields use: the squeezes' capacities, and a candidate's residual
  loops' counts, checked.
-/

module

public import LeanVM.Guest.B1.Whir.CHonBuf
public import LeanVM.Guest.B1.Whir.LastRun

/-!
# The fields' small facts

`capSq_length`, `capSq_word`: a level's squeezes' capacities have five cells and squeeze to its
samples. `FieldStatic c`: each non-final level's residual loop runs at least once; decided per
candidate in `Whir/CHonFields1`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem capSq_length (L : LvAt) (logN j : ℕ) : (L.capSq logN j).length = 5 :=
  squeezeN_cap_length _ _ (by simp [capOf])

theorem capSq_word (L : LvAt) (logN : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    (⟨L.capSq logN j, []⟩ : Fs).squeeze.1 = L.word logN j := by
  simp only [LvAt.word, LvAt.capSq, sqSample, show j ≠ 0 by omega, ↓reduceIte, sqCap]
  rw [← squeezeN_mk]

/-- A level's positions are its samples' windows. -/
theorem LvAt.qs_eq_sq (L : LvAt) (logN : ℕ) :
    L.qs logN = sqPositions (L.dp logN) (L.word logN) L.level.queries := by
  unfold LvAt.qs LvAt.word LvAt.qS
  rcases L.d with ⟨rw, W⟩ | ⟨rw, W⟩ <;> rfl

theorem LvAt.qs_length (L : LvAt) (logN : ℕ) : (L.qs logN).length = L.level.queries := by
  rw [L.qs_eq_sq]; simp [sqPositions]

/-- **A level's positions, one by one.** -/
theorem LvAt.qs_getD_eq (L : LvAt) (logN : ℕ) {lv : OsLv} (hdep : lv.depth = L.dp logN)
    (hq : L.level.queries = lv.queries) :
    ∀ k < lv.queries, (L.qs logN).getD k 0 =
      qwPosOf lv.depth (L.word logN (k / sqPer lv)) (k % sqPer lv) := by
  intro k hk
  rw [L.qs_eq_sq, sqPositions, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp [sqPer, hdep]

/-- A non-final level's record's positions are its positions. -/
theorem LvAt.osRec_qs (L : LvAt) (logN : ℕ) {rw : List E} {W : NextW} (hd : L.d = .next rw W) :
    (L.osRec logN).qs = L.qs logN := by
  unfold LvAt.osRec LvAt.qs
  rw [hd]
  rfl

/-- **Each non-final level's residual loop runs at least once**, checked. -/
def FieldStatic (c : OsCfg) : Prop :=
  ∀ l < c.yrLevel, 0 < (osLvAt c l).queries / resBatch

instance (c : OsCfg) : Decidable (FieldStatic c) := by
  unfold FieldStatic; infer_instance

end
end LeanVM.Guest.B1.Whir
