/-
  LeanVM.Guest.B1.Place.OsPosWritten

  A level's query positions are written: its queries fit its squeezes' positions, which fit the
  positions buffer, and `level_positions` writes every squeeze's positions.
-/

module

public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Common.Basic

/-!
# A level's positions, written

* `osPos_fits`: at every size, rate and level, the queries fit the positions the squeezes draw
  (`LIG_QUERIES ≤ LIG_SQUEEZES·(128/depth)`), and those fit the positions buffer after the level's
  offset (`LIG_POS_OFF + LIG_SQUEEZES·(128/depth) ≤ LIG_POS_TOTAL`, `osPosTotal_eq`), by the kernel;
* `os_positions_written`: on a memory holding every squeeze's positions at the level's positions
  `qpos·g^posOff` (squeeze `j`'s position `i` at offset `j·(128/d) + i`, as `level_positions` stores
  them, `LpMem`), the cell `qpos·g^(posOff + q)` holds query `q`'s position, for every query `q`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir LeanVM.Protocol.Verifier

@[expose] public section

/-- The tables' check: every level's queries within its squeezes' positions, these within the
positions buffer, and the buffer `LIG_POS_TOTAL`. -/
def osPosFitsChk : Bool :=
  (List.range ligNSizes).all fun m ↦ (List.range ligNRates).all fun r ↦
    decide (lig Data.arr_LIG_POS_TOTAL (m + r * ligNSizes) = osPosTotal (osCfgR m r)) &&
    (List.range (osNLevels m)).all fun l ↦
      decide ((osLvR m r l).queries ≤ (osLvR m r l).squeezes * (128 / (osLvR m r l).depth) ∧
        (osLvR m r l).posOff + (osLvR m r l).squeezes * (128 / (osLvR m r l).depth) ≤
          osPosTotal (osCfgR m r))

theorem osPosFitsChk_ok : osPosFitsChk = true := by decide +kernel

/-- **A level's queries fit its squeezes' positions, and these the positions buffer.** -/
theorem osPos_fits {m r lvl : ℕ} (hm : m < ligNSizes) (hr : r < ligNRates) (hl : lvl < osNLevels m) :
    (osLvR m r lvl).queries ≤ (osLvR m r lvl).squeezes * (128 / (osLvR m r lvl).depth) ∧
      (osLvR m r lvl).posOff + (osLvR m r lvl).squeezes * (128 / (osLvR m r lvl).depth) ≤
        osPosTotal (osCfgR m r) := by
  have h := osPosFitsChk_ok
  simp only [osPosFitsChk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h m hm r hr).2 lvl hl

/-- **The positions buffer is `LIG_POS_TOTAL` at the rate.** -/
theorem osPosTotal_eq {m r : ℕ} (hm : m < ligNSizes) (hr : r < ligNRates) :
    lig Data.arr_LIG_POS_TOTAL (m + r * ligNSizes) = osPosTotal (osCfgR m r) := by
  have h := osPosFitsChk_ok
  simp only [osPosFitsChk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h m hm r hr).1

/-- **Every query's position is written** at `qpos·g^(posOff + q)`, on a memory holding
`level_positions`' words at the level's positions `qpos·g^posOff`. -/
theorem os_positions_written {lv : OsLv} {qpos : E} {rd : Reader} {v : ℕ → ℕ → E}
    (h : ∀ j < lv.squeezes, ∀ i < 128 / lv.depth,
      LoadHolds rd (qpos * gen ^ lv.posOff) (j * (128 / lv.depth) + i) (v j i))
    (hq : lv.queries ≤ lv.squeezes * (128 / lv.depth)) :
    ∀ q < lv.queries, LoadHolds rd qpos (lv.posOff + q) (v (q / (128 / lv.depth)) (q % (128 / lv.depth))) := by
  intro q hql
  have hP : 0 < 128 / lv.depth := by
    rcases Nat.eq_zero_or_pos (128 / lv.depth) with h0 | h0
    · rw [h0, Nat.mul_zero] at hq; omega
    · exact h0
  have hj : q / (128 / lv.depth) < lv.squeezes := by
    rw [Nat.div_lt_iff_lt_mul hP]; omega
  have hi : q % (128 / lv.depth) < 128 / lv.depth := Nat.mod_lt _ hP
  have e := h _ hj _ hi
  rw [loadHolds_mul_gen_pow, Nat.mul_comm, Nat.div_add_mod] at e
  exact e

end
end LeanVM.Guest.B1
