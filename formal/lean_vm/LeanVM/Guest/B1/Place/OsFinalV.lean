/-
  LeanVM.Guest.B1.Place.OsFinalV

  The body's valuation at the call sites the placed lift reads.
-/

module

public import LeanVM.Guest.B1.Place.OsValsBody
public import LeanVM.Guest.B1.Place.OsLvKs

/-!
# The valuation at the call sites

For σ the body's valuation (`osBodyF` filled in from `9`): level `l`'s squeeze run's pointer, its
squeeze loop's guard and arguments, its row weights' pointer (`osVal_sqz`, `osVal_guard`,
`osVal_wp`), and the head's `query_positions` and `query_bit_ptrs` pointers (`osVal_qpos`,
`osVal_qbp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

theorem spDats_getElem : ∀ (Ls : List SpLv) (i : ℕ) (sq wp : ℕ → E) (j : ℕ)
    (hj : j < (spDats Ls i sq wp).length),
    (spDats Ls i sq wp)[j].sqz = sq (i + j) ∧ (spDats Ls i sq wp)[j].wp = wp (i + j)
  | [], _, _, _, _, hj => absurd hj (by simp [spDats])
  | L :: Ls, i, sq, wp, 0, _ => ⟨rfl, rfl⟩
  | L :: Ls, i, sq, wp, j + 1, hj => by
    have := spDats_getElem Ls (i + 1) sq wp j (by simpa [spDats] using hj)
    simp only [spDats, List.getElem_cons_succ]
    rw [this.1, this.2, show i + 1 + j = i + (j + 1) by omega]
    exact ⟨rfl, rfl⟩

/-- The levels before level `j`, then the rest. -/
theorem osLevels_split_at (c : OsCfg) : ∀ (lvs : List OsLv) (lvl : ℕ) (s : OsSt) (j : ℕ),
    (osLevels c lvl lvs s).2 = (osLevels c (lvl + j) (lvs.drop j) (osLevels c lvl (lvs.take j) s).2).2
  | [], _, _, j => by simp [osLevels]
  | _ :: _, _, _, 0 => by simp [osLevels]
  | lv :: rest, lvl, s, j + 1 => by
    have e1 : (osLevels c lvl (lv :: rest) s).2 = (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).2 :=
      rfl
    have e2 : (osLevels c lvl ((lv :: rest).take (j + 1)) s).2 =
        (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv s).2).2 := rfl
    rw [e1, e2, osLevels_split_at c rest (lvl + 1) _ j, List.drop_succ_cons,
      show lvl + 1 + j = lvl + (j + 1) by omega]

/-- **Level `j`'s buffers lie before the levels' end.** -/
theorem osLevel_in_levels (c : OsCfg) (lvs : List OsLv) (s : OsSt) (j : ℕ) (hj : j < lvs.length) :
    s.k ≤ (osLevelA c j lvs[j] (osLevels c 0 (lvs.take j) s).2).2.1.k ∧
      wpVar c j lvs[j] (osLevelA c j lvs[j] (osLevels c 0 (lvs.take j) s).2).2.1 + 6 ≤
        (osLevels c 0 lvs s).2.k := by
  have e := osLevels_split_at c lvs 0 s j
  rw [Nat.zero_add] at e
  have ed : lvs.drop j = lvs[j] :: lvs.drop (j + 1) := List.drop_eq_getElem_cons hj
  rw [ed] at e
  have e2 : (osLevels c j (lvs[j] :: lvs.drop (j + 1)) (osLevels c 0 (lvs.take j) s).2).2 =
      (osLevels c (j + 1) (lvs.drop (j + 1)) (osLevel c j lvs[j] (osLevels c 0 (lvs.take j) s).2).2).2 :=
    rfl
  rw [e2] at e
  have h1 := osLevels_k_ge c 0 (lvs.take j) s
  have h2 := osLevelA_k_le c j lvs[j] (osLevels c 0 (lvs.take j) s).2
  have h3 := osLevel_k_le c j lvs[j] (osLevels c 0 (lvs.take j) s).2
  have h4 := osLevels_k_ge c (j + 1) (lvs.drop (j + 1)) (osLevel c j lvs[j] (osLevels c 0 (lvs.take j) s).2).2
  rw [e]
  exact ⟨le_trans h1 h2, le_trans h3 h4⟩

section Vals

variable {c : OsCfg} {tr : OsTr} {σ0 : Val} {c0 c2 : E} {b0 : ℕ}

/-- The body's valuation. -/
noncomputable def osSigma (c : OsCfg) (tr : OsTr) (σ0 : Val) (c0 c2 : E) (b0 : ℕ) : Val :=
  fill σ0 9 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) (osBodyF c tr σ0 c0 c2 (osAtOf c b0))

/-- Level `j`'s state, before its squeezes. -/
def osAj (c : OsCfg) (j : ℕ) : OsSt :=
  (osLevelA c j (lvAt c j) (osLevels c 0 (c.levels.take j) (osHead c).2).2).2.1

theorem osAj_bounds (c : OsCfg) {j : ℕ} (hj : j < c.levels.length) :
    164 ≤ (osAj c j).k ∧ wpVar c j (lvAt c j) (osAj c j) + 6 ≤ (osLvSt c).k := by
  have h := osLevel_in_levels c c.levels (osHead c).2 j hj
  have e : c.levels[j] = lvAt c j := (List.getD_eq_getElem _ _ hj).symm
  rw [e] at h
  exact ⟨h.1, h.2⟩

theorem osSigma_lvs {i : ℕ} (h1 : 164 ≤ i)
    (h2 : i < (osLvSt c).k) :
    osSigma c tr σ0 c0 c2 b0 (.n i) = lvsF c 0 c.levels (tr.Ds (osAtOf c b0)) (osHead c).2
      (fill σ0 9 164 (headF c σ0 (osAtOf c b0).P c0 c2)) i := by
  have ht : (osLvSt c).k + 2 ≤ (osTlSt c).2.1.k := osTail_k2 c (osLvSt c)
  have hfe : (osTlSt c).2.1.k + 6 ≤ osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2 := osFinEnd_ge c _ _
  unfold osSigma
  rw [fill_in (by omega) (by omega)]
  exact bodyF_lvs h1 h2

theorem osDs_get (hlen : tr.Ls.length = c.levels.length) {j : ℕ} (hj : j < c.levels.length) :
    ∃ hD : j < (tr.Ds (osAtOf c b0)).length, (tr.Ds (osAtOf c b0))[j].sqz = (osAtOf c b0).sqz j ∧
      (tr.Ds (osAtOf c b0))[j].wp = (osAtOf c b0).wp j := by
  have hl : (tr.Ds (osAtOf c b0)).length = c.levels.length := by rw [OsTr.Ds, spDats_len, hlen]
  refine ⟨by rw [hl]; exact hj, ?_⟩
  have := spDats_getElem tr.Ls 0 (osAtOf c b0).sqz (osAtOf c b0).wp j (by rw [spDats_len, hlen]; exact hj)
  simp only [Nat.zero_add] at this
  exact this

/-- **Level `j`'s squeeze run's pointer.** -/
theorem osVal_sqz (hlen : tr.Ls.length = c.levels.length) {j : ℕ} (hj : j < c.levels.length) :
    osSigma c tr σ0 c0 c2 b0 (.n ((osAj c j).k + 1)) = (osAtOf c b0).sqz j := by
  obtain ⟨hb1, hb2⟩ := osAj_bounds c hj
  have hw := osSqueezes_k c j (lvAt c j) (osAj c j)
  unfold wpVar at hb2
  rw [osSigma_lvs (by omega) (by omega)]
  obtain ⟨hD, hs, -⟩ := osDs_get (b0 := b0) hlen hj
  have hB := (lvsF_bufs c c.levels (tr.Ds (osAtOf c b0)) 0 (osHead c).2
    (fill σ0 9 164 (headF c σ0 (osAtOf c b0).P c0 c2)) j hj hD).2.1
  simp only [Nat.zero_add] at hB
  rw [← hs, ← hB]
  unfold osAj lvAt
  rw [List.getD_eq_getElem _ _ hj]

/-- **Level `j`'s row weights' pointer.** -/
theorem osVal_wp (hlen : tr.Ls.length = c.levels.length) {j : ℕ} (hj : j < c.levels.length) :
    osSigma c tr σ0 c0 c2 b0 (.n (wpVar c j (lvAt c j) (osAj c j))) = (osAtOf c b0).wp j := by
  obtain ⟨hb1, hb2⟩ := osAj_bounds c hj
  have hw := osSqueezes_k c j (lvAt c j) (osAj c j)
  rw [osSigma_lvs (by unfold wpVar; omega) (by omega)]
  obtain ⟨hD, -, hp⟩ := osDs_get (b0 := b0) hlen hj
  have hB := (lvsF_bufs c c.levels (tr.Ds (osAtOf c b0)) 0 (osHead c).2
    (fill σ0 9 164 (headF c σ0 (osAtOf c b0).P c0 c2)) j hj hD).2.2.2
  simp only [Nat.zero_add] at hB
  rw [← hp, ← hB]
  unfold osAj lvAt
  rw [List.getD_eq_getElem _ _ hj]

/-- **Level `j`'s squeeze loop's guard and arguments.** -/
theorem osVal_guard (hlen : tr.Ls.length = c.levels.length) {j : ℕ} (hj : j < c.levels.length)
    {t : ℕ} (ht : t < 5) :
    osSigma c tr σ0 c0 c2 b0 (.n ((osAj c j).k + 2 + t)) = (sqGuardVals (lvAt c j)).getD t 0 := by
  obtain ⟨hb1, hb2⟩ := osAj_bounds c hj
  have hw := osSqueezes_k c j (lvAt c j) (osAj c j)
  unfold wpVar at hb2
  rw [osSigma_lvs (by omega) (by omega)]
  obtain ⟨hD, -, -⟩ := osDs_get (b0 := b0) hlen hj
  have hB := lvsF_guard c c.levels (tr.Ds (osAtOf c b0)) 0 (osHead c).2
    (fill σ0 9 164 (headF c σ0 (osAtOf c b0).P c0 c2)) j hj hD ht
  simp only [Nat.zero_add] at hB
  have e : c.levels[j] = lvAt c j := (List.getD_eq_getElem _ _ hj).symm
  rw [e] at hB
  exact hB

theorem osSigma_head {i : ℕ} (h1 : 9 ≤ i) (h2 : i < 164) :
    osSigma c tr σ0 c0 c2 b0 (.n i) = headF c σ0 (osAtOf c b0).P c0 c2 i := by
  have hk : 164 ≤ (osLvSt c).k := osLevels_k_ge c 0 c.levels (osHead c).2
  have ht : (osLvSt c).k + 2 ≤ (osTlSt c).2.1.k := osTail_k2 c (osLvSt c)
  have hfe : (osTlSt c).2.1.k + 6 ≤ osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2 := osFinEnd_ge c _ _
  unfold osSigma
  rw [fill_in h1 (by omega)]
  exact bodyF_head h2

theorem osVal_qpos : osSigma c tr σ0 c0 c2 b0 (.n osQpos) = (osAtOf c b0).P.qpos := by
  rw [osSigma_head (by decide) (by decide)]; rfl

theorem osVal_qbp : osSigma c tr σ0 c0 c2 b0 (.n osQbp) = (osAtOf c b0).P.qbp := by
  rw [osSigma_head (by decide) (by decide)]; rfl

theorem osVal_win : osSigma c tr σ0 c0 c2 b0 (.n osWin) = (osAtOf c b0).P.win := by
  rw [osSigma_head (by decide) (by decide)]; rfl

theorem osSigma_arg {j : ℕ} (hj : j < 9) : osSigma c tr σ0 c0 c2 b0 (.n j) = σ0 (.n j) := by
  unfold osSigma; exact fill_lt hj

end Vals

end
end LeanVM.Guest.B1
