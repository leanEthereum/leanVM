/-
  LeanVM.Guest.B1.Place.OsCallsOk

  open_stacked's callee facts at the dispatch relation, on the honest trace.
-/

module

public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Whir.BrCaps
public import LeanVM.Guest.B1.Whir.CFold
public import LeanVM.Guest.B1.Whir.CFinal
public import LeanVM.Guest.B1.Opening.Fold
public import LeanVM.Guest.B1.Whir.RateCfg
public import LeanVM.Guest.B1.Place.OsLkMem

/-!
# The body's calls at `osCR`

`osSp c tr A`: the helpers placed apart, at their honest arguments and returns: level `l`'s
`level_positions`, `level_queries` and `level_residual`. `OsNames c ri`: the configuration's callee
names are the table's (`osKindOf`) at the kinds the body calls them with, the helpers are not in
it, and rate `ri`'s rows are the configuration's levels (decided per configuration).
`osCallsOk_honest`: on memory holding the honest buffers, at the rate's selector `g^ri`, the
body's calls hold at `osCR rd (osSp c tr A)`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- Level `l`'s `level_positions` arguments. -/
abbrev osLpArgs (c : OsCfg) (tr : OsTr) (A : OsAt) (l : ℕ) : List E :=
  (tr.L l).F2.cap ++ [A.P.qpos * gen ^ (lvAt c l).posOff, A.P.qbp * gen ^ (lvAt c l).posOff, A.P.win]

/-- Level `l`'s `level_queries` arguments. -/
abbrev osLqArgs (c : OsCfg) (tr : OsTr) (A : OsAt) (l : ℕ) : List E :=
  [(tr.L l).lam, A.P.qbp * gen ^ (lvAt c l).posOff, A.wp l]

/-- Level `l`'s `level_queries` returns. -/
abbrev osLqRets (c : OsCfg) (tr : OsTr) (l : ℕ) : List E :=
  [(digestHalves (tr.L l).root).1, (digestHalves (tr.L l).root).2, (tr.L l).enforced,
    (tr.L l).lam ^ (lvAt c l).queries]

/-- Level `l`'s `level_residual` arguments. -/
abbrev osLrArgs (c : OsCfg) (tr : OsTr) (A : OsAt) (l : ℕ) : List E :=
  [A.P.qpos * gen ^ (lvAt c l).posOff, A.BD * gen ^ (l * ligColsCap), finM tr l]

/-- **The helpers placed apart**, at their honest arguments and returns. -/
def osSp (c : OsCfg) (tr : OsTr) (A : OsAt) : String → List E → List E → Prop := fun f a r ↦
  ∃ l < c.levels.length,
    (f = osPositionsName (lvAt c l) ∧ a = osLpArgs c tr A l ∧
      r = sqLast (lvAt c l) (tr.L l).F2.cap) ∨
    (f = osQueriesName l (lvAt c l) ∧ a = osLqArgs c tr A l ∧ r = osLqRets c tr l) ∨
    (f = osResidualName (lvAt c l) ∧ a = osLrArgs c tr A l ∧ r = [finH c tr l])

/-- **The configuration's callee names at rate `ri`**, decided per configuration. -/
structure OsNames (c : OsCfg) (ri : ℕ) : Prop where
  ri4 : ri < 4
  rate : ∀ i < c.levels.length, (c.lvAt i).length = 4 ∧ (c.lvAt i).getD ri default = lvAt c i
  ood : ∀ i < c.levels.length, i ≠ c.yrLevel →
    osKindOf ("opening_ood_point__L" ++ natStr (lvAt c i).logCols) = some (.ood (lvAt c i).logCols)
  grind : ∀ i < c.levels.length,
    osKindOf ("grind_check__L" ++ natStr (lvAt c i).grind) = some (.grind Whir.queryGrindingBits)
  fm : osKindOf ("opening_final_message__L" ++ natStr c.yrLen) = some (.fm c.yrLen)
  rw : ∀ i < c.levels.length,
    osKindOf ("opening_row_weights__L" ++ natStr (lvAt c i).folds ++ "_L" ++
      natStr (if i = 0 then 1 else 0)) = some (.rw (lvAt c i).folds (if i = 0 then 1 else 0))
  ffm : osKindOf ("fold_final_msg__L" ++ natStr c.yrLog) = some (.ffm c.yrLog)
  pos : ∀ i < c.levels.length, osKindOf (osPositionsName (lvAt c i)) = none
  q : ∀ i < c.levels.length, osKindOf (osQueriesName i (lvAt c i)) = none
  res : ∀ i < c.levels.length, osKindOf (osResidualName (lvAt c i)) = none
  il : ∀ i < c.levels.length,
    2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds) ≤ c.maxIl

theorem osKindOf_fold : osKindOf "opening_fold" = some .fold := by
  simp [osKindOf, osKindTable]
theorem osKindOf_can : osKindOf "assert_canonical" = some .can := by
  simp [osKindOf, osKindTable, List.lookup]

theorem lf_ml' {c : OsCfg} {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) {tr : OsTr}
    (h : TrFit c tr) : tr.Lf.ml = c.yrLog := by
  have hn := hF.n2
  rw [h.lf, (h.fit _ (by omega)).ml]
  have := hF.last
  rwa [getLastD_eq_getD _ (by intro h; rw [h] at hn; simp at hn)] at this

/-- **A dispatch on the rate's selector `g^ri`** into rate `ri`'s row's name holds. -/
theorem dispC_rate {C : CallRel} {rd : Reader} {c : OsCfg} {l ri : ℕ}
    (hrate : (c.lvAt l).length = 4 ∧ (c.lvAt l).getD ri default = lvAt c l) (hri : ri < 4)
    (f : OsLv → String) {a r : List E} (h : C (f (lvAt c l)) a r) :
    DispC C rd (ofK (addressOfIndex ri)) ((c.lvAt l).map f) a r := by
  have hl : ri < (c.lvAt l).length := by rw [hrate.1]; exact hri
  refine dispC_of (by simpa using hl) rfl ?_
  rw [List.getElem_map, ← List.getD_eq_getElem _ default hl, hrate.2]
  exact h

section Placed

variable {κ : ℕ} {c : OsCfg} {tr : OsTr} {b0 : ℕ} {Lin : Layout}

/-- A slice of own buffer `j` (but the window pointers), fixed on every memory holding the callees'
words. -/
theorem lk_slice (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap)
    (htl : tr.Lf.ml ≤ yrLogCap) {j off n : ℕ} (hj : j < 16 + c.levels.length) (hne : j ≠ 6)
    (hb : off + n ≤ ((osOwnL c tr fun _ _ ↦ 0).getD j []).length) :
    ((((osOwnL c tr fun _ _ ↦ 0).getD j []).drop off).take n).length = n ∧
      ∀ rd, LowDef κ rd → MemL rd (osLk c tr b0 Lin) →
        ReadsAt rd (osPtrAt c b0 j * gen ^ off) ((((osOwnL c tr fun _ _ ↦ 0).getD j []).drop off).take n) :=
  ⟨by simp only [List.length_take, List.length_drop]; omega,
    fun _ _ hm ↦ os_readsAt_shift (osLk_readsAt hpt htl hm hj hne) hb⟩

theorem lk_slice0 (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap)
    (htl : tr.Lf.ml ≤ yrLogCap) {j n : ℕ} (hj : j < 16 + c.levels.length) (hne : j ≠ 6)
    (hb : n ≤ ((osOwnL c tr fun _ _ ↦ 0).getD j []).length) :
    ((((osOwnL c tr fun _ _ ↦ 0).getD j []).drop 0).take n).length = n ∧
      ∀ rd, LowDef κ rd → MemL rd (osLk c tr b0 Lin) →
        ReadsAt rd (osPtrAt c b0 j) ((((osOwnL c tr fun _ _ ↦ 0).getD j []).drop 0).take n) := by
  obtain ⟨h1, h2⟩ := lk_slice (κ := κ) (b0 := b0) (Lin := Lin) hpt htl hj hne (off := 0) (n := n)
    (by omega)
  refine ⟨h1, fun rd hl hm ↦ ?_⟩
  have := h2 rd hl hm
  rwa [pow_zero, mul_one] at this

/-- **The body's calls hold at `osCR`** on every memory holding the callees' words, at the rate's
selector `g^ri`, the read words of the row weights, the folded message and the final message's
`out` fixed there. -/
theorem osCallsOk_honest {μ r : ℕ} {cfg : List Whir.Level} {ri : ℕ}
    (hF : CandFacts c μ r cfg) (h : TrFit c tr) (hs : OsSizes c) (hN : OsNames c ri)
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap)
    {rd : Reader} (hmk : MemL rd (osLk c tr b0 Lin)) :
    OsCallsOk (osCR rd (osSp c tr (osAtOf c b0)) (OsXOk κ (osLk c tr b0 Lin))) rd
      (ofK (addressOfIndex ri)) (osAtOf c b0) c tr := by
  have hm := osMem_of_memLk hpt htl hmk
  have hW := fun i (hi : i < c.levels.length) ↦ osLk_wp hpt htl hmk hi
  have hn := hF.n2
  obtain ⟨g0, -, g2, -⟩ := osOwnL_getD_head c tr fun _ _ ↦ 0
  have hT := (osOwnL_getD_fin c tr fun _ _ ↦ 0).1
  -- the final message's `out`
  have hfm : ∀ a : List E, a.getD 8 0 = (osAtOf c b0).P.fmsg →
      OsXOk κ (osLk c tr b0 Lin) (.fm c.yrLen) a := fun a h8 ↦ by
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    obtain ⟨l1, l2⟩ := lk_slice0 (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 0) (n := c.yrLen)
      (by omega) (by omega) (by rw [g0]; simp [fmsgC])
    exact ⟨_, l1, fun rd' hl hm' ↦ by rw [h8]; exact l2 rd' hl hm'⟩
  have hfold0 : FoldCallC (osCR rd (osSp c tr (osAtOf c b0)) (OsXOk κ (osLk c tr b0 Lin))) rd :=
    fun _ _ hmf ↦ osCR_named osKindOf_fold hmf trivial
  refine ⟨hfold0, fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
  · refine ⟨hfold0, fun _ _ hm' ↦ osCR_named osKindOf_can hm' trivial,
      fun hne _ _ hm' ↦ osCR_named (hN.ood i hi hne) hm' trivial,
      fun _ _ hm' ↦ osCR_named (hN.grind i hi) hm' trivial,
      fun _ a _ hm' h8 ↦ osCR_named hN.fm hm' (hfm a h8), ?_, ?_, ?_⟩
    · exact dispC_rate (hN.rate i hi) hN.ri4 osPositionsName
        (osCR_special (hN.pos i hi) ⟨i, hi, Or.inl ⟨rfl, rfl, rfl⟩⟩)
    · -- the row weights
      refine osCR_named (hN.rw i hi) (rw_meaning_at hF h hm.fixed hi (hW i hi) (hN.il i hi)) ?_
      have hcl : (tr.L i).chs.length = (lvAt c i).folds := by
        rw [SpLv.chs_length, (h.fit i hi).fold]
      have hpre : (lvAt c i).foldsOff + (lvAt c i).folds ≤ c.nFolds := by
        have hp := (h.pre i hi).length_le
        rw [SpLv.wsEnd_folds, List.length_append, h.off i hi, hcl, fall_length hF h] at hp
        exact hp
      intro q hq
      simp only [rowWeightsSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · obtain ⟨l1, l2⟩ := lk_slice (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 2)
          (off := (lvAt c i).foldsOff) (n := (lvAt c i).folds) (by omega) (by omega)
          (by rw [g2]; simpa [fchC] using hpre)
        exact ⟨_, l1, l2⟩
      · obtain ⟨l1, l2⟩ := lk_slice0 (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := osIxWp i)
          (n := 2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds))
          (by unfold osIxWp; omega) (by unfold osIxWp; omega)
          (by rw [osOwnL_getD_lv c tr _ hi]; simpa [wpC] using hN.il i hi)
        exact ⟨_, l1, l2⟩
    · exact dispC_rate (hN.rate i hi) hN.ri4 (osQueriesName i)
        (osCR_special (hN.q i hi) ⟨i, hi, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩)
  · exact dispC_rate (hN.rate i hi) hN.ri4 osResidualName
      (osCR_special (hN.res i hi) ⟨i, hi, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩)
  · -- the folded message
    refine osCR_named hN.ffm (ffm_meaning_at hF h hs hm.fixed hm.T) ?_
    have hml := lf_ml' hF h
    intro q hq
    simp only [foldFinalSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨l1, l2⟩ := lk_slice0 (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 0)
        (n := 2 ^ c.yrLog) (by omega) (by omega) (by rw [g0, hF.ylen]; simp [fmsgC])
      exact ⟨_, l1, l2⟩
    · obtain ⟨l1, l2⟩ := lk_slice0 (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := osIxT c)
        (n := c.yrLog) (by unfold osIxT; omega) (by unfold osIxT; omega)
        (by rw [hT, tailC, List.length_append, tailChs_length, List.length_replicate, hml]
            have := hs.yr; omega)
      exact ⟨_, l1, l2⟩

end Placed

end
end LeanVM.Guest.B1
