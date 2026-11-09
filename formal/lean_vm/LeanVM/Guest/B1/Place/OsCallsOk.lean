/-
  LeanVM.Guest.B1.Place.OsCallsOk

  open_stacked's callee facts at the dispatch relation, on the honest trace.
-/

module

public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Whir.BrCaps
public import LeanVM.Guest.B1.Place.OsLkMem

/-!
# The body's calls at `osCR`

`osSp c tr A`: the callees placed apart, at their honest arguments and returns: level `l`'s
squeeze loop, its `opening_queries`, its residual loop. `OsNames c`: the configuration's callee
names are the table's (`osKindOf`), at the kinds the body calls them with, and the others are
not in it (decided per configuration). `osCallsOk_honest`: on memory holding the honest buffers,
the body's calls hold at `osCR rd (osSp c tr A)`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- Level `l`'s squeeze loop's arguments. -/
abbrev osSqArgs (c : OsCfg) (A : OsAt) (l : ℕ) : List E :=
  [1, gen ^ (lvAt c l).squeezes, A.sqz l, A.P.qpos, A.P.qbp, A.P.win]

/-- Level `l`'s `opening_queries` arguments. -/
abbrev osQArgs (c : OsCfg) (tr : OsTr) (A : OsAt) (l : ℕ) : List E :=
  [A.P.caps * gen ^ (4 * (lvAt c l).capOff), A.P.flags * gen ^ (lvAt c l).capOff, (tr.L l).lam,
    (tr.L l).lam ^ (lvAt c l).queries, A.P.qbp * gen ^ (lvAt c l).posOff, A.wp l,
    gen ^ ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))]

/-- Level `l`'s residual loop's arguments. -/
abbrev osResArgs (c : OsCfg) (tr : OsTr) (A : OsAt) (l : ℕ) : List E :=
  [1, gen ^ ((lvAt c l).queries / resBatch), A.P.qpos, A.BD, A.rc l, finM tr l]

/-- **The callees placed apart**, at their honest arguments and returns. -/
def osSp (c : OsCfg) (tr : OsTr) (A : OsAt) : String → List E → List E → Prop := fun f a r ↦
  ∃ l < c.levels.length,
    (f = c.sqLoop l ∧ a = osSqArgs c A l ∧ r = []) ∨
    (f = osQueriesName l (lvAt c l) ∧ a = osQArgs c tr A l ∧ r = [(tr.L l).enforced]) ∨
    (f = c.resLoop l ∧ a = osResArgs c tr A l ∧ r = [])

/-- **The configuration's callee names**, decided per configuration. -/
structure OsNames (c : OsCfg) : Prop where
  ood : ∀ i < c.levels.length, i ≠ c.yrLevel →
    osKindOf ("opening_ood_point__L" ++ natStr (lvAt c i).logCols) = some (.ood (lvAt c i).logCols)
  grind : ∀ i < c.levels.length,
    osKindOf ("grind_check__L" ++ natStr (lvAt c i).grind) = some (.grind Whir.queryGrindingBits)
  fm : osKindOf ("opening_final_message__L" ++ natStr c.yrLen) = some (.fm c.yrLen)
  rw : ∀ i < c.levels.length,
    osKindOf ("opening_row_weights__L" ++ natStr (lvAt c i).folds ++ "_L" ++
      natStr (if i = 0 then 1 else 0)) = some (.rw (lvAt c i).folds (if i = 0 then 1 else 0))
  cap : ∀ i < c.levels.length,
    osKindOf ("verify_merkle_cap__L" ++ natStr (lvAt c i).capDepth) = some (.cap (lvAt c i).capDepth)
  ffm : osKindOf ("fold_final_msg__L" ++ natStr c.yrLog) = some (.ffm c.yrLog)
  sq : ∀ i < c.levels.length, osKindOf (c.sqLoop i) = none
  q : ∀ i < c.levels.length, osKindOf (osQueriesName i (lvAt c i)) = none
  res : ∀ i < c.levels.length, osKindOf (c.resLoop i) = none
  il : ∀ i < c.levels.length,
    2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds) ≤ c.maxIl
  cdd : ∀ i < c.levels.length, (lvAt c i).capDepth ≤ (lvAt c i).depth
  sqres : ∀ i < c.levels.length, ∀ j < c.levels.length, c.sqLoop i ≠ c.resLoop j

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

section Placed

variable {κ : ℕ} {c : OsCfg} {tr : OsTr} {b0 : ℕ} {Lin : Layout}

/-- A slice of own buffer `j` (but the window pointers), fixed on every memory holding the callees'
words. -/
theorem lk_slice (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap)
    (htl : tr.Lf.ml ≤ yrLogCap) {j off n : ℕ} (hj : j < 18 + 3 * c.levels.length) (hne : j ≠ 8)
    (hb : off + n ≤ ((osOwnL c tr fun _ _ ↦ 0).getD j []).length) :
    ((((osOwnL c tr fun _ _ ↦ 0).getD j []).drop off).take n).length = n ∧
      ∀ rd, LowDef κ rd → MemL rd (osLk c tr b0 Lin) →
        ReadsAt rd (osPtrAt c b0 j * gen ^ off) ((((osOwnL c tr fun _ _ ↦ 0).getD j []).drop off).take n) :=
  ⟨by simp only [List.length_take, List.length_drop]; omega,
    fun _ _ hm ↦ os_readsAt_shift (osLk_readsAt hpt htl hm hj hne) hb⟩

theorem lk_slice0 (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap)
    (htl : tr.Lf.ml ≤ yrLogCap) {j n : ℕ} (hj : j < 18 + 3 * c.levels.length) (hne : j ≠ 8)
    (hb : n ≤ ((osOwnL c tr fun _ _ ↦ 0).getD j []).length) :
    ((((osOwnL c tr fun _ _ ↦ 0).getD j []).drop 0).take n).length = n ∧
      ∀ rd, LowDef κ rd → MemL rd (osLk c tr b0 Lin) →
        ReadsAt rd (osPtrAt c b0 j) ((((osOwnL c tr fun _ _ ↦ 0).getD j []).drop 0).take n) := by
  obtain ⟨h1, h2⟩ := lk_slice (κ := κ) (b0 := b0) (Lin := Lin) hpt htl hj hne (off := 0) (n := n)
    (by omega)
  refine ⟨h1, fun rd hl hm ↦ ?_⟩
  have := h2 rd hl hm
  rwa [pow_zero, mul_one] at this

/-- **The body's calls hold at `osCR`** on every memory holding the callees' words, the read words
of the row weights, the cap, the folded message and the final message's `out` fixed there. -/
theorem osCallsOk_honest {μ r : ℕ} {cfg : List Whir.Level}
    (hF : CandFacts c μ r cfg) (h : TrFit c tr) (hs : OsSizes c) {target : E} {S : KeccakState}
    {xs : List E} {os : List (List Opening)} {root : Digest} (hrun : TrRun c μ r target S xs os root tr)
    (hcaps : Whir.CapsAgree μ r target S xs os root) (hN : OsNames c)
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap)
    {rd : Reader} (hmk : MemL rd (osLk c tr b0 Lin)) :
    OsCallsOk (osCR rd (osSp c tr (osAtOf c b0)) (OsXOk κ (osLk c tr b0 Lin))) rd (osAtOf c b0)
      c tr := by
  have hm := osMem_of_memLk hpt htl hmk
  have hC := osLk_caps hpt htl hmk
  have hFl := osLk_flags hpt htl hmk
  have hW := fun i (hi : i < c.levels.length) ↦ osLk_wp hpt htl hmk hi
  have hn := hF.n2
  obtain ⟨g0, g1, g2, -, g4, -⟩ := osOwnL_getD_head c tr fun _ _ ↦ 0
  have hT := (osOwnL_getD_fin c tr fun _ _ ↦ 0).1
  have hlen : ∀ (l : List E) (n : ℕ), l = (List.range n).map (fun _ ↦ (0 : E)) → l.length = n :=
    fun l n h ↦ by rw [h]; simp
  -- the final message's `out`
  have hfm : ∀ a : List E, a.getD 8 0 = (osAtOf c b0).P.fmsg →
      OsXOk κ (osLk c tr b0 Lin) (.fm c.yrLen) a := fun a h8 ↦ by
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    obtain ⟨l1, l2⟩ := lk_slice0 (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 2) (n := c.yrLen)
      (by omega) (by omega) (by rw [g2]; simp [fmsgC])
    exact ⟨_, l1, fun rd' hl hm' ↦ by rw [h8]; exact l2 rd' hl hm'⟩
  refine ⟨fun _ _ hm' ↦ osCR_named osKindOf_fold hm' trivial, fun i hi ↦ ?_, fun i hi _ ↦ ?_, ?_⟩
  · refine ⟨fun _ _ hm' ↦ osCR_named osKindOf_fold hm' trivial,
      fun _ _ hm' ↦ osCR_named osKindOf_can hm' trivial,
      fun hne _ _ hm' ↦ osCR_named (hN.ood i hi hne) hm' trivial,
      fun _ _ hm' ↦ osCR_named (hN.grind i hi) hm' trivial,
      fun _ a _ hm' h8 ↦ osCR_named hN.fm hm' (hfm a h8), fun _ ↦ ?_, ?_, ?_, ?_⟩
    · exact osCR_special (hN.sq i hi) ⟨i, hi, Or.inl ⟨rfl, rfl, rfl⟩⟩
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
      · obtain ⟨l1, l2⟩ := lk_slice (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 4)
          (off := (lvAt c i).foldsOff) (n := (lvAt c i).folds) (by omega) (by omega)
          (by rw [g4]; simpa [fchC] using hpre)
        exact ⟨_, l1, l2⟩
      · obtain ⟨l1, l2⟩ := lk_slice0 (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := osIxWp i)
          (n := 2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds))
          (by unfold osIxWp; omega) (by unfold osIxWp; omega)
          (by rw [(osOwnL_getD_lv c tr _ hi).2]; simpa [wpC] using hN.il i hi)
        exact ⟨_, l1, l2⟩
    · -- the cap
      refine osCR_named (hN.cap i hi) (cap_meaning_at h hs hrun hcaps hC hFl hi (hN.cdd i hi)) ?_
      have hendC := off_end (off := fun i ↦ 4 * (lvAt c i).capOff)
        (span := fun i ↦ 2 ^ ((lvAt c i).capDepth + 2)) hs.caps (c.levels.length - 1 - i) i
        (by omega)
      have hendF := off_end (off := fun i ↦ (lvAt c i).capOff)
        (span := fun i ↦ 2 ^ (lvAt c i).capDepth) hs.flags (c.levels.length - 1 - i) i (by omega)
      have hC' : 4 * (lvAt c i).capOff + 2 ^ ((lvAt c i).capDepth + 2) ≤ 4 * c.capLen := hendC
      have hF' : (lvAt c i).capOff + 2 ^ (lvAt c i).capDepth ≤ c.capLen := hendF
      intro q hq
      simp only [merkleCapSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · obtain ⟨l1, l2⟩ := lk_slice (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 0)
          (off := 4 * (lvAt c i).capOff) (n := 2 ^ ((lvAt c i).capDepth + 2)) (by omega) (by omega)
          (by rw [g0]; simpa [capsC] using hC')
        exact ⟨_, l1, l2⟩
      · obtain ⟨l1, l2⟩ := lk_slice (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 1)
          (off := (lvAt c i).capOff) (n := 2 ^ (lvAt c i).capDepth) (by omega) (by omega)
          (by rw [g1]; simpa [flagsC] using hF')
        exact ⟨_, l1, l2⟩
    · have hq : osSp c tr (osAtOf c b0) (osQueriesName i (lvAt c i)) (osQArgs c tr (osAtOf c b0) i)
          [(tr.L i).enforced] := ⟨i, hi, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      exact osCR_special (hN.q i hi) hq
  · exact osCR_special (hN.res i hi) ⟨i, hi, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
  · -- the folded message
    refine osCR_named hN.ffm (ffm_meaning_at hF h hs hm.fixed hm.T) ?_
    have hml := lf_ml' hF h
    intro q hq
    simp only [foldFinalSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨l1, l2⟩ := lk_slice0 (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 2)
        (n := 2 ^ c.yrLog) (by omega) (by omega) (by rw [g2, hF.ylen]; simp [fmsgC])
      exact ⟨_, l1, l2⟩
    · obtain ⟨l1, l2⟩ := lk_slice0 (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := osIxT c)
        (n := c.yrLog) (by unfold osIxT; omega) (by unfold osIxT; omega)
        (by rw [hT, tailC, List.length_append, tailChs_length, List.length_replicate, hml]
            have := hs.yr; omega)
      exact ⟨_, l1, l2⟩

end Placed

end
end LeanVM.Guest.B1
