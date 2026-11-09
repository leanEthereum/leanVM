/-
  LeanVM.Guest.B1.Place.OsKidsSp5

  open_stacked's opening_queries calls, placed on the honest trace.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsSp4
public import LeanVM.Guest.B1.Opening.QueriesPlacedAll
public import LeanVM.Guest.B1.Opening.LoopsTable
public import LeanVM.Guest.B1.Whir.Facts

/-!
# The queries, placed

**`os_q_completeAtB`**: level `l`'s `opening_queries` call, at its honest arguments (the cap and
flags at the level's offsets, `λ`, `λ^q`, the window pointers at the level's offset, the row
weights, `g^N`), is `CompleteAtB`, by a tree of at most `oqBound` words, on the callees' words
`osLk`, the window pointers `osW … l p` and the decoders' runs `osS … l p`, for every placement
`p` of the level's squeeze loop, returning the level's enforced sum; `os_q_completeAtD`, its
`CompleteAtD`. From `OqCompleteDB` (`OqFits` is `True`): the positions decoded, their windows in
the decoders' `wins` runs (`osS_wins`), the row weights, the cap's cells and flags the honest cap
holds at the openings' climbs (`SpLv.cap_writes`, the openings agreeing by `CapsAgree`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem osAtOf_caps (c : OsCfg) (b : ℕ) : (osAtOf c b).P.caps = osPtrAt c b 0 := rfl
theorem osAtOf_flags (c : OsCfg) (b : ℕ) : (osAtOf c b).P.flags = osPtrAt c b 1 := rfl
theorem osAtOf_qbp (c : OsCfg) (b : ℕ) : (osAtOf c b).P.qbp = osPtrAt c b 8 := rfl

/-- Level `l`'s `opening_queries` shape. -/
def osQShape (c : OsCfg) (l : ℕ) : Oq :=
  ⟨if l = 0 then 1 else 0, (lvAt c l).interleave, (lvAt c l).depth - (lvAt c l).capDepth,
    (lvAt c l).capDepth⟩

theorem osQShape_base (c : OsCfg) (l : ℕ) : (osQShape c l).base = if l = 0 then 1 else 0 := rfl
theorem osQShape_I (c : OsCfg) (l : ℕ) : (osQShape c l).I = (lvAt c l).interleave := rfl
theorem osQShape_pd (c : OsCfg) (l : ℕ) :
    (osQShape c l).pd = (lvAt c l).depth - (lvAt c l).capDepth := rfl
theorem osQShape_cd (c : OsCfg) (l : ℕ) : (osQShape c l).cd = (lvAt c l).capDepth := rfl

theorem pow_div_lt {q a b : ℕ} (h : q < 2 ^ (a + b)) : q / 2 ^ a < 2 ^ b :=
  Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact h)

/-- **Level `l`'s `opening_queries` call, placed**, for every placement `p` of its squeeze loop,
by a tree of at most `oqBound` words: its frame, its chain buffer and its iterations' frames. -/
theorem os_q_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {c : OsCfg}
    {tr : OsTr} {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E}
    {os : List (List Opening)} {root : Digest} (h : TrFit c tr)
    (hs : OsSizes c) (hrun : TrRun c μ r target S xs os root tr)
    (hcaps : Whir.CapsAgree μ r target S xs os root) {l : ℕ} (hl : l < c.levels.length)
    (hnm : NamesOk c l (lvAt c l))
    (hfits : OqFits fs cert (osQueriesName l (lvAt c l)) (oqLoopOf (osQueriesName l (lvAt c l)))
      (osQShape c l) ((lvAt c l).queries % 2 * (if l = 0 then 1 else 0)))
    (hidx : (tr.L l).index = l) (hwd : (tr.L l).width = lvWidth l (lvAt c l))
    (hil : rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤
      c.maxIl)
    (hqo : (lvAt c l).queries + 1 < ordG) (b : ℕ) (Lin : Layout) (p : ℕ) :
    CompleteAtB fs cert κ (osQueriesName l (lvAt c l))
      (osLk c tr b Lin ++ osW fs cert c b l p ++ osS fs cert c tr l p)
      [(osAtOf c b).P.caps * gen ^ (4 * (lvAt c l).capOff),
        (osAtOf c b).P.flags * gen ^ (lvAt c l).capOff, (tr.L l).lam,
        (tr.L l).lam ^ (lvAt c l).queries, (osAtOf c b).P.qbp * gen ^ (lvAt c l).posOff,
        osPtrAt c b (osIxWp l), gen ^ ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))]
      (Returns [(tr.L l).enforced])
      (oqBound fs (osQueriesName l (lvAt c l)) (oqLoopOf (osQueriesName l (lvAt c l)))
        ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))) := by
  -- the level's facts
  have hil' : l < tr.Ls.length := by rw [h.len]; exact hl
  obtain ⟨R, d, hOk⟩ := h.ok l hl
  have hlv := h.lvb l hl
  have hfit := h.fit l hl
  have hD : (tr.L l).D = (lvAt c l).depth := by rw [SpLv.D, hfit.ml, hlv.depth]
  have hh : (tr.L l).height = (lvAt c l).depth := by rw [hrun.height l hil', hD]
  have hcdd := hlv.cdd
  have hcd2 := hlv.cd
  have hql : (tr.L l).qs.length = (lvAt c l).queries := by rw [SpLv.qs_length, hlv.queries]
  have hos : (tr.L l).os.length = (tr.L l).qs.length := hOk.osLen
  have hch : (tr.L l).chs.length = (lvAt c l).folds := by rw [SpLv.chs_length, hfit.fold]
  have hper := hlv.per
  have hspan : (lvAt c l).queries ≤ (lvAt c l).squeezes * (192 / (lvAt c l).depth) := by
    rw [hlv.squeezes]; exact ceilDiv_mul_ge hper
  have hmemL : tr.L l ∈ tr.Ls := by
    rw [OsTr.L, List.getD_eq_getElem _ _ hil']; exact List.getElem_mem hil'
  have hag := SpLv.batchAgrees (tr.L l) hcaps (hrun.qs _ hmemL)
  have hpend : (tr.L l).F2.pend = [] := SpLv.F2_pend _
  -- the openings
  have hopen : ∀ k < (lvAt c l).queries, ((tr.L l).os.getD k default).leaf.length =
      lvWidth l (lvAt c l) ∧ ((tr.L l).os.getD k default).path.length = (lvAt c l).depth := by
    intro k hk
    have hk1 : k < (tr.L l).qs.length := by omega
    have hk2 : k < (tr.L l).os.length := by omega
    obtain ⟨e1, e2, -⟩ := openOne_facts (hOk.opens k hk1 hk2)
    rw [List.getD_eq_getElem _ _ hk2]
    exact ⟨by rw [e1, hwd], by rw [e2, hh]⟩
  have hqsk : ∀ k < (lvAt c l).queries, (tr.L l).qs.getD k 0 < 2 ^ (lvAt c l).depth := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by omega), ← hD]
    exact SpLv.qs_lt _ _ (List.getElem_mem _)
  -- the callee
  have hloop : (osQueriesName l (lvAt c l), oqLoopOf (osQueriesName l (lvAt c l)), osQShape c l,
      (lvAt c l).queries % 2 * (if l = 0 then 1 else 0)) ∈ openingQueriesLoops :=
    shapes_loops hnm.2.2.2.2.2.1
  have hOq := opening_queries_completeAtB fs cert _ hloop
  dsimp only at hOq
  have hQ := oqCount_q (lvAt c l).queries l
  have key := hOq hfits κ (osLk c tr b Lin ++ osW fs cert c b l p ++ osS fs cert c tr l p)
    ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))
    (osBase c b 0 + 4 * (lvAt c l).capOff) (osBase c b 1 + (lvAt c l).capOff)
    (osBase c b 8 + (lvAt c l).posOff) (osBase c b (osIxWp l)) (tr.L l).lam
    ((tr.L l).lam ^ (lvAt c l).queries) (fun i ↦ (wpC c tr l).getD i 0) (osEb fs cert c l p)
    (fun k ↦ (tr.L l).qs.getD k 0) (fun k ↦ ((tr.L l).os.getD k default).leaf)
    (fun k ↦ ((tr.L l).os.getD k default).path.take ((lvAt c l).depth - (lvAt c l).capDepth))
    (by have : (lvAt c l).queries / (1 + if l = 0 then 1 else 0) ≤ (lvAt c l).queries :=
          Nat.div_le_self _ _
        omega)
    hOk.lam ?_ ?_ ?_
  · -- the returns
    simp only [osQShape_base, osQShape_I] at key
    rw [q_ret hlv.row hil hidx hch hql hos hOk.lam fun k hk ↦ (hopen k hk).1] at key
    rw [osAtOf_caps, osAtOf_flags, osAtOf_qbp, osPtrAt_eq, osPtrAt_eq, osPtrAt_eq, osPtrAt_eq,
      ofK_gpow_mul_gen, ofK_gpow_mul_gen, ofK_gpow_mul_gen]
    exact key
  · -- the static facts
    simp only [osQShape_base, osQShape_pd, osQShape_cd]
    rw [hQ]
    intro k hk
    refine ⟨?_, ?_, ?_⟩
    · show (tr.L l).qs.getD k 0 < 2 ^ ((lvAt c l).depth - (lvAt c l).capDepth + (lvAt c l).capDepth)
      rw [Nat.sub_add_cancel hcdd]; exact hqsk k hk
    · show ((tr.L l).os.getD k default).leaf.length = Oq.R ⟨_, _, _, _⟩
      rw [(hopen k hk).1, Oq.R, lvWidth]
      by_cases h0 : l = 0 <;> simp [h0]
    · show (List.take _ ((tr.L l).os.getD k default).path).length = _
      rw [List.length_take, (hopen k hk).2]
      simp
  · -- the regions
    rw [osQShape_base, hQ]
    have hendF := off_end (off := fun i ↦ (lvAt c i).capOff)
      (span := fun i ↦ 2 ^ (lvAt c i).capDepth) hs.flags (c.levels.length - 1 - l) l (by omega)
    have hendC := off_end (off := fun i ↦ 4 * (lvAt c i).capOff)
      (span := fun i ↦ 2 ^ ((lvAt c i).capDepth + 2)) hs.caps (c.levels.length - 1 - l) l (by omega)
    obtain ⟨g0, g1, -, -, -⟩ := osOwnL_getD_head6 c tr fun _ _ ↦ 0
    refine ⟨fun l' hl' ↦ ?_, fun k hk ↦ ⟨?_, fun t ht ↦ ?_, ?_, fun e he ↦ ?_⟩⟩
    · refine regionL_append_left (regionL_append_left (osLk_region c tr b Lin (fun _ _ ↦ 0)
        (j := osIxWp l) (by unfold osIxWp; omega) (by unfold osIxWp; omega) ?_))
      rw [(osOwnL_getD_lv6 c tr (fun _ _ ↦ 0) hl).2]
      simp only [wpC, List.length_map, List.length_range]
      simp only [osQShape, Oq.lo] at hl'
      omega
    · exact regionL_append_left (regionL_append_right (osW_region (fs := fs) (cert := cert)
        (c := c) (b := b) (l := l) (p := p) (by omega)))
    · simp only [osQShape_pd, osQShape_cd, Nat.sub_add_cancel hcdd] at ht
      exact regionL_append_right (osS_region (fs := fs) (cert := cert) (c := c) (tr := tr) (l := l)
        (p := p) (by omega) ht)
    · have hq := hqsk k hk
      simp only [osQShape_pd, osQShape_cd]
      rw [← Nat.sub_add_cancel hcdd, show (lvAt c l).depth - (lvAt c l).capDepth +
        (lvAt c l).capDepth = ((lvAt c l).depth - (lvAt c l).capDepth + 1) +
        ((lvAt c l).capDepth - 1) by omega] at hq
      have h1 := pow_div_lt hq
      have h2 : 2 ^ (lvAt c l).capDepth = 2 * 2 ^ ((lvAt c l).capDepth - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [Nat.add_assoc]
      refine regionL_append_left (regionL_append_left (osLk_region c tr b Lin (fun _ _ ↦ 0)
        (j := 1) (by omega) (by omega) ?_))
      rw [g1]
      simp only [flagsC, List.length_map, List.length_range]
      omega
    · have hq := hqsk k hk
      simp only [osQShape_pd, osQShape_cd]
      rw [← Nat.sub_add_cancel hcdd] at hq
      have h1 := pow_div_lt hq
      have h2 : 2 ^ ((lvAt c l).capDepth + 2) = 4 * 2 ^ (lvAt c l).capDepth := by
        rw [pow_add]; ring
      rw [Nat.add_assoc]
      refine regionL_append_left (regionL_append_left (osLk_region c tr b Lin (fun _ _ ↦ 0)
        (j := 0) (by omega) (by omega) ?_))
      rw [g0]
      simp only [capsC, List.length_map, List.length_range]
      omega
  · -- the memory
    intro rd _ hm
    obtain ⟨hm12, hmS⟩ := Main.memL_append.mp hm
    obtain ⟨hmk, hmW⟩ := Main.memL_append.mp hm12
    rw [osQShape_base, hQ]
    obtain ⟨g0, g1, -, -, -⟩ := osOwnL_getD_head6 c tr fun _ _ ↦ 0
    have hC : ReadsAt rd (osPtrAt c b 0) (capsC c tr) := by
      have := osLk_reads hmk (fun _ _ ↦ 0) (j := 0) (by omega) (by omega); rwa [g0] at this
    have hFl : ReadsAt rd (osPtrAt c b 1) (flagsC c tr) := by
      have := osLk_reads hmk (fun _ _ ↦ 0) (j := 1) (by omega) (by omega); rwa [g1] at this
    refine ⟨fun l' hl' ↦ ?_, fun k hk ↦ ⟨?_, fun t ht ↦ ?_, ?_⟩⟩
    · have hr := osLk_reads hmk (fun _ _ ↦ 0) (j := osIxWp l) (by unfold osIxWp; omega)
        (by unfold osIxWp; omega)
      rw [(osOwnL_getD_lv6 c tr (fun _ _ ↦ 0) hl).2] at hr
      simp only [osQShape, Oq.lo] at hl'
      have hl2 : l' < (wpC c tr l).length := by
        simp only [wpC, List.length_map, List.length_range]
        omega
      have := hr l' hl2
      show LoadHolds rd _ l' ((wpC c tr l).getD l' 0)
      rw [List.getD_eq_getElem _ _ hl2]
      exact this
    · exact osW_reads hmW (by omega)
    · simp only [osQShape_pd, osQShape_cd, Nat.sub_add_cancel hcdd] at ht ⊢
      have hb := osS_wins (tr := tr) (fs := fs) (cert := cert) (p := p) hmS (k := k) (by omega) ht
      have hq : (tr.L l).qs.getD k 0 = qwPosOf (lvAt c l).depth (sqWJ ((tr.L l).F2.squeezeN 0).2.cap
          (k / (192 / (lvAt c l).depth))) (k % (192 / (lvAt c l).depth)) := by
        unfold qwPosOf
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp only [SpLv.qs, queriesOf, List.getElem_map, List.getElem_range, hD]
        congr 3
        have hj : k / (192 / (lvAt c l).depth) < (tr.L l).nsq := by
          rw [hfit.nsq]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
        rw [squeezeN_getD _ _ _ hj]
        unfold sqWJ sqCapJ
        rw [show (Fs.squeezeN 0 (tr.L l).F2).2.cap = (tr.L l).F2.cap from rfl,
          ← fs_of_pend_nil hpend, ← fs_of_pend_nil (squeezeN_pend hpend _)]
        rfl
      rw [hq]
      exact hb
    · have hk1 : k < (tr.L l).qs.length := by omega
      have hk2 : k < (tr.L l).os.length := by omega
      have hw := SpLv.cap_writes (tr.L l) hOk (hrun.height l hil') hag hcd2 (by rw [hh]; exact hcdd)
        (rd := rd) (cap := osPtrAt c b 0 * gen ^ (4 * (lvAt c l).capOff))
        (flags := osPtrAt c b 1 * gen ^ (lvAt c l).capOff)
        (fun k' _ hk' ↦ caps_get hs hC hl hk') (fun k' _ hk' ↦ flags_get hs hFl hl hk') k hk1 hk2
      rw [osPtrAt_eq, osPtrAt_eq, ofK_gpow_mul_gen, ofK_gpow_mul_gen, hh] at hw
      simp only [osQShape_pd, osQShape_cd]
      rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2]
      exact hw

/-- **Level `l`'s `opening_queries` call, placed**, `CompleteAtD`. -/
theorem os_q_completeAtD (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {c : OsCfg}
    {tr : OsTr} {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E}
    {os : List (List Opening)} {root : Digest} (h : TrFit c tr)
    (hs : OsSizes c) (hrun : TrRun c μ r target S xs os root tr)
    (hcaps : Whir.CapsAgree μ r target S xs os root) {l : ℕ} (hl : l < c.levels.length)
    (hnm : NamesOk c l (lvAt c l))
    (hfits : OqFits fs cert (osQueriesName l (lvAt c l)) (oqLoopOf (osQueriesName l (lvAt c l)))
      (osQShape c l) ((lvAt c l).queries % 2 * (if l = 0 then 1 else 0)))
    (hidx : (tr.L l).index = l) (hwd : (tr.L l).width = lvWidth l (lvAt c l))
    (hil : rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤
      c.maxIl)
    (hqo : (lvAt c l).queries + 1 < ordG) (b : ℕ) (Lin : Layout) (p : ℕ) :
    CompleteAtD fs cert κ (osQueriesName l (lvAt c l))
      (osLk c tr b Lin ++ osW fs cert c b l p ++ osS fs cert c tr l p)
      [(osAtOf c b).P.caps * gen ^ (4 * (lvAt c l).capOff),
        (osAtOf c b).P.flags * gen ^ (lvAt c l).capOff, (tr.L l).lam,
        (tr.L l).lam ^ (lvAt c l).queries, (osAtOf c b).P.qbp * gen ^ (lvAt c l).posOff,
        osPtrAt c b (osIxWp l), gen ^ ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))]
      (Returns [(tr.L l).enforced]) :=
  (os_q_completeAtB fs cert κ h hs hrun hcaps hl hnm hfits hidx hwd hil hqo b Lin p).toCompleteAtD

end
end LeanVM.Guest.B1
