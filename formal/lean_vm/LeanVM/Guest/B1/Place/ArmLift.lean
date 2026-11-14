/-
  LeanVM.Guest.B1.Place.ArmLift

  An arm of `open_stacked` at the merged template is complete placed, at an optional words bound,
  from the body's completeness at honest values and its callees' placed statements.
-/

module

public import LeanVM.Guest.B1.Place.ArmKids

/-!
# An arm, placed

**`arm_completeAtO`**: a function whose body is `osBody (osCfgR m ri)`, called on arguments whose
first is the rate's selector `g^ri`, with the body's honest data (`OsHonestA`) and the caller's
words holding the cursor's words and the window table, is `CompleteAtO` returning the claim, the
point buffers' pointers, the glued weight and the residual's value, the buffers `pt`, `pt1`, within
`osBos` words at a bound: from the named callees' placed statements (`hnamed`) and the helpers'
(`LpAtO`, `LqAtO`, `LrAtO`).

The proof (`os_completeAt_placeJFO`): the buffers at `osSizesL` after the frame; the body's values
from `OsHonestA.body` at their base; the callees after the buffers, the levels' by
`os_levels_kidsO` (`arm_lv_ok`), then the rest by `os_kids_blockO` (`arm_rest_ok`);
`query_win_ptrs` then holds the window pointers into the decoders where each `level_positions` was
placed (`qbpA`). When no memory holds the callees' words, every obligation on a memory is void.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **Whir's flat statements are flat.** -/
theorem flatF_of_flat : ∀ l : List Stmt, l.all Whir.Stmt.flat = true → l.all Core.Stmt.flat = true
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, flatF_of_flat l h.2⟩
    match s, h.1 with
    | .atom _, _ => rfl
    | .call .., _ => rfl
    | .callIf .., _ => rfl
    | .dispatch .., _ => rfl

/-- **A dispatch on the rate's selector `g^ri`** enters the rate's row's callee. -/
theorem selName_rate {σ : Val} {m ri : ℕ} (hri : ri < 4)
    (hR : σ (.n osRate) = ofK (addressOfIndex ri)) (l : ℕ) (f : OsLv → String) :
    selName σ (osCfgR m ri) l f = f (osLvA (osCfgR m ri) l) := by
  have h4 : ri < ((osCfgR m ri).lvAt l).length := by rw [osCfgR_lvAt_length]; exact hri
  unfold selName
  rw [hR, logG_spec (by omega), List.getD_eq_getElem _ _ (by simpa using h4), List.getElem_map,
    ← List.getD_eq_getElem _ default h4, osCfgR_lvAt_getD l hri]

theorem bufL_mem_getD {b : ℕ} {sizes : List ℕ} {own : List (List E)}
    (hl : own.length = sizes.length) {j : ℕ} (hj : j < sizes.length) :
    ((bases b sizes).getD j 0, own.getD j []) ∈ bufL b sizes own := by
  have hjl : j < (bufL b sizes own).length := by
    rw [bufL, List.length_zip, os_length_bases, hl, Nat.min_self]; exact hj
  have e : (bufL b sizes own)[j] = ((bases b sizes).getD j 0, own.getD j []) := by
    simp only [bufL, List.getElem_zip]
    rw [List.getD_eq_getElem _ _ (by rw [os_length_bases]; exact hj),
      List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]
  rw [← e]
  exact List.getElem_mem hjl

set_option maxHeartbeats 1600000 in
/-- **An arm at a configuration and rate is complete placed**, at an optional words bound. -/
theorem arm_completeAtO {Bd : Option (String → ℕ)} {m ri : ℕ} (hm : m < 11) (hri : ri < 4)
    {name : String} {fn : Fn} (hfind : coreProgram.find? name = some fn)
    (hp : fn.params = osParams 11) (hb : fn.body = osBody (osCfgR m ri))
    (hnamed : ∀ f ∈ osCalleeNames (osCfgR m ri), ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hlp : ∀ e ∈ lpTable, e.1 ∈ osCalleeNames (osCfgR m ri) →
      LpAtO fs cert κ e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2 (Bd.map (· e.1)))
    (hlq : ∀ e ∈ lqTable, e.1 ∈ osCalleeNames (osCfgR m ri) →
      LqAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1
      e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.2.2 (Bd.map (· e.1)))
    (hlr : ∀ e ∈ lrTable, e.1 ∈ osCalleeNames (osCfgR m ri) →
      LrAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 (Bd.map (· e.1)))
    {args : List E} (hargs : args.length = 11) (hsel0 : args.getD 0 0 = ofK (addressOfIndex ri))
    {cur tabs : E} {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA (osCfgR m ri) args cur tabs xs tgt inn res pt pt1) {Lin : Layout}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) :
    CompleteAtO fs cert κ name Lin args
      (fun rets Lout ↦ ∃ b b1 : ℕ,
        rets = [tgt, ofK (addressOfIndex b), ofK (addressOfIndex b1), inn, res] ∧
          Lout = [(b, pt), (b1, pt1)])
      (Bd.map fun Bk ↦ osBos fs Bk name (osCfgR m ri)) := by
  set c := osCfgR m ri with hc
  obtain ⟨hB, haddrs, hyr⟩ := armBody_ok ri hm
  have hLv := armLv_ok hm hri
  have hl : H.own.length = (osSizesL c).length := H.own_len.length_eq
  have hSL := osSizesL_length (c := c) hyr.le
  have hbA : fn.body = osBodyA c ++ [.ret (osBodyRet c)] := hb.trans (osBody_eq c)
  have hloop : coreProgram.loop name = false := by
    obtain ⟨a, l, he⟩ : ∃ a l, osBodyRet c = a :: l := ⟨_, _, rfl⟩
    rw [Program.loop_of_find? hfind, Fn.loop, hbA, he]
    simp [List.reverse_append]
  have hjs : [osIxPtA c, osIxPt1A c].Nodup := by simp [osIxPtA, osIxPt1A]
  have hjl : ∀ j ∈ [osIxPtA c, osIxPt1A c], j < (osSizesL c).length := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp only [osIxPtA, osIxPt1A] <;> omega
  refine os_completeAt_placeJFO hfind hloop κ Lin args _ (Bd.map fun Bk ↦ osBos fs Bk name c) hbA
    (flatF_of_flat _ (osBodyA_flat c)) haddrs (osSizesL c) [osIxPtA c, osIxPt1A c] hjs hjl
    (C := fun _ _ _ ↦ True) fun fp ↦ ?_
  set b0 := fp + fs name with hb0
  obtain ⟨kEnd, f, hbody⟩ := H.body b0
  set σ := fill (Val.ofArgs args) 11 kEnd f with hσ
  set Lk := osLkA c b0 H.own Lin with hLk
  have hBlk : ∀ rd, LowDef κ rd → MemL rd Lk →
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ Lk)) rd σ (osBodyA c) ∧
        OsOutA c b0 tabs tgt inn res H.own H.D σ :=
    fun rd hlow hm ↦ hbody _ rd (osHA_of_lk hl hLin hlow hm) σ (agree_fill _ _ _ _) (range_fill _ _ _ _)
  have hR : σ (.n osRate) = ofK (addressOfIndex ri) := by
    rw [hσ, fill_lt (by decide), ofArgs_n]; exact hsel0
  have hdo : ∀ s ∈ osBodyA c, DispOk σ s := fun s hs ↦ by
    match s, hs with
    | .dispatch x fs' a r, hs =>
      obtain ⟨hx, hl4⟩ := bodyOkS_dispatch (List.all_eq_true.mp hB _ hs)
      subst hx
      exact ⟨ri, by omega, by omega, hR⟩
    | .atom _, _ => trivial
    | .call .., _ => trivial
    | .callIf .., _ => trivial
    | .ite .., _ => trivial
    | .match_ .., _ => trivial
    | .ret _, _ => trivial
  have hfl : ∀ s ∈ osBodyA c, ∀ x fs' a r, s = .dispatch x fs' a r → fs'.length < 2 ^ 64 - 1 := by
    intro s hs x fs' a r he
    subst he
    have := (bodyOkS_dispatch (List.all_eq_true.mp hB _ hs)).2
    omega
  have hsel : ∀ l (g : OsLv → String), selName σ c l g = g (osLvA c l) := selName_rate hri hR
  have hparams : fn.params.map σ = args := by
    rw [hp]
    refine List.ext_getElem (by simp [osParams, hargs]) fun j h1 h2 ↦ ?_
    have hj : j < 11 := by simpa [osParams] using h1
    simp only [osParams, List.getElem_map, List.getElem_range]
    rw [hσ, fill_lt hj, ofArgs_n, List.getD_eq_getElem _ _ h2]
  -- `query_win_ptrs`, the levels' `level_positions` placed at `ps`
  set own' : List ℕ → List (List E) := fun ps ↦
    H.own.set osIxQbpA (qbpA c fun l ↦ winPtrsA fs cert c l (ps.getD l 0)) with hown'
  have hqb : (osSizesL c).getD osIxQbpA 0 = c.levels.length * ligPosCap := rfl
  have hfit : ∀ ps, List.Forall₂ (fun w s ↦ w.length ≤ s) (own' ps) (osSizesL c) := fun ps ↦
    forall₂_set (H.own_len.imp fun _ _ h ↦ le_of_eq h) (by rw [hqb, qbpA_length])
  have hgetD : ∀ ps j, j ≠ osIxQbpA → (own' ps).getD j [] = H.own.getD j [] := fun ps j hj ↦ by
    simp only [hown', List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]
  have hpt : H.own.getD (osIxPtA c) [] = pt := H.own_pt
  have hpt1 : H.own.getD (osIxPt1A c) [] = pt1 := H.own_pt1
  have hOut : ∀ ps, ∃ b b1 : ℕ,
      [tgt, osPtrA c b0 (osIxPtA c), osPtrA c b0 (osIxPt1A c), inn, res] =
        [tgt, ofK (addressOfIndex b), ofK (addressOfIndex b1), inn, res] ∧
      osLoutJ b0 (osSizesL c) (own' ps) [osIxPtA c, osIxPt1A c] = [(b, pt), (b1, pt1)] := fun ps ↦ by
    refine ⟨b0 + ((osSizesL c).take (osIxPtA c)).sum, b0 + ((osSizesL c).take (osIxPt1A c)).sum,
      ?_, ?_⟩
    · rw [osPtrA_eq, osPtrA_eq, baseA_eq c b0 (hjl _ (by simp)), baseA_eq c b0 (hjl _ (by simp))]
    · simp only [osLoutJ, List.map_cons, List.map_nil]
      rw [hgetD ps _ (by simp only [osIxPtA, osIxQbpA]; omega),
        hgetD ps _ (by simp only [osIxPt1A, osIxQbpA]; omega), hpt, hpt1]
  have hcalls := osBodyA_calls σ c
  set ks := osLvKOf σ c 0 c.levels (osHead c).2 with hks
  set rest := ((osTlA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
    (finFrames σ c).map (Main.mkCall σ) with hrest
  have hbound : ∀ N1 N2 : ℕ,
      (∀ Bk ∈ Bd, N1 ≤ ((ks.flatMap OsLvK.calls).map fun c' ↦ max (fs c'.f) (Bk c'.f)).sum) →
      (∀ Bk ∈ Bd, N2 ≤ (rest.map fun c' ↦ max (fs c'.f) (Bk c'.f)).sum) →
      ∀ B ∈ Bd.map (fun Bk ↦ osBos fs Bk name c), fs name + (osSizesL c).sum + (N1 + N2) ≤ B := by
    intro N1 N2 h1 h2 B hB'
    obtain ⟨Bk, hBk, rfl⟩ := Option.mem_map.mp hB'
    have hk := osKids_bound fs Bk hdo (σ := σ)
    rw [hcalls, List.map_append, List.sum_append] at hk
    have := h1 Bk hBk
    have := h2 Bk hBk
    unfold osBos
    omega
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk
  swap
  · -- no memory holds the callees' words: every obligation on a memory is void
    refine ⟨σ, own' [], [tgt, osPtrA c b0 (osIxPtA c), osPtrA c b0 (osIxPt1A c), inn, res], 0, [],
      fun _ ↦ False, _, rfl, hdo, hfit _, hOut _, fun q hq ↦ by simp at hq, disj_nil, ?_, hparams,
      fun rd hlow hBm hLin' ↦ absurd ⟨rd, hlow, memL_osLkA hBm hLin'⟩ hex,
      fun rd hlow hBm _ hLin' ↦ absurd ⟨rd, hlow, memL_osLkA hBm hLin'⟩ hex⟩
    intro B hB'
    obtain ⟨Bk, -, rfl⟩ := Option.mem_map.mp hB'
    unfold osBos
    omega
  obtain ⟨rd0, hl0, hm0⟩ := hex
  have hHV : OsHelperVals c b0 tabs H.own H.D σ := (hBlk rd0 hl0 hm0).2.2.2.2
  have hall : ∀ rd, LowDef κ rd → MemL rd Lk →
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ Lk)) rd σ (osBodyA c) :=
    fun rd hlow hm ↦ (hBlk rd hlow hm).1
  have hksl : ks.length = c.levels.length := osLvKOf_length σ c 0 c.levels _
  have hks_get : ∀ i (h : i < ks.length), ks[i] = lvK σ c i (osLvA c i) (osLvSt c i) := fun i h ↦ by
    have hi : i < c.levels.length := hksl ▸ h
    have e := osLvKOf_get σ c 0 c.levels (osHead c).2 i hi
    rw [Nat.zero_add, levels_getElem_eq hi] at e
    exact e
  -- the levels
  obtain ⟨N1, L1, ps, hps, hW1, hD1, hB1, hK1⟩ := os_levels_kidsO (fs := fs) (cert := cert)
    (κ := κ) σ Lk (winW fs cert c b0) (runsS fs cert c H.D) Bd ks 0 (fun i hi ↦ by
      have hi' : i < c.levels.length := hksl ▸ hi
      rw [hks_get i hi, Nat.zero_add]
      exact arm_lv_ok H hLin hall hdo hfl hB ⟨rd0, hl0, hm0⟩ hHV hsel hyr hnamed hlp hlq hi'
        (hLv i hi') fun c' hc' ↦ by
          rw [hcalls]
          refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hi, ?_⟩)
          rw [hks_get i hi]
          exact hc')
    (b0 + (osSizesL c).sum)
  -- the closing rounds, `fold_final_msg`, the residuals
  obtain ⟨N2, L2, hW2, hD2, hB2, hK2⟩ := os_kids_blockO (fs := fs) (cert := cert) (κ := κ) Lk σ
    rest Bd (fun c' hc' ht ↦ arm_rest_ok H hall hdo hfl hB ⟨rd0, hl0, hm0⟩ hHV hsel hyr hLv hnamed
      hlr hc' (by rw [hcalls]; exact List.mem_append_right _ hc') ht)
    (b0 + (osSizesL c).sum + N1)
  have hfit' := hfit ps
  refine ⟨σ, own' ps, [tgt, osPtrA c b0 (osIxPtA c), osPtrA c b0 (osIxPt1A c), inn, res], N1 + N2,
    L1 ++ L2, fun _ ↦ False, _, rfl, hdo, hfit', hOut _, ?_, disj_append hD1 hD2 hW1 hW2 le_rfl,
    hbound N1 N2 hB1 hB2, hparams, ?_, ?_⟩
  · rw [within_append]
    exact ⟨hW1.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
  · -- the body
    intro rd hlow hBm hLin'
    obtain ⟨hA', hO⟩ := hBlk rd hlow (memL_osLkA hBm hLin')
    refine ⟨?_, hO.2.1, hO.2.2.1⟩
    rw [hbA, holdsList_flat_ret _ (osBodyA_flat c)]
    exact ⟨os_allOk_mono (fun _ _ _ _ ↦ trivial) hA', hO.1⟩
  · -- the callees
    intro rd hlow hBm hL hLin'
    have hmk : MemL rd Lk := memL_osLkA hBm hLin'
    obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
    have hRk : ∀ i, RegionL Lk i →
        RegionL Lin i ∨ RegionL (bufL (fp + fs name) (osSizesL c) (own' ps)) i :=
      fun i hi ↦ regionL_osLkA hi
    have hl' : (own' ps).length = (osSizesL c).length := hfit'.length_eq
    have hqbW : (own' ps).getD osIxQbpA [] = qbpA c fun l ↦ winPtrsA fs cert c l (ps.getD l 0) := by
      have h10 : osIxQbpA < H.own.length := by rw [hl]; simp only [osIxQbpA]; omega
      simp [hown', List.getD_eq_getElem?_getD, h10]
    have hqbE : (baseA c b0 osIxQbpA, qbpA c fun l ↦ winPtrsA fs cert c l (ps.getD l 0)) ∈
        bufL b0 (osSizesL c) (own' ps) := by
      rw [← hqbW]
      exact bufL_mem_getD hl' (by simp only [osIxQbpA]; omega)
    rw [hcalls]
    refine kidsFromIn_append _ _ _ _ _ _ _ _ (hK1 rd _ (fun _ ↦ False) hlow hL1 hmk (fun i hi ↦ ?_) hRk
      (fun l _ hl2 p i hi ↦ ?_)) fun D1 _ ↦ hK2 rd _ D1 hlow hL2 hmk fun i hi ↦ Or.inl (hRk i hi)
    · -- the window pointers, where `level_positions` was placed
      have hi' : i < c.levels.length := by rw [hps, hksl] at hi; exact hi
      have hrd := hBm _ hqbE
      dsimp only at hrd
      have := memL_qbp_slice (ws := fun l ↦ winPtrsA fs cert c l (ps.getD l 0)) hrd hi' (by
        show (winPtrsA fs cert c i (ps.getD i 0)).length ≤ ligPosCap
        rw [winPtrsA_length fs cert]
        exact (hLv i hi').2.2.2.2.1)
      rw [Nat.zero_add, winW_eq, ← List.getD_eq_getElem _ 0 hi]
      exact this
    · -- their region, wherever placed
      have hl3 : l < c.levels.length := by rw [hksl] at hl2; omega
      rw [winW_eq] at hi
      obtain ⟨x, hx, h1, h2⟩ := hi
      rw [List.mem_singleton] at hx
      subst hx
      simp only [winPtrsA_length] at h2
      have hS : (osLvA c l).squeezes * (128 / (osLvA c l).depth) ≤ ligPosCap :=
        (hLv l hl3).2.2.2.2.1
      refine Or.inr ⟨_, hqbE, ?_, ?_⟩
      · simp only at h1 ⊢; omega
      · simp only [qbpA_length] at h2 ⊢
        have : (l + 1) * ligPosCap ≤ c.levels.length * ligPosCap := Nat.mul_le_mul_right _ hl3
        rw [Nat.add_mul, one_mul] at this
        omega

end
end LeanVM.Guest.B1.Arm
