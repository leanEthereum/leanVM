/-
  LeanVM.Guest.B1.Whir.CHonLvCM

  A non-final level's MidC at the honest data, from `OsH`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLvC

/-!
# `MidC` from `OsH`

`midC_of`: on every call relation and memory satisfying `OsH` at the honest buffers, level
`l < yr`'s calls and memory at the honest data (`LvAt.midW` with the level's root's cells), from
the run's step (`LvAt.NextStep`), the configuration's facts and the run facts named as
hypotheses: the row against the Spec's level, the carried capacity's length, the level's words a
suffix of the cursor's, the next root, the fold challenges, the rounds' counts, the out-of-domain
points' lengths, the root's height and the cap's cells, flags and agreement.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem getD_five2 {cap : List E} (hc : cap.length = 5) (x y : E) :
    (cap ++ [x, y]).getD 5 0 = x ∧ (cap ++ [x, y]).getD 6 0 = y := by
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ := five_of hc
  exact ⟨rfl, rfl⟩

theorem getD_five1 {cap : List E} (hc : cap.length = 5) (x : E) : (cap ++ [x]).getD 5 0 = x := by
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ := five_of hc
  rfl

theorem capOf_length (S : KeccakState) : (capOf S).length = 5 := rfl

theorem seg_eq {A B C : List E} {k : ℕ} (hk : k = A.length) : ((A ++ (B ++ C)).drop k).take B.length = B := by
  subst hk; simp

/-- **A non-final level's calls and memory**, honestly. -/
theorem midC_of {h : OsHD} {b : ℕ} {cur tabs : E} {xs : List E} {l : ℕ}
    (hS : HonStatic h.c) (hNm : HonNames h.c) (hl : l < h.c.yrLevel) {σ : Val}
    (hp : ∀ i < 13, σ (.n (11 + 2 * i)) = osPtrF h.c b i) (ht : σ (.n osTabs) = tabs) (batched : E)
    (hN : LvAt.NextStep h.logN l (h.L l) (h.L (l + 1)))
    (hfold : (h.L l).level.fold = (osLvAt h.c l).folds) (hmu : (h.L l).mu h.logN = (osLvAt h.c l).logCols)
    (hdep : (osLvAt h.c l).depth = (h.L l).dp h.logN) (hq : (h.L l).level.queries = (osLvAt h.c l).queries)
    (hsq : (osLvAt h.c l).squeezes = sqCount (128 / (osLvAt h.c l).depth) (osLvAt h.c l).queries)
    (hcols : 1 ≤ (osLvAt h.c l).logCols) (hcap5 : (h.L l).cap.length = 5) (hsuf : (h.L l).xs <:+ xs)
    (hR : digestHalves (h.root (l + 1)) = ((h.L l).nw.x0, (h.L l).nw.x1))
    (hG : ∀ j < (osLvAt h.c l).folds, h.G.getD ((osLvAt h.c l).foldsOff + j) 0 =
      (roundsSpec (osLvAt h.c l).folds (h.L l).s (h.L l).cap (h.L l).rw).1.gammas.getD
        ((h.L l).s.gammas.length + j) 0)
    (hL : h.Ls.length = h.c.levels.length)
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = (osLvAt h.c i).folds)
    (hz0 : ((h.L l).osRec h.logN).z0.length = (osLvAt h.c l).logCols)
    (hz1 : ((h.L l).osRec h.logN).z1.length = (osLvAt h.c l).logCols)
    (hht : ((h.L l).R.getD l default).2.1 = (osLvAt h.c l).depth)
    (hcv : h.cv l = capCellH (osLvAt h.c l).depth ((h.L l).qs h.logN) (h.L l).phase)
    (hfv : h.fv l = capFlH (osLvAt h.c l).depth (osLvAt h.c l).capDepth ((h.L l).qs h.logN) (h.L l).phase)
    (hag : Guest.Limits.OpeningsAgree (osLvAt h.c l).depth (((h.L l).qs h.logN).zip (h.L l).phase))
    (hps : ∀ q ∈ (h.L l).qs h.logN, q < 2 ^ (osLvAt h.c l).depth)
    (hq0 : 0 < ((h.L l).qs h.logN).length) (hsq1 : 1 ≤ (osLvAt h.c l).squeezes) :
    ∀ C rd, OsH C rd h.c b h.own cur tabs xs →
      MidC C rd σ h.c l (osLvAt h.c l) (h.capAt l) (h.claimAt l)
        (cur * gen ^ (xs.length - (h.xsAt l).length))
        ((h.L l).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 batched
          (osPtrF h.c b (13 + 2 * l)) (osPtrF h.c b (14 + 2 * l))) := by
  intro C rd hH
  have hyr := hS.yr
  have hln : l < h.c.levels.length := by omega
  have hrdx : ReadsAt rd cur xs := hH.1
  have hwt : WinTabs rd tabs := hH.2.1
  have hm : OsMemF rd h.c b h.own := hH.2.2.1
  obtain ⟨rw, W', hd, hrl7, hrok, hxsL, -, hnext, -, -, -⟩ := id hN
  have hLrw : (h.L l).rw = rw := by simp only [LvAt.rw, hd]
  have hLnw : (h.L l).nw = W' := by simp only [LvAt.nw, hd]
  have hxa : h.xsAt l = (h.L l).xs := by
    simp only [OsHD.xsAt, show l ≤ h.c.yrLevel by omega, ↓reduceIte]
  have hca : h.capAt l = (h.L l).cap := by
    simp only [OsHD.capAt, show l ≤ h.c.yrLevel by omega, ↓reduceIte]
  rw [hxa, hca]
  have hE := midEqs hN hfold hmu hdep hq hsq hcols (digestHalves (h.root l)).1 (digestHalves (h.root l)).2
    batched (osPtrF h.c b (13 + 2 * l)) (osPtrF h.c b (14 + 2 * l)) (h.claimAt l)
  have hW := lvAt_words (h.L l) h.logN hdep hq hsq
  -- the head's pointers
  have p0 : σ (.n osCaps) = osPtrF h.c b 0 := hp 0 (by norm_num)
  have p1 : σ (.n osFlags) = osPtrF h.c b 1 := hp 1 (by norm_num)
  have p3 : σ (.n osRoots) = osPtrF h.c b 3 := hp 3 (by norm_num)
  have p4 : σ (.n osFch) = osPtrF h.c b 4 := hp 4 (by norm_num)
  have p5 : σ (.n osCoefs) = osPtrF h.c b 5 := hp 5 (by norm_num)
  have p6 : σ (.n osBetas) = osPtrF h.c b 6 := hp 6 (by norm_num)
  have p7 : σ (.n osMus) = osPtrF h.c b 7 := hp 7 (by norm_num)
  have p8 : σ (.n osHs) = osPtrF h.c b 8 := hp 8 (by norm_num)
  have p9 : σ (.n osOodz) = osPtrF h.c b 9 := hp 9 (by norm_num)
  have p10 : σ (.n osOodSc) = osPtrF h.c b 10 := hp 10 (by norm_num)
  -- the level's words
  have hrwl : rw.length = 7 * (osLvAt h.c l).folds := by rw [hrl7, hfold]
  have hhl : W'.high.length = (osLvAt h.c l).folds := by rw [hnext.hlen, hfold]
  have hxs' : (h.L l).xs = rw ++ ((W'.x0 :: W'.x1 :: W'.high) ++
      ([W'.y0, W'.y1, W'.nn] ++ (W'.n2 :: (h.L (l + 1)).xs))) := by
    rw [hxsL]; simp [NextW.words]
  have hlen : (h.L l).xs.length = 7 * (osLvAt h.c l).folds + (2 + (osLvAt h.c l).folds) + 3 + 1 +
      (h.L (l + 1)).xs.length := by
    rw [hxs']; simp [hrwl, hhl]; omega
  have e0 : (((h.L l).xs.drop 0).take rw.length) = rw := by
    rw [hxs', List.drop_zero, List.take_left' rfl]
  have e1 : (((h.L l).xs.drop (7 * (osLvAt h.c l).folds)).take (W'.x0 :: W'.x1 :: W'.high).length) =
      W'.x0 :: W'.x1 :: W'.high := by
    rw [hxs']; exact seg_eq hrwl.symm
  have e2 : (((h.L l).xs.drop (7 * (osLvAt h.c l).folds + (2 + (osLvAt h.c l).folds))).take 3) =
      [W'.y0, W'.y1, W'.nn] := by
    rw [hxs', ← List.append_assoc]
    exact seg_eq (B := [W'.y0, W'.y1, W'.nn]) (by simp [hrwl, hhl]; omega)
  have e3 : (((h.L l).xs.drop (7 * (osLvAt h.c l).folds + (2 + (osLvAt h.c l).folds) + 3)).take 1) =
      [W'.n2] := by
    rw [hxs', ← List.append_assoc, ← List.append_assoc, show W'.n2 :: (h.L (l + 1)).xs =
      [W'.n2] ++ (h.L (l + 1)).xs from rfl]
    exact seg_eq (B := [W'.n2]) (by simp [hrwl, hhl]; omega)
  have hml : (W'.x0 :: W'.x1 :: W'.high).length = 2 + (osLvAt h.c l).folds := by simp [hhl]; omega
  -- the reads at the cursor
  have r0 := segR hrdx hsuf (k := 0) (m := rw.length) (by omega)
  rw [e0, Nat.add_zero] at r0
  have r1 := segR hrdx hsuf (k := 7 * (osLvAt h.c l).folds) (m := (W'.x0 :: W'.x1 :: W'.high).length)
    (by rw [hml]; omega)
  rw [e1] at r1
  have r2 := segR hrdx hsuf (k := 7 * (osLvAt h.c l).folds + (2 + (osLvAt h.c l).folds)) (m := 3) (by omega)
  rw [e2] at r2
  have r3 := segR hrdx hsuf (k := 7 * (osLvAt h.c l).folds + (2 + (osLvAt h.c l).folds) + 3) (m := 1)
    (by omega)
  rw [e3] at r3
  -- the level's Spec values
  have hqS : (h.L l).qS h.logN = W'.qS (rsF (h.L l).level (h.L l).cap rw)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).gammas.length) := by
    simp only [LvAt.qS, hd, LvAt.F, LvAt.mu, LvAt.s1, hLrw]
  have hF3 : (h.L l).F3 h.logN = W'.F3 (rsF (h.L l).level (h.L l).cap rw)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).gammas.length)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).gammas.length + (h.L l).level.logInvRate)
      (h.L l).level.queries := by
    simp only [LvAt.F3, hd, LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hLrw]
  have hqs : (h.L l).qs h.logN = W'.qs (rsF (h.L l).level (h.L l).cap rw)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).gammas.length)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).gammas.length + (h.L l).level.logInvRate)
      (h.L l).level.queries := by
    simp only [LvAt.qs, hd, LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hLrw]
  have hph : (h.L l).phase = W'.phase := by simp only [LvAt.phase, hd]
  -- the root and the openings
  obtain ⟨root, height, width, hRi, hopen⟩ := hnext.root
  have hRg : (h.L l).R.getD l default = (root, height, width) := by
    rw [List.getD_eq_getElem?_getD, hRi, Option.getD_some]
  have hroot : h.root l = root := by simp only [OsHD.root, hRg]
  have hheight : height = (osLvAt h.c l).depth := by rw [← hht, hRg]
  have hplen : (h.L l).phase.length = ((h.L l).qs h.logN).length := by rw [hph, hqs]; exact hnext.plen
  have hcd := (hNm.2.2.2.2.2.2.2.2 l hln)
  -- sizes
  have h9 : (osSizesF h.c).getD 9 0 = 2 * h.c.levels.length * 22 := by
    rw [hS.head (j := 9) (by omega)]; rfl
  have hmid := hS.mid hl
  have hsz0 := hS.lv0 hln
  simp only [show l ≠ h.c.yrLevel by omega, ↓reduceIte] at hsz0
  have hfe := h.foldsEnd_le hS hln
  have h4 : (osSizesF h.c).getD 4 0 = h.c.nFolds := by rw [hS.head (j := 4) (by omega)]; rfl
  have h5 : (osSizesF h.c).getD 5 0 = 3 * h.c.nFolds := by rw [hS.head (j := 5) (by omega)]; rfl
  refine ⟨?f_rounds, ?f_om, ?f_sent, ?f_spf, ?f_sp, ?f_ys, ?f_g17, ?f_rows, ?f_dec, ?f_loop, ?f_nb, ?f_g14, ?f_mcap, ?f_roots, ?f_hs, ?f_q, ?f_glue⟩
  case f_rounds =>
    rw [p4, p5, ht]
    change RoundsC C (osPtrF h.c b 4) (osPtrF h.c b 5) tabs _ _ _ _ _ (h.L l).rw
    rw [hLrw]
    refine roundsC_of (cur0 := cur) (xs0 := xs)
      (fun a r hmr hwa hx ↦ osH_named hH hNm.1 ⟨hmr, hwa⟩ hx) hwt (osLvAt h.c l).folds
      (osLvAt h.c l).foldsOff (h.L l).cap (h.claimAt l) _ rw hcap5 hrwl r0 ?_ fun j hj ↦ ?_
    · rw [← hfold]
      refine roundsMem_of _ _ (h.L l).s (h.L l).cap (h.claimAt l) rw hrok (fun j hj ↦ ?_) (fun j hj ↦ ?_)
      · rw [hfold] at hj ⊢
        have := h.fch_load hS hm (i := (osLvAt h.c l).foldsOff + j) (by omega)
        rw [hG j hj, hLrw] at this
        exact this
      · rw [hfold] at hj ⊢
        obtain ⟨a0, a1, a2⟩ := h.coefs_load hS hm (i := (osLvAt h.c l).foldsOff + j) (by omega)
        rw [h.allRounds_getD hS hL hrl hln hj] at a0 a1 a2
        simp only [LvAt.rounds, rsRounds, hLrw, hfold] at a0 a1 a2
        exact ⟨a0, a1, a2⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [mul_gen_pow_add]
        exact segF hsuf (by rw [hlen]; omega)
      · exact h.fixedAt_own (hS.headLt (j := 4) (by omega)) (by unfold osIxQbp; omega) (by rw [h4]; omega)
      · exact h.fixedAt_own (hS.headLt (j := 5) (by omega)) (by unfold osIxQbp; omega) (by rw [h5]; omega)
  case f_om =>
    have hk := (hNm.2.2.2.2.2.2.1 l hl).1
    have hc5 : (MidW.cap1 (osLvAt h.c l) (h.L l).cap (h.claimAt l) ((h.L l).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 batched (osPtrF h.c b (13 + 2 * l)) (osPtrF h.c b (14 + 2 * l)))).length = 5 :=
      roundsTr_length _ _ _ _ hcap5
    have hw0 := h.ownW_lv0 hln
    simp only [show l ≠ h.c.yrLevel by omega, ↓reduceIte] at hw0
    have hrd := h.reads hm (hS.lvLt hln).1 (by unfold osIxQbp; omega)
      (by rw [hw0, hsz0]; simp only [OsHD.sentC, hLnw, List.length_cons, hhl]; omega)
    rw [hw0] at hrd
    refine osH_named hH hk ?_ ?_
    · refine om_pre hc5 ?_ ?_ ?_
      · simp only [MidW.msg, LvAt.midW, hLnw]; exact hml
      · simp only [MidW.msg, LvAt.midW, hLnw, MidW.cur1, mul_gen_pow_add]; exact r1
      · exact hrd
    · intro q hq
      simp only [OsKind.spec, msgSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · dsimp only
        rw [(getD_five2 hc5 _ _).1]
        simp only [MidW.cur1, mul_gen_pow_add]
        exact segF hsuf (by rw [hlen]; omega)
      · dsimp only
        rw [(getD_five2 hc5 _ _).2]
        exact h.fixedAt_own0 (hS.lvLt hln).1 (by unfold osIxQbp; omega) (by rw [hsz0])
  case f_sent =>
    rw [p3]
    exact h.mid_sent hS hm hl hR
  case f_spf =>
    have hk := (hNm.2.2.2.2.2.2.1 l hl).2.1
    rw [hE.cap1, p9]
    refine osH_named hH hk (spf_pre (capOf_length _) ?_) ?_
    · rw [hE.z0]; exact (h.ood_rows hS hm hl hz0 hz1).1
    · intro q hq
      simp only [OsKind.spec, spfSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      dsimp only
      rw [(getD_five2 (capOf_length _) _ _).2]
      have hc22 : (osLvAt h.c l).logCols ≤ 22 := hmid.1
      exact h.fixedAt_own (hS.headLt (j := 9) (by omega)) (by unfold osIxQbp; omega)
        (by rw [h9]; show 2 * (l + 1) * 22 + _ ≤ _; omega)
  case f_sp =>
    have hk := (hNm.2.2.2.2.2.2.1 l hl).2.2
    rw [hE.cap1, p9]
    have hc5 : (spfRets (h.L l).cap1 ((h.L l).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 batched (osPtrF h.c b (13 + 2 * l)) (osPtrF h.c b (14 + 2 * l))).msg (osLvAt h.c l).logCols).length = 5 :=
      squeezeN_cap_length _ _ (capOf_length _)
    refine osH_named hH hk (sp_pre hc5 ?_) ?_
    · rw [hE.z1]; exact (h.ood_rows hS hm hl hz0 hz1).2
    · intro q hq
      simp only [OsKind.spec, spSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      dsimp only
      rw [getD_five1 hc5]
      have hc22 : (osLvAt h.c l).logCols ≤ 22 := hmid.1
      exact h.fixedAt_own (hS.headLt (j := 9) (by omega)) (by unfold osIxQbp; omega)
        (by rw [h9]; show (2 * (l + 1) + 1) * 22 + _ ≤ _; omega)
  case f_ys =>
    simp only [LvAt.midW, hLnw, MidW.cur1, mul_gen_pow_add, Nat.add_assoc]
    exact r2
  case f_g17 =>
    rw [ht]
    refine osH_named hH hNm.2.2.1 (grind_pre hwt ?_) (fun q hq ↦ by simp [OsKind.spec] at hq)
    rw [hE.S2, rdCell_one, hqS]
    exact grind_lane (by decide) hnext.ok1
  case f_rows =>
    have hix : osIxSqz h.c l = 14 + 2 * l := by
      simp only [osIxSqz, show l ≠ h.c.yrLevel by omega, ↓reduceIte]; ring
    obtain ⟨ra, rb⟩ := h.rows_lo_hi hS hm hln hsq1
    rw [hix] at ra rb
    rw [hE.S2, hE.cap3, ← hW.2.2.1, ← hW.2.2.2]
    exact ⟨ra, rb⟩
  case f_dec => exact osH_special hH hcd.2.1 _ _
  case f_loop => exact fun _ ↦ osH_special hH hcd.2.2.1 _ _
  case f_nb =>
    simp only [LvAt.midW, hLnw, MidW.cur1, mul_gen_pow_add, Nat.add_assoc]
    exact r3 0 (by simp)
  case f_g14 =>
    rw [ht]
    refine osH_named hH hNm.2.2.2.1 (grind_pre hwt ?_) (fun q hq ↦ by simp [OsKind.spec] at hq)
    rw [hE.SL, rdCell_one, hF3]
    simp only [LvAt.midW, hLnw]
    exact grind_lane (by decide) hnext.ok2
  case f_mcap =>
    rw [p0, p1]
    subst hheight
    rw [hqs] at hcv hfv hag hps hq0 hplen
    rw [hph] at hcv hfv hag hplen
    refine osH_named hH hcd.1 ?_ (h.cap_fixed hS hln)
    have := h.cap_pre hS hm hln (root := root) (width := width) hplen hopen hps hag hcd.2.2.2.2.1
      hcd.2.2.2.2.2 hq0 hcv hfv
    simp only [LvAt.midW, hroot]
    exact this
  case f_roots =>
    rw [p3]
    exact h.mid_roots hS hm hln
  case f_hs =>
    intro j hj
    rw [p8]
    exact h.mid_hs hS hm hl hj
  case f_q => exact osH_special hH hcd.2.2.2.1 _ _
  case f_glue =>
    rw [p10, p6, p7, hE.lam]
    exact h.mid_glue hS hm hl
end
end LeanVM.Guest.B1.Whir
