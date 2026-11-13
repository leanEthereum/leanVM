/-
  LeanVM.Guest.B1.Whir.CHonLvCM

  A non-final level's MidC at the honest data, from `OsHA`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLvC
public import LeanVM.Guest.B1.Whir.CHonMemFin
public import LeanVM.Guest.B1.Whir.CHonNames

/-!
# `MidC` from `OsHA`

`midC_of`: on every call relation and memory satisfying `OsHA` at the honest buffers, level
`l < yr`'s calls and memory at the honest data (`LvAt.midW` with the level's root's cells), from
the run's step (`LvAt.NextStep`), the configuration's facts and the run facts named as
hypotheses: the row against the Spec's level, the carried capacity's length, the level's words a
suffix of the cursor's, the next root, the fold challenges, the rounds' counts, the out-of-domain
points' lengths. The dispatches into `level_positions` and `level_queries` hold under `OsHA` at
any returns.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem getD_five2 {cap : List E} (hc : cap.length = 5) (x y : E) :
    (cap ++ [x, y]).getD 5 0 = x ∧ (cap ++ [x, y]).getD 6 0 = y := by
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ := five_of hc
  exact ⟨rfl, rfl⟩

theorem capOf_length (S : KeccakState) : (capOf S).length = 5 := rfl

theorem seg_eq {A B C : List E} {k : ℕ} (hk : k = A.length) : ((A ++ (B ++ C)).drop k).take B.length = B := by
  subst hk; simp

/-- **A non-final level's calls and memory**, honestly. -/
theorem midC_of {h : OsHD} {b : ℕ} {cur tabs : E} {xs : List E} {l : ℕ}
    (hS : HonStatic h.c) (hNm : HonNames h.c) (hl : l < h.c.yrLevel) {σ : Val}
    (hp : ∀ i < 11, σ (.n (12 + 2 * i)) = osPtrA h.c b i) (ht : σ (.n osTabs) = tabs) (batched : E)
    (hN : LvAt.NextStep h.logN l (h.L l) (h.L (l + 1)))
    (hfold : (h.L l).level.fold = ((h.c.levels.getD l default)).folds) (hmu : (h.L l).mu h.logN = ((h.c.levels.getD l default)).logCols)
    (hdep : ((h.c.levels.getD l default)).depth = (h.L l).dp h.logN) (hq : (h.L l).level.queries = ((h.c.levels.getD l default)).queries)
    (hsq : ((h.c.levels.getD l default)).squeezes = sqCount (128 / ((h.c.levels.getD l default)).depth) ((h.c.levels.getD l default)).queries)
    (hcols : 1 ≤ ((h.c.levels.getD l default)).logCols) (hcap5 : (h.L l).cap.length = 5) (hsuf : (h.L l).xs <:+ xs)
    (hR : digestHalves (h.root (l + 1)) = ((h.L l).nw.x0, (h.L l).nw.x1))
    (hG : ∀ j < ((h.c.levels.getD l default)).folds, h.G.getD (((h.c.levels.getD l default)).foldsOff + j) 0 =
      (roundsSpec ((h.c.levels.getD l default)).folds (h.L l).s (h.L l).cap (h.L l).rw).1.alphas.getD
        ((h.L l).s.alphas.length + j) 0)
    (hL : h.Ls.length = h.c.levels.length)
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = ((h.c.levels.getD i default)).folds)
    (hz0 : ((h.L l).osRec h.logN).z0.length = ((h.c.levels.getD l default)).logCols) :
    ∀ C rd, OsHA C rd h.c b h.own cur tabs xs →
      MidC C rd σ h.c l ((h.c.levels.getD l default)) (h.capAt l) (h.claimAt l)
        (cur * gen ^ (xs.length - (h.xsAt l).length))
        ((h.L l).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 batched
          (osPtrA h.c b (11 + l))) := by
  intro C rd hH
  have hyr := hS.yr
  have hln : l < h.c.levels.length := by omega
  have hrdx : ReadsAt rd cur xs := hH.1
  have hwt : WinTabs rd tabs := hH.2.1
  have hm : OsMemA rd h.c b h.own := hH.2.2.1
  obtain ⟨rw, W', hd, hrl7, hrok, hxsL, -, hnext, -, -, -⟩ := id hN
  have hLrw : (h.L l).rw = rw := by simp only [LvAt.rw, hd]
  have hLnw : (h.L l).nw = W' := by simp only [LvAt.nw, hd]
  have hxa : h.xsAt l = (h.L l).xs := by
    simp only [OsHD.xsAt, show l ≤ h.c.yrLevel by omega, ↓reduceIte]
  have hca : h.capAt l = (h.L l).cap := by
    simp only [OsHD.capAt, show l ≤ h.c.yrLevel by omega, ↓reduceIte]
  rw [hxa, hca]
  have hE := midEqs hN hfold hmu hdep hq hsq hcols (digestHalves (h.root l)).1 (digestHalves (h.root l)).2
    batched (osPtrA h.c b (11 + l)) (h.claimAt l)
  have hW := lvAt_words (h.L l) h.logN hdep hq hsq
  -- the head's pointers
  have p3 : σ (.n osRoots) = osPtrA h.c b 1 := hp 1 (by norm_num)
  have p4 : σ (.n osFch) = osPtrA h.c b 2 := hp 2 (by norm_num)
  have p5 : σ (.n osCoefs) = osPtrA h.c b 3 := hp 3 (by norm_num)
  have p6 : σ (.n osBetas) = osPtrA h.c b 4 := hp 4 (by norm_num)
  have p7 : σ (.n osMus) = osPtrA h.c b 5 := hp 5 (by norm_num)
  have p8 : σ (.n osHs) = osPtrA h.c b 6 := hp 6 (by norm_num)
  have p9 : σ (.n osOodz) = osPtrA h.c b 7 := hp 7 (by norm_num)
  have p10 : σ (.n osOodSc) = osPtrA h.c b 8 := hp 8 (by norm_num)
  -- the level's words
  have hrwl : rw.length = 5 * ((h.c.levels.getD l default)).folds := by rw [hrl7, hfold]
  have hhl : W'.high.length = ((h.c.levels.getD l default)).folds := by rw [hnext.hlen, hfold]
  have hxs' : (h.L l).xs = rw ++ ((W'.x0 :: W'.x1 :: W'.high) ++
      ([W'.n1] ++ ([W'.y0, W'.nn] ++ (h.L (l + 1)).xs))) := by
    rw [hxsL]; simp [NextW.words]
  have hlen : (h.L l).xs.length = 5 * ((h.c.levels.getD l default)).folds + (2 + ((h.c.levels.getD l default)).folds) + 1 + 2 +
      (h.L (l + 1)).xs.length := by
    rw [hxs']; simp [hrwl, hhl]; omega
  have e0 : (((h.L l).xs.drop 0).take rw.length) = rw := by
    rw [hxs', List.drop_zero, List.take_left' rfl]
  have e1 : (((h.L l).xs.drop (5 * ((h.c.levels.getD l default)).folds)).take (W'.x0 :: W'.x1 :: W'.high).length) =
      W'.x0 :: W'.x1 :: W'.high := by
    rw [hxs']; exact seg_eq hrwl.symm
  have e1n : (((h.L l).xs.drop (5 * ((h.c.levels.getD l default)).folds + (2 + ((h.c.levels.getD l default)).folds))).take 1) =
      [W'.n1] := by
    rw [hxs', ← List.append_assoc]
    exact seg_eq (B := [W'.n1]) (by simp [hrwl, hhl]; omega)
  have e2 : (((h.L l).xs.drop (5 * ((h.c.levels.getD l default)).folds + (2 + ((h.c.levels.getD l default)).folds) + 1)).take 2) =
      [W'.y0, W'.nn] := by
    rw [hxs', ← List.append_assoc, ← List.append_assoc]
    exact seg_eq (B := [W'.y0, W'.nn]) (by simp [hrwl, hhl]; omega)
  have hml : (W'.x0 :: W'.x1 :: W'.high).length = 2 + ((h.c.levels.getD l default)).folds := by simp [hhl]; omega
  -- the reads at the cursor
  have r0 := segR hrdx hsuf (k := 0) (m := rw.length) (by omega)
  rw [e0, Nat.add_zero] at r0
  have r1 := segR hrdx hsuf (k := 5 * ((h.c.levels.getD l default)).folds) (m := (W'.x0 :: W'.x1 :: W'.high).length)
    (by rw [hml]; omega)
  rw [e1] at r1
  have r1n := segR hrdx hsuf (k := 5 * ((h.c.levels.getD l default)).folds + (2 + ((h.c.levels.getD l default)).folds)) (m := 1)
    (by omega)
  rw [e1n] at r1n
  have r2 := segR hrdx hsuf (k := 5 * ((h.c.levels.getD l default)).folds + (2 + ((h.c.levels.getD l default)).folds) + 1) (m := 2)
    (by omega)
  rw [e2] at r2
  -- the level's Spec values
  have hqS : (h.L l).qS h.logN = W'.qS (rsF (h.L l).level (h.L l).cap rw)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).alphas.length) := by
    simp only [LvAt.qS, hd, LvAt.F, LvAt.mu, LvAt.s1, hLrw]
  have hF3 : (h.L l).F3 h.logN = W'.F3 (rsF (h.L l).level (h.L l).cap rw)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).alphas.length)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).alphas.length + (h.L l).level.logInvRate)
      (h.L l).level.queries := by
    simp only [LvAt.F3, hd, LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hLrw]
  have hqs : (h.L l).qs h.logN = W'.qs (rsF (h.L l).level (h.L l).cap rw)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).alphas.length)
      (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).alphas.length + (h.L l).level.logInvRate)
      (h.L l).level.queries := by
    simp only [LvAt.qs, hd, LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hLrw]
  have hph : (h.L l).phase = W'.phase := by simp only [LvAt.phase, hd]
  -- sizes
  have h9 : (osSizesL h.c).getD 7 0 = h.c.levels.length * 24 := by
    rw [hS.head (j := 7) (by omega)]; rfl
  have hmid := hS.mid hl
  have hsz0 := hS.sent hl
  have hfe := h.foldsEnd_le hS hln
  have h4 : (osSizesL h.c).getD 2 0 = h.c.nFolds := by rw [hS.head (j := 2) (by omega)]; rfl
  have h5 : (osSizesL h.c).getD 3 0 = 2 * h.c.nFolds := by rw [hS.head (j := 3) (by omega)]; rfl
  refine ⟨?f_rounds, ?f_om, ?f_g0, ?f_sent, ?f_spf, ?f_ys, ?f_g17, ?f_lp, ?f_hs, ?f_q, ?f_roots, ?f_glue⟩
  case f_rounds =>
    rw [p4, p5, ht]
    change RoundsC C (osPtrA h.c b 2) (osPtrA h.c b 3) tabs _ _ _ _ _ (h.L l).rw
    rw [hLrw]
    refine roundsC_of (cur0 := cur) (xs0 := xs)
      (fun a r hmr hwa hx ↦ osH_named hH hNm.1 ⟨hmr, hwa⟩ hx) hwt ((h.c.levels.getD l default)).folds
      ((h.c.levels.getD l default)).foldsOff (h.L l).cap (h.claimAt l) _ rw hcap5 hrwl r0 ?_ fun j hj ↦ ?_
    · rw [← hfold]
      refine roundsMem_of _ _ (h.L l).s (h.L l).cap (h.claimAt l) rw hrok (fun j hj ↦ ?_) (fun j hj ↦ ?_)
      · rw [hfold] at hj ⊢
        have := h.fch_load hS hm (i := ((h.c.levels.getD l default)).foldsOff + j) (by omega)
        rw [hG j hj, hLrw] at this
        exact this
      · rw [hfold] at hj ⊢
        obtain ⟨a0, a1⟩ := h.coefs_load hS hm (i := ((h.c.levels.getD l default)).foldsOff + j) (by omega)
        rw [h.allRounds_getD hS hL hrl hln hj] at a0 a1
        simp only [LvAt.rounds, rsRounds, hLrw, hfold] at a0 a1
        exact ⟨a0, a1⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [mul_gen_pow_add]
        exact segF hsuf (by rw [hlen]; omega)
      · exact h.fixedAt_own (hS.headLt (j := 2) (by omega)) (by unfold osIxQbpA; omega) (by rw [h4]; omega)
      · exact h.fixedAt_own (hS.headLt (j := 3) (by omega)) (by unfold osIxQbpA; omega) (by rw [h5]; omega)
  case f_om =>
    have hk := (hNm.2.2.2.2.2.2.1 l hl).1
    have hc5 : (MidW.cap1 ((h.c.levels.getD l default)) (h.L l).cap (h.claimAt l) ((h.L l).midW (digestHalves (h.root l)).1 (digestHalves (h.root l)).2 batched (osPtrA h.c b (11 + l)))).length = 5 :=
      roundsTr_length _ _ _ _ hcap5
    have hw0 := h.ownW_sent hl
    have hrd := h.reads hm (hS.sentLt (le_of_lt hl)) (by unfold osIxQbpA; omega)
      (by rw [hw0, hsz0]; simp only [OsHD.sentC, hLnw, List.length_cons, hhl]; omega)
    rw [hw0] at hrd
    refine osH_named hH hk ?_ ?_
    · refine omN_pre hc5 ?_ ?_ ?_ ?_
      · simp only [MidW.msg, LvAt.midW, hLnw]; exact hml
      · simp only [MidW.msg, LvAt.midW, hLnw, MidW.cur1, mul_gen_pow_add]; exact r1
      · simp only [LvAt.midW, hLnw, MidW.cur1, mul_gen_pow_add]
        have := r1n 0 (by simp)
        rw [loadHolds_mul_gen_pow] at this ⊢
        rw [show xs.length - (h.L l).xs.length + 5 * ((h.c.levels.getD l default)).folds + (2 + ((h.c.levels.getD l default)).folds) =
          xs.length - (h.L l).xs.length + (5 * ((h.c.levels.getD l default)).folds + (2 + ((h.c.levels.getD l default)).folds)) + 0 by
          omega]
        exact this
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
        exact h.fixedAt_own0 (hS.sentLt (le_of_lt hl)) (by unfold osIxQbpA; omega) (by rw [hsz0])
  case f_g0 =>
    rw [ht]
    refine osH_named hH hNm.2.2.2.1 (grind_pre hwt ?_) (fun q hq ↦ by simp [OsKind.spec] at hq)
    have hlane := grind_lane (by decide) (hnext.ok0.resolve_left (by decide))
    simp only [NextW.F1] at hlane
    rw [hE.cap1]
    simp only [LvAt.midW, hLnw, MidW.msg]
    unfold LvAt.cap1
    rw [hLrw]
    exact hlane
  case f_sent =>
    rw [p3]
    exact h.mid_sent hS hm hl hR
  case f_spf =>
    have hk := (hNm.2.2.2.2.2.2.1 l hl).2.1
    rw [hE.cap1, p9]
    refine osH_named hH hk (spf_pre (capOf_length _) ?_) ?_
    · rw [hE.z0]; exact h.ood_rows hS hm hl hz0
    · intro q hq
      simp only [OsKind.spec, spfSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      dsimp only
      rw [(getD_five2 (capOf_length _) _ _).2]
      have hc24 : ((h.c.levels.getD l default)).logCols ≤ 24 := hmid.1
      exact h.fixedAt_own (hS.headLt (j := 7) (by omega)) (by unfold osIxQbpA; omega)
        (by rw [h9]; show (l + 1) * 24 + _ ≤ _; omega)
  case f_ys =>
    simp only [LvAt.midW, hLnw, MidW.cur1, mul_gen_pow_add, Nat.add_assoc]
    exact r2
  case f_g17 =>
    rw [ht]
    refine osH_named hH hNm.2.2.1 (grind_pre hwt ?_) (fun q hq ↦ by simp [OsKind.spec] at hq)
    rw [hE.S2, rdCell_one, hqS]
    have hg := grind_lane (bits := Whir.queryGrindingBits) (n := W'.nn)
      (s := (oodPt (rsF (h.L l).level (h.L l).cap rw) (W'.x0 :: W'.x1 :: W'.high) W'.n1
        (h.logN - (rsSt (h.L l).level (h.L l).s (h.L l).cap rw).alphas.length)).2.absorbAll [W'.y0]
          dsObserve) (by decide) hnext.ok1
    exact hg
  case f_lp =>
    exact osH_special hH (hNm.2.2.2.2.2.2.2 l hln).1 _ _
  case f_roots =>
    rw [p3]
    exact h.mid_roots hS hm hln
  case f_hs =>
    intro j hj
    rw [p8]
    exact h.mid_hs hS hm hl hj
  case f_q => exact osH_special hH (hNm.2.2.2.2.2.2.2 l hln).2 _ _
  case f_glue =>
    rw [p10, p6, p7, hE.lam]
    exact h.mid_glue hS hm hl
end
end LeanVM.Guest.B1.Whir
