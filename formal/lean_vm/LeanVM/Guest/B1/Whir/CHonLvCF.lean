/-
  LeanVM.Guest.B1.Whir.CHonLvCF

  The final level's FinC and the closing rounds' TailC at the honest data, from `OsH`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLvCM

/-!
# `FinC` and `TailC` from `OsH`

`finC_of`: on every call relation and memory satisfying `OsH` at the honest buffers, the final
level's calls and memory at the honest data (`LvAt.finWD` with the level's root's cells), from
its end (`LvAt.FinStep`) and the run facts named as hypotheses. `tailC_from`: the closing rounds'
calls and challenges (`TailC`), as `body_of` takes them; `tail_zero`: `tail_challenges`' unused
entries.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The final level's calls and memory**, honestly. -/
theorem finC_of {h : OsHD} {b : ℕ} {cur tabs : E} {xs : List E} {lane : ℕ} {w : WhirEnd}
    (hS : HonStatic h.c) (hNm : HonNames h.c) {σ : Val}
    (hp : ∀ i < 13, σ (.n (11 + 2 * i)) = osPtrF h.c b i) (ht : σ (.n osTabs) = tabs) (batched : E)
    (hF : LvAt.FinStep h.logN lane h.c.yrLevel h.Lf w)
    (hfold : h.Lf.level.fold = (osLvAt h.c h.c.yrLevel).folds)
    (hdep : (osLvAt h.c h.c.yrLevel).depth = h.Lf.dp h.logN)
    (hq : h.Lf.level.queries = (osLvAt h.c h.c.yrLevel).queries)
    (hsq : (osLvAt h.c h.c.yrLevel).squeezes =
      sqCount (128 / (osLvAt h.c h.c.yrLevel).depth) (osLvAt h.c h.c.yrLevel).queries)
    (hcap5 : h.Lf.cap.length = 5) (hsuf : h.Lf.xs <:+ xs)
    (hlane : h.Lf.fw.fold.length = h.c.yrLen + (osLvAt h.c h.c.yrLevel).folds)
    (hG : ∀ j < (osLvAt h.c h.c.yrLevel).folds, h.G.getD ((osLvAt h.c h.c.yrLevel).foldsOff + j) 0 =
      (roundsSpec (osLvAt h.c h.c.yrLevel).folds h.Lf.s h.Lf.cap h.Lf.rw).1.alphas.getD
        (h.Lf.s.alphas.length + j) 0)
    (hL : h.Ls.length = h.c.levels.length)
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = (osLvAt h.c i).folds)
    (hht : (h.Lf.R.getD h.c.yrLevel default).2.1 = (osLvAt h.c h.c.yrLevel).depth)
    (hcv : h.cv h.c.yrLevel = capCellH (osLvAt h.c h.c.yrLevel).depth (h.Lf.qs h.logN) h.Lf.phase)
    (hfv : h.fv h.c.yrLevel = capFlH (osLvAt h.c h.c.yrLevel).depth (osLvAt h.c h.c.yrLevel).capDepth
      (h.Lf.qs h.logN) h.Lf.phase)
    (hag : Guest.Limits.OpeningsAgree (osLvAt h.c h.c.yrLevel).depth ((h.Lf.qs h.logN).zip h.Lf.phase))
    (hps : ∀ q ∈ h.Lf.qs h.logN, q < 2 ^ (osLvAt h.c h.c.yrLevel).depth)
    (hq0 : 0 < (h.Lf.qs h.logN).length) (hsq1 : 1 ≤ (osLvAt h.c h.c.yrLevel).squeezes) :
    ∀ C rd, OsH C rd h.c b h.own cur tabs xs →
      FinC C rd σ h.c h.c.yrLevel (osLvAt h.c h.c.yrLevel) (h.capAt h.c.yrLevel) (h.claimAt h.c.yrLevel)
        (cur * gen ^ (xs.length - (h.xsAt h.c.yrLevel).length))
        (h.Lf.finWD (digestHalves (h.root h.c.yrLevel)).1 (digestHalves (h.root h.c.yrLevel)).2 batched
          (osPtrF h.c b (13 + 2 * h.c.yrLevel)) (osPtrF h.c b (14 + 2 * h.c.yrLevel))) := by
  intro C rd hH
  have hyr := hS.yr
  have hln : h.c.yrLevel < h.c.levels.length := by omega
  have hrdx : ReadsAt rd cur xs := hH.1
  have hwt : WinTabs rd tabs := hH.2.1
  have hm : OsMemF rd h.c b h.own := hH.2.2.1
  obtain ⟨rw, W', hd, hrl7, hrok, hxsL, -, hfin, -⟩ := id hF
  have hLrw : h.Lf.rw = rw := by simp only [LvAt.rw, hd]
  have hLfw : h.Lf.fw = W' := by simp only [LvAt.fw, hd]
  have hxa : h.xsAt h.c.yrLevel = h.Lf.xs := by simp only [OsHD.xsAt, le_refl, ↓reduceIte]
  have hca : h.capAt h.c.yrLevel = h.Lf.cap := by simp only [OsHD.capAt, le_refl, ↓reduceIte]
  rw [hxa, hca]
  have hE := finEqs hF hfold hdep hq hsq (digestHalves (h.root h.c.yrLevel)).1
    (digestHalves (h.root h.c.yrLevel)).2 batched (osPtrF h.c b (13 + 2 * h.c.yrLevel))
    (osPtrF h.c b (14 + 2 * h.c.yrLevel)) (h.claimAt h.c.yrLevel)
  have hW := lvAt_words h.Lf h.logN hdep hq hsq
  have p0 : σ (.n osCaps) = osPtrF h.c b 0 := hp 0 (by norm_num)
  have p1 : σ (.n osFlags) = osPtrF h.c b 1 := hp 1 (by norm_num)
  have p2 : σ (.n osFmsg) = osPtrF h.c b 2 := hp 2 (by norm_num)
  have p3 : σ (.n osRoots) = osPtrF h.c b 3 := hp 3 (by norm_num)
  have p4 : σ (.n osFch) = osPtrF h.c b 4 := hp 4 (by norm_num)
  have p5 : σ (.n osCoefs) = osPtrF h.c b 5 := hp 5 (by norm_num)
  -- the level's words
  have hrwl : rw.length = 5 * (osLvAt h.c h.c.yrLevel).folds := by rw [hrl7, hfold]
  have hfl : W'.fold.length = h.c.yrLen + (osLvAt h.c h.c.yrLevel).folds := by rw [← hLfw]; exact hlane
  have hxs' : h.Lf.xs = rw ++ (W'.fold ++ ([W'.nn] ++ tailWords W'.pairs)) := by
    rw [hxsL]; simp [FinW.words]
  have hlen : h.Lf.xs.length = 5 * (osLvAt h.c h.c.yrLevel).folds +
      (h.c.yrLen + (osLvAt h.c h.c.yrLevel).folds) + 1 + (tailWords W'.pairs).length := by
    rw [hxs']; simp [hrwl, hfl]; omega
  have e0 : ((h.Lf.xs.drop 0).take rw.length) = rw := by
    rw [hxs', List.drop_zero, List.take_left' rfl]
  have e1 : ((h.Lf.xs.drop (5 * (osLvAt h.c h.c.yrLevel).folds)).take W'.fold.length) = W'.fold := by
    rw [hxs']; exact seg_eq hrwl.symm
  have e2 : ((h.Lf.xs.drop (5 * (osLvAt h.c h.c.yrLevel).folds + W'.fold.length)).take 1) = [W'.nn] := by
    rw [hxs', ← List.append_assoc]
    exact seg_eq (B := [W'.nn]) (by simp [hrwl])
  have r0 := segR hrdx hsuf (k := 0) (m := rw.length) (by omega)
  rw [e0, Nat.add_zero] at r0
  have r1 := segR hrdx hsuf (k := 5 * (osLvAt h.c h.c.yrLevel).folds) (m := W'.fold.length) (by omega)
  rw [e1] at r1
  have r2 := segR hrdx hsuf (k := 5 * (osLvAt h.c h.c.yrLevel).folds + W'.fold.length) (m := 1) (by omega)
  rw [e2] at r2
  have hqS : h.Lf.qS h.logN = W'.qS (rsF h.Lf.level h.Lf.cap rw) := by
    simp only [LvAt.qS, hd, LvAt.F, hLrw]
  have hqs : h.Lf.qs h.logN = W'.qs (rsF h.Lf.level h.Lf.cap rw)
      (h.logN - (rsSt h.Lf.level h.Lf.s h.Lf.cap rw).alphas.length + h.Lf.level.logInvRate)
      h.Lf.level.queries := by
    simp only [LvAt.qs, hd, LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hLrw]
  have hph : h.Lf.phase = W'.phase := by simp only [LvAt.phase, hd]
  obtain ⟨root, height, width, hRi, hopen⟩ := hfin.root
  have hRg : h.Lf.R.getD h.c.yrLevel default = (root, height, width) := by
    rw [List.getD_eq_getElem?_getD, hRi, Option.getD_some]
  have hroot : h.root h.c.yrLevel = root := by simp only [OsHD.root, hRg]
  have hheight : height = (osLvAt h.c h.c.yrLevel).depth := by rw [← hht, hRg]
  have hplen : h.Lf.phase.length = (h.Lf.qs h.logN).length := by rw [hph, hqs]; exact hfin.plen
  have hcd := (hNm.2.2.2.2.2.2.2.2 h.c.yrLevel hln)
  have hfe := h.foldsEnd_le hS hln
  have h2 : (osSizesF h.c).getD 2 0 = h.c.yrLen + (osLvAt h.c h.c.yrLevel).folds := by
    rw [hS.head (j := 2) (by omega)]; rfl
  have h4 : (osSizesF h.c).getD 4 0 = h.c.nFolds := by rw [hS.head (j := 4) (by omega)]; rfl
  have h5 : (osSizesF h.c).getD 5 0 = 2 * h.c.nFolds := by rw [hS.head (j := 5) (by omega)]; rfl
  refine ⟨?f_rounds, ?f_om, ?f_g17, ?f_rows, ?f_dec, ?f_loop, ?f_mcap, ?f_roots, ?f_hs, ?f_q⟩
  case f_rounds =>
    rw [p4, p5, ht]
    change RoundsC C (osPtrF h.c b 4) (osPtrF h.c b 5) tabs _ _ _ _ _ h.Lf.rw
    rw [hLrw]
    refine roundsC_of (cur0 := cur) (xs0 := xs)
      (fun a r hmr hwa hx ↦ osH_named hH hNm.1 ⟨hmr, hwa⟩ hx) hwt (osLvAt h.c h.c.yrLevel).folds
      (osLvAt h.c h.c.yrLevel).foldsOff h.Lf.cap (h.claimAt h.c.yrLevel) _ rw hcap5 hrwl r0 ?_ fun j hj ↦ ?_
    · rw [← hfold]
      refine roundsMem_of _ _ h.Lf.s h.Lf.cap (h.claimAt h.c.yrLevel) rw hrok (fun j hj ↦ ?_) (fun j hj ↦ ?_)
      · rw [hfold] at hj ⊢
        have := h.fch_load hS hm (i := (osLvAt h.c h.c.yrLevel).foldsOff + j) (by omega)
        rw [hG j hj, hLrw] at this
        exact this
      · rw [hfold] at hj ⊢
        obtain ⟨a0, a1⟩ := h.coefs_load hS hm (i := (osLvAt h.c h.c.yrLevel).foldsOff + j) (by omega)
        rw [h.allRounds_getD hS hL hrl hln hj] at a0 a1
        simp only [LvAt.rounds, rsRounds, hLrw, hfold] at a0 a1
        exact ⟨a0, a1⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [mul_gen_pow_add]
        exact segF hsuf (by rw [hlen]; omega)
      · exact h.fixedAt_own (hS.headLt (j := 4) (by omega)) (by unfold osIxQbp; omega) (by rw [h4]; omega)
      · exact h.fixedAt_own (hS.headLt (j := 5) (by omega)) (by unfold osIxQbp; omega) (by rw [h5]; omega)
  case f_om =>
    have hk := hNm.2.2.2.2.2.1
    have hc5 : (FinWD.cap1 (osLvAt h.c h.c.yrLevel) h.Lf.cap (h.claimAt h.c.yrLevel)
        (h.Lf.finWD (digestHalves (h.root h.c.yrLevel)).1 (digestHalves (h.root h.c.yrLevel)).2 batched
          (osPtrF h.c b (13 + 2 * h.c.yrLevel)) (osPtrF h.c b (14 + 2 * h.c.yrLevel)))).length = 5 :=
      roundsTr_length _ _ _ _ hcap5
    have hrd := h.reads hm (hS.headLt (j := 2) (by omega)) (by unfold osIxQbp; omega)
      (by rw [h.ownW_fmsg, h2, OsHD.fmsgC, hLfw, hfl])
    rw [h.ownW_fmsg, OsHD.fmsgC] at hrd
    rw [p2]
    refine osH_named hH hk ?_ ?_
    · refine omN_pre hc5 ?_ ?_ ?_ hrd
      · simp only [LvAt.finWD]; exact hlane
      · simp only [LvAt.finWD, hLfw, MidW.cur1, mul_gen_pow_add]; exact r1
      · simp only [LvAt.finWD, hLfw, MidW.cur1, mul_gen_pow_add]
        have := r2 0 (by simp)
        simp only [List.getElem_cons_zero] at this
        rw [← Nat.add_assoc, ← mul_gen_pow_add, loadHolds_mul_gen_pow, Nat.add_zero] at this
        rw [← hfl]
        exact this
    · intro q hq
      simp only [OsKind.spec, msgSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · dsimp only
        rw [(getD_five2 hc5 _ _).1]
        simp only [MidW.cur1, mul_gen_pow_add]
        exact segF hsuf (by rw [hlen]; omega)
      · dsimp only
        rw [(getD_five2 hc5 _ _).2]
        exact h.fixedAt_own0 (hS.headLt (j := 2) (by omega)) (by unfold osIxQbp; omega) (by rw [h2])
  case f_g17 =>
    rw [ht]
    refine osH_named hH hNm.2.2.1 (grind_pre hwt ?_) (fun q hq ↦ by simp [OsKind.spec] at hq)
    rw [hE.S2, hqS]
    exact grind_lane (by decide) hfin.ok1
  case f_rows =>
    have hix : osIxSqz h.c h.c.yrLevel = 13 + 2 * h.c.yrLevel := by simp only [osIxSqz, ↓reduceIte]; ring
    obtain ⟨ra, rb⟩ := h.rows_lo_hi hS hm hln hsq1
    rw [hix] at ra rb
    rw [hE.S2, hE.cap3, ← hW.2.2.1, ← hW.2.2.2]
    exact ⟨ra, rb⟩
  case f_dec => exact osH_special hH hcd.2.1 _ _
  case f_loop => exact fun _ ↦ osH_special hH hcd.2.2.1 _ _
  case f_mcap =>
    rw [p0, p1]
    subst hheight
    rw [hqs] at hcv hfv hag hps hq0 hplen
    rw [hph] at hcv hfv hag hplen
    refine osH_named hH hcd.1 ?_ (h.cap_fixed hS hln)
    have := h.cap_pre hS hm hln (root := root) (width := width) hplen hopen hps hag hcd.2.2.2.2.1
      hcd.2.2.2.2.2 hq0 hcv hfv
    simp only [LvAt.finWD, hroot]
    exact this
  case f_roots =>
    rw [p3]
    exact h.mid_roots hS hm hln
  case f_hs =>
    intro j hj
    rw [p2]
    have := h.fin_hs hS hm hj
    simp only [LvAt.finWD]
    exact this
  case f_q => exact osH_special hH hcd.2.2.2.1 _ _

/-! ## The closing rounds -/

theorem tailWords_seg : ∀ (pairs : List (E × E)) (j : ℕ), j < pairs.length →
    ((tailWords pairs).drop (2 * j)).take 2 = [(pairs.getD j (0, 0)).1, (pairs.getD j (0, 0)).2]
  | [], _, h => absurd h (by simp)
  | (a, b) :: rest, 0, _ => by simp [tailWords]
  | (a, b) :: rest, j + 1, h => by
    have := tailWords_seg rest j (by simp at h; omega)
    simp only [tailWords, List.flatMap_cons, List.getD_cons_succ] at this ⊢
    rw [show 2 * (j + 1) = 2 + 2 * j by ring, ← List.drop_drop, List.drop_left' (by simp)]
    exact this

theorem tailWords_length (pairs : List (E × E)) : (tailWords pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p rest ih => simp only [tailWords, List.flatMap_cons, List.length_append] at ih ⊢; simp [ih]; ring

theorem tailRun_cap_length : ∀ (pairs : List (E × E)) (cap : List E) (cl : E), cap.length = 5 →
    (tailRun pairs cap cl).2.2.length = 5
  | [], _, _, h => h
  | (c0, c2) :: rest, cap, cl, _ => by
    rw [tailRun_cons]
    exact tailRun_cap_length rest _ _ (by simp [Fs.squeeze, capOf])

/-- **The closing rounds' calls and challenges**, as `body_of` takes them. -/
theorem tailC_from {h : OsHD} {b : ℕ} {cur tabs : E} {xs : List E} (hS : HonStatic h.c) (hNm : HonNames h.c)
    (hsuf : tailWords h.Lf.fw.pairs <:+ xs) (hpl : h.Lf.fw.pairs.length = h.c.yrLog)
    (hcap5 : (h.Lf.F3 h.logN).cap.length = 5) :
    ∀ C rd, OsH C rd h.c b h.own cur tabs xs →
      TailC C rd (osPtrF h.c b (13 + 2 * h.c.levels.length)) tabs 0 h.Lf.fw.pairs
        (h.capAt h.c.levels.length) (h.claimAt h.c.levels.length)
        (cur * gen ^ (xs.length - (h.xsAt h.c.levels.length).length)) := by
  intro C rd hH
  have hyr := hS.yr
  have hn : ¬ h.c.levels.length ≤ h.c.yrLevel := by omega
  have hxa : h.xsAt h.c.levels.length = tailWords h.Lf.fw.pairs := by simp only [OsHD.xsAt, hn, ↓reduceIte]
  have hca : h.capAt h.c.levels.length = (h.Lf.F3 h.logN).cap := by simp only [OsHD.capAt, hn, ↓reduceIte]
  have hcl : h.claimAt h.c.levels.length = h.cl1F := by simp only [OsHD.claimAt, hn, ↓reduceIte]
  rw [hxa, hca, hcl]
  have hTl : h.T.length = h.c.yrLog := by rw [OsHD.T, OsHD.tr, tailRun_length, hpl]
  have hrT := h.tail_reads hS hH.2.2.1 (by rw [hTl]; exact hS.ylog)
  refine tailC_of _ 0 _ _ _ (fun j hj ↦ ?_) (fun j hj ↦ ?_)
  · have hc5 := tailRun_cap_length (h.Lf.fw.pairs.take j) _ h.cl1F hcap5
    refine osH_named hH hNm.2.1 (tail_pre hc5 ?_) ?_
    · have := segR hH.1 hsuf (k := 2 * j) (m := 2) (by rw [tailWords_length]; omega)
      rw [tailWords_seg _ _ hj] at this
      rw [mul_gen_pow_add]
      exact this
    · intro q hq
      simp only [OsKind.spec, tailSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      obtain ⟨f0, f1, f2, f3, f4, he⟩ := five_of hc5
      dsimp only
      rw [he]
      show FixedAt _ _ _ _ _ _ (cur * gen ^ (xs.length - (tailWords h.Lf.fw.pairs).length) * gen ^ (2 * j)) 2
      rw [mul_gen_pow_add]
      exact segF hsuf (by rw [tailWords_length]; omega)
  · have := hrT j (by rw [hTl, ← hpl]; exact hj)
    rw [Nat.zero_add]
    rw [← List.getD_eq_getElem _ 0] at this
    exact this

/-- **`tail_challenges`' unused entries are zero.** -/
theorem tail_zero {h : OsHD} {b : ℕ} {rd : Reader} (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own)
    (hpl : h.Lf.fw.pairs.length = h.c.yrLog) :
    ∀ i < yrLogCap - h.c.yrLog, LoadHolds rd (osPtrF h.c b (13 + 2 * h.c.levels.length)) (h.c.yrLog + i) 0 := by
  intro i hi
  have hTl : h.T.length = h.c.yrLog := by rw [OsHD.T, OsHD.tr, tailRun_length, hpl]
  have hsz := hS.fin (k := 0) (by omega)
  have a := h.load hm (hS.finLt (k := 0) (by omega)) (by unfold osIxQbp; omega) (e := h.c.yrLog + i)
    (by rw [Nat.add_zero] at hsz ⊢; rw [hsz]; simp; omega)
  rw [h.ownW_fin (by omega), Nat.add_zero] at a
  simpa [List.getD_eq_getElem?_getD, hTl] using a

end
end LeanVM.Guest.B1.Whir
