/-
  LeanVM.Guest.B1.Tables.VerifyTablesCAtB

  `verify_tables` is complete, placed, by a bounded tree (`CompleteTablesAtB`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCAtD
public import LeanVM.Guest.B1.Tables.VtKidsB

/-!
# `verify_tables`, placed and bounded

`verify_tables_completeAt_of` with `completeAt_flatW`: its tree is its frame, its 205 buffers
(`vtSizes n`, at most `vtSzPre.sum + 198`) and its 75 callees, each within its name's bound
(`vt_kids_completeW`, `vtKids_bound`), and it weighs its frame and its callees' weights
(`vtTablesBoundW`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_tables` is complete, placed, by a bounded tree within weights**, given the placed
form's conditions and the fit of the placements. -/
theorem verify_tables_completeAtW_of (hPl : VtPlacedOk) (hF : VtFits) (fs : String → ℕ)
    (cert : String → V → ℕ) {Θ : Type} (w : Θ → String → ℕ) {κ : ℕ} (hκ : 7 ≤ κ) (bytecode : List K) :
    CompleteTablesAtW fs cert κ bytecode TCtx w (vtTablesBound fs) fun θ => vtTablesBoundW (w θ) := by
  intro pi logMem alphas point values cv xs cv' rowsN bus claims beta bv rm gzcn c z lp sq dims rows bk fpw pool
    cplen chi Lin hb hdep hpl hgz h16 h32 hal hvl hrl hrows hcl hrun hLin
  set L := layoutOf bytecode logMem rowsN with hL
  obtain ⟨hlb, -⟩ := layoutOf_blocks bytecode hb logMem rowsN hrl
  have hbv := bytecodeAt_const bv bytecode (point.take L.logBytecode ++ alphas)
  obtain ⟨memory, mF, bF, cl, cvr, wsr, ch, evss, hml, hbus, hxs, hcl0, hcvr0, hrnd, hevl, hevw, hfin, hcls,
    hcv'⟩ := RunsTo.tablesSeg_trace hbv (hrun _ hbv)
  obtain ⟨m0, m1, m2, rfl⟩ := List.length_eq_three.mp hml
  obtain ⟨v0, v1, v2, rfl⟩ := List.length_eq_three.mp hvl
  subst hbus
  set bus := busVal L alphas beta point [v0, v1, v2] [m0, m1, m2] mF bF bv with hbusd
  set τs : ℕ → ℕ := fun t => log2Ceil (rowsN.getD t 0) with hτs
  set n := vtN L with hn
  set chis := ((List.range n).map ch).reverse with hchis
  set cur := ofK (Parameters.gpow c) with hcur
  set rmR := challengeOf (sqCv (obsAll (cvr n) evss.flatten)) with hrmR
  have hdep' : (busLayout [0, logMem, 18] (layoutOf bytecode logMem rowsN).push).depth = point.length :=
    hdep.symm
  obtain ⟨hlmμ, h18μ, hτμ, hfit⟩ := hF bytecode hb logMem rowsN h16 h32 hrl hrows
  rw [hdep'] at hlmμ h18μ hτμ hfit
  have hτ29 : ∀ t < 6, τs t < 29 := fun t ht =>
    hrows _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hheights : L.tableLogHeights = (List.range 6).map τs := by
    show rowsN.map log2Ceil = _
    apply List.ext_getElem (by simp [hrl])
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range, hτs]
    rw [List.getD_eq_getElem _ _ (by simpa [hrl] using h1)]
  have hnf : n = ((List.range 6).map τs).foldl max 0 := by rw [hn, vtN, hheights]
  have hτn : ∀ t < 6, τs t ≤ n := fun t ht => by
    rw [hnf]; exact vt_le_foldl_max _ 0 _ (Or.inl (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
  obtain ⟨tmax, htm, htmx⟩ := exists_eq_foldl_max τs 6 (by norm_num)
  have hnp : n ≤ point.length := by rw [hnf, ← htmx]; exact hτμ tmax htm
  have hchisl : chis.length = n := by simp [hchis]
  have hfs := vt_forms_shaped hb logMem hrl alphas beta point [v0, v1, v2] [m0, m1, m2] mF bF bv
  have hfl : bus.forms.length = 6 := hfs.1
  have hhl : L.tableLogHeights.length = 6 := by show (rowsN.map log2Ceil).length = 6; simp [hrl]
  have hX6 : (vtRows L bus chis).length = 6 := by
    simp only [vtRows, List.length_zip, hfl, hhl, tableWeights_length, tables_length']; rfl
  have hshape : evss.map List.length = vtEvalVars.map List.length := by
    apply List.ext_getElem (by simp [hevl, hX6, vt_evalVars_length])
    intro i h1 h2
    have hi : i < 6 := by simpa [vt_evalVars_length] using h2
    simp only [List.getElem_map]
    rw [hevw i (by simpa using h1) (by rw [hX6]; exact hi)]
    have e := vt_widths_eq i hi
    rw [List.getD_eq_getElem _ _ (by simp [tables_length']; omega),
      List.getD_eq_getElem _ _ (by simp [vt_evalVars_length]; omega)] at e
    simp only [vtRows, List.getElem_zip]
    exact e
  have hflat : evss.flatten.length = 104 := by rw [List.length_flatten, hshape]; rfl
  have hcls' : claims = bus.claims ++ (List.zip (vtRows L bus chis) evss).flatMap (rowClaims chis) ++
      piClaims L pi rmR := by
    rw [hcls, ttVal_snd _ _ _ _ _ _ _ _ hevl, List.nil_append]
  obtain ⟨hTV, hTP⟩ := vt_claimsT hb logMem hrl alphas beta point [v0, v1, v2] [m0, m1, m2] mF bF bv chis hshape
  set pv0 := ofK ((digestScalars pi).1.limb 0) + rmR * (ofK ((digestScalars pi).1.limb 0) +
    ofK ((digestScalars pi).2.limb 0)) with hpv0
  set pv1 := ofK ((digestScalars pi).1.limb 1) + rmR * (ofK ((digestScalars pi).1.limb 1) +
    ofK ((digestScalars pi).2.limb 1)) with hpv1
  have hvals : claims.map (·.value) = [m0, m1, m2, mF, bF] ++ evss.flatten ++ [pv0, pv1, 0] := by
    rw [hcls', List.map_append, List.map_append, hTV]
    congr 1
    simp only [piClaims, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
      multilinearEval_two, List.cons.injEq, and_true]
    have h3 : (digestScalars pi).1.limb 2 = 0 := (isCanonical128_digestScalars pi).1
    have h4 : (digestScalars pi).2.limb 2 = 0 := (isCanonical128_digestScalars pi).2
    refine ⟨by rw [hpv0]; ring, by rw [hpv1]; ring, ?_⟩
    rw [h3, h4]; simp
  have hpts : claims.map (·.point) = [point.take logMem, point.take logMem, point.take logMem,
      point.take logMem, point.take 18] ++ ((List.range 6).flatMap fun t =>
        List.replicate (evCnt.getD t 0) (chis.take (τs t))) ++
      List.replicate 3 (rmR :: List.replicate ((L.placements.getD memory0 default).vars - 1) 0) := by
    rw [hcls', List.map_append, List.map_append, hTP]
    congr 2
    show [point.take L.logMemory, point.take L.logMemory, point.take L.logMemory, point.take L.logMemory,
      point.take L.logBytecode] = _
    rw [hlb]; rfl
  have hxsl : xs.length = 5 + 3 * n + 104 := by
    have hwsl : ((List.range n).flatMap wsr).length = 3 * n := by
      rw [List.length_flatMap]
      have : ∀ r ∈ List.range n, (wsr r).length = 3 := fun r hr =>
        RunsTo.roundPoly4_inv (hrnd r (List.mem_range.mp hr))
      rw [List.map_congr_left this]; simp [Nat.mul_comm]
    rw [hxs]; simp only [List.length_append, hwsl, hflat]; simp; omega
  have hrowsg : rowsN.map (fun n => gen ^ log2Ceil n) = (List.range 6).map fun t => gen ^ τs t := by
    apply List.ext_getElem (by simp [hrl])
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range, hτs]
    rw [List.getD_eq_getElem _ _ (by simpa [hrl] using h1)]
  set cpw := ((claims.map (·.point)).take nPooled).map fun p => gen ^ p.length with hcpw
  have pts_at : ∀ j < 109, (claims.map (·.point))[j]? = some (((claims.map (·.point)).take nPooled).getD j []) := by
    intro j hj
    have hl : (claims.map (·.point)).length = 112 := by simp [hcl]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_take, hl]; show j < min 109 112; omega), List.getElem_take,
      List.getElem?_eq_getElem]
  have pt_lo : ∀ j < 4, (claims.map (·.point))[j]? = some (point.take logMem) := by
    intro j hj; rw [hpts]; interval_cases j <;> rfl
  have pt_4 : (claims.map (·.point))[4]? = some (point.take 18) := by rw [hpts]; rfl
  have pt_T : ∀ t < 6, ∀ jj < evCnt.getD t 0,
      (claims.map (·.point))[5 + (evFirst.getD t 0 + jj)]? = some (chis.take (τs t)) := by
    intro t ht jj hjj
    rw [hpts, List.append_assoc, List.getElem?_append_right (by simp),
      List.getElem?_append_left (by
        have := flatMap_replicate_getElem? (fun t => chis.take (τs t)) (fun t => evCnt.getD t 0) 6 t jj ht hjj
        rw [← evFirst_sum t ht] at this
        simp only [List.length_cons, List.length_nil]
        rw [show 5 + (evFirst.getD t 0 + jj) - 5 = evFirst.getD t 0 + jj by omega]
        exact (List.getElem?_eq_some_iff.mp this).1)]
    simp only [List.length_cons, List.length_nil, show 5 + (evFirst.getD t 0 + jj) - 5 = evFirst.getD t 0 + jj by omega]
    rw [evFirst_sum t ht]
    exact flatMap_replicate_getElem? (fun t => chis.take (τs t)) (fun t => evCnt.getD t 0) 6 t jj ht hjj
  have pt_109 : (claims.map (·.point))[109]? =
      some (rmR :: List.replicate ((L.placements.getD memory0 default).vars - 1) 0) := by
    have hfl : ((List.range 6).flatMap fun t => List.replicate (evCnt.getD t 0) (chis.take (τs t))).length =
        104 := by
      simp only [List.length_flatMap, List.length_replicate]; decide
    rw [hpts, List.append_assoc, List.getElem?_append_right (by simp),
      List.getElem?_append_right (by rw [hfl]; simp), hfl]
    simp
  have evb : ∀ t < 6, evFirst.getD t 0 + evCnt.getD t 0 ≤ 104 := by decide
  have mem : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd cur xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n) ∧
      ReadsAt rd (ofK (Parameters.gpow bk)) (blockKappas (gen ^ logMem) (rowsN.map fun n ↦ gen ^ log2Ceil n)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) (claims.map (·.value)) ∧
      ReadsAt rd (ofK (Parameters.gpow chi)) chis ∧ ReadsAt rd (ofK (Parameters.gpow cplen)) cpw ∧ rm = rmR ∧
      (∀ j < 4, LoadHolds rd (ofK (Parameters.gpow cplen)) j (gen ^ logMem)) ∧
      LoadHolds rd (ofK (Parameters.gpow cplen)) 4 (gen ^ 18) ∧
      (∀ t < 6, ∀ jj < evCnt.getD t 0, LoadHolds rd (ofK (Parameters.gpow cplen)) (5 + (evFirst.getD t 0 + jj))
        (gen ^ log2Ceil (rowsN.getD t 0))) := by
    intro rd hlow hL
    obtain ⟨hxsR, hzR, hexp, hrowsR, hdimsR, hbkR, hfpwR, hpoolR, hT⟩ := hLin rd hlow hL
    obtain ⟨chis', -, -, hchi', -, -, -, -, hpt⟩ := hT
    refine ⟨hxsR, hzR, hexp, hrowsR, hdimsR, hbkR, hfpwR, hpoolR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hb0 := evb tmax htm
      have hc0 := evCnt_pos tmax htm
      have h := (hpt _ _ (pt_T tmax htm 0 (evCnt_pos tmax htm))).2.2.1 (by omega) (by show _ < 109; omega)
      have e1 : τs tmax = n := htmx.trans hnf.symm
      rw [e1, List.take_of_length_le (by rw [hchisl])] at h
      rw [h, hchisl]
      intro j hj
      simp only [List.length_take] at hj
      rw [List.getElem_take]; exact hchi' j (by omega)
    · intro k hk
      simp only [hcpw, List.length_map, List.length_take, List.length_map] at hk
      have hk' : k < 109 := by have : k < min nPooled claims.length := hk; simp [hcl] at this; omega
      have := (hpt k _ (pts_at k hk')).1 (by show k < 109; omega)
      rw [List.getD_eq_getElem _ _ (by simp [hcl]; show k < min 109 112; omega)] at this
      simp only [hcpw, List.getElem_map]
      exact this
    · have h := (hpt 109 _ pt_109).2.2.2 (by show 109 ≤ 109; omega)
      exact (List.cons.inj h).1.symm
    · intro j hj
      have := (hpt j _ (pt_lo j hj)).1 (by show j < 109; omega)
      rwa [List.length_take, min_eq_left hlmμ] at this
    · have := (hpt 4 _ pt_4).1 (by show 4 < 109; omega)
      rwa [List.length_take, min_eq_left h18μ] at this
    · intro t ht jj hjj
      have hb0 := evb t ht
      have := (hpt _ _ (pt_T t ht jj hjj)).1 (by show _ < 109; omega)
      rwa [List.length_take, min_eq_left (by rw [hchisl]; exact hτn t ht)] at this
  set ks := vtKs logMem τs with hks
  set own := vtOwnW ks point logMem n cvr cur cl ch chis with hown
  have hsplit : ∀ rd, ReadsAt rd cur xs → ReadsAt rd cur [m0, m1, m2, mF, bF] ∧
      ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr ++ evss.flatten) := fun rd h => by
    rw [hxs] at h; exact Main.readsAt_append'.mp h
  refine Main.CompleteAtW.bmono (B := fs "verify_tables" + (vtSizes n).sum + vtKidsTot fs) ?_
    (by have := vtSizes_sum_le (n := n) (by omega); simp only [vtTablesBound]; omega)
  refine completeAt_flatW find_verify_tables vt_not_loop κ Lin _ _ core11_body vtPre_flat vtPre_addrs (vtSizes n)
    (fun _ => own) (fun _ => vtOwnW_fit _ _ _ _ _ _ _ _ _)
    (fun fp => vtKids Lin (fp + fs "verify_tables") n point.length logMem ks τs (fun t => rowsN.getD t 0) point
      (ofK (Parameters.gpow z)) (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi)) own)
    (fun k => vtNameBd fs k.f) (fun k θ => vtNameBd (w θ) k.f) (vtKidsTot fs) (fun θ => vtKidsTot (w θ)) ?_
    (fun fp => vtKids_bound fs _ _ _ _ _ _ _ _ _ _ _ _ _ hτ29)
    (fun fp θ => (Main.kidsBoundW_le_kidsBound _ θ (w θ) _ (fun _ => le_rfl) _).trans
      (vtKids_bound (w θ) _ _ _ _ _ _ _ _ _ _ _ _ _ hτ29)) ?_ ?_ ?_
  · intro fp k hk ht
    exact vt_kids_completeW fs cert Θ w κ hκ Lin (fp + fs "verify_tables") n logMem ks τs (fun t => rowsN.getD t 0)
      point chis cvr cur cl ch wsr _ _ _ hpl hlmμ h18μ hnp (fun i hi => (hfit i hi).1)
      (fun t ht => ⟨hτ29 t ht, hτμ t ht, le_two_pow_log2Ceil _⟩) rfl hrnd
      (fun rd hlow hL => by
        obtain ⟨hx, hz, he, -, -, -, -, -, hc, -⟩ := mem rd hlow hL
        exact ⟨hz, fun j hj => (he j hj).2, hc, (Main.readsAt_append'.mp (hsplit rd hx).2).1⟩) k hk ht
  · intro fp k hk _ i hi
    simp only [vtKids, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
      or_false] at hk
    rcases hk with (((⟨t, -, rfl⟩ | (rfl | rfl | rfl | rfl | rfl)) | ⟨j, -, rfl⟩) | (rfl | rfl)) <;>
      first | exact Or.inl hi | exact regionL_append.mp hi
  · intro fp rd hB hL k hk
    simp only [vtKids, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
      or_false] at hk
    rcases hk with (((⟨t, -, rfl⟩ | (rfl | rfl | rfl | rfl | rfl)) | ⟨j, -, rfl⟩) | (rfl | rfl)) <;>
      first | exact hL | exact Main.memL_append.mpr ⟨hL, hB⟩
  · intro fp outs ho rd hlow hB hL
    set b := fp + fs "verify_tables" with hbd
    obtain ⟨hxsR, hzR, hexp, hrowsR, hdimsR, hbkR, hfpwR, hpoolR, hchiR, hcpwR, hrm, hlo, h4, hcT⟩ :=
      mem rd hlow hL
    obtain ⟨hcur5, hxs5⟩ := hsplit rd hxsR
    have rmap : ∀ {p : E} {m k : ℕ} {f : ℕ → E}, ReadsAt rd p ((List.range m).map f) → k < m →
        LoadHolds rd p k (f k) := fun h hk => by
      have := h _ (by simp; omega); simpa using this
    have get : ∀ j < 205, ReadsAt rd (vtPtr b n j) (own.getD j []) := fun j hj =>
      memL_bufL_get (i := j) hB (by rw [vtSizes_length]; exact hj) (by rw [vtOwnW_length]; exact hj)
    obtain ⟨z202, z203, z204⟩ := vtOwnW_zc ks point logMem n cvr cur cl ch chis
    have R0 : ReadsAt rd (vtPtr b n 0) (sortW ks) := get 0 (by norm_num)
    have R1 : ReadsAt rd (vtPtr b n 1) sideW := get 1 (by norm_num)
    have R2 : ReadsAt rd (vtPtr b n 2) (offW ks) := get 2 (by norm_num)
    have R3 : ReadsAt rd (vtPtr b n 3) idxcW := get 3 (by norm_num)
    have R4 : ReadsAt rd (vtPtr b n 4) (bimW point logMem) := get 4 (by norm_num)
    have R11 : ReadsAt rd (vtPtr b n 11) (idxChainW point logMem) := get 11 (by norm_num)
    have R15 : ReadsAt rd (vtPtr b n 15) (idxChainW point 18) := get 15 (by norm_num)
    have R202 := get 202 (by norm_num); rw [z202] at R202
    have R203 := get 203 (by norm_num); rw [z203] at R203
    have R204 := get 204 (by norm_num); rw [z204] at R204
    have hbk : ∀ b' < 102, LoadHolds rd (ofK (Parameters.gpow bk)) b' (gen ^ ks b') :=
      vt_kappas (by rw [← hrowsg]; exact hbkR)
    have hm := selMem_of hB hbk hfit hpl
    obtain ⟨hpA, hpB⟩ := Main.readsAt_append'.mp (by rw [hvals] at hpoolR; exact hpoolR)
    obtain ⟨hpA1, hpA2⟩ := Main.readsAt_append'.mp hpA
    have B := vt_body (rd := rd) hκ hlow (σ := Val.ofArgs [(digestScalars cv).1, (digestScalars cv).2, cur,
        (digestScalars pi).1, (digestScalars pi).2, ofK (Parameters.gpow z), gen ^ point.length,
        ofK (Parameters.gpow dims), ofK (Parameters.gpow rows), ofK (Parameters.gpow bk),
        ofK (Parameters.gpow sq), ofK (Parameters.gpow fpw), beta, ofK (Parameters.gpow pool),
        ofK (Parameters.gpow cplen), ofK (Parameters.gpow chi), v0, v1, v2]) (ptr := vtPtr b n)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hb hal hrl hτ29 hτμ h16 h32 hlmμ h18μ hpl
      (fun r hr => by have := rmap R0 (show r < 102 by omega); simp only [hr, ↓reduceIte] at this; exact this)
      (fun r hr => by
        have := rmap R0 (k := 74 + r) (by omega)
        simp only [show ¬ 74 + r < 37 by omega, show 74 ≤ 74 + r by omega, ↓reduceIte, Nat.add_sub_cancel_left]
          at this
        exact this)
      (fun b' hb' => by simpa [sideW] using rmap R1 hb') hbk (fun j hj => (hexp j hj).2)
      (fun i hi => by have := rmap R2 (show i < 102 by omega); simp only [hi, ↓reduceIte] at this; exact this)
      (fun i hi => by
        have := rmap R2 (k := 74 + i) (by omega)
        simp only [show ¬ 74 + i < 37 by omega, show 74 ≤ 74 + i by omega, ↓reduceIte, Nat.add_sub_cancel_left]
          at this
        exact this)
      hdimsR hrowsR hzR (fun t ht => by simpa [idxcW] using rmap R3 ht) hm hfpwR R11
      (by simpa [bimW] using rmap R4 (k := 1) (by norm_num)) R15
      (by simpa [bimW] using rmap R4 (k := 2) (by norm_num)) hcur5 hpA1 hlo h4 hcl0 hcvr0 hrnd hshape hflat
      hfin hxs5 hchiR R202 R203 R204
      (fun j hj => by
        have := hpA2 j (by rw [hflat]; exact hj)
        rw [loadHolds_mul_gen_pow] at this
        rw [List.getD_eq_getElem _ _ (by rw [hflat]; exact hj)]
        exact this)
      (by have := hpB 0 (by simp); rw [loadHolds_mul_gen_pow, List.length_append, hflat] at this; exact this)
      (by have := hpB 1 (by simp); rw [loadHolds_mul_gen_pow, List.length_append, hflat] at this; exact this)
      (by have := hpB 2 (by simp); rw [loadHolds_mul_gen_pow, List.length_append, hflat] at this; exact this) hcT
    obtain ⟨σ, hext, hpost, hhold⟩ := B
    obtain ⟨hsel, q24, q25, q128, q1817, q1852, q1925, q2029, z36, z39, z55, z54, r71, r72, r75, r76, r77,
      r78⟩ := hpost
    have hvt : ∀ m, 7899 ≤ m → (vtPre.drop 0).take m = vtPre := fun m hm => by
      rw [List.drop_zero]; exact List.take_of_length_le (by rw [vtPre_length]; exact hm)
    rw [hvt _ (by norm_num)] at hhold
    have hVt : VtHolds rd σ := ⟨_, hhold True (fun _ => True) trivial⟩
    have hσlow : ∀ k < 19, σ (.n k) = ([(digestScalars cv).1, (digestScalars cv).2, cur,
        (digestScalars pi).1, (digestScalars pi).2, ofK (Parameters.gpow z), gen ^ point.length,
        ofK (Parameters.gpow dims), ofK (Parameters.gpow rows), ofK (Parameters.gpow bk),
        ofK (Parameters.gpow sq), ofK (Parameters.gpow fpw), beta, ofK (Parameters.gpow pool),
        ofK (Parameters.gpow cplen), ofK (Parameters.gpow chi), v0, v1, v2] : List E).getD k 0 :=
      fun k hk => Ext.apply hext (Or.inl hk)
    have halloc : ∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i := by
      intro i hi
      rcases vt_alloc_cover i hi with h | ⟨h1, h2, h3⟩
      · rcases h with h | h | h | h
        · interval_cases i
          · exact q24
          · exact q25
          · exact q128
          · exact q1817
          · exact q1852
        · subst h; exact q1925
        · subst h; exact q2029
        · interval_cases i
          · exact z36
          · exact z39
          · exact z55
      · have sp := hsel _ h1
        unfold SelPost at sp
        obtain ⟨-, -, s12, s15, s16⟩ := sp
        generalize selK i = k at h2 h3
        generalize selIdx i = j at h1 h2 h3 s12 s15 s16
        subst h3
        rw [vt_alloc_sel j h1 k h2]
        interval_cases k
        · exact s12
        · exact s15
        · exact s16
    have P := hPl κ hκ rd σ Lin b logMem n rowsN point xs chis (claims.map (·.value)) cpw cvr cl ch alphas
      c z lp sq dims rows bk fpw pool cplen chi outs hVt hlow hL hpl h16 h32 hrl hrows hal hnf hnp hlmμ h18μ hxsl
      (by simp [hcl]) hchisl (by simp [hcpw, hcl]) (hσlow 2 (by norm_num)) (hσlow 5 (by norm_num))
      (hσlow 6 (by norm_num)) (hσlow 7 (by norm_num)) (hσlow 8 (by norm_num)) (hσlow 9 (by norm_num))
      (hσlow 10 (by norm_num)) (hσlow 11 (by norm_num)) (hσlow 13 (by norm_num)) (hσlow 14 (by norm_num))
      (hσlow 15 (by norm_num)) halloc z54
      (fun rd' hlow' hL' => by
        obtain ⟨hx, hz, he, hr, hd, hk, hf, hp, hc, hcp, -⟩ := mem rd' hlow' hL'
        exact ⟨hx, hz, he, hr, hd, hk, hf, hp, hc, hcp⟩) hB ho
    refine ⟨σ, ?_, P.1, ?_, P.2.1, P.2.2.1, P.2.2.2.1, P.2.2.2.2⟩
    · rw [core11_params, List.map_map]
      apply List.ext_getElem (by simp)
      intro k h1 h2
      simp only [List.length_map, List.length_range] at h1
      rw [List.getElem_map, List.getElem_range, Function.comp_apply, hσlow k h1]
      interval_cases k <;> rfl
    · rw [core11_body, holdsList_append]
      refine hhold _ _ ?_
      simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
      rw [r71, r72, r75, r76, r77, r78, hrm, hcv', hgz, hxsl, mul_assoc, ← pow_add]
      rfl

/-- **`verify_tables` is complete, placed, by a bounded tree within weights** (`CompleteTablesAtW`). -/
theorem verify_tables_completeAtW (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type} (w : Θ → String → ℕ)
    {κ : ℕ} (hκ : 7 ≤ κ) (bytecode : List K) :
    CompleteTablesAtW fs cert κ bytecode TCtx w (vtTablesBound fs) fun θ => vtTablesBoundW (w θ) :=
  verify_tables_completeAtW_of vt_placed_ok vt_fits fs cert w hκ bytecode

/-- **`verify_tables` is complete, placed, by a bounded tree** (`CompleteTablesAtB`). -/
theorem verify_tables_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 7 ≤ κ)
    (bytecode : List K) : CompleteTablesAtB fs cert κ bytecode TCtx (vtTablesBound fs) :=
  (verify_tables_completeAtW fs cert (Θ := Empty) (fun e => e.elim) hκ bytecode).toB

end
end LeanVM.Guest.B1.VerifySub
