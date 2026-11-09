/-
  LeanVM.Guest.B1.Whir.QueriesBlk

  The template's queries block of a level: the row weights, the cap's root, the queries, the
  intro message.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesOpenW
public import LeanVM.Guest.B1.Whir.Squeezes
public import LeanVM.Protocol.WithHash

/-!
# A level's queries block (G:1598-1620)

`osQueries_sound`: the row weights (`opening_row_weights`, the level's folds), the cap checked
against the level's root (`verify_merkle_cap`, stored in `level_roots`), the queries
(`opening_queries`) at the positions the decodes wrote, then the intro message's two words read at
the cursor: the Spec's openings (each passing `openOne` against the root), the queries' sum its
`enforcedSum`, the intro's coefficients.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The rows as the Spec reads them (V:1811-1813): at level 0 the `K` words reversed, deeper the
`E` words. -/
def specRow (lvl : ℕ) (row : List K) : List E := if lvl = 0 then row.reverse.map ofK else extRow row

/-- A level's row shape: the weights' factors, the row's words and width. -/
structure RowShape (lvl : ℕ) (lv : OsLv) : Prop where
  folds : lv.folds = if lvl = 0 then 6 else 4
  interleave : lv.interleave = if lvl = 0 then 64 else 16

theorem rwLo_six : rwLo 6 = 3 := rfl
theorem rwLo_four : rwLo 4 = 3 := rfl

/-- **The row's dot product with the weights `opening_row_weights` writes** is the Spec's: at
level 0 against the rows reversed, deeper against their `E` words (`rowDot_level0`,
`rowDot_deeper`). -/
theorem rowDot_spec {lvl : ℕ} {lv : OsLv} (hs : RowShape lvl lv) {rs : List E}
    (hrl : rs.length = lv.folds) {rw : E}
    (hlo : ∀ i < 2 ^ rwLo lv.folds, LoadHolds rd rw i ((eqKernel (rs.take (rwLo lv.folds))).getD
      (rwSlot (rwLo lv.folds) (if lvl = 0 then 1 else 0) i) 0))
    (hhi : ∀ i < 2 ^ (lv.folds - rwLo lv.folds), LoadHolds rd rw (2 ^ rwLo lv.folds + i)
      ((eqKernel (rs.drop (rwLo lv.folds))).getD
        (rwSlot (lv.folds - rwLo lv.folds) (if lvl = 0 then 1 else 0) i) 0))
    (row : List K) (w : ℕ → E)
    (hrow : row.length = (if (if lvl = 0 then 1 else 0) = 1 then lv.interleave else 3 * lv.interleave))
    (hwl : ∀ l < rowLo lv.interleave + lv.interleave / rowLo lv.interleave, LoadHolds rd rw l (w l)) :
    rowDot (if lvl = 0 then 1 else 0) lv.interleave row w = dot (specRow lvl row) (eqKernel rs) := by
  obtain ⟨hf, hI⟩ := hs
  by_cases h0 : lvl = 0
  · simp only [h0, ↓reduceIte] at hf hI hrow hlo hhi ⊢
    rw [hf] at hrl hlo hhi
    rw [hI] at hrow hwl ⊢
    simp only [specRow, ↓reduceIte, rwLo_six] at hlo hhi ⊢
    refine rowDot_level0 hrow hrl (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · have := hlo i (by simp; omega)
      exact loadHolds_unique (hwl i (by rw [rowLo_64]; omega)) (by simpa [rwSlot] using this)
    · have := hhi i (by simp; omega)
      exact loadHolds_unique (hwl (8 + i) (by rw [rowLo_64]; omega)) (by simpa [rwSlot] using this)
  · simp only [h0, ↓reduceIte] at hf hI hrow hlo hhi ⊢
    rw [hf] at hrl hlo hhi
    rw [hI] at hrow hwl ⊢
    simp only [specRow, h0, ↓reduceIte, rwLo_four] at hlo hhi ⊢
    refine rowDot_deeper (by simpa using hrow) hrl (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · have := hlo i (by simp; omega)
      exact loadHolds_unique (hwl i (by rw [rowLo_16]; omega)) (by simpa [rwSlot] using this)
    · have := hhi i (by simp; omega)
      exact loadHolds_unique (hwl (8 + i) (by rw [rowLo_16]; omega)) (by simpa [rwSlot] using this)

theorem width_eq (lvl I : ℕ) :
    (if (if lvl = 0 then 1 else 0) = 1 then I else 3 * I) = (if lvl = 0 then I else 3 * I) := by
  by_cases h : lvl = 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, zero_ne_one]

theorem oqCount_q (q : ℕ) (lvl : ℕ) :
    oqCount (q % 2 * (if lvl = 0 then 1 else 0)) (if lvl = 0 then 1 else 0)
      (q / (1 + if lvl = 0 then 1 else 0)) = q := by
  by_cases h : lvl = 0
  · simp only [h, ↓reduceIte, oqCount]; omega
  · simp [h, oqCount]

/-- **A level's queries block**, its openings named: those the queries' witness `W` gives at the
call's words (`lvOpenings`). -/
theorem osQueries_sound {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) {c : OsCfg}
    {lvl : ℕ} {lv : OsLv} {lam lamN : ℕ} {s : OsSt}
    (hok : AllOk C rd σ (osQueries c lvl lv lam lamN s).1) (hmats : MatsOk σ s.mats)
    (hs : RowShape lvl lv) (hcd : 2 ≤ lv.capDepth) (hcd8 : lv.capDepth ≤ 8)
    (hcdd : lv.capDepth ≤ lv.depth)
    (hRW : ∀ args rets, coreProgram.Rel rd ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
      natStr (if lvl = 0 then 1 else 0)) args rets →
        MeaningOpeningRowWeights lv.folds (if lvl = 0 then 1 else 0) rd args rets)
    (hCap : ∀ args rets, coreProgram.Rel rd ("verify_merkle_cap__L" ++ natStr lv.capDepth) args rets →
      MeaningVerifyMerkleCap lv.capDepth rd args rets)
    (W : List E → List E → List QW)
    (hQW : ∀ args rets, C (osQueriesName lvl lv) args rets →
      args.getD 6 0 = gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0)) →
      lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG → lv.capDepth ≤ lv.depth →
      (∀ N, args.getD 6 0 = gen ^ N → N < ordG → QueryWinsOk rd (args.getD 4 0)
        (oqCount (lv.queries % 2 * (if lvl = 0 then 1 else 0)) (if lvl = 0 then 1 else 0) N)
        lv.depth lv.capDepth) →
      MeaningOpeningQueriesW (lv.queries % 2 * (if lvl = 0 then 1 else 0))
        (if lvl = 0 then 1 else 0) lv.interleave lv.depth lv.capDepth rd (W args rets) args rets)
    {lf : List E} (hlf : lf.length = lv.folds)
    (hfch : ∀ j < lv.folds, LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j) (lf.getD j 0))
    {root : Digest} (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestHalves root).1)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestHalves root).2)
    (qs : List ℕ) (hqsl : qs.length = lv.queries) (hqlt : ∀ k < lv.queries, qs.getD k 0 < 2 ^ lv.depth)
    (hpos : ∀ k < lv.queries, ∃ bp, LoadHolds rd (σ (.n osQbp)) (lv.posOff + k) bp ∧
      FrameRun rd bp (qwN lv.depth lv.capDepth) fun i ↦ gen ^ qwVal lv.depth lv.capDepth (qs.getD k 0) i)
    (hlamN : σ (.n lamN) = σ (.n lam) ^ lv.queries)
    (hbo : lv.foldsOff < u128Bound ∧ 4 * lv.capOff < u128Bound ∧ lv.capOff < u128Bound ∧
      lv.posOff < u128Bound ∧ lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG ∧
      lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound) :
    ∃ (ic0 ic2 : E), (lvOpenings rd σ lv W (osQueriesCall c lvl lv lam lamN s)).length = lv.queries ∧
      (∀ k (hk : k < qs.length) (ho : k < (lvOpenings rd σ lv W (osQueriesCall c lvl lv lam lamN s)).length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root lv.depth
          (if lvl = 0 then lv.interleave else 3 * lv.interleave) qs[k]
            (lvOpenings rd σ lv W (osQueriesCall c lvl lv lam lamN s))[k]) = true) ∧
      σ (.n (osQueries c lvl lv lam lamN s).2.2.1) =
        enforcedSum (((lvOpenings rd σ lv W (osQueriesCall c lvl lv lam lamN s)).map (·.leaf)).map
          (specRow lvl)) lf (powers (σ (.n lam)) lv.queries) ∧
      ReadsAt rd (s.cur σ) [ic0, ic2] ∧ σ (.n (osQueries c lvl lv lam lamN s).2.2.2.1) = ic0 ∧
      σ (.n (osQueries c lvl lv lam lamN s).2.2.2.2.2) = ic2 ∧
      σ (.n (osQueries c lvl lv lam lamN s).2.2.2.2.1) =
        σ (.n (osQueries c lvl lv lam lamN s).2.2.1) + ic2 ∧
      MatsOk σ (osQueriesMats c lv s) ∧
      (lvOpenings rd σ lv W (osQueriesCall c lvl lv lam lamN s)).map Opening.leafIndex = qs := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hbo
  set k := s.k
  set P := c.plan
  set m0 := s.mats
  set fp := osMatP P m0 osFch lv.foldsOff (k + 2)
  set m1 := osMatsAfter P m0 osFch lv.foldsOff (k + 2)
  set cp := osMatP P m1 osCaps (4 * lv.capOff) fp.2.2
  set m2 := osMatsAfter P m1 osCaps (4 * lv.capOff) fp.2.2
  set flp := osMatP P m2 osFlags lv.capOff cp.2.2
  set m3 := osMatsAfter P m2 osFlags lv.capOff cp.2.2
  set r := flp.2.2
  set cp2 := osMatP P m3 osCaps (4 * lv.capOff) (r + 2)
  set flp2 := osMatP P m3 osFlags lv.capOff cp2.2.2
  set bp := osMatP P m3 osQbp lv.posOff flp2.2.2
  set g := bp.2.2
  have hst : (osQueries c lvl lv lam lamN s).1 = osHeap c.maxIl k ++ fp.1 ++
      [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
        natStr (if lvl = 0 then 1 else 0)) [.n fp.2.1, .n (k + 1)] []] ++
      cp.1 ++ flp.1 ++
      [.call ("verify_merkle_cap__L" ++ natStr lv.capDepth) [.n cp.2.1, .n flp.2.1] [.n r, .n (r + 1)],
        .atom (.load (.n r) (.n osRoots) (2 * lvl)),
        .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1))] ++
      cp2.1 ++ flp2.1 ++ bp.1 ++
      [.atom (.const (.n g) (gw (lv.queries / (1 + if lvl = 0 then 1 else 0)))),
        .call (osQueriesName lvl lv) [.n cp2.2.1, .n flp2.2.1, .n lam, .n lamN, .n bp.2.1,
          .n (k + 1), .n g] [.n (g + 1)],
        .atom (.load (.n (g + 2)) (.n s.cb) s.co), .atom (.load (.n (g + 3)) (.n s.cb) (s.co + 1)),
        .atom (.add (.n (g + 4)) (.n (g + 1)) (.n (g + 3)))] := rfl
  have hr : (osQueries c lvl lv lam lamN s).2 = (g + 5, g + 1, g + 2, g + 4, g + 3) := rfl
  have hcall : osQueriesCall c lvl lv lam lamN s = (osQueriesName lvl lv, [.n cp2.2.1, .n flp2.2.1,
      .n lam, .n lamN, .n bp.2.1, .n (k + 1), .n g], [.n (g + 1)]) := rfl
  rw [hst] at hok
  rw [hr, hcall]
  simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
    List.map_nil, and_assoc] at hok
  obtain ⟨-, hfp, hrw, hcp, hflp, hcap, hs0, hs1, hcp2, hflp2, hbp, hcg, hq, hi0, hi2, hi1⟩ := hok
  have k1 := osMatsAfter_ok hmats hb1 hfp
  have k2 := osMatsAfter_ok k1 hb2 hcp
  have k3 := osMatsAfter_ok k2 hb3 hflp
  have efp := osMatP_val hmats hb1 hfp
  have ecp := osMatP_val k1 hb2 hcp
  have eflp := osMatP_val k2 hb3 hflp
  have ecp2 := osMatP_val k3 hb2 hcp2
  have eflp2 := osMatP_val k3 hb3 hflp2
  have ebp := osMatP_val k3 hb4 hbp
  have hmq : MatsOk σ (osQueriesMats c lv s) := osMatsAfter_ok k3 hb4 hbp
  set N0 := lv.queries / (1 + if lvl = 0 then 1 else 0)
  have eg : σ (.n g) = gen ^ N0 := by rw [hcg, gw_eq hb6]
  have er0 := loadHolds_unique hs0 hr0
  have er1 := loadHolds_unique hs1 hr1
  have hroot : (σ (.n r), σ (.n (r + 1))) = digestHalves root := by rw [er0, er1]
  obtain ⟨-, rs, hrsl, hrs, hlo, hhi⟩ := hRW _ _ (hle _ _ _ hrw)
  have hrsf : rs = lf := by
    apply List.ext_getElem (by rw [hrsl, hlf])
    intro j h1 h2
    have a := hrs j h1
    rw [efp, loadHolds_mul_gen_pow] at a
    have b := hfch j (by rw [← hrsl]; exact h1)
    rw [List.getD_eq_getElem _ _ h2] at b
    exact loadHolds_unique a b
  subst hrsf
  have hbits : ∀ k' < lv.queries, ∃ bpv, LoadHolds rd (σ (.n bp.2.1)) k' bpv ∧
      FrameRun rd bpv (qwN lv.depth lv.capDepth)
        fun i ↦ gen ^ qwVal lv.depth lv.capDepth (qs.getD k' 0) i := by
    intro k' hk'
    obtain ⟨bpv, h1, h2⟩ := hpos k' hk'
    exact ⟨bpv, by rw [ebp, loadHolds_mul_gen_pow]; exact h1, h2⟩
  have hqb : ∀ N, σ (.n g) = gen ^ N → N < ordG → QueryWinsOk rd (σ (.n bp.2.1))
      (oqCount (lv.queries % 2 * (if lvl = 0 then 1 else 0)) (if lvl = 0 then 1 else 0) N)
      lv.depth lv.capDepth := by
    intro N hN hNo k' hk' bpv hbpv
    have hNN : N = N0 := gen_pow_inj hNo hb5 (hN.symm.trans eg)
    rw [hNN, oqCount_q] at hk'
    obtain ⟨bpv', h1, h2⟩ := hbits k' hk'
    rw [loadHolds_unique hbpv h1]
    exact ⟨_, hqlt k' hk', h2⟩
  have hm := hQW _ _ hq eg hb5 hcdd (fun N hN hNo ↦ hqb N hN hNo)
  simp only [lvOpenings, List.map_cons, List.map_nil, List.headD_cons]
  have hm' := meaningW_args hm (A' := [σ (.n cp.2.1), σ (.n flp.2.1), σ (.n lam), σ (.n lamN),
    σ (.n bp.2.1), σ (.n (k + 1)), σ (.n g)]) (by rw [ecp2, eflp2, ← ecp, ← eflp])
  obtain ⟨hol, hop, hsum, hidx⟩ := queries_open_w (q := lv.queries) (N0 := N0) (cap0 := σ (.n cp2.2.1))
    (by rw [ecp2, ← ecp]) hm'
    (hCap _ _ (hle _ _ _ hcap)) hroot hcd hcd8 hcdd eg (by omega) (oqCount_q _ _)
    (by split_ifs <;> simp; omega) (by by_cases h : lvl = 0 <;> simp [h]) qs hqsl hqlt hbits hlamN
    (width := if lvl = 0 then lv.interleave else 3 * lv.interleave) (width_eq lvl lv.interleave)
    (specRow lvl) rs (fun row w hrow hw ↦ rowDot_spec hs hrsl hlo hhi row w
      (hrow.trans (width_eq lvl lv.interleave).symm) hw)
  refine ⟨σ (.n (g + 2)), σ (.n (g + 3)), hol, hop, hsum, ?_, rfl, rfl, hi1, hmq, hidx⟩
  intro i hi
  rcases i with _ | _ | i
  · exact load_cur (by simpa using hi0)
  · exact load_cur hi2
  · simp at hi

end
end LeanVM.Guest.B1.Whir
