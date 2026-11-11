/-
  LeanVM.Guest.B1.Whir.QueriesBlk

  The template's queries block of a level: the row weights, the cap's root, the queries, the
  intro message.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesOpenW
public import LeanVM.Guest.B1.Whir.Squeezes
public import LeanVM.Guest.B1.Whir.LvQW
public import LeanVM.Protocol.WithHash

/-!
# A level's queries block

`osQueries_sound`: the row weights (`opening_row_weights`, the level's folds), then the dispatch
on the rate into `level_queries` (`level_queries_frame`: the cap hinted and checked by
`verify_merkle_cap` to the root it returns, which the body checks against `level_roots`, `λ^q`,
and the queries (`opening_queries`) at the positions the decodes wrote), then the intro message's
two words read at the cursor: the Spec's openings (each passing `openOne` against the root), the
queries' sum its `enforcedSum`, the intro's coefficients.
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

/-! ## `level_queries` -/

/-- `level_queries`' body before its `ret`. -/
def lqA (q base il leaf d cd : ℕ) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits q) 0 9
  let k := 9 + osPowLen q
  let iters := if base = 1 then q / 2 else q
  osHeap (4 * 2 ^ cd) 3 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n 4) 0 (4 * 2 ^ cd))))] ++
    osHeap (2 ^ cd) 5 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 6) 0 (2 ^ cd)))),
      .call ("verify_merkle_cap__L" ++ natStr cd) [.n 4, .n 6] [.n 7, .n 8]] ++
    pw.1 ++
    [.atom (.const (.n k) (gw iters)),
      .call (oqName q base il leaf d cd) [.n 4, .n 6, .n 0, .n pw.2, .n 1, .n 2, .n k] [.n (k + 1)],
      .atom (.copy (.n (k + 2)) (.n 7)), .atom (.copy (.n (k + 3)) (.n 8)),
      .atom (.copy (.n (k + 4)) (.n (k + 1))), .atom (.copy (.n (k + 5)) (.n pw.2))]

theorem lqBody_split (q base il leaf d cd : ℕ) : lqBody q base il leaf d cd =
    lqA q base il leaf d cd ++ [.ret [.n (9 + osPowLen q + 2), .n (9 + osPowLen q + 3),
      .n (9 + osPowLen q + 4), .n (9 + osPowLen q + 5)]] := by
  simp only [lqBody, lqA, List.append_assoc, List.cons_append, List.nil_append]

theorem lqA_flat (q base il leaf d cd : ℕ) : (lqA q base il leaf d cd).all Stmt.flat = true := by
  simp [lqA, osHeap, osPowSteps_allFlat, Stmt.flat]

/-- **`level_queries`' frame**: from its body at the frame `σ'` on the arguments `lam, win_ptrs,
row_eq_weights`, the cap checked to the root it returns, `lam^q`, and the `opening_queries` call
(`lqCall`) on the cap, its flags, `lam`, `lam^q`, the pointers, the weights and `g^iters`,
whose sum it returns. -/
theorem level_queries_frame {C : CallRel} {q base il leaf d cd : ℕ} {σ' : Val} {args rets : List E}
    (hp : (osParams 3).map σ' = args)
    (hh : Stmt.HoldsList C rd σ' (lqBody q base il leaf d cd) False (fun rs ↦ rs = rets))
    (hdig : digitsVal (osPowDigits q) 1 = q)
    (hit : (if base = 1 then q / 2 else q) < u128Bound) :
    args = [σ' (.n 0), σ' (.n 1), σ' (.n 2)] ∧
    rets = [σ' (.n 7), σ' (.n 8), σ' (.n (9 + osPowLen q + 1)), σ' (.n 0) ^ q] ∧
    C ("verify_merkle_cap__L" ++ natStr cd) [σ' (.n 4), σ' (.n 6)] [σ' (.n 7), σ' (.n 8)] ∧
    C (oqName q base il leaf d cd)
      [σ' (.n 4), σ' (.n 6), σ' (.n 0), σ' (.n (osPowSteps 0 (osPowDigits q) 0 9).2), σ' (.n 1),
        σ' (.n 2), σ' (.n (9 + osPowLen q))] [σ' (.n (9 + osPowLen q + 1))] ∧
    σ' (.n (osPowSteps 0 (osPowDigits q) 0 9).2) = σ' (.n 0) ^ q ∧
    σ' (.n (9 + osPowLen q)) = gen ^ (if base = 1 then q / 2 else q) := by
  rw [lqBody_split, holdsList_flat_ret _ (lqA_flat _ _ _ _ _ _)] at hh
  obtain ⟨hok, hret⟩ := hh
  simp only [lqA, osHeap, allOk_append, allOk_cons, allOk_nil, and_true, true_and, StmtOk,
    Atom.Holds, and_assoc] at hok
  obtain ⟨-, -, hcap, hpw, hk, hoq, e2, e3, e4, e5⟩ := hok
  have hpv := osPowSteps_val (C := C) (rd := rd) (σ := σ') 0 (osPowDigits q) 0 9 1 (by rw [pow_one])
    hpw
  rw [hdig] at hpv
  simp only [List.map_cons, List.map_nil] at hcap hoq hret
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append] at hp
  refine ⟨hp.symm, ?_, hcap, hoq, hpv, by rw [hk, gw_eq hit]⟩
  rw [← hret, e2, e3, e4, e5, hpv]

theorem iters_eq (q lvl : ℕ) :
    (if (if lvl = 0 then 1 else 0) = 1 then q / 2 else q) = q / (1 + if lvl = 0 then 1 else 0) := by
  by_cases h : lvl = 0 <;> simp [h]

/-- **A level's queries block**, its openings named: those the queries' witness `W` gives at the
`opening_queries` call in the frame `V` gives the `level_queries` call the dispatch on the rate
makes (`lvOpenings` at `lqCall`). -/
theorem osQueries_sound {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) {V : FrameMap}
    (hU : UnfoldsV rd C V) {c : OsCfg} {lvl : ℕ} {lv : OsLv} {lam : ℕ} {s : OsSt}
    (hok : AllOk C rd σ (osQueries c lvl lv lam s).1) (hmats : MatsOk σ s.mats)
    (hrate : LvRate σ c lvl lv)
    (hfn : FnIs (osQueriesName lvl lv) (osParams 3)
      (lqBody lv.queries (if lvl = 0 then 1 else 0) lv.interleave lv.leafCells lv.depth lv.capDepth))
    (hdig : digitsVal (osPowDigits lv.queries) 1 = lv.queries)
    (hs : RowShape lvl lv) (hcd : 2 ≤ lv.capDepth) (hcd8 : lv.capDepth ≤ 8)
    (hcdd : lv.capDepth ≤ lv.depth)
    (hRW : ∀ args rets, coreProgram.Rel rd ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
      natStr (if lvl = 0 then 1 else 0)) args rets →
        MeaningOpeningRowWeights lv.folds (if lvl = 0 then 1 else 0) rd args rets)
    (hCap : ∀ args rets, coreProgram.Rel rd ("verify_merkle_cap__L" ++ natStr lv.capDepth) args rets →
      MeaningVerifyMerkleCap lv.capDepth rd args rets)
    (W : List E → List E → List QW) (hQW : LvQW rd C lvl lv W)
    {lf : List E} (hlf : lf.length = lv.folds)
    (hfch : ∀ j < lv.folds, LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j) (lf.getD j 0))
    {root : Digest} (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestHalves root).1)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestHalves root).2)
    (qs : List ℕ) (hqsl : qs.length = lv.queries) (hqlt : ∀ k < lv.queries, qs.getD k 0 < 2 ^ lv.depth)
    (hpos : ∀ k < lv.queries, ∃ bp, LoadHolds rd (σ (.n osQbp)) (lv.posOff + k) bp ∧
      FrameRun rd bp (qwN lv.depth lv.capDepth) fun i ↦ gen ^ qwVal lv.depth lv.capDepth (qs.getD k 0) i)
    (hbo : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound ∧
      lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG ∧
      lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound) :
    let os := lvOpenings rd (V (osQueriesName lvl lv) ((osQueriesDisp c lvl lv lam s).2.1.map σ)
      ((osQueriesDisp c lvl lv lam s).2.2.map σ)) lv W (lqCall lvl lv)
    ∃ (ic0 ic2 : E), os.length = lv.queries ∧
      (∀ k (hk : k < qs.length) (ho : k < os.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root lv.depth
          (if lvl = 0 then lv.interleave else 3 * lv.interleave) qs[k] os[k]) = true) ∧
      σ (.n (osQueries c lvl lv lam s).2.2.1) =
        enforcedSum ((os.map (·.leaf)).map (specRow lvl)) lf (powers (σ (.n lam)) lv.queries) ∧
      σ (.n (osQueries c lvl lv lam s).2.2.2.1) = σ (.n lam) ^ lv.queries ∧
      ReadsAt rd (s.cur σ) [ic0, ic2] ∧ σ (.n (osQueries c lvl lv lam s).2.2.2.2.1) = ic0 ∧
      σ (.n (osQueries c lvl lv lam s).2.2.2.2.2.2) = ic2 ∧
      σ (.n (osQueries c lvl lv lam s).2.2.2.2.2.1) =
        σ (.n (osQueries c lvl lv lam s).2.2.1) + ic2 ∧
      MatsOk σ (osQueriesMats c lv s) ∧ os.map Opening.leafIndex = qs := by
  intro os
  obtain ⟨hb1, hb4, hb5, hb6⟩ := hbo
  set k := s.k
  set P := c.plan
  set m0 := s.mats
  set fp := osMatP P m0 osFch lv.foldsOff (k + 2)
  set m1 := osMatsAfter P m0 osFch lv.foldsOff (k + 2)
  set bp := osMatP P m1 osQbp lv.posOff fp.2.2
  set r := bp.2.2
  have hst : (osQueries c lvl lv lam s).1 = osHeap c.maxIl k ++ fp.1 ++
      [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
        natStr (if lvl = 0 then 1 else 0)) [.n fp.2.1, .n (k + 1)] []] ++
      bp.1 ++
      [.dispatch (.n osRate) ((c.lvAt lvl).map (osQueriesName lvl)) [.n lam, .n bp.2.1, .n (k + 1)]
          (osRun r 4),
        .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1)),
        .atom (.load (.n (r + 4)) (.n s.cb) s.co), .atom (.load (.n (r + 5)) (.n s.cb) (s.co + 1)),
        .atom (.add (.n (r + 6)) (.n (r + 2)) (.n (r + 5)))] := rfl
  have hr : (osQueries c lvl lv lam s).2 = (r + 7, r + 2, r + 3, r + 4, r + 6, r + 5) := rfl
  have hdisp : osQueriesDisp c lvl lv lam s =
      (osQueriesName lvl lv, [.n lam, .n bp.2.1, .n (k + 1)], osRun r 4) := rfl
  rw [hst] at hok
  rw [hr]
  simp only [os, hdisp] at *
  rw [allOk_append, allOk_cons] at hok
  obtain ⟨hpre, hD, hok⟩ := hok
  simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
    List.map_nil] at hpre hok
  obtain ⟨⟨⟨-, hfp⟩, hrw⟩, hbp⟩ := hpre
  obtain ⟨hs0, hs1, hi0, hi2, hi1⟩ := hok
  have k1 := osMatsAfter_ok hmats hb1 hfp
  have efp := osMatP_val hmats hb1 hfp
  have ebp := osMatP_val k1 hb4 hbp
  have hmq : MatsOk σ (osQueriesMats c lv s) := osMatsAfter_ok k1 hb4 hbp
  -- the dispatch into `level_queries`
  have hcall := dispatch_rate hrate (osQueriesName lvl) hD
  simp only [osRun, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Nat.add_zero] at hcall ⊢
  obtain ⟨fn, hf, hpar, hbody⟩ := hU _ _ _ hcall
  obtain ⟨fn', hf', hps', hb'⟩ := hfn
  rw [hf] at hf'
  cases hf'
  rw [hps'] at hpar
  rw [hb'] at hbody
  set σ' := V (osQueriesName lvl lv) [σ (.n lam), σ (.n bp.2.1), σ (.n (k + 1))]
    [σ (.n r), σ (.n (r + 1)), σ (.n (r + 2)), σ (.n (r + 3))]
  set q := lv.queries
  set base := if lvl = 0 then 1 else 0
  set N0 := q / (1 + base)
  obtain ⟨hargs, hrets, hcapc, hoq, hpw, hkv⟩ := level_queries_frame hpar hbody hdig
    (by rw [iters_eq]; exact hb6)
  simp only [List.cons.injEq, and_true] at hargs hrets
  obtain ⟨a0, a1, a2⟩ := hargs
  obtain ⟨r0, r1, r2, r3⟩ := hrets
  rw [iters_eq] at hkv
  have er0 := loadHolds_unique hs0 hr0
  have er1 := loadHolds_unique hs1 hr1
  have hroot : (σ' (.n 7), σ' (.n 8)) = digestHalves root := by rw [← r0, ← r1, er0, er1]
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
  have hbits : ∀ k' < q, ∃ bpv, LoadHolds rd (σ' (.n 1)) k' bpv ∧
      FrameRun rd bpv (qwN lv.depth lv.capDepth)
        fun i ↦ gen ^ qwVal lv.depth lv.capDepth (qs.getD k' 0) i := by
    intro k' hk'
    obtain ⟨bpv, h1, h2⟩ := hpos k' hk'
    exact ⟨bpv, by rw [← a1, ebp, loadHolds_mul_gen_pow]; exact h1, h2⟩
  have hqb : ∀ N, gen ^ N0 = gen ^ N → N < ordG → QueryWinsOk rd (σ' (.n 1))
      (oqCount (q % 2 * base) base N) lv.depth lv.capDepth := by
    intro N hN hNo k' hk' bpv hbpv
    have hNN : N = N0 := gen_pow_inj hNo hb5 hN.symm
    rw [hNN, oqCount_q] at hk'
    obtain ⟨bpv', h1, h2⟩ := hbits k' hk'
    rw [loadHolds_unique hbpv h1]
    exact ⟨_, hqlt k' hk', h2⟩
  have hm := hQW _ _ hoq hkv hb5 hcdd (fun N hN hNo ↦ hqb N (hkv.symm.trans hN) hNo)
  have hlc : lqCall lvl lv = (oqNameOf lvl lv, [.n 4, .n 6, .n 0,
      .n (osPowSteps 0 (osPowDigits q) 0 9).2, .n 1, .n 2, .n (9 + osPowLen q)],
      [.n (9 + osPowLen q + 1)]) := rfl
  obtain ⟨hol, hop, hsum, hidx⟩ := queries_open_w (q := q) (N0 := N0) (cap0 := σ' (.n 4))
    rfl hm (hCap _ _ (hle _ _ _ hcapc)) hroot hcd hcd8 hcdd hkv hb5 (oqCount_q _ _)
    (by split_ifs <;> simp; omega) (by by_cases h : lvl = 0 <;> simp [h]) qs hqsl hqlt hbits
    hpw
    (width := if lvl = 0 then lv.interleave else 3 * lv.interleave) (width_eq lvl lv.interleave)
    (specRow lvl) rs (fun row w hrow hw ↦ rowDot_spec hs hrsl hlo hhi row w
      (hrow.trans (width_eq lvl lv.interleave).symm) (by rw [a2]; exact hw))
  refine ⟨σ (.n (r + 4)), σ (.n (r + 5)), ?_, ?_, ?_, ?_, ?_, rfl, rfl, hi1, hmq, ?_⟩
  · simp only [lvOpenings, hlc]; exact hol
  · simp only [lvOpenings, hlc]; exact hop
  · simp only [lvOpenings, hlc]
    rw [show powers (σ (.n lam)) q = powers (σ' (.n 0)) q by rw [a0]]
    exact r2.trans hsum
  · rw [r3, ← a0]
  · intro i hi
    rcases i with _ | _ | i
    · exact load_cur (by simpa using hi0)
    · exact load_cur hi2
    · simp at hi
  · simp only [lvOpenings, hlc]; exact hidx

end
end LeanVM.Guest.B1.Whir
