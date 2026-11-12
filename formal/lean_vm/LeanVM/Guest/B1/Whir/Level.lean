/-
  LeanVM.Guest.B1.Whir.Level

  A non-final level of `open_stacked` runs the Spec's: its fold rounds, then `levelNext`.
-/

module

public import LeanVM.Guest.B1.Whir.LevelRun
public import LeanVM.Guest.B1.Whir.LevelB
public import LeanVM.Guest.B1.Opening.QueriesAllW
public import LeanVM.Guest.B1.Whir.LpSound
public import LeanVM.Guest.B1.Whir.LqSound

/-!
# A non-final level (G:1556-1694)

`LvIn` is the guest's state at a level's start against the Spec's: the sponge it carries, the
claim the guest's plus the deficit `recsDeficit` of the levels so far (each level's high-part
share of its queries, `λ² Σ_k λ^k novelEval(high, Ŵ(x_k))·Ŵ_μ(x_k)`, scaled by the `α`s drawn
after it), the `α`s stored in `fold_challenges`, the commitments so far and the level's root in
`level_roots`, the glued claims those of the records (`recGlued`).

`osLevelMid_sound`: a non-final level's template runs `foldRounds` then `levelNext` from `LvIn`,
reading `lvWords` words at the cursor and one phase of openings, the witness's (`osLevelW` at
the level's `level_queries` call, `osQCallOf`), and leaves the next level's `LvIn` with the
level's record appended, whose values the finish rereads (`RecStored`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The level's `level_queries` call -/

theorem lqIters_base (q lvl : ℕ) : lqIters q (lvBase lvl) = q / (1 + lvBase lvl) := by
  by_cases h : lvl = 0 <;> simp [lqIters, lvBase, h]

/-- **The level's queries, unfolded**: the `level_queries` call's frame `Vq` holds the cap and its
flags (cells `7`, `9`), checked to the root it returns, which is that in `level_roots`, and its
`opening_queries` call, whose return is the batch; `λ^n` is `λ`'s power. -/
theorem osLq_sound {V : FrameMap} (hU : UnfoldsV rd C V) {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    {st : OsSt} (hr : LvRate σ c lvl lv)
    (hlq : FnIs (osQueriesName c lvl lv) (osParams 6) (osLqBody c lvl lv))
    (hit : lv.queries / (1 + lvBase lvl) < u128Bound)
    (hpwQ : digitsVal (osPowDigits lv.queries) 1 = lv.queries)
    (hm : MatsOk σ st.mats) (hf : 2 * lv.foldsOff < u128Bound)
    (hh : lvl * hsStride < u128Bound) (hp : lv.posOff < u128Bound)
    (hok : AllOk C rd σ (osQueries c lvl lv st).1) :
    let A := osQArgs σ c lvl lv st
    let Vq := V (osQueriesName c lvl lv) A ((osQCallOf c lvl lv st).2.map σ)
    (osQCallOf c lvl lv st).1.map σ = A ∧
      C ("verify_merkle_cap__L" ++ natStr lv.capDepth) [Vq (.n 7), Vq (.n 9)]
        [Vq (.n 10), Vq (.n 11)] ∧
      C (osOqName c lvl lv) (osOqArgs Vq A (lv.queries / (1 + lvBase lvl))) [Vq (.n 13)] ∧
      σ (.n (osQueries c lvl lv st).2.batched) = Vq (.n 13) ∧
      σ (.n (osQueries c lvl lv st).2.lamPow) = A.getD 0 0 ^ lv.queries ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl) (Vq (.n 10)) ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (Vq (.n 11)) ∧
      MatsOk σ (osQueries c lvl lv st).2.mats ∧
      (osQueries c lvl lv st).2 = { st with
        k := (osQueries c lvl lv st).2.k
        mats := (osQueries c lvl lv st).2.mats
        batched := (osQueries c lvl lv st).2.batched
        lamPow := (osQueries c lvl lv st).2.lamPow } := by
  intro A Vq
  obtain ⟨ha, hC, ⟨r0, r1, hR, l0, l1⟩, hm', hst⟩ := osQueries_sound hr hm hf hh hp hok
  simp only [osLqBody] at hlq
  have hU' := lq_unfold hU hlq (by rw [lqIters_base]; exact hit) hpwQ hC
  obtain ⟨-, hcap, hoq, hret⟩ := hU'
  rw [lqIters_base] at hoq
  have hret' := hR.symm.trans hret
  simp only [List.cons.injEq, and_true] at hret'
  obtain ⟨e0, e1, e2, e3⟩ := hret'
  rw [e0] at l0
  rw [e1] at l1
  exact ⟨ha, hcap, hoq, e2, e3, l0, l1, hm', hst⟩

/-! ## The positions -/

/-- **The decoded positions**: query `k` of the squeezes' samples, its word in `query_positions`
and its windows behind `query_win_ptrs`. -/
theorem sq_positions {d cd po S Q : ℕ} {w : ℕ → E} {qpos qbp tabs : E} (hP : 1 ≤ 128 / d)
    (hS : S = sqCount (128 / d) Q)
    (hdec : ∀ j < S, MeaningDecodeQueryWindows d cd rd
      [w j, qpos * gen ^ (po + j * (128 / d)), qbp * gen ^ (po + j * (128 / d)), tabs] []) :
    ∀ k < Q, LoadHolds rd (qpos * gen ^ po) k (eOfNat ((sqPositions d w Q).getD k 0)) ∧
      (sqPositions d w Q).getD k 0 < 2 ^ d ∧
      ∃ bp, LoadHolds rd (qbp * gen ^ po) k bp ∧
        FrameRun rd bp (qwN d cd) fun i ↦ gen ^ qwVal d cd ((sqPositions d w Q).getD k 0) i := by
  intro k hk
  set P := 128 / d with hPd
  have hj : k / P < S := by
    rw [hS, sqCount]
    have h1 : (k + P) / P = k / P + 1 := Nat.add_div_right k (by omega)
    have h2 : (k + P) / P ≤ (Q + P - 1) / P := Nat.div_le_div_right (by omega)
    omega
  have hD := hdec (k / P) hj
  simp only [MeaningDecodeQueryWindows] at hD
  obtain ⟨-, hD⟩ := hD
  obtain ⟨hpos, bp, hbp, hfr⟩ := hD (k % P) (Nat.mod_lt _ (by omega))
  have hg : (sqPositions d w Q).getD k 0 = qwPosOf d (w (k / P)) (k % P) := by
    rw [List.getD_eq_getElem _ _ (by simpa [sqPositions] using hk)]
    simp [sqPositions, hPd]
  have hk' : po + k / P * P + k % P = po + k := by
    rw [Nat.add_assoc, Nat.div_add_mod']
  rw [hg]
  refine ⟨?_, Nat.mod_lt _ (by positivity), bp, ?_, hfr⟩
  · rw [loadHolds_mul_gen_pow] at hpos ⊢
    rwa [hk'] at hpos
  · rw [loadHolds_mul_gen_pow] at hbp ⊢
    rwa [hk'] at hbp

/-! ## Records and the deficit -/

/-- What a non-final level glues, for the finish: its `λ`, the folds before its claims, its
message log, its out-of-domain point, its positions and its high part. -/
structure OsRec where
  lam : E
  F : ℕ
  mu : ℕ
  z0 : List E
  qs : List ℕ
  high : List E

/-- The claims a non-final level glues (`glueLevel`). -/
def recGlued (r : OsRec) : List GluedClaim :=
  [⟨r.lam, r.F, fun x ↦ eqEval r.z0 x⟩,
    ⟨r.lam * r.lam, r.F, inducedWeight r.mu r.qs (powers r.lam r.qs.length)⟩]

/-- A query's share of the high part: `novelEval(high, Ŵ(x))·Ŵ_μ(x)`. -/
def highTerm (mu : ℕ) (high : List E) (q : ℕ) : E :=
  novelEval high (subspaceAt mu (K.ofBits q)) * ofK ((subspaceAt mu (K.ofBits q)).getD mu 0)

/-- The high part's share of a level's batch, `Σ_k λ^k highTerm(q_k)`. -/
def recH (r : OsRec) : E :=
  ∑ k ∈ Finset.range r.qs.length, r.lam ^ k * highTerm r.mu r.high (r.qs.getD k 0)

/-- **The deficit**: the Spec's claim less the guest's, each level's `λ²·recH` times the `α`s
drawn after it. -/
def recsDeficit (recs : List OsRec) (alphas : List E) : E :=
  (recs.map fun r ↦ r.lam ^ 2 * recH r * (alphas.drop r.F).prod).sum

theorem recsDeficit_append_alphas (recs : List OsRec) (alphas gs : List E)
    (h : ∀ r ∈ recs, r.F ≤ alphas.length) :
    recsDeficit recs (alphas ++ gs) = gs.prod * recsDeficit recs alphas := by
  unfold recsDeficit
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun r hr ↦ ?_)
  rw [List.drop_append_of_le_length (h r hr), List.prod_append]
  ring

theorem recsDeficit_snoc (recs : List OsRec) (r : OsRec) (alphas : List E)
    (h : r.F = alphas.length) :
    recsDeficit (recs ++ [r]) alphas = recsDeficit recs alphas + r.lam ^ 2 * recH r := by
  simp [recsDeficit, h]

/-! ## The batch -/

theorem sumE_eq_sum' (l : List E) : sumE l = l.sum := by
  unfold sumE
  rw [List.sum_eq_foldl]

theorem length_powersFrom (acc lam : E) : ∀ t, (powersFrom acc lam t).length = t
  | 0 => rfl
  | t + 1 => by simp [powersFrom, length_powersFrom _ _ t]

theorem getD_powersFrom (acc lam : E) : ∀ (t k : ℕ), k < t →
    (powersFrom acc lam t).getD k 0 = acc * lam ^ k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | t + 1, 0, _ => by simp [powersFrom]
  | t + 1, k + 1, h => by
    rw [powersFrom, List.getD_cons_succ, getD_powersFrom _ _ t k (by omega), pow_succ]
    ring

/-- A batch with `powers λ` as `Σ_k λ^k f(k)`. -/
theorem sumE_zipWith_powers {α : Type} [Inhabited α] (f : α → E) (lam : E) :
    ∀ (l : List α) (acc : E),
      sumE (List.zipWith (fun a w ↦ w * f a) l (powersFrom acc lam l.length)) =
        ∑ k ∈ Finset.range l.length, acc * lam ^ k * f (l.getD k default)
  | [], _ => by simp [sumE]
  | a :: l, acc => by
    have ih := sumE_zipWith_powers f lam l (acc * lam)
    have e : ∀ k ∈ Finset.range l.length, acc * lam * lam ^ k * f (l.getD k default) =
        acc * lam ^ (k + 1) * f ((a :: l).getD (k + 1) default) := fun k _ ↦ by
      rw [List.getD_cons_succ, pow_succ]; ring
    rw [sumE_eq_sum'] at ih ⊢
    rw [List.length_cons, show powersFrom acc lam (l.length + 1) =
        acc :: powersFrom (acc * lam) lam l.length from rfl, List.zipWith_cons_cons, List.sum_cons, ih,
      Finset.sum_congr rfl e, Finset.sum_range_succ' _ l.length, List.getD_cons_zero, pow_zero, mul_one,
      add_comm]

/-- **The Spec's batch splits**: the folds' share and the high part's. -/
theorem levelBatched_eq (mu index : ℕ) (rounds : List FoldRound) (high : List E) (qs : List ℕ)
    (words : List (List K)) (hl : words.length = qs.length) (lam : E) :
    levelBatched mu index rounds high qs words lam =
      ∑ k ∈ Finset.range qs.length, lam ^ k *
        foldRow (specLanes index (words.getD k [])) (K.ofBits (qs.getD k 0)) rounds +
      ∑ k ∈ Finset.range qs.length, lam ^ k * highTerm mu high (qs.getD k 0) := by
  unfold levelBatched powers
  have hz : (List.zip qs words).length = qs.length := by simp [hl]
  rw [← hz, sumE_zipWith_powers (fun (p : ℕ × List K) ↦
    foldRow (specLanes index p.2) (K.ofBits p.1) rounds +
      novelEval high (subspaceAt mu (K.ofBits p.1)) * ofK ((subspaceAt mu (K.ofBits p.1)).getD mu 0)),
    hz, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < qs.length := Finset.mem_range.mp hk
  rw [List.getD_eq_getElem (List.zip qs words) default (by rw [hz]; exact hk'), List.getElem_zip,
    List.getD_eq_getElem qs 0 hk', List.getD_eq_getElem words [] (by omega), highTerm]
  ring

/-! ## A level's start -/

/-- The width of level `lvl`'s rows in `K` words. -/
def lvWidth (lvl : ℕ) (lv : OsLv) : ℕ := rowLen (if lvl = 0 then 1 else 0) lv.folds

/-- **A level's start**: the guest's state against the Spec's. -/
structure LvIn (rd : Reader) (σ : Val) (lvl : ℕ) (lv : OsLv) (st : OsSt) (ws : WhirState)
    (recs : List OsRec) (R : List (Digest × ℕ × ℕ)) (root : Digest) : Prop where
  fs : st.fs.length = 5
  co : st.co < u128Bound
  pad : PadOk σ st.pad
  mats : MatsOk σ st.mats
  claim : ws.claim = σ (.n st.claim) + recsDeficit recs ws.alphas
  glen : ws.alphas.length = lv.foldsOff
  fch : ∀ j (h : j < ws.alphas.length), LoadHolds rd (σ (.n osFch)) j ws.alphas[j]
  rlen : R.length = lvl + 1
  R : R[lvl]? = some (root, lv.depth, lvWidth lvl lv)
  r0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestHalves root).1
  r1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestHalves root).2
  glued : ws.glued = recs.flatMap recGlued
  recF : ∀ r ∈ recs, r.F ≤ ws.alphas.length

/-- What the finish rereads of a non-final level's record. -/
structure RecStored (rd : Reader) (σ : Val) (lvl : ℕ) (lv : OsLv) (r : OsRec) : Prop where
  F : r.F = lv.foldsOff + lv.folds
  mu : r.mu = lv.logCols
  qlen : r.qs.length = lv.queries
  hlen : r.high.length = lv.folds
  lam1 : LoadHolds rd (σ (.n osOodSc)) (lvl + 1) r.lam
  z0len : r.z0.length = lv.logCols
  z0 : ReadsAt rd (σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap)) r.z0
  beta : LoadHolds rd (σ (.n osBetas)) lvl (r.lam ^ 2 * r.lam ^ lv.queries)
  mus : ∃ li, LoadHolds rd (σ (.n osMus)) lvl li ∧ r.lam * li = 1
  hs : ∀ c < lv.folds, LoadHolds rd (σ (.n osHs)) (lvl * hsStride + c)
    (r.high.getD c 0 * word (hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 0)
  pos : ∀ k < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + k) (eOfNat (r.qs.getD k 0))

/-! ## The level's facts and callees -/

/-- The level's `opening_queries` specialization: its entry and its shape against the row. -/
def QShapeOk (c : OsCfg) (lvl : ℕ) (lv : OsLv) (fin : ℕ) (loop : String) (sh : OqShape) : Prop :=
  (osOqName c lvl lv, loop, sh) ∈ openingQueriesLoops ∧
    oqEntry (osOqName c lvl lv) = some (osOqName c lvl lv, loop, sh) ∧
    sh.odd = lv.queries % 2 * (if lvl = 0 then 1 else 0) ∧ sh.base = (if lvl = 0 then 1 else 0) ∧
    sh.folds = lv.folds ∧ sh.depth = lv.depth ∧ sh.cd = lv.capDepth ∧ sh.final = fin ∧
    2 ≤ sh.cd ∧ sh.cd ≤ 8 ∧ sh.cd ≤ sh.depth ∧
    oqCount sh.odd sh.base (lv.queries / (1 + if lvl = 0 then 1 else 0)) = lv.queries

/-- A non-final level's facts: its row against the Spec's level and the next. -/
structure MidFacts (c : OsCfg) (logN lvl : ℕ) (lv : OsLv) (level next : Whir.Level) (lv' : OsLv) :
    Prop where
  nf : lvl ≠ c.yrLevel
  fold : level.fold = lv.folds
  cols : logN - (lv.foldsOff + lv.folds) = lv.logCols
  cols1 : 1 ≤ lv.logCols
  depth : lv.depth = lv.logCols + level.logInvRate
  queries : level.queries = lv.queries
  q0 : 0 < lv.queries
  qu : lv.queries < u128Bound
  P1 : 1 ≤ 128 / lv.depth
  sq : lv.squeezes = sqCount (128 / lv.depth) lv.queries
  pw : digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth
  pwQ : digitsVal (osPowDigits lv.queries) 1 = lv.queries
  posOff : lv.posOff < u128Bound
  sq1 : 1 ≤ lv.squeezes
  sqo : lv.squeezes < ordG
  sq5 : lv.squeezes * 5 < u128Bound
  r3 : 2 * (lv.foldsOff + lv.folds) < u128Bound
  ood : (lvl + 1) * ligColsCap < u128Bound
  hs8 : lvl * hsStride < u128Bound
  shape : levelShape lv.logCols next (2 * 2 ^ next.fold) = (lv'.depth, lvWidth (lvl + 1) lv')
  off' : lv'.foldsOff = lv.foldsOff + lv.folds
  qsh : ∃ loop sh, QShapeOk c lvl lv 0 loop sh
  N : lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG
  it : lv.queries / (1 + lvBase lvl) < u128Bound

/-- A non-final level's callees, by their meanings. -/
structure MidCalls (rd : Reader) (C : CallRel) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    Prop where
  round : ∀ a r, WinTabs rd (a.getD 7 0) → C "opening_round" a r → MeaningOpeningRound rd a r
  msg : ∀ a r, C ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1") a r →
    MeaningOpeningMessage (2 + lv.folds) 1 rd a r
  spf : ∀ a r, C ("squeeze_point_from__L" ++ natStr lv.logCols) a r →
    MeaningSqueezePointFrom lv.logCols rd a r
  g17 : ∀ w, C ("grind_check__L" ++ natStr queryGrind) [w, σ (.n osTabs)] [] →
    (w.limb 0).lane.toNat % 2 ^ queryGrind = 0
  g15 : ∀ w, C ("grind_check__L" ++ natStr levelOodGrind) [w, σ (.n osTabs)] [] →
    (w.limb 0).lane.toNat % 2 ^ levelOodGrind = 0
  rate : LvRate σ c lvl lv
  lp : ∀ a r, WinTabs rd (a.getD 8 0) → C (osPositionsName lv) a r →
    MeaningLevelPositions lv.squeezes lv.depth lv.capDepth rd a r
  lq : FnIs (osQueriesName c lvl lv) (osParams 6) (osLqBody c lvl lv)
  cap : ∀ a r, C ("verify_merkle_cap__L" ++ natStr lv.capDepth) a r →
    MeaningVerifyMerkleCap lv.capDepth rd a r

theorem lanesOf_base (lvl : ℕ) : lanesOf (if lvl = 0 then 1 else 0) = specLanes lvl := by
  funext row
  by_cases h : lvl = 0 <;> simp [lanesOf, specLanes, h]

theorem oqEntry_shape {name loop : String} {sh : OqShape}
    (h : oqEntry name = some (name, loop, sh)) : oqShapeOf name = sh ∧ oqLoopOf name = loop := by
  simp [oqShapeOf, oqLoopOf, h]

end
end LeanVM.Guest.B1.Whir
