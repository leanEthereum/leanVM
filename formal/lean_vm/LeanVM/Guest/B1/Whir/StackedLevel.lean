/-
  LeanVM.Guest.B1.Whir.StackedLevel

  One level of `open_stacked` against one level of `whirLevelsOpen`: the folds, the next
  commitment or the final message, the proof of work, the query positions, the queries and the
  glue.
-/

module

public import LeanVM.Guest.B1.Whir.StackedQueries

/-!
# A level of the stacked opening (TRIAGE #36)

`osLevel_sound`: from the guest's state at the start of level `lvl` against the specification's
(`OsLvInv`: the chain state, the words read, the running quadratic and claim, the fold challenges
stored, the roots read so far with the level's root at its slot, and the claims glued so far,
`osGluedOf` of a record `OsRec` per level), the level's three programs in `os_whirLevelsOpen_cons`
(`foldRounds`, `osLevelMid`, `osLevelQueries`) run, reading the words and the openings the guest
reads, and the invariant holds at the next level. The configuration's facts the proof uses are
`LvSpec`, decided per candidate; the callees' meanings are `LvCallees`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## Records and the configuration's facts -/

/-- What a level leaves for the terminal: its batching challenge, its query positions, and the
out-of-domain point of the commitment it reads next (none at the last level). -/
structure OsRec where
  lam : E
  queries : List ℕ
  ood : Option (List E)
  deriving Inhabited

/-- The configuration's level `i`. -/
abbrev OsCfg.lv (cfg : OsCfg) (i : ℕ) : OsLvl := cfg.levels.getD i default

/-- The fold challenges through level `i`. -/
def osLevelF (cfg : OsCfg) (i : ℕ) : ℕ := (cfg.lv i).foldsOff + (cfg.lv i).folds

/-- The claims a level glues (V:1745-1748), after `F` fold challenges. -/
def osRecGlued (logN F : ℕ) (r : OsRec) : List GluedClaim :=
  match r.ood with
  | none => [⟨1 * r.lam, F, fun x ↦ inducedWeight (logN - F) r.queries
      (powers r.lam r.queries.length) x⟩]
  | some z => [⟨1 * r.lam, F, fun x ↦ eqEval z x⟩, ⟨1 * r.lam * r.lam, F, fun x ↦
      inducedWeight (logN - F) r.queries (powers r.lam r.queries.length) x⟩]

/-- The claims glued by the levels of the records. -/
def osGluedOf (logN : ℕ) (cfg : OsCfg) (recs : List OsRec) : List GluedClaim :=
  (recs.zipIdx.map fun p ↦ osRecGlued logN (osLevelF cfg p.2) p.1).flatten

private theorem gluedOf_append (logN : ℕ) (cfg : OsCfg) (recs : List OsRec) (r : OsRec) :
    osGluedOf logN cfg (recs ++ [r]) = osGluedOf logN cfg recs ++ osRecGlued logN (osLevelF cfg recs.length) r := by
  simp [osGluedOf, List.zipIdx_append]

/-- What the guest stored for level `i`'s record: its positions, its query weights, its scalar,
and its out-of-domain point and scalar. -/
def OsRecOk (rd : Reader) (σ : Val) (cfg : OsCfg) (i : ℕ) (r : OsRec) : Prop :=
  r.queries.length = (cfg.lv i).queries ∧
    (∀ j < (cfg.lv i).queries,
      LoadHolds rd (σ (.n osQpos)) ((cfg.lv i).posOff + j) (eOfNat (r.queries.getD j 0))) ∧
    (∀ j < (cfg.lv i).queries, LoadHolds rd (σ (.n osQw)) (i * cfg.maxQ + j) (r.lam ^ j)) ∧
    (r.ood = none ↔ i = cfg.yrLevel) ∧ (r.ood = none → LoadHolds rd (σ (.n osBetas)) i r.lam) ∧
    ∀ z, r.ood = some z → LoadHolds rd (σ (.n osBetas)) i (r.lam * r.lam) ∧
      z.length = (cfg.lv i).logCols ∧ ReadsAt rd (σ (.n osOodz) * gen ^ ((i + 1) * 22)) z ∧
      LoadHolds rd (σ (.n osOod)) ((i + 1) * 4) r.lam

/-- The configuration's level `lvl` against the specification's level `L` with the levels
`rest` after it, for a stack of log-size `logN`. -/
def LvSpec (cfg : OsCfg) (logN lvl : ℕ) (L : Whir.Level) (rest : List Whir.Level) : Prop :=
  let lv := cfg.lv lvl
  let ml := logN - osLevelF cfg lvl
  lv.folds = L.fold ∧ 0 < L.fold ∧ lv.queries = L.queries ∧ 0 < ml ∧ ml < 2 ^ 62 ∧
    lv.logCols = ml ∧ lv.depth = ml + L.logInvRate ∧ lv.grindBits = Whir.queryGrindingBits ∧
    0 < 192 / lv.depth ∧ lv.queries ≤ lv.squeezes * (192 / lv.depth) ∧
    ((lv.squeezes - 1) * (192 / lv.depth) < lv.queries ∨ lv.squeezes = 0) ∧
    lv.squeezes ≤ lv.queries ∧ lv.squeezes < 2 ^ 62 ∧
    osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth ∧
    1 ≤ lv.capDepth ∧ lv.capDepth ≤ lv.depth ∧ lv.foldsOff < 2 ^ 128 ∧ 4 * lv.capOff < 2 ^ 128 ∧
    lvl * cfg.maxQ < 2 ^ 128 ∧ lv.posOff < 2 ^ 128 ∧ lv.queries < 2 ^ 62 ∧ (lvl + 1) * 22 < 2 ^ 128 ∧
    (rest = [] ↔ lvl = cfg.yrLevel) ∧ (rest = [] → cfg.yrLen = 2 ^ ml) ∧
    ∀ next ∈ rest.head?, lv.oodNext = 1 ∧ (cfg.lv (lvl + 1)).foldsOff = osLevelF cfg lvl ∧
      (cfg.lv (lvl + 1)).folds = next.fold ∧
      (cfg.lv (lvl + 1)).depth = ml - next.fold + next.logInvRate

instance (cfg : OsCfg) (logN lvl : ℕ) (L : Whir.Level) (rest : List Whir.Level) :
    Decidable (LvSpec cfg logN lvl L rest) := by unfold LvSpec; exact inferInstance

/-- The callees of level `lvl`, as their meanings. -/
structure LvCallees (rd : Reader) (cfg : OsCfg) (lvl : ℕ) : Prop where
  rw : ∀ a r, coreProgram.Rel rd (cfg.lv lvl).rowWeights a r →
    MeaningOpeningRowWeights (cfg.lv lvl).folds (if lvl = 0 then 1 else 0) rd a r
  cap : ∀ a r, coreProgram.Rel rd (cfg.lv lvl).verifyCap a r →
    MeaningVerifyMerkleCap (cfg.lv lvl).capDepth rd a r
  queries : ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E) (rets : List E), n < ordG →
    QueryBits rd qbp n (cfg.lv lvl).depth pos →
    coreProgram.Rel rd (cfg.lv lvl).queriesFn [cap, flags, qw, qbp, rew, gen ^ n] rets →
    ∃ qsc, MeaningOpeningQueries (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)
      (cfg.lv lvl).depth (cfg.lv lvl).capDepth n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets
  decode : ∀ a r, coreProgram.Rel rd (cfg.lv lvl).decode a r →
    MeaningDecodeQueryBits (cfg.lv lvl).depth rd a r
  sq : ∃ fn, coreProgram.find? (cfg.lv lvl).sqLoop = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧ fn.body = sqLoopOf (cfg.lv lvl)

/-! ## The invariant -/

/-- The guest at the start of level `lvl` against the specification's state `w`, chain state
`cv`, words `xs` and roots `roots`. -/
structure OsLvInv (rd : Reader) (σ : Val) (cfg : OsCfg) (logN : ℕ) (cur : E) (lvl : ℕ) (st : OsSt)
    (cv : Digest) (xs : List E) (w : WhirState) (roots : List (Digest × ℕ × ℕ)) : Prop where
  cur : OsCur rd σ cur st cv xs
  co : st.co ≤ 8
  quad : w.quad = [σ (.n st.c), σ (.n st.b), σ (.n st.a)]
  target : w.target = σ (.n st.t)
  nfolds : w.folds.length = (cfg.lv lvl).foldsOff
  folds : ∀ j < w.folds.length, LoadHolds rd (σ (.n osFch)) j (w.folds.getD j 0)
  rootsLen : roots.length = lvl + 1
  root : ∃ rt, roots[lvl]? = some (rt, (cfg.lv lvl).depth,
      oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)) ∧
    LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestScalars rt).1 ∧
    LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestScalars rt).2
  glued : ∃ recs : List OsRec, recs.length = lvl ∧ w.glued = osGluedOf logN cfg recs ∧
    ∀ i < lvl, OsRecOk rd σ cfg i (recs.getD i default)

theorem LvSpec.yrLen {cfg : OsCfg} {logN lvl : ℕ} {L : Whir.Level} (h : LvSpec cfg logN lvl L []) :
    cfg.yrLen = 2 ^ (logN - osLevelF cfg lvl) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hyr, -⟩ := h
  exact hyr rfl

theorem LvSpec.nextFolds {cfg : OsCfg} {logN lvl : ℕ} {L next : Whir.Level} {rest : List Whir.Level}
    (h : LvSpec cfg logN lvl L (next :: rest)) : (cfg.lv (lvl + 1)).foldsOff = osLevelF cfg lvl := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnext⟩ := h
  exact (hnext next rfl).2.1

theorem LvSpec.logCols {cfg : OsCfg} {logN lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (h : LvSpec cfg logN lvl L rest) : (cfg.lv lvl).logCols = logN - osLevelF cfg lvl ∧
      1 ≤ (cfg.lv lvl).logCols ∧ (cfg.lv lvl).queries < 2 ^ 62 := by
  obtain ⟨-, -, -, h0, -, hlc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnq, -⟩ := h
  exact ⟨hlc, by omega, hnq⟩

/-! ## The positions' bits -/

variable {rd : Reader} {σ : Val}

/-- **The query positions and their bit runs** from `decode_query_bits` at every squeeze: query
`i`'s position is `osPosOf` (V:1598) at `qpos[posOff + i]`, and its bits at `qbp[posOff + i]`. -/
private theorem queryBits_of_decode {depth nq nsq posOff : ℕ} {qpos qbp : E} {cv : Digest}
    (hper : 0 < 192 / depth) (hs1 : nq ≤ nsq * (192 / depth))
    (hdec : ∀ j < nsq, MeaningDecodeQueryBits depth rd [challengeOf (sqCv (sqAll j cv).2),
      qpos * gen ^ (posOff + j * (192 / depth)), qbp * gen ^ (posOff + j * (192 / depth))] []) :
    QueryBits rd (qbp * gen ^ posOff) nq depth (osPosOf depth cv) ∧
      ∀ i < nq, LoadHolds rd qpos (posOff + i) (eOfNat (osPosOf depth cv i)) := by
  have hdiv : ∀ i < nq, i / (192 / depth) < nsq := fun i hi => by
    rw [Nat.div_lt_iff_lt_mul hper]; omega
  have hidx : ∀ i, posOff + i / (192 / depth) * (192 / depth) + i % (192 / depth) = posOff + i := by
    intro i; rw [Nat.add_assoc, Nat.div_add_mod']
  refine ⟨fun i hi => ⟨Nat.mod_lt _ (Nat.two_pow_pos _), fun dbp hdbp => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨-, p, ⟨hpK, hfr⟩, hj⟩ := hdec _ (hdiv i hi)
    have hc := Nat.mod_lt i hper
    obtain ⟨-, lp⟩ := hj _ hc
    rw [loadHolds_mul_gen_pow, hidx] at lp
    rw [loadHolds_mul_gen_pow] at hdbp
    have hdq := loadHolds_unique lp hdbp
    subst hdq
    have hK : IsInK (p * gen ^ (i % (192 / depth) * depth)) := isInK_mul hpK (gen_pow_isInK _)
    refine ⟨hK, fun l hl w hw => ?_⟩
    rw [gen_pow_eq_ofK, limb0_mul_ofK hpK, mul_assoc, Parameters.gpow, Parameters.gpow, ← pow_add] at hw
    have hlt : i % (192 / depth) * depth + l < 192 := by
      have : i % (192 / depth) * depth + depth ≤ 192 / depth * depth := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
      have := Nat.div_mul_le_self 192 depth
      omega
    rw [hfr _ hlt w hw, osPosOf, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [hl]
  · obtain ⟨-, p, -, hj⟩ := hdec _ (hdiv i hi)
    obtain ⟨lq, -⟩ := hj _ (Nat.mod_lt i hper)
    rw [loadHolds_mul_gen_pow, hidx] at lq
    exact lq

/-! ## A level's proof of work, positions and queries -/

theorem os_getD_map_range {α : Type} {d : α} (f : ℕ → α) {n j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]

/-- **A level after its claims** (G:1136-1193): the nonce, the positions, `lam`, the query
weights and the queries; `osLevelQueries` (V:1737-1749) runs over the words and openings the guest
reads, gluing whatever claims are pending before the level's query claim. -/
theorem osLevelQ_sound {cfg : OsCfg} {logN lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg logN lvl L rest) (hcall : LvCallees rd cfg lvl)
    {cur : E} {s sg ssq : OsSt} {cvm : Digest} {xsm : List E} (hat : OsCur rd σ cur s cvm xsm)
    {lf : List E} (hlfl : lf.length = (cfg.lv lvl).folds)
    (hlf : ∀ j < (cfg.lv lvl).folds,
      LoadHolds rd (σ (.n osFch)) ((cfg.lv lvl).foldsOff + j) (lf.getD j 0))
    {roots : List (Digest × ℕ × ℕ)} {rt : Digest}
    (hrt : roots[lvl]? = some (rt, (cfg.lv lvl).depth,
      oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)))
    (lrt0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestScalars rt).1)
    (lrt1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestScalars rt).2)
    (hsg : (osGrind (cfg.lv lvl).grindBits s).2 = sg)
    (hssq : (osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop sg).2 = ssq)
    {kret : List E → Prop}
    (hG : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osGrind (cfg.lv lvl).grindBits s).1 True kret)
    (hS : Stmt.HoldsList (coreProgram.Rel rd) rd σ
      (osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop sg).1 True kret)
    (hL : Stmt.HoldsList (coreProgram.Rel rd) rd σ
      (osLamPows (ssq.k - 1) osQw (lvl * cfg.maxQ) ssq.k (cfg.lv lvl).queries) True kret)
    (hQ : Stmt.HoldsList (coreProgram.Rel rd) rd σ
      (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).1 True kret) :
    ∃ (lam : E) (qs : List ℕ) (ysQ : List E) (os : List Opening) (cvq : Digest) (c0 c2 : E),
      σ (.n (ssq.k - 1)) = lam ∧
      OsCur rd σ cur (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.1
        cvq (xsm ++ ysQ) ∧
      (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.1.co = s.co + 3 ∧
      σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.2.1) = c0 ∧
      σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.2.2.2) = c2 ∧
      σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.2.2.1) =
        σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.1) + c2 ∧
      qs.length = (cfg.lv lvl).queries ∧
      (∀ j < (cfg.lv lvl).queries,
        LoadHolds rd (σ (.n osQpos)) ((cfg.lv lvl).posOff + j) (eOfNat (qs.getD j 0))) ∧
      (∀ j < (cfg.lv lvl).queries, LoadHolds rd (σ (.n osQw)) (lvl * cfg.maxQ + j) (lam ^ j)) ∧
      ∀ (w1 : WhirState) (pending : List (E × List E × (List E → E))) (r : List E) (o : List Opening),
        Runs (osLevelQueries (logN - osLevelF cfg lvl) lvl L lf w1 pending) ⟨cvm, ysQ ++ r, os ++ o, roots⟩
          (glue lam w1 (pending ++
            [(σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.1),
              [c0, σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.1)
                + c2, c2],
              fun x ↦ inducedWeight (logN - osLevelF cfg lvl) qs (powers lam qs.length) x)]))
          ⟨cvq, r, o, roots⟩ := by
  obtain ⟨hf, hf0, hq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  obtain ⟨sqfn, hsqf, hsqp, hsqb⟩ := hcall.sq
  -- the nonce
  obtain ⟨n, hatg, hpow, hcog⟩ := osGrind_sound (by rw [hgr]; decide) (by rw [hgr]; decide) hat hG
  rw [hsg] at hatg hcog
  rw [hgr] at hpow
  -- the positions and `lam`
  obtain ⟨hatq, hlam, hdec, hcoq⟩ := osSqueezes_sound hsqf hsqp hsqb hcall.decode hdig
    (by omega) (by omega) hatg hS
  rw [hssq] at hatq hlam hcoq
  set cvg := absorbCv cvm n 4
  set lam := challengeOf (sqCv (sqAll (cfg.lv lvl).squeezes cvg).2)
  obtain ⟨hbits, hqpos⟩ := queryBits_of_decode hper hs1 hdec
  have hqw := osLamPows_sound _ hL
  rw [hlam] at hqw
  -- the queries
  obtain ⟨root, os, c0, c2, lr0, lr1, hosl, hos, hsum, hatQ, hcoQ, e0, e1, e2⟩ :=
    osQueries_sound rfl hcall.rw hcall.cap hcall.queries hcd1 hcd2 hb1 hb2 hb4 hb5 (by omega)
      hlfl hlf (fun i hi => by simpa using hqw i hi) hbits
      (s := { ssq with k := ssq.k + (cfg.lv lvl).queries })
      (cv := sqCv (sqAll (cfg.lv lvl).squeezes cvg).2) ⟨hatq.fs, hatq.reads, hatq.cursor⟩ hQ
  have hroot : root = rt := digestScalars_injective (Prod.ext (loadHolds_unique lr0 lrt0)
    (loadHolds_unique lr1 lrt1))
  subst hroot
  set qs := (List.range (cfg.lv lvl).queries).map (osPosOf (cfg.lv lvl).depth cvg)
  have hqsl : qs.length = (cfg.lv lvl).queries := by simp [qs]
  refine ⟨lam, qs, [n, c0, c2], os, _, c0, c2, hlam, by simpa using hatQ, by rw [hcoQ, hcoq, hcog],
    e0, e2, e1, hqsl, fun j hj => ?_, fun j hj => by simpa using hqw j hj,
    fun w1 pending r o => ?_⟩
  · rw [os_getD_map_range _ hj]
    exact hqpos j hj
  simp only [osLevelQueries]
  conv at hsum => rhs; rw [← hqsl]
  rw [← hdep, ← hq, hsum]
  refine Runs.bind (os_runs_grindP hpow _ _ _) ?_
  refine Runs.bind (RunsTo.runs (os_runsTo_sampleQueries hper hs1 hs2 hs3 cvg) _ _ _) ?_
  refine Runs.bind (os_runs_sampleE _) ?_
  refine Runs.bind (os_runs_queryP hrt (os_openAll_of qs os o (by rw [hosl, hqsl]) fun j hj => ?_)) ?_
  · obtain ⟨h1, h2, h3⟩ := hos j hj
    refine ⟨h1, h2, ?_⟩
    rw [os_getD_map_range _ (show j < (cfg.lv lvl).queries by omega)]
    exact h3
  refine Runs.bind (os_runs_roundPoly3 _ _ c0 c2 r _ _) ?_
  exact Runs.ret _ _

/-! ## A level -/

/-- The guest after its last level `n - 1`, before the tail. -/
structure OsEndInv (rd : Reader) (σ : Val) (cfg : OsCfg) (logN : ℕ) (cur : E) (n : ℕ) (st : OsSt)
    (cv : Digest) (xs : List E) (w : WhirState) : Prop where
  cur : OsCur rd σ cur st cv xs
  co : st.co ≤ 8
  quad : w.quad = [σ (.n st.c), σ (.n st.b), σ (.n st.a)]
  target : w.target = σ (.n st.t)
  nfolds : w.folds.length = osLevelF cfg (n - 1)
  folds : ∀ j < w.folds.length, LoadHolds rd (σ (.n osFch)) j (w.folds.getD j 0)
  glued : ∃ recs : List OsRec, recs.length = n ∧ w.glued = osGluedOf logN cfg recs ∧
    ∀ i < n, OsRecOk rd σ cfg i (recs.getD i default)

theorem osFinal_keep (name : String) (fmsg : ℕ) (s : OsSt) :
    (osFinal name fmsg s).2.c = s.c ∧ (osFinal name fmsg s).2.b = s.b ∧
      (osFinal name fmsg s).2.a = s.a ∧ (osFinal name fmsg s).2.t = s.t := ⟨rfl, rfl, rfl, rfl⟩

theorem osCommit_keep (lvl logCols roots oodz ood : ℕ) (s : OsSt) :
    (osCommit lvl logCols 1 roots oodz ood s).2.c = s.c ∧ (osCommit lvl logCols 1 roots oodz ood s).2.b = s.b ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.a = s.a ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.t = s.t := ⟨rfl, rfl, rfl, rfl⟩

theorem osRest_keep (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) :
    let sq := (osSqueezes cfg.maxSq lv.squeezes osQpos osQbp lv.sqLoop (osGrind lv.grindBits s).2).2
    let q := (osQueries cfg lv lvl { sq with k := sq.k + lv.queries }).2.1
    q.c = s.c ∧ q.b = s.b ∧ q.a = s.a ∧ q.t = s.t := ⟨rfl, rfl, rfl, rfl⟩

private theorem digestOfScalars_pair {x0 x1 : E} (h0 : IsCanonical128 x0) (h1 : IsCanonical128 x1) :
    digestOfScalars (x0, x1) = some (pairDigest x0 x1) := by
  simp [digestOfScalars, h0, h1, pairDigest]

private theorem recOk_append {cfg : OsCfg} {recs : List OsRec} {r : OsRec} {n : ℕ} (hl : recs.length = n)
    (hrecs : ∀ i < n, OsRecOk rd σ cfg i (recs.getD i default)) (hr : OsRecOk rd σ cfg n r) :
    ∀ i < n + 1, OsRecOk rd σ cfg i ((recs ++ [r]).getD i default) := by
  intro i hi
  rcases Nat.lt_or_ge i n with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    exact hrecs i h
  · obtain rfl : i = n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, Nat.sub_self]
    exact hr

private theorem folds_append {fch : E} {ws chs : List E} {off : ℕ} (hoff : ws.length = off)
    (h1 : ∀ j < ws.length, LoadHolds rd fch j (ws.getD j 0))
    (h2 : ∀ j < chs.length, LoadHolds rd fch (off + j) (chs.getD j 0)) :
    ∀ j < (ws ++ chs).length, LoadHolds rd fch j ((ws ++ chs).getD j 0) := by
  intro j hj
  rw [List.length_append] at hj
  rcases Nat.lt_or_ge j ws.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
    exact h1 j h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]
    have := h2 (j - ws.length) (by omega)
    rw [hoff] at this ⊢
    rwa [show off + (j - off) = j by omega] at this

theorem osFinal_noRet (name : String) (fmsg : ℕ) (s : OsSt) :
    Stmt.noRetList (osFinal name fmsg s).1 = true := by
  unfold osFinal; simp only [noRetList_append, osMat_noRet, Bool.true_and]; rfl

theorem osCommit_noRet (lvl logCols roots oodz ood : ℕ) (s : OsSt) :
    Stmt.noRetList (osCommit lvl logCols 1 roots oodz ood s).1 = true := by
  simp [osCommit, osOods, osOodSample, osFsNext, fsNextT, fsCompressT, Stmt.noRetList, Stmt.noRet]

theorem osGrind_noRet (bits : ℕ) (s : OsSt) : Stmt.noRetList (osGrind bits s).1 = true := by
  unfold osGrind; split <;> simp [fsCompressT, Stmt.noRetList, Stmt.noRet]

theorem osSqueezes_noRet (maxSq nsq qpos qbp : ℕ) (loop : String) (s : OsSt) :
    Stmt.noRetList (osSqueezes maxSq nsq qpos qbp loop s).1 = true := by
  simp [osSqueezes, osHeap, squeezeT, squeezeStateT, challengeT, Stmt.noRetList, Stmt.noRet]

theorem osLamPows_noRet (lam qw base k : ℕ) : ∀ nq, Stmt.noRetList (osLamPows lam qw base k nq) = true
  | 0 => rfl
  | nq + 1 => by
    simp only [osLamPows, noRetList_append]
    split
    · rfl
    · rw [noRetList_append, noRetList_flatten_range _ _ (fun _ => rfl)]; rfl

theorem osQueries_noRet (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) :
    Stmt.noRetList (osQueries cfg lv lvl s).1 = true := by
  simp [osQueries, osHeap, osFsNext, fsNextT, fsCompressT, noRetList_append, osMat_noRet,
    Stmt.noRetList, Stmt.noRet]

theorem osOodGlues_noRet (lvl lam sc : ℕ) (s : OsSt) :
    Stmt.noRetList (osOodGlues lvl lam 0 1 sc s).1 = true := by
  simp [osOodGlues, osOodGlue, Stmt.noRetList, Stmt.noRet]

/-- **One level** of `open_stacked` (G:1096-1213) against one level of `whirLevelsOpen`
(`os_whirLevelsOpen_cons`): `foldRounds`, `osLevelMid` and `osLevelQueries` run over the words and the
openings the guest reads; the invariant holds at the next level, or, after the last level, what
the tail needs and the final message. -/
theorem osLevel_sound {cfg : OsCfg} {logN lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg logN lvl L rest) (hcall : LvCallees rd cfg lvl)
    (hfin : ∀ a r, coreProgram.Rel rd cfg.finalMsg a r → MeaningOpeningFinalMessage cfg.yrLen rd a r)
    {cur : E} {st : OsSt} {cv : Digest} {xs : List E} {w : WhirState} {roots : List (Digest × ℕ × ℕ)}
    (hinv : OsLvInv rd σ cfg logN cur lvl st cv xs w roots) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osLevel cfg lvl (cfg.lv lvl) st).1 True kret) :
    ∃ (ys1 : List E) (cv1 : Digest) (w1 : WhirState) (chs : List E),
      RunsTo (foldRounds L.fold w []) cv ys1 (w1, chs) cv1 ∧ w1.folds.length = osLevelF cfg lvl ∧
    ∃ (ysM : List E) (cv2 : Digest) (residual : List E)
      (pending : List (E × List E × (List E → E))) (roots2 : List (Digest × ℕ × ℕ)),
      (∀ r o, Runs (osLevelMid (logN - osLevelF cfg lvl) rest) ⟨cv1, ysM ++ r, o, roots⟩ (residual, pending)
        ⟨cv2, r, o, roots2⟩) ∧
    ∃ (ysQ : List E) (os : List Opening) (cv' : Digest) (w' : WhirState),
      (∀ r o, Runs (osLevelQueries (logN - osLevelF cfg lvl) lvl L chs w1 pending)
        ⟨cv2, ysQ ++ r, os ++ o, roots2⟩ w' ⟨cv', r, o, roots2⟩) ∧
      (rest = [] → residual.length = cfg.yrLen ∧ ReadsAt rd (σ (.n osFmsg)) residual ∧
        OsEndInv rd σ cfg logN cur (lvl + 1) (osLevel cfg lvl (cfg.lv lvl) st).2 cv'
          (xs ++ ys1 ++ ysM ++ ysQ) w') ∧
      (rest ≠ [] → OsLvInv rd σ cfg logN cur (lvl + 1) (osLevel cfg lvl (cfg.lv lvl) st).2 cv'
        (xs ++ ys1 ++ ysM ++ ysQ) w' roots2) := by
  have hspec' := hspec
  obtain ⟨hf, hf0, hq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  obtain ⟨hat, hco, hquad, htgt, hnf, hfch, hrl, ⟨rt, hrt, lrt0, lrt1⟩, ⟨recs, hrecl, hgl, hrecs⟩⟩ :=
    hinv
  unfold osLevel at h ⊢
  simp only at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨hF, h⟩ := holdsList_true_of (osFolds_noRet _ _ _ _) h
  obtain ⟨ys1, cv1, chs, w1, hat1, hrun1, hchl, hq1, ht1, hfo1, hgl1, hlf1, hco1⟩ :=
    osFolds_sound (fch := osFch) _ _ _ _ _ w [] hat (by omega) hquad htgt hF
  rw [ite_neg' (by rw [hf]; omega)] at hco1
  have hw1l : w1.folds.length = osLevelF cfg lvl := by
    rw [hfo1, List.length_append, hnf, hchl, osLevelF]
  refine ⟨ys1, cv1, w1, chs, by rw [← hf]; simpa using hrun1, hw1l, ?_⟩
  generalize hfr : osFolds osFch (cfg.lv lvl).foldsOff (cfg.lv lvl).folds st = fr at *
  by_cases hl : lvl = cfg.yrLevel
  · have hr0 : rest = [] := hlast.mpr hl
    subst hr0
    have he : (lvl = cfg.yrLevel) = True := eq_true hl
    simp only [he, ↓reduceIte] at h ⊢
    obtain ⟨hM, h⟩ := holdsList_true_of (osFinal_noRet _ _ _) h
    obtain ⟨ms, hmsl, hatM, hfm, hcoM⟩ := osFinal_sound hfin hat1 (by omega) hM
    obtain ⟨hG, h⟩ := holdsList_true_of (osGrind_noRet _ _) h
    obtain ⟨hS, h⟩ := holdsList_true_of (osSqueezes_noRet _ _ _ _ _ _) h
    obtain ⟨hL, h⟩ := holdsList_true_of (osLamPows_noRet _ _ _ _ _) h
    obtain ⟨hQ, h⟩ := holdsList_true_of (osQueries_noRet _ _ _ _) h
    obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
    obtain ⟨hB, h⟩ := holdsList_true_of (by rfl) h
    obtain ⟨lam, qs, ysQ, os, cvq, c0, c2, hlam, hatQ, hcoQ, e0, e2, e1, hqsl, hqpos, hqw, hrunQ⟩ :=
      osLevelQ_sound hspec' hcall hatM (lf := chs) (by rw [hchl]) hlf1 hrt lrt0 lrt1 rfl rfl hG hS hL hQ
    have hgl := osGlue_sound h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hB
    have hk := osRest_keep cfg (cfg.lv lvl) lvl (osFinal cfg.finalMsg osFmsg fr.2).2
    simp only at hk
    obtain ⟨k1, k2, k3, k4⟩ := hk
    obtain ⟨f1, f2, f3, f4⟩ := osFinal_keep cfg.finalMsg osFmsg fr.2
    generalize (osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop
      (osGrind (cfg.lv lvl).grindBits (osFinal cfg.finalMsg osFmsg fr.2).2).2).2 = ssq at *
    generalize osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries } = qq at *
    obtain ⟨g1, g2, g3, g4⟩ := hgl
    rw [hlam] at g1 g2 g3 g4 hB
    rw [k1, f1] at g1
    rw [k2, f2, e1] at g2
    rw [k3, f3, e2] at g3
    rw [k4, f4] at g4
    rw [e0] at g1
    have hyr' := hyr rfl
    refine ⟨ms, obsAll cv1 ms, ms, [], roots, fun r o => ?_, ysQ, os, cvq, _, fun r o => hrunQ w1 [] r o,
      fun _ => ⟨by rw [hmsl], hfm, ?_⟩, fun hne => absurd rfl hne⟩
    · simp only [osLevelMid]
      rw [← hyr', ← hmsl]
      exact Runs.bind (RunsTo.runs (runsTo_readN cv1 ms) _ _ _) (Runs.ret _ _)
    · simp only [List.nil_append, os_glue_one]
      refine ⟨⟨hatQ.fs, hatQ.reads, hatQ.cursor⟩, by
          show qq.2.1.co ≤ 8; rw [hcoQ, hcoM]; omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq1]
        simp only [List.zipWith_cons_cons, List.zipWith_nil_right, one_mul]
        show [σ (.n fr.2.c) + lam * c0, σ (.n fr.2.b) + lam * (σ (.n qq.2.2.1) + c2),
          σ (.n fr.2.a) + lam * c2] = _
        rw [g1, g2, g3]
      · show w1.target + 1 * lam * σ (.n qq.2.2.1) = _
        rw [ht1, g4, one_mul]
      · show w1.folds.length = osLevelF cfg (lvl + 1 - 1)
        rw [hw1l, Nat.add_sub_cancel]
      · show ∀ j < w1.folds.length, LoadHolds rd (σ (.n osFch)) j (w1.folds.getD j 0)
        rw [hfo1]
        exact folds_append hnf hfch (fun j hj => hlf1 j (by rw [← hchl]; exact hj))
      · refine ⟨recs ++ [⟨lam, qs, none⟩], by simp [hrecl], ?_, recOk_append hrecl hrecs
          ⟨hqsl, hqpos, hqw, by simp [hl], fun _ => hB, fun z hz => absurd hz (by simp)⟩⟩
        show w1.glued ++ _ = _
        rw [gluedOf_append, hgl1, hgl, hrecl, hw1l]
        simp [osRecGlued]
  · obtain ⟨next, rest', rfl⟩ : ∃ next rest', rest = next :: rest' := by
      cases rest with
      | nil => exact absurd (hlast.mp rfl) hl
      | cons a b => exact ⟨a, b, rfl⟩
    obtain ⟨hood, hfo', hfl', hdep'⟩ := hnext next rfl
    have he : (lvl = cfg.yrLevel) = False := eq_false hl
    simp only [he, ↓reduceIte] at h ⊢
    rw [hood] at h ⊢
    simp only [osOodGlues, List.append_nil, Nat.zero_mul, Nat.add_zero] at h ⊢
    generalize hLC : (cfg.lv lvl).logCols = lc at h ⊢
    obtain rfl : lc = logN - osLevelF cfg lvl := hLC.symm.trans hlc
    obtain ⟨hM, h⟩ := holdsList_true_of (osCommit_noRet _ _ _ _ _ _) h
    obtain ⟨x0, x1, y, c0o, c2o, hk0, hk1, lx0, lx1, hatM, hrs, ly, lc0, lc2, hcoM⟩ :=
      osCommit_sound (by omega) (by omega) hb6 hat1 hM
    obtain ⟨hG, h⟩ := holdsList_true_of (osGrind_noRet _ _) h
    obtain ⟨hS, h⟩ := holdsList_true_of (osSqueezes_noRet _ _ _ _ _ _) h
    obtain ⟨hL, h⟩ := holdsList_true_of (osLamPows_noRet _ _ _ _ _) h
    obtain ⟨hQ, h⟩ := holdsList_true_of (osQueries_noRet _ _ _ _) h
    obtain ⟨hO, h⟩ := holdsList_true_of (by simp [osOodGlue, Stmt.noRetList, Stmt.noRet]) h
    obtain ⟨hB, h⟩ := holdsList_true_of (by rfl) h
    have hrt' : (roots ++ [(pairDigest x0 x1, levelShape (logN - osLevelF cfg lvl) next
        (3 * 2 ^ next.fold))])[lvl]? = some (rt, (cfg.lv lvl).depth,
        oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)) := by
      rw [List.getElem?_append_left (by omega)]; exact hrt
    obtain ⟨lam, qs, ysQ, os, cvq, c0, c2, hlam, hatQ, hcoQ, e0, e2, e1, hqsl, hqpos, hqw, hrunQ⟩ :=
      osLevelQ_sound hspec' hcall hatM (lf := chs) (by rw [hchl]) hlf1 hrt' lrt0 lrt1 rfl rfl hG hS hL hQ
    obtain ⟨lo, o1, o2, o3, o4, o5⟩ := osOodGlue_sound ly lc0 lc2 hO
    have hgl := osGlue_sound h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hB
    have hk := osRest_keep cfg (cfg.lv lvl) lvl
      (osCommit lvl (logN - osLevelF cfg lvl) 1 osRoots osOodz osOod fr.2).2
    simp only at hk
    obtain ⟨k1, k2, k3, k4⟩ := hk
    obtain ⟨f1, f2, f3, f4⟩ := osCommit_keep lvl (logN - osLevelF cfg lvl) osRoots osOodz osOod fr.2
    generalize (osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop
      (osGrind (cfg.lv lvl).grindBits (osCommit lvl (logN - osLevelF cfg lvl) 1 osRoots osOodz osOod
        fr.2).2).2).2 = ssq at *
    generalize osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries } = qq at *
    obtain ⟨g1, g2, g3, g4⟩ := hgl
    rw [o5, hlam] at g1 g2 g3 g4 hB
    rw [hlam] at lo o1 o2 o3 o4
    rw [o1, k1, f1, e0] at g1
    rw [o2, k2, f2, e1] at g2
    rw [o3, k3, f3, e2] at g3
    rw [o4, k4, f4] at g4
    set ml := logN - osLevelF cfg lvl
    set cv12 := obsCv (obsCv cv1 x0) x1
    refine ⟨[x0, x1, y, c0o, c2o], obsCv (obsCv (obsCv (sqAll ml cv12).2 y) c0o) c2o, [],
      [(y, [c0o, y + c2o, c2o], fun x ↦ eqEval (sqAll ml cv12).1 x)],
      roots ++ [(pairDigest x0 x1, levelShape ml next (3 * 2 ^ next.fold))], fun r o => ?_,
      ysQ, os, cvq, _, fun r o => hrunQ w1 _ r o, fun h0 => absurd h0 (by simp), fun _ => ?_⟩
    · simp only [osLevelMid, levelShape]
      refine Runs.bind (os_runs_commitP (digestOfScalars_pair hk0 hk1) _ _ _ _ _) ?_
      refine Runs.bind (RunsTo.runs (runsTo_sampleN ml cv12) _ _ _) ?_
      refine Runs.bind (os_runs_readE _ _ _ _ _) ?_
      refine Runs.bind (os_runs_roundPoly3 _ _ _ _ _ _ _) ?_
      exact Runs.ret _ _
    · simp only [List.singleton_append, os_glue_two]
      refine ⟨⟨hatQ.fs, hatQ.reads, hatQ.cursor⟩, by
          show qq.2.1.co ≤ 8; rw [hcoQ, hcoM, hco1], ?_, ?_, ?_, ?_, by simp [hrl], ?_, ?_⟩
      · rw [hq1]
        simp only [List.zipWith_cons_cons, List.zipWith_nil_right, one_mul]
        show [σ (.n fr.2.c) + lam * c0o + lam * lam * c0,
          σ (.n fr.2.b) + lam * (y + c2o) + lam * lam * (σ (.n qq.2.2.1) + c2),
          σ (.n fr.2.a) + lam * c2o + lam * lam * c2] = _
        rw [g1, g2, g3]
      · show w1.target + 1 * lam * y + 1 * lam * lam * σ (.n qq.2.2.1) = _
        rw [ht1, g4]; simp only [one_mul]
      · show w1.folds.length = (cfg.lv (lvl + 1)).foldsOff
        rw [hw1l, hfo']
      · show ∀ j < w1.folds.length, LoadHolds rd (σ (.n osFch)) j (w1.folds.getD j 0)
        rw [hfo1]
        exact folds_append hnf hfch (fun j hj => hlf1 j (by rw [← hchl]; exact hj))
      · refine ⟨pairDigest x0 x1, ?_, ?_, ?_⟩
        · rw [List.getElem?_append_right (by omega), hrl, Nat.sub_self, List.getElem?_cons_zero,
            hdep', hfl']
          simp [levelShape, oqR]
        · rw [← (pairDigest_eq hk0 hk1)]; simpa [Nat.mul_add] using lx0
        · rw [← (pairDigest_eq hk0 hk1)]; simpa [Nat.mul_add] using lx1
      · refine ⟨recs ++ [⟨lam, qs, some (sqAll ml cv12).1⟩], by simp [hrecl], ?_, recOk_append hrecl hrecs
          ⟨hqsl, hqpos, hqw, by simp [hl], fun hz => absurd hz (by simp), fun z hz => ?_⟩⟩
        · show w1.glued ++ _ ++ _ = _
          rw [gluedOf_append, hgl1, hgl, hrecl, hw1l]
          simp [osRecGlued, ml]
        · simp only [Option.some.injEq] at hz
          subst hz
          exact ⟨hB, by rw [length_sqAll, hlc], hrs, lo⟩

end
end LeanVM.Guest.B1
