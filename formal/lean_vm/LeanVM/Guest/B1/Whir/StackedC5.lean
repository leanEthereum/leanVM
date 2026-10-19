/-
  LeanVM.Guest.B1.Whir.StackedC5

  A level of the stacked opening's run, inverted into the data the guest's honest values need.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC4
public import LeanVM.Guest.B1.Whir.StackedLevel
public import LeanVM.Guest.B1.Whir.OpenLen
public import LeanVM.Guest.B1.Whir.OsSteps

/-!
# A level's honest data (TRIAGE #36)

`os_level_inv`: a run of one level of `whirLevelsOpen` from `p` words of the stream `xs` gives the
level's data (`OsLvH`: its state and challenges after its folds, the next root, the opened rows) and
`OsLvOk`, with every other value a function of them (`osHCv2`, `osHQs`, `osHLam`, `osHWEnd`, ...):
the guest reads what these name.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- A level's data from the specification's run: the state and challenges after its folds, the
chain state then, the next commitment's root, the opened rows and the openings after them. -/
structure OsLvH where
  w1 : WhirState
  chs : List E
  cv1 : Digest
  root : Digest
  rows : List (List K)
  osq : List Opening

instance : Inhabited OsLvH := ⟨⟨⟨0, [], [], []⟩, [], default, default, [], []⟩⟩

variable (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ)

/-- The stream position after the level's folds. -/
def osHP1 : ℕ := p + 2 * (cfg.lv lvl).folds

/-- The stream position after the residual or the next commitment. -/
def osHP2 : ℕ := osHP1 cfg lvl p + if lvl = cfg.yrLevel then cfg.yrLen else 5

/-- The stream position after the level. -/
def osHPEnd : ℕ := osHP2 cfg lvl p + 3

/-- The residual (the last level). -/
def osHMs : List E := (xs.drop (osHP1 cfg lvl p)).take cfg.yrLen

/-- Word `i` after the folds: the next root's scalars, the out-of-domain value and intro. -/
def osHW (i : ℕ) : E := xs.getD (osHP1 cfg lvl p + i) 0

/-- The chain state after the next root. -/
def osHCv12 (cv1 : Digest) : Digest := obsCv (obsCv cv1 (osHW cfg lvl xs p 0)) (osHW cfg lvl xs p 1)

/-- The chain state after the residual or the next commitment and its out-of-domain claim. -/
def osHCv2 (cv1 : Digest) : Digest :=
  if lvl = cfg.yrLevel then obsAll cv1 (osHMs cfg lvl xs p)
  else obsCv (obsCv (obsCv (sqAll (cfg.lv lvl).logCols (osHCv12 cfg lvl xs p cv1)).2 (osHW cfg lvl xs p 2))
    (osHW cfg lvl xs p 3)) (osHW cfg lvl xs p 4)

/-- The query nonce. -/
def osHNonce : E := xs.getD (osHP2 cfg lvl p) 0

/-- The chain state after the nonce. -/
def osHCv3 (cv1 : Digest) : Digest := absorbCv (osHCv2 cfg lvl xs p cv1) (osHNonce cfg lvl xs p) 4

/-- The query positions. -/
def osHQs (cv1 : Digest) : List ℕ :=
  (List.range (cfg.lv lvl).queries).map (osPosOf (cfg.lv lvl).depth (osHCv3 cfg lvl xs p cv1))

/-- The chain state after the positions' squeezes. -/
def osHCv4 (cv1 : Digest) : Digest := (sqAll (cfg.lv lvl).squeezes (osHCv3 cfg lvl xs p cv1)).2

/-- The batching challenge. -/
def osHLam (cv1 : Digest) : E := challengeOf (sqCv (osHCv4 cfg lvl xs p cv1))

/-- The queries' intro, `c0` at `i = 0` and `c2` at `i = 1`. -/
def osHC (i : ℕ) : E := xs.getD (osHP2 cfg lvl p + 1 + i) 0

/-- The chain state after the level. -/
def osHCvEnd (cv1 : Digest) : Digest :=
  obsCv (obsCv (sqCv (osHCv4 cfg lvl xs p cv1)) (osHC cfg lvl xs p 0)) (osHC cfg lvl xs p 1)

/-- The opened rows over the extension. -/
def osHRowsE (rows : List (List K)) : List (List E) :=
  if lvl = 0 then rows.map fun row ↦ row.reverse.map ofK else rows.map extRow

/-- The queries' enforced sum. -/
def osHEnf (H : OsLvH) : E :=
  enforcedSum (osHRowsE lvl H.rows) H.chs
    (powers (osHLam cfg lvl xs p H.cv1) (osHQs cfg lvl xs p H.cv1).length)

/-- The out-of-domain claim the level glues (none at the last level). -/
def osHPending (cv1 : Digest) : List (E × List E × (List E → E)) :=
  if lvl = cfg.yrLevel then []
  else [(osHW cfg lvl xs p 2, [osHW cfg lvl xs p 3, osHW cfg lvl xs p 2 + osHW cfg lvl xs p 4, osHW cfg lvl xs p 4],
    fun x ↦ eqEval (sqAll (cfg.lv lvl).logCols (osHCv12 cfg lvl xs p cv1)).1 x)]

/-- The state after the level. -/
def osHWEnd (H : OsLvH) : WhirState :=
  glue (osHLam cfg lvl xs p H.cv1) H.w1 (osHPending cfg lvl xs p H.cv1 ++
    [(osHEnf cfg lvl xs p H, [osHC cfg lvl xs p 0, osHEnf cfg lvl xs p H + osHC cfg lvl xs p 1, osHC cfg lvl xs p 1],
      fun x ↦ inducedWeight (cfg.lv lvl).logCols (osHQs cfg lvl xs p H.cv1)
        (powers (osHLam cfg lvl xs p H.cv1) (osHQs cfg lvl xs p H.cv1).length) x)])

/-- The roots after the level. -/
def osHRootsEnd (roots : List (Digest × ℕ × ℕ)) (H : OsLvH) : List (Digest × ℕ × ℕ) :=
  if lvl = cfg.yrLevel then roots
  else roots ++ [(H.root, (cfg.lv (lvl + 1)).depth, 3 * 2 ^ (cfg.lv (lvl + 1)).folds)]

/-- What the run of level `lvl` from `p` words says of its data. -/
structure OsLvOk (μ : ℕ) (L : Whir.Level) (cv : Digest) (w : WhirState) (osp : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (H : OsLvH) : Prop where
  folds : Runs (foldRounds L.fold w []) ⟨cv, xs.drop p, osp, roots⟩ (H.w1, H.chs)
    ⟨H.cv1, xs.drop (osHP1 cfg lvl p), osp, roots⟩
  len : osHPEnd cfg lvl p ≤ xs.length
  root : lvl ≠ cfg.yrLevel → digestOfScalars (osHW cfg lvl xs p 0, osHW cfg lvl xs p 1) = some H.root
  pow : powOk Whir.queryGrindingBits (osHNonce cfg lvl xs p)
    (gcDigest (osHCv2 cfg lvl xs p H.cv1) (osHNonce cfg lvl xs p)) = true
  open_ : ∃ rt hh ww, (osHRootsEnd cfg lvl roots H)[lvl]? = some (rt, hh, ww) ∧
    openAll (m := Id) blake2sBytes rt hh ww (osHQs cfg lvl xs p H.cv1) osp = some (H.rows, H.osq)
  w1len : H.w1.folds.length = osLevelF cfg lvl
  chs : H.w1.folds = w.folds ++ H.chs ∧ H.chs.length = (cfg.lv lvl).folds

end

@[expose] public section

/-! ## The stream -/

theorem os_foldRounds_st : ∀ {n : ℕ} {w : WhirState} {lf xs : List E} {p : ℕ} {cv : Digest}
    {osp : List Opening} {roots : List (Digest × ℕ × ℕ)} {res : WhirState × List E} {s' : St},
    Runs (foldRounds n w lf) ⟨cv, xs.drop p, osp, roots⟩ res s' →
      s'.stream = xs.drop (p + 2 * n) ∧ s'.openings = osp ∧ s'.roots = roots ∧
        (n = 0 ∨ p + 2 * n ≤ xs.length)
  | 0, w, lf, xs, p, cv, osp, roots, res, s', h => by
    obtain ⟨rfl, rfl⟩ := os_inv_pure h
    exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | n + 1, w, lf, xs, p, cv, osp, roots, res, s', h => by
    rw [foldRounds_succ] at h
    obtain ⟨⟨ch, t, q'⟩, sp1, h1, h2⟩ := os_inv_bind h
    obtain ⟨d0, d2, rest, hs, -, hsp1⟩ := os_runs_foldStep h1
    simp only at hs
    have hlen := congrArg List.length hs
    simp only [List.length_drop, List.length_cons] at hlen
    obtain ⟨-, -, hrest⟩ := os_drop_cons2 hs
    subst hsp1 hrest
    obtain ⟨e1, e2, e3, e4⟩ := os_foldRounds_st h2
    refine ⟨by rw [e1]; ring_nf, e2, e3, Or.inr ?_⟩
    omega

theorem os_drop_append {xs ys rest : List E} {p : ℕ} (h : xs.drop p = ys ++ rest) :
    ys = (xs.drop p).take ys.length ∧ rest = xs.drop (p + ys.length) ∧
      (0 < ys.length → p + ys.length ≤ xs.length) := by
  have hl := congrArg List.length h
  simp only [List.length_drop, List.length_append] at hl
  refine ⟨by rw [h, List.take_left' rfl], by rw [← List.drop_drop, h, List.drop_left' rfl], fun h0 => by omega⟩

/-! ## The inversion -/

/-- **A level's queries, inverted** (V:1737-1749): the nonce, the positions, `lam`, the openings and
the intro, from `p2` words of `xs`. -/
theorem os_lq_inv {ml idx nsq depth nq : ℕ} {L : Whir.Level} {lf : List E} {w1 : WhirState}
    {pend : List (E × List E × (List E → E))} (hdq : ml + L.logInvRate = depth) (hnq : L.queries = nq)
    (hper : 0 < 192 / depth) (hs1 : nq ≤ nsq * (192 / depth))
    (hs2 : (nsq - 1) * (192 / depth) < nq ∨ nsq = 0) (hs3 : nsq ≤ nq)
    {cv2 : Digest} {xs : List E} {p2 : ℕ} {op : List Opening} {ro : List (Digest × ℕ × ℕ)} {w' : WhirState}
    {s3 : St} (h : Runs (osLevelQueries ml idx L lf w1 pend) ⟨cv2, xs.drop p2, op, ro⟩ w' s3) :
    let n := xs.getD p2 0
    let cv3 := absorbCv cv2 n 4
    let qs := (List.range nq).map (osPosOf depth cv3)
    let cv4 := (sqAll nsq cv3).2
    let lam := challengeOf (sqCv cv4)
    let c0 := xs.getD (p2 + 1) 0
    let c2 := xs.getD (p2 + 2) 0
    p2 + 3 ≤ xs.length ∧ powOk Whir.queryGrindingBits n (gcDigest cv2 n) = true ∧
      ∃ (rows : List (List K)) (osq : List Opening) (rt : Digest) (hh ww : ℕ), ro[idx]? = some (rt, hh, ww) ∧
        openAll (m := Id) blake2sBytes rt hh ww qs op = some (rows, osq) ∧
        w' = glue lam w1 (pend ++ [(enforcedSum (if idx = 0 then rows.map fun row ↦ row.reverse.map ofK
            else rows.map extRow) lf (powers lam qs.length),
          [c0, enforcedSum (if idx = 0 then rows.map fun row ↦ row.reverse.map ofK else rows.map extRow) lf
            (powers lam qs.length) + c2, c2], fun x ↦ inducedWeight ml qs (powers lam qs.length) x)]) ∧
        s3 = ⟨obsCv (obsCv (sqCv cv4) c0) c2, xs.drop (p2 + 3), osq, ro⟩ ∧
        queriesOf (osLevelQueries ml idx L lf w1 pend) ⟨cv2, xs.drop p2, op, ro⟩ = [(hh, qs.zip op)] := by
  subst hdq hnq
  intro n cv3 qs cv4 lam c0 c2
  simp only [osLevelQueries] at h
  obtain ⟨u, sA, hA, h1⟩ := os_inv_bind h
  obtain ⟨n', rA, hsA, hpow, rfl⟩ := os_inv_grindP hA
  simp only at hsA
  obtain ⟨hn, hrA⟩ := os_drop_cons hsA
  subst hrA hn
  have hlenA := congrArg List.length hsA
  simp only [List.length_drop, List.length_cons] at hlenA
  obtain ⟨qs', sB, hB, h2⟩ := os_inv_bind h1
  obtain ⟨rfl, rfl⟩ := os_runs_det (rest := xs.drop (p2 + 1)) hB
    (os_runsTo_sampleQueries hper hs1 hs2 hs3 _) rfl
  obtain ⟨lam', sC, hC, h3⟩ := os_inv_bind h2
  obtain ⟨rfl, rfl⟩ := os_inv_sampleE hC
  obtain ⟨words, sD, hD, h4⟩ := os_inv_bind h3
  obtain ⟨rt, hh, ww, osq, hr, hoa, rfl⟩ := os_inv_queryP hD
  obtain ⟨intro, sE, hE, h5⟩ := os_inv_bind h4
  obtain ⟨d0, d2, rE, hsE, rfl, rfl⟩ := os_inv_roundPoly3 hE
  simp only at hsE
  have hlenE := congrArg List.length hsE
  simp only [List.length_drop, List.length_cons] at hlenE
  obtain ⟨hd0, hd2, hrE⟩ := os_drop_cons2 hsE
  obtain ⟨rfl, rfl⟩ := os_inv_ret h5
  subst hrE
  refine ⟨by omega, hpow, words, osq, rt, hh, ww, hr, hoa, ?_, ?_, ?_⟩
  · dsimp only; rw [← hd0, ← hd2, show p2 + 1 + 1 = p2 + 2 by ring]
  · dsimp only; rw [← hd0, ← hd2, show p2 + 1 + 1 = p2 + 2 by ring, show p2 + 1 + 2 = p2 + 3 by ring]
  · simp only [osLevelQueries, prog_bind_eq]
    rw [os_queriesOf_bind _ _ _ hA, os_queriesOf_noQ (Prog.grindP _) trivial, List.nil_append,
      os_queriesOf_bind _ _ _ hB, os_queriesOf_noQ (sampleQueries _ _) (os_noQ_sampleQueriesAux _ _ _),
      List.nil_append,
      os_queriesOf_bind _ _ _ hC, os_queriesOf_noQ Prog.sampleE (fun _ => trivial), List.nil_append,
      os_queriesOf_bind _ _ _ hD, os_queriesOf_queryP hr hoa,
      os_queriesOf_bind _ _ _ hE, os_queriesOf_noQ _ (os_noQ_roundPoly3 _), List.nil_append]
    rfl


theorem os_noQ_levelMid (ml : ℕ) (rest : List Whir.Level) : osNoQ (osLevelMid ml rest) := by
  cases rest with
  | nil =>
    simp only [osLevelMid, prog_bind_eq]
    exact os_noQ_bind _ _ (os_noQ_readN _) fun _ => trivial
  | cons next rest =>
    simp only [osLevelMid, prog_bind_eq]
    exact os_noQ_bind _ _ trivial fun _ => os_noQ_bind _ _ (os_noQ_sampleN _) fun _ =>
      os_noQ_bind _ _ (fun _ => trivial) fun _ => os_noQ_bind _ _ (os_noQ_roundPoly3 _) fun _ => trivial

/-- A level's query steps: its queries', then the rest's. -/
theorem os_qOf_level {μ lane lvl ml : ℕ} {L : Whir.Level} {rest : List Whir.Level} {w w1 w' : WhirState}
    {lf res : List E} {pend : List (E × List E × (List E → E))} {st st1 st2 st3 : St}
    (h1 : Runs (foldRounds L.fold w []) st (w1, lf) st1) (hml : μ - w1.folds.length = ml)
    (h3 : Runs (osLevelMid ml rest) st1 (res, pend) st2)
    (h5 : Runs (osLevelQueries ml lvl L lf w1 pend) st2 w' st3) :
    queriesOf (whirLevelsOpen μ lane lvl (L :: rest) w) st = queriesOf (osLevelQueries ml lvl L lf w1 pend) st2 ++
      queriesOf (match rest with
        | [] => osTailOpen ml lane w' res
        | _ :: _ => whirLevelsOpen μ lane (lvl + 1) rest w') st3 := by
  rw [os_whirLevelsOpen_cons, prog_bind_eq, os_queriesOf_bind _ _ _ h1,
    os_queriesOf_noQ _ (os_noQ_foldRounds _ _ _), List.nil_append]
  dsimp only
  rw [hml, prog_bind_eq, os_queriesOf_bind _ _ _ h3, os_queriesOf_noQ _ (os_noQ_levelMid _ _), List.nil_append]
  dsimp only
  rw [prog_bind_eq, os_queriesOf_bind _ _ _ h5]
  cases rest <;> rfl

/-- **A level of the run, inverted**: one level of `whirLevelsOpen` from `p` words of `xs` has its
data `H` (`OsLvOk`), and the rest of the run continues from the level's end. -/
theorem os_level_inv {cfg : OsCfg} {μ lane lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {w : WhirState} (hfl : w.folds.length = (cfg.lv lvl).foldsOff)
    {cv : Digest} {xs : List E} {p : ℕ} {osp : List Opening} {roots : List (Digest × ℕ × ℕ)}
    (hrl : lvl < roots.length) {e : WhirEnd} {sp' : St}
    (h : Runs (whirLevelsOpen μ lane lvl (L :: rest) w) ⟨cv, xs.drop p, osp, roots⟩ e sp') :
    ∃ H : OsLvH, OsLvOk cfg lvl xs p μ L cv w osp roots H ∧
      (rest = [] → Runs (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEnd cfg lvl xs p H) (osHMs cfg lvl xs p))
        ⟨osHCvEnd cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩ e sp') ∧
      (rest ≠ [] → Runs (whirLevelsOpen μ lane (lvl + 1) rest (osHWEnd cfg lvl xs p H))
        ⟨osHCvEnd cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, osHRootsEnd cfg lvl roots H⟩ e sp') ∧
      ∃ rt hh ww, (osHRootsEnd cfg lvl roots H)[lvl]? = some (rt, hh, ww) ∧
        (rest = [] → queriesOf (whirLevelsOpen μ lane lvl (L :: rest) w) ⟨cv, xs.drop p, osp, roots⟩ =
          (hh, (osHQs cfg lvl xs p H.cv1).zip osp) ::
            queriesOf (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEnd cfg lvl xs p H) (osHMs cfg lvl xs p))
              ⟨osHCvEnd cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩) ∧
        (rest ≠ [] → queriesOf (whirLevelsOpen μ lane lvl (L :: rest) w) ⟨cv, xs.drop p, osp, roots⟩ =
          (hh, (osHQs cfg lvl xs p H.cv1).zip osp) ::
            queriesOf (whirLevelsOpen μ lane (lvl + 1) rest (osHWEnd cfg lvl xs p H))
              ⟨osHCvEnd cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, osHRootsEnd cfg lvl roots H⟩) := by
  obtain ⟨hf, hf0, hq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  rw [os_whirLevelsOpen_cons] at h
  obtain ⟨⟨w1, chs⟩, s1, h1, h2⟩ := os_inv_bind h
  obtain ⟨e1, e2, e3, e4⟩ := os_foldRounds_st h1
  obtain ⟨cv1, st1, op1, ro1⟩ := s1
  simp only at e1 e2 e3
  subst e1 e2 e3
  have hl1 := os_foldRounds_len _ _ _ _ _ _ h1
  obtain ⟨chs', hF1, hF2, hFl⟩ := os_foldRounds_folds h1
  simp only [List.nil_append] at hF1 hF2 hl1
  subst hF2
  have hw1l : w1.folds.length = osLevelF cfg lvl := by rw [hl1, hfl, osLevelF, hf]
  have hml : μ - w1.folds.length = (cfg.lv lvl).logCols := by rw [hw1l, hlc]
  dsimp only at h2
  rw [hml] at h2
  obtain ⟨⟨res, pend⟩, s2, h3, h4⟩ := os_inv_bind h2
  have h3o := h3
  have hd' : (cfg.lv lvl).logCols + L.logInvRate = (cfg.lv lvl).depth := by rw [hdep, hlc]
  have eP1 : osHP1 cfg lvl p = p + 2 * L.fold := by simp only [osHP1, hf]
  have hfolds : w1.folds = w.folds ++ chs ∧ chs.length = (cfg.lv lvl).folds := by
    refine ⟨hF1, ?_⟩
    have := congrArg List.length hF1
    simp only [List.length_append] at this
    omega
  cases rest with
  | nil =>
    have hyl : lvl = cfg.yrLevel := hlast.mp rfl
    have hyr' : cfg.yrLen = 2 ^ (cfg.lv lvl).logCols := by rw [hyr rfl, hlc]
    simp only [osLevelMid] at h3
    obtain ⟨res', sM, hM, hM2⟩ := os_inv_bind h3
    obtain ⟨hb, rfl⟩ := os_inv_pure hM2
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨hmsl, r, hsM, rfl⟩ := os_inv_readN hM
    simp only at hsM
    obtain ⟨hms, hr, hlenM⟩ := os_drop_append hsM
    subst hr
    have eP2 : p + 2 * L.fold + res.length = osHP2 cfg lvl p := by
      rw [osHP2, eP1, ite_pos' hyl, hmsl, hyr']
    have eMs : res = osHMs cfg lvl xs p := by rw [osHMs, eP1, hyr', ← hmsl]; exact hms
    have eCv2 : obsAll cv1 res = osHCv2 cfg lvl xs p cv1 := by rw [osHCv2, ite_pos' hyl, eMs]
    rw [eP2, eCv2] at h4 h3o
    simp only at h4
    obtain ⟨w', s3, h5, h6⟩ := os_inv_bind h4
    obtain ⟨hlen, hpow, rows, osq, rt, hh, ww, hro, hoa, rfl, rfl, hqs⟩ := os_lq_inv (nsq := (cfg.lv lvl).squeezes)
      hd' hq.symm hper hs1 hs2 hs3 h5
    have hqo := os_qOf_level (lane := lane) h1 hml h3o h5
    refine ⟨⟨w1, chs, cv1, default, rows, osq⟩, ⟨by rw [eP1]; exact h1, hlen, fun h' => absurd hyl h', hpow,
      ⟨rt, hh, ww, by simp only [osHRootsEnd, ite_pos' hyl]; exact hro, hoa⟩, hw1l, hfolds⟩, fun _ => ?_,
      fun h' => absurd rfl h', rt, hh, ww, by simp only [osHRootsEnd, ite_pos' hyl]; exact hro, fun _ => ?_,
      fun h' => absurd rfl h'⟩
    swap
    · rw [hqo, hqs, List.singleton_append, ← eMs, ← hlc]
      congr 2
      simp only [osHWEnd, osHPending, ite_pos' hyl, List.nil_append, osHEnf, osHRowsE, osHQs, osHLam, osHCv4,
        osHCv3, osHNonce, osHC]
    rw [← eMs, ← hlc]
    convert h6 using 2
    all_goals try rfl
    simp only [osHWEnd, osHPending, ite_pos' hyl, List.nil_append, osHEnf, osHRowsE, osHQs, osHLam, osHCv4, osHCv3,
      osHNonce, osHC]
  | cons next rest' =>
    have hyl : lvl ≠ cfg.yrLevel := fun h' => absurd (hlast.mpr h') (by simp)
    obtain ⟨hood, hfo', hfl', hdep'⟩ := hnext next rfl
    simp only [osLevelMid, levelShape] at h3
    obtain ⟨u, sA, hA, h3⟩ := os_inv_bind h3
    obtain ⟨x0, x1, rA, root, hsA, hroot, rfl⟩ := os_inv_commitP hA
    simp only at hsA
    obtain ⟨hx0, hx1, rfl⟩ := os_drop_cons2 hsA
    obtain ⟨z, sB, hB, h3⟩ := os_inv_bind h3
    obtain ⟨rfl, rfl⟩ := os_inv_sampleN hB
    obtain ⟨y, sC, hC, h3⟩ := os_inv_bind h3
    obtain ⟨rC, hsC, rfl⟩ := os_inv_readE hC
    simp only at hsC
    obtain ⟨hy, rfl⟩ := os_drop_cons hsC
    obtain ⟨intro, sD, hD, h3⟩ := os_inv_bind h3
    obtain ⟨c0o, c2o, rD, hsD, rfl, rfl⟩ := os_inv_roundPoly3 hD
    simp only at hsD
    obtain ⟨hc0, hc2, rfl⟩ := os_drop_cons2 hsD
    obtain ⟨hb, rfl⟩ := os_inv_pure h3
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have eW : ∀ i, osHW cfg lvl xs p i = xs.getD (p + 2 * L.fold + i) 0 := fun i => by rw [osHW, eP1]
    have e0 : x0 = osHW cfg lvl xs p 0 := by rw [eW, Nat.add_zero, hx0]
    have e1 : x1 = osHW cfg lvl xs p 1 := by rw [eW, hx1]
    have e2 : y = osHW cfg lvl xs p 2 := by rw [eW, ← hy]
    have e3 : c0o = osHW cfg lvl xs p 3 := by rw [eW, ← hc0]
    have e4 : c2o = osHW cfg lvl xs p 4 := by rw [eW, ← hc2]
    have eP2 : p + 2 * L.fold + 2 + 1 + 2 = osHP2 cfg lvl p := by rw [osHP2, eP1, ite_neg' hyl]
    have eCv2 : obsCv (obsCv (obsCv (sqAll (cfg.lv lvl).logCols (obsCv (obsCv cv1 x0) x1)).2 y) c0o) c2o =
        osHCv2 cfg lvl xs p cv1 := by rw [osHCv2, ite_neg' hyl, osHCv12, e0, e1, e2, e3, e4]
    rw [eP2, eCv2] at h4 h3o
    simp only at h4
    obtain ⟨w', s3, h5, h6⟩ := os_inv_bind h4
    obtain ⟨hlen, hpow, rows, osq, rt, hh, ww, hro, hoa, rfl, rfl, hqs⟩ := os_lq_inv (nsq := (cfg.lv lvl).squeezes)
      hd' hq.symm hper hs1 hs2 hs3 h5
    have hqo := os_qOf_level (lane := lane) h1 hml h3o h5
    have eRoots : ro1 ++ [(root, (cfg.lv lvl).logCols - next.fold + next.logInvRate, 3 * 2 ^ next.fold)] =
        osHRootsEnd cfg lvl ro1 ⟨w1, chs, cv1, root, rows, osq⟩ := by
      rw [osHRootsEnd, ite_neg' hyl, hdep', hfl', hlc]
    refine ⟨⟨w1, chs, cv1, root, rows, osq⟩, ⟨by rw [eP1]; exact h1, hlen, fun _ => by rw [← e0, ← e1]; exact hroot,
      hpow, ⟨rt, hh, ww, by rw [← eRoots]; exact hro, hoa⟩, hw1l, hfolds⟩, fun h' => absurd h' (by simp),
      fun _ => ?_, rt, hh, ww, by rw [← eRoots]; exact hro, fun h' => absurd h' (by simp), fun _ => ?_⟩
    swap
    · rw [hqo, hqs, List.singleton_append, ← eRoots]
      congr 2
      simp only [osHWEnd, osHPending, ite_neg' hyl, osHEnf, osHRowsE, osHQs, osHLam, osHCv4, osHCv3,
        osHNonce, osHC, osHCv12, ← e0, ← e1, ← e2, ← e3, ← e4, List.singleton_append]
    rw [← eRoots]
    convert h6 using 2
    all_goals try rfl
    simp only [osHWEnd, osHPending, ite_neg' hyl, osHEnf, osHRowsE, osHQs, osHLam, osHCv4, osHCv3,
      osHNonce, osHC, osHCv12, ← e0, ← e1, ← e2, ← e3, ← e4, List.singleton_append]

end
end LeanVM.Guest.B1
