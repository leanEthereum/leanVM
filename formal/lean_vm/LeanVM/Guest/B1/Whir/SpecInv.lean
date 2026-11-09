/-
  LeanVM.Guest.B1.Whir.SpecInv

  An accepting run of `whirOpenNZ`, level by level, backwards: the head, a level that is not the
  last, the last level with its tail.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.SpecLevel
public import LeanVM.Guest.B1.Whir.SpecQS
public import LeanVM.Protocol.WithHash

/-!
# The run, level by level

* `head_inv`: the run reads the first quadratic's two words `c0, c2` and runs the levels from the
  sponge with them waiting, the state `⟨target, [c0, target + c2, c2], [], []⟩`.
* `level_nf_inv`: a level that is not the last reads the words `L.words` and the openings `L.os`
  of some `L : SpLv` with `L.Ok`, and the run goes on from `L.Fend`, `L.wsEnd`, its next
  commitment read.
* `level_fin_inv`: the last level the same, then its tail rounds (`tailTr`), the end `w`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem foldsTr_take : ∀ (n : ℕ) (F : Fs) (q : List E) (t : E) (xs : List E),
    foldsTr n F q t (xs.take (2 * n)) = foldsTr n F q t xs
  | 0, _, _, _, _ => rfl
  | n + 1, F, q, t, xs => by
    match xs with
    | [] => rfl
    | [x] =>
      simp only [foldsTr, show 2 * (n + 1) = 2 * n + 2 by ring, List.take_succ_cons,
        List.take_nil, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, List.drop_succ_cons,
        List.drop_nil]
    | x0 :: x1 :: xs =>
      simp only [foldsTr, show 2 * (n + 1) = 2 * n + 2 by ring, List.take_succ_cons,
        List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]
      rw [foldsTr_take n]

theorem take_append_drop' (xs : List E) (n : ℕ) : xs = xs.take n ++ xs.drop n :=
  (List.take_append_drop n xs).symm

/-- The query steps of a level's queries and intro: the query, then the continuation's. -/
theorem rest_qs {β : Type} {ml index : ℕ} {level : Whir.Level} {lf : List E} {ws1 : WhirStateT}
    {pending : List (E × List E × (List E → E))} {F2 : Fs} {R : List (Digest × ℕ × ℕ)}
    (hd : 1 ≤ 192 / (ml + level.logInvRate)) {K : WhirStateT → VerifierProgram β}
    {osL : List Opening} {osR : List (List Opening)} {ic0 ic2 : E} {xsR : List E} {root : Digest} {height width : ℕ}
    (hlam : (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1 ≠ 0)
    (hR : R[index]? = some (root, height, width))
    (hol : osL.length = (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
      (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1 level.queries).length)
    (hok : ∀ k (hk : k < (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
      (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1 level.queries).length)
      (ho : k < osL.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width
        (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
          (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1
          level.queries)[k] osL[k]) = true)
    (hidx : osL.map Opening.leafIndex = queriesOf (192 / (ml + level.logInvRate))
      (ml + level.logInvRate) (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1
      level.queries) :
    queryStepsOf ((sampleQueries (ml + level.logInvRate) level.queries).bind fun queries ↦
      VerifierProgram.sampleChallenge.bind fun lam ↦ (VerifierProgram.require (lam ≠ 0)).bind
          fun _ ↦
        (VerifierProgram.queryOpenings index queries).bind fun words ↦
          (sumcheckRoundPoly 3 (enforcedSum (if index = 0 then words.map fun row ↦ row.reverse.map ofK
            else words.map extRow) lf (powers lam queries.length)) none).bind fun intro ↦
            K (glueT lam ws1 (pending ++ [(enforcedSum (if index = 0 then
              words.map fun row ↦ row.reverse.map ofK else words.map extRow) lf
              (powers lam queries.length), intro,
              fun x ↦ inducedWeight ml queries (powers lam queries.length) x)])))
      ⟨F2, ic0 :: ic2 :: xsR, osL :: osR, R⟩ =
      (height, (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
          (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1
          level.queries).zip osL) ::
        queryStepsOf (K (glueT (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1
          ws1 (pending ++ [(enforcedSum (if index = 0 then
          (osL.map (·.leaf)).map fun row ↦ row.reverse.map ofK else (osL.map (·.leaf)).map extRow)
          lf (powers (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1
            (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
              (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1
              level.queries).length),
          [ic0, enforcedSum (if index = 0 then
            (osL.map (·.leaf)).map fun row ↦ row.reverse.map ofK else (osL.map (·.leaf)).map extRow)
            lf (powers (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1
              (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
                (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1
                level.queries).length) + ic2, ic2],
          fun x ↦ inducedWeight ml (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
              (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1 level.queries)
            (powers (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1
              (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
                (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1
                level.queries).length) x)])))
        ⟨foldStep (F2.squeezeN (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2 ic0 ic2,
          xsR, osR, R⟩ := by
  rw [qs_sampleQueries_bind hd, qs_sampleE_bind, qs_require_bind _ _ hlam,
    qs_queryP_bind _ _ _ _ _ _ hR (openPhase_eq_leaves keccak256 hol hok hidx), sumcheck3_bind,
    qs_readE_bind, qs_readE_bind, squeeze_absorb_two]

/-- **The head**: the first quadratic, then the levels. -/
theorem head_inv {μ r : ℕ} {target : E} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {res : WhirEnd × FSt}
    (h : runF (whirOpenNZ μ r target) ⟨F, xs, os, R⟩ = some res) :
    ∃ (cfg : List Whir.Level) (c0 c2 : E) (xs' : List E), Whir.ladder μ r = some cfg ∧
      xs = c0 :: c2 :: xs' ∧
      runF (whirLevelsOpenNZ μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [c0, target + c2, c2],
        [], []⟩) ⟨(F.absorb c0 dsObserve).absorb c2 dsObserve, xs', os, R⟩ = some res ∧
      queryStepsOf (whirOpenNZ μ r target) ⟨F, xs, os, R⟩ =
        queryStepsOf (whirLevelsOpenNZ μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg
          ⟨target, [c0, target + c2, c2], [], []⟩)
          ⟨(F.absorb c0 dsObserve).absorb c2 dsObserve, xs', os, R⟩ := by
  simp only [whirOpenNZ, VerifierProgram.bind_eq] at h
  cases hc : Whir.ladder μ r with
  | none => simp [hc, Verifier.liftOption, VerifierProgram.bind, runF] at h
  | some cfg =>
    simp only [hc, Verifier.liftOption, VerifierProgram.ret_bind] at h
    rw [sumcheck3_bind] at h
    obtain ⟨c0, xs1, hx1, h1⟩ := runF_readE_bind h
    obtain ⟨c2, xs2, hx2, h2⟩ := runF_readE_bind h1
    subst hx1 hx2
    refine ⟨cfg, c0, c2, xs2, rfl, rfl, h2, ?_⟩
    simp only [whirOpenNZ, VerifierProgram.bind_eq, hc, Verifier.liftOption,
        VerifierProgram.ret_bind, sumcheck3_bind]
    rfl

/-- **A level that is not the last, backwards.** -/
theorem level_nf_inv {logN lane index : ℕ} {level next : Whir.Level} {rest : List Whir.Level}
    {ws : WhirStateT} {F : Fs} {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
    {res : WhirEnd × FSt} (hF : F.pend.length = 2) (hR : index < R.length)
    (hml : 1 ≤ logN - (ws.folds.length + level.fold))
    (hd : 1 ≤ 192 / (logN - (ws.folds.length + level.fold) + level.logInvRate))
    (h : runF (whirLevelsOpenNZ logN lane index (level :: next :: rest) ws) ⟨F, xs, os, R⟩ =
      some res) :
    ∃ (L : SpLv) (d : Digest) (xsR : List E) (osR : List (List Opening)),
      L.logN = logN ∧ L.index = index ∧ L.level = level ∧ L.fin = false ∧ L.ws = ws ∧ L.F = F ∧
      L.Ok R d ∧ xs = L.words ++ xsR ∧ os = L.os :: osR ∧
      runF (whirLevelsOpenNZ logN lane (index + 1) (next :: rest) L.wsEnd)
        ⟨L.Fend, xsR, osR, R ++ [(d, levelShape L.ml next (3 * 2 ^ next.fold))]⟩ = some res ∧
      queryStepsOf (whirLevelsOpenNZ logN lane index (level :: next :: rest) ws) ⟨F, xs, os, R⟩ =
          (L.height, L.qs.zip L.os) :: queryStepsOf (whirLevelsOpenNZ logN lane (index + 1)
            (next :: rest) L.wsEnd)
            ⟨L.Fend, xsR, osR, R ++ [(d, levelShape L.ml next (3 * 2 ^ next.fold))]⟩ := by
  rw [whirLevelsOpenNZ] at h
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq] at h
  obtain ⟨hl, hnz, h1⟩ := foldsNZ_inv _ _ _ _ _ _ _ _ h
  simp only [VerifierProgram.ret_bind, List.nil_append] at h1
  have hF1 : (foldsTr level.fold F ws.quad ws.target xs).1.pend.length = 2 :=
    foldsTr_pend _ _ _ _ _ hF
  have hfl : (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length =
      ws.folds.length + level.fold := by
    rw [List.length_append, foldsTr_chs_length]
  obtain ⟨ra, rb, xs2, d, hx2, hdig, h2⟩ := runF_commitP_bind h1
  rw [absorb_two hF1, runF_sampleN_bind, squeezeN_cF1 _ _ (by rw [hfl]; exact hml)] at h2
  obtain ⟨y, xs3, hx3, h3⟩ := runF_readE_bind h2
  rw [sumcheck3_bind] at h3
  obtain ⟨c0, xs4, hx4, h4⟩ := runF_readE_bind h3
  obtain ⟨c2, xs5, hx5, h5⟩ := runF_readE_bind h4
  obtain ⟨nonce, xs6, hx6, hpow, h6⟩ := runF_grindP_bind h5
  rw [absorb_four] at hpow h6
  have hd' : 1 ≤ 192 / (logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length +
      level.logInvRate) := by
    rw [hfl]; exact hd
  obtain ⟨osL, osR, ic0, ic2, xsR, root, height, width, eos, hx7, hlam, hroot, hol, hok, hidx, h7⟩ :=
    rest_inv hd' h6
  subst hx3 hx4 hx5 hx6 hx7
  set L : SpLv := ⟨logN, index, level, false, ws, F, xs.take (2 * level.fold), ra, rb, y, c0, c2,
    [], nonce, osL, ic0, ic2, root, height, width⟩ with hL
  have eTr : L.tr = foldsTr level.fold F ws.quad ws.target xs := foldsTr_take _ _ _ _ _
  have eChs : L.chs = (foldsTr level.fold F ws.quad ws.target xs).2.1 := by rw [SpLv.chs, eTr]
  have eF1 : L.F1 = (foldsTr level.fold F ws.quad ws.target xs).1 := by rw [SpLv.F1, eTr]
  have eWs1 : L.ws1 = { ws with
      target := (foldsTr level.fold F ws.quad ws.target xs).2.2.2
      quad := (foldsTr level.fold F ws.quad ws.target xs).2.2.1
      folds := ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1 } := by
    rw [SpLv.ws1, eTr, eChs]
  have eMl : L.ml = logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length := by
    rw [SpLv.ml, eWs1]
  have eF2 : L.F2 = ⟨capOf (cF2 (foldsTr level.fold F ws.quad ws.target xs).1 ra rb
      (logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length) y c0 c2
      nonce).perm, []⟩ := by
    rw [SpLv.F2, ← eF1, ← eMl]
    rfl
  have eD : L.D = logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length +
      level.logInvRate := by rw [SpLv.D, eMl]
  have eNsq : L.nsq = ceilDiv level.queries (192 / (logN - (ws.folds ++
      (foldsTr level.fold F ws.quad ws.target xs).2.1).length + level.logInvRate)) := by
    rw [SpLv.nsq, eD]
  have eQs : L.qs = queriesOf (192 / (logN - (ws.folds ++
      (foldsTr level.fold F ws.quad ws.target xs).2.1).length + level.logInvRate))
      (logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length +
        level.logInvRate)
      ((Fs.squeezeN (ceilDiv level.queries (192 / (logN - (ws.folds ++
        (foldsTr level.fold F ws.quad ws.target xs).2.1).length + level.logInvRate)))
        ⟨capOf (cF2 (foldsTr level.fold F ws.quad ws.target xs).1 ra rb
          (logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length) y c0 c2
          nonce).perm, []⟩).1) level.queries := by
    rw [SpLv.qs, eD, eF2, eNsq]
  have eLam : L.lam = (Fs.squeezeN (ceilDiv level.queries (192 / (logN - (ws.folds ++
        (foldsTr level.fold F ws.quad ws.target xs).2.1).length + level.logInvRate)))
        ⟨capOf (cF2 (foldsTr level.fold F ws.quad ws.target xs).1 ra rb
          (logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length) y c0 c2
          nonce).perm, []⟩).2.squeeze.1 := by
    rw [SpLv.lam, eF2, eNsq]
  have ePend : L.pending = [(y, [c0, y + c2, c2], fun x ↦ eqEval (oodZ
      (foldsTr level.fold F ws.quad ws.target xs).1 ra rb
      (logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length)) x)] := by
    rw [SpLv.pending, ← eF1, ← eMl]
    rfl
  have eEnf : L.enforced = enforcedSum L.rows (foldsTr level.fold F ws.quad ws.target xs).2.1
      (powers L.lam L.qs.length) := by
    rw [SpLv.enforced, eChs]
  have eWsEnd : L.wsEnd = glueT L.lam L.ws1 (L.pending ++ [(L.enforced,
      [ic0, L.enforced + ic2, ic2], fun x ↦ inducedWeight L.ml L.qs (powers L.lam L.qs.length) x)]) :=
    rfl
  have eFend : L.Fend = foldStep (Fs.squeezeN (ceilDiv level.queries (192 / (logN - (ws.folds ++
        (foldsTr level.fold F ws.quad ws.target xs).2.1).length + level.logInvRate)))
        ⟨capOf (cF2 (foldsTr level.fold F ws.quad ws.target xs).1 ra rb
          (logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length) y c0 c2
          nonce).perm, []⟩).2 ic0 ic2 := by
    rw [SpLv.Fend, eF2, eNsq]
  refine ⟨L, d, xsR, osR, rfl, rfl, rfl, rfl, rfl, rfl, ⟨?_, ?_, fun _ ↦ hdig, fun _ ↦ ?_,
    fun h ↦ absurd h Bool.false_ne_true, fun h ↦ absurd h Bool.false_ne_true, ?_,
    by rw [List.getElem?_append_left hR] at hroot; exact hroot, by rw [eQs]; exact hol, ?_⟩, ?_, eos,
    ?_, ?_⟩
  · show (xs.take (2 * level.fold)).length = 2 * level.fold
    simp only [List.length_take]; omega
  · intro c hc; rw [eChs] at hc; exact hnz c hc
  · rw [eF1, eMl]; exact hpow
  · rw [eLam]; exact hlam
  · rw [eQs]
    exact hok
  · show xs = (xs.take (2 * level.fold) ++ (if false = true then [] ++ [nonce] else
      [ra, rb, y, c0, c2, nonce]) ++ [ic0, ic2]) ++ xsR
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [← hx2, List.take_append_drop]
  · rw [eWsEnd, eFend, eEnf, eLam, eWs1, ePend, eQs, eMl]
    exact h7
  · rw [eWsEnd, eFend, eEnf, eLam, eWs1, ePend, eQs, eMl]
    rw [whirLevelsOpenNZ]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    rw [qs_folds _ _ _ _ _ _ _ hl hnz]
    simp only [VerifierProgram.ret_bind, List.nil_append]
    rw [hx2, qs_commitP_bind _ _ _ _ _ _ _ hdig, absorb_two hF1, qs_sampleN_bind,
      squeezeN_cF1 _ _ (by rw [hfl]; exact hml), qs_readE_bind, sumcheck3_bind, qs_readE_bind,
      qs_readE_bind, qs_grindP_bind _ _ _ _ _ _ (by rw [absorb_four]; exact hpow), absorb_four, eos]
    exact rest_qs hd' hlam hroot hol hok hidx

/-- **The last level, backwards**: its words and openings, then its tail rounds and the end. -/
theorem level_fin_inv {logN lane index : ℕ} {level : Whir.Level} {ws : WhirStateT} {F : Fs}
    {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {res : WhirEnd × FSt}
    (hd : 1 ≤ 192 / (logN - (ws.folds.length + level.fold) + level.logInvRate))
    (h : runF (whirLevelsOpenNZ logN lane index [level] ws) ⟨F, xs, os, R⟩ = some res) :
    ∃ (L : SpLv) (xsR : List E) (osR : List (List Opening)),
      L.logN = logN ∧ L.index = index ∧ L.level = level ∧ L.fin = true ∧ L.ws = ws ∧ L.F = F ∧
      L.Ok R (Vector.replicate 4 0) ∧ xs = L.words ++ xsR ∧ os = L.os :: osR ∧
      2 * (L.ml - 1) ≤ xsR.length ∧
      (∀ c ∈ (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1, c ≠ 0) ∧
      res = (⟨(L.wsEnd.folds ++ (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1).drop lane ++
          (L.wsEnd.folds ++ (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1).take lane,
        L.wsEnd.glued.foldl (fun weight claim ↦ weight + claim.scalar *
          claim.weightAt (L.wsEnd.folds.drop claim.foldStart ++
            (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1)) 0,
        multilinearEval L.ms (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.1,
        (tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).2.2⟩,
        ⟨(tailTr L.ml L.Fend L.wsEnd.quad L.wsEnd.target xsR).1,
          xsR.drop (2 * (L.ml - 1)), osR, R⟩) ∧
      queryStepsOf (whirLevelsOpenNZ logN lane index [level] ws) ⟨F, xs, os, R⟩ =
        [(L.height, L.qs.zip L.os)] := by
  rw [whirLevelsOpenNZ_last] at h
  simp only [VerifierProgram.bind_eq] at h
  obtain ⟨hl, hnz, h1⟩ := foldsNZ_inv _ _ _ _ _ _ _ _ h
  simp only at h1
  have hfl : (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length =
      ws.folds.length + level.fold := by
    rw [List.length_append, foldsTr_chs_length]
  obtain ⟨hml, h2⟩ := runF_readN_bind _ h1
  obtain ⟨nonce, xs3, hx3, hpow, h3⟩ := runF_grindP_bind h2
  have hd' : 1 ≤ 192 / (logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length +
      level.logInvRate) := by
    rw [hfl]; exact hd
  obtain ⟨osL, osR, ic0, ic2, xsR, root, height, width, eos, hx7, hlam, hroot, hol, hok, hidx, h7⟩ :=
    rest_inv' hd' h3
  subst hx7
  simp only [List.nil_append] at h7
  set ml := logN - (ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1).length with hmldef
  set ms := (List.drop (2 * level.fold) xs).take (2 ^ ml) with hms
  set L : SpLv := ⟨logN, index, level, true, ws, F, xs.take (2 * level.fold), 0, 0, 0, 0, 0,
    ms, nonce, osL, ic0, ic2, root, height, width⟩ with hL
  have eTr : L.tr = foldsTr level.fold F ws.quad ws.target xs := foldsTr_take _ _ _ _ _
  have eChs : L.chs = (foldsTr level.fold F ws.quad ws.target xs).2.1 := by rw [SpLv.chs, eTr]
  have eF1 : L.F1 = (foldsTr level.fold F ws.quad ws.target xs).1 := by rw [SpLv.F1, eTr]
  have eWs1 : L.ws1 = { ws with
      target := (foldsTr level.fold F ws.quad ws.target xs).2.2.2
      quad := (foldsTr level.fold F ws.quad ws.target xs).2.2.1
      folds := ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1 } := by
    rw [SpLv.ws1, eTr, eChs]
  have eMl : L.ml = ml := by rw [SpLv.ml, eWs1]
  have eF2 : L.F2 = ((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
      dsObserve).absorb nonce dsPowNonce).squeeze.2) := by
    rw [SpLv.F2, ← eF1]
    rfl
  have eD : L.D = ml + level.logInvRate := by rw [SpLv.D, eMl]
  have eNsq : L.nsq = ceilDiv level.queries (192 / (ml + level.logInvRate)) := by
    rw [SpLv.nsq, eD]
  have eQs : L.qs = queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
      ((((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
        dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
        (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1) level.queries := by
    rw [SpLv.qs, eD, eF2, eNsq]
  have eLam : L.lam = (((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
        dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
        (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1 := by
    rw [SpLv.lam, eF2, eNsq]
  have ePend : L.pending = [] := rfl
  have eEnf : L.enforced = enforcedSum L.rows (foldsTr level.fold F ws.quad ws.target xs).2.1
      (powers L.lam L.qs.length) := by
    rw [SpLv.enforced, eChs]
  have eWsEnd : L.wsEnd = glueT L.lam L.ws1 (L.pending ++ [(L.enforced,
      [ic0, L.enforced + ic2, ic2], fun x ↦ inducedWeight L.ml L.qs (powers L.lam L.qs.length) x)]) :=
    rfl
  have eFend : L.Fend = foldStep (((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
        dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
        (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2 ic0 ic2 := by
    rw [SpLv.Fend, eF2, eNsq]
  have eW : L.wsEnd = glueT (((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
        dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
        (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1
      { ws with
        target := (foldsTr level.fold F ws.quad ws.target xs).2.2.2
        quad := (foldsTr level.fold F ws.quad ws.target xs).2.2.1
        folds := ws.folds ++ (foldsTr level.fold F ws.quad ws.target xs).2.1 }
      [(enforcedSum (if index = 0 then (osL.map (·.leaf)).map fun row ↦ row.reverse.map ofK
            else (osL.map (·.leaf)).map extRow) (foldsTr level.fold F ws.quad ws.target xs).2.1
          (powers (((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
            dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
            (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1
            (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
              ((((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
                dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
                (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1)
              level.queries).length),
        [ic0, enforcedSum (if index = 0 then (osL.map (·.leaf)).map fun row ↦ row.reverse.map ofK
            else (osL.map (·.leaf)).map extRow) (foldsTr level.fold F ws.quad ws.target xs).2.1
          (powers (((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
            dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
            (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1
            (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
              ((((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
                dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
                (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1)
              level.queries).length) + ic2, ic2],
        fun x ↦ inducedWeight ml (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
              ((((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
                dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
                (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1)
              level.queries)
          (powers (((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
            dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
            (ceilDiv level.queries (192 / (ml + level.logInvRate)))).2.squeeze.1
            (queriesOf (192 / (ml + level.logInvRate)) (ml + level.logInvRate)
              ((((((foldsTr level.fold F ws.quad ws.target xs).1.absorbAll ms
                dsObserve).absorb nonce dsPowNonce).squeeze.2).squeezeN
                (ceilDiv level.queries (192 / (ml + level.logInvRate)))).1)
              level.queries).length) x)] := by
    rw [eWsEnd, eEnf, eLam, eWs1, ePend, eQs, eMl]
    rfl
  simp only [levelTailNZ, VerifierProgram.bind_eq, VerifierProgram.pure_eq] at h7
  obtain ⟨htl, htnz, h8⟩ := tailNZ_inv _ _ _ _ _ _ _ _ h7
  simp only at h8
  have hres := runF_ret_some h8
  refine ⟨L, xsR, osR, rfl, rfl, rfl, rfl, rfl, rfl, ⟨?_, ?_, fun h ↦ Bool.noConfusion h,
    fun h ↦ Bool.noConfusion h, fun _ ↦ ?_, fun _ ↦ ?_, ?_, hroot, by rw [eQs]; exact hol, ?_⟩, ?_,
    eos, ?_, ?_, ?_, ?_⟩
  · show (xs.take (2 * level.fold)).length = 2 * level.fold
    simp only [List.length_take]; omega
  · intro c hc; rw [eChs] at hc; exact hnz c hc
  · rw [eMl]
    show ((List.drop (2 * level.fold) xs).take (2 ^ ml)).length = 2 ^ ml
    simp only [List.length_take]; omega
  · rw [eF1]; exact hpow
  · rw [eLam]; exact hlam
  · rw [eQs]
    exact hok
  · show xs = (xs.take (2 * level.fold) ++ (if true = true then ms ++ [nonce] else
      [0, 0, 0, 0, 0, nonce]) ++ [ic0, ic2]) ++ xsR
    simp only [↓reduceIte, List.append_assoc, List.cons_append, List.nil_append, hms]
    rw [← hx3, List.take_append_drop, List.take_append_drop]
  · rw [eMl]; exact htl
  · rw [eW, eFend, eMl]; exact htnz
  · rw [eW, eFend, eMl]; exact hres
  · rw [eQs, whirLevelsOpenNZ_last]
    simp only [VerifierProgram.bind_eq]
    rw [qs_folds _ _ _ _ _ _ _ hl hnz]
    simp only
    rw [qs_readN_bind _ _ _ _ _ _ hml, hx3, qs_grindP_bind _ _ _ _ _ _ hpow, eos]
    simp only [levelRestNZ, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    rw [rest_qs hd' hlam hroot hol hok hidx]
    simp only [List.nil_append, levelTailNZ, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    rw [qs_tail _ _ _ _ _ _ _ htl htnz]
    rfl

end
end LeanVM.Guest.B1.Whir
