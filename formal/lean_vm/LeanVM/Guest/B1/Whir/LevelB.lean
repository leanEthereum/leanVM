/-
  LeanVM.Guest.B1.Whir.LevelB

  A level after its proof of work runs the Spec's `levelRest`.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.LevelRest
public import LeanVM.Protocol.WithHash

/-!
# A level's queries and glue, soundly (G:1554-1646)

`osLevelB_sound`: `osLevelB`'s atoms and calls (the squeezes, the weights, the queries, the glue)
run `levelRest` from the sponge with nothing waiting after the proof of work, and leave the
level's record (`LvRec`) for the terminal's weights.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The state a level leaves -/

section
variable (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt)

/-- The positions' state. -/
abbrev bSq : OsSt := (osPositions c lvl lv st).2
/-- The batching challenge's value. -/
abbrev bLam : ℕ := (bSq c lvl lv st).k - 1
/-- `μ`'s block. -/
abbrev bMu : List Stmt × ℕ := osMu lvl (bLam c lvl lv st) (bSq c lvl lv st).k
/-- The state the queries block starts from. -/
abbrev bQs : OsSt := { bSq c lvl lv st with k := (bMu c lvl lv st).2 }
/-- The queries block. -/
abbrev bQ : List Stmt × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  osQueries c lvl lv (bLam c lvl lv st) (bQs c lvl lv st)
/-- `lam^q`'s value. -/
abbrev bLamN : ℕ := (bQ c lvl lv st).2.2.2.1
/-- The state after the intro. -/
abbrev bS1 : OsSt :=
  { bSq c lvl lv st with
    k := (bQ c lvl lv st).2.1
    w0 := (bQ c lvl lv st).2.2.2.2.1
    w1 := (bQ c lvl lv st).2.2.2.2.2.2
    co := (bSq c lvl lv st).co + 2
    mats := osQueriesMats c lv (bQs c lvl lv st) }

/-- The level's openings, named by the frames `V` and the queries' witness `W`. -/
abbrev bOs (rd : Reader) (σ : Val) (V : FrameMap) (W : List E → List E → List QW) :
    List Opening :=
  lvOpenings rd (V (osQueriesName lvl lv)
    ((osQueriesDisp c lvl lv (bLam c lvl lv st) (bQs c lvl lv st)).2.1.map σ)
    ((osQueriesDisp c lvl lv (bLam c lvl lv st) (bQs c lvl lv st)).2.2.map σ)) lv W (lqCall lvl lv)

theorem osLevelB_eq : osLevelB c lvl lv st =
    if lvl = c.yrLevel then
      ((osPositions c lvl lv st).1 ++ (bMu c lvl lv st).1 ++
        (bQ c lvl lv st).1 ++ [] ++
        [.atom (.mul (.n (bS1 c lvl lv st).k) (.n (bLam c lvl lv st)) (.n (bLamN c lvl lv st))),
          .atom (.load (.n (bS1 c lvl lv st).k) (.n osBetas) lvl)] ++
        (osGlue (bLam c lvl lv st) (bQ c lvl lv st).2.2.1 (bQ c lvl lv st).2.2.2.2.1
          (bQ c lvl lv st).2.2.2.2.2.1 (bQ c lvl lv st).2.2.2.2.2.2
          { bS1 c lvl lv st with k := (bS1 c lvl lv st).k + 1 }).1,
       (osGlue (bLam c lvl lv st) (bQ c lvl lv st).2.2.1 (bQ c lvl lv st).2.2.2.2.1
          (bQ c lvl lv st).2.2.2.2.2.1 (bQ c lvl lv st).2.2.2.2.2.2
          { bS1 c lvl lv st with k := (bS1 c lvl lv st).k + 1 }).2)
    else
      ((osPositions c lvl lv st).1 ++ (bMu c lvl lv st).1 ++
        (bQ c lvl lv st).1 ++ (osOodGlue lvl (bLam c lvl lv st) (bS1 c lvl lv st)).1 ++
        [.atom (.mul (.n ((bS1 c lvl lv st).k + 13)) (.n ((bS1 c lvl lv st).k + 12))
            (.n (bLamN c lvl lv st))),
          .atom (.load (.n ((bS1 c lvl lv st).k + 13)) (.n osBetas) lvl)] ++
        (osGlue ((bS1 c lvl lv st).k + 12) (bQ c lvl lv st).2.2.1 (bQ c lvl lv st).2.2.2.2.1
          (bQ c lvl lv st).2.2.2.2.2.1 (bQ c lvl lv st).2.2.2.2.2.2
          { (osOodGlue lvl (bLam c lvl lv st) (bS1 c lvl lv st)).2 with
            k := (bS1 c lvl lv st).k + 13 + 1 }).1,
       (osGlue ((bS1 c lvl lv st).k + 12) (bQ c lvl lv st).2.2.1 (bQ c lvl lv st).2.2.2.2.1
          (bQ c lvl lv st).2.2.2.2.2.1 (bQ c lvl lv st).2.2.2.2.2.2
          { (osOodGlue lvl (bLam c lvl lv st) (bS1 c lvl lv st)).2 with
            k := (bS1 c lvl lv st).k + 13 + 1 }).2) := by
  unfold osLevelB
  by_cases h : lvl = c.yrLevel
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    rfl

end

/-- The callees of a level's queries, at the rate's row `lv`: `level_positions`,
`level_queries`'s template, the row weights and the cap. -/
structure LvQCallees (rd : Reader) (lvl : ℕ) (lv : OsLv) : Prop where
  lp : ∀ args rets, coreProgram.Rel rd (osPositionsName lv) args rets →
    WinTabs rd (args.getD 7 0) → MeaningLevelPositions lv.depth lv.capDepth lv.squeezes rd args rets
  lq : FnIs (osQueriesName lvl lv) (osParams 3)
    (lqBody lv.queries (if lvl = 0 then 1 else 0) lv.interleave lv.leafCells lv.depth lv.capDepth)
  rw : ∀ args rets, coreProgram.Rel rd ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
    natStr (if lvl = 0 then 1 else 0)) args rets →
      MeaningOpeningRowWeights lv.folds (if lvl = 0 then 1 else 0) rd args rets
  cap : ∀ args rets, coreProgram.Rel rd ("verify_merkle_cap__L" ++ natStr lv.capDepth) args rets →
    MeaningVerifyMerkleCap lv.capDepth rd args rets

theorem ceilDiv_le {a b : ℕ} (hb : 1 ≤ b) : ceilDiv a b ≤ a := by
  unfold ceilDiv
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.zero_add]; exact (Nat.div_eq_of_lt (by omega)).le
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    apply Nat.div_le_of_le_mul
    have e : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
    rw [e]
    nlinarith [Nat.zero_le (a' * b')]

theorem le_ceilDiv_mul {a b : ℕ} (hb : 1 ≤ b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) (show 0 < b by omega)
  rw [Nat.mul_comm]
  generalize (a + b - 1) / b = q at h1 ⊢
  generalize (a + b - 1) % b = r at h1 h2
  omega

/-- The positions, `μ` and the queries of a level. -/
theorem osLevelB_common {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) {V : FrameMap}
    (hU : UnfoldsV rd C V) {c : OsCfg}
    {lvl : ℕ} {lv : OsLv} {st : OsSt} {level : Whir.Level}
    {ml : ℕ} (hcfg : LvB c lvl lv level ml)
    (hsq : AllOk C rd σ (osPositions c lvl lv st).1)
    (hmu : AllOk C rd σ (bMu c lvl lv st).1)
    (hq : AllOk C rd σ (bQ c lvl lv st).1)
    (hcal : LvQCallees rd lvl lv) (hrate : LvRate σ c lvl lv)
    (hwt : WinTabs rd (σ (.n osWin)))
    (W : List E → List E → List QW) (hQW : LvQW rd C lvl lv W)
    (hfs : st.fs.length = 5) (hpad : PadOk σ st.pad) (hmats : MatsOk σ st.mats)
    {lf : List E} (hlf : lf.length = lv.folds)
    (hfch : ∀ j < lv.folds, LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j) (lf.getD j 0))
    {root : Digest}
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestHalves root).1)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestHalves root).2) :
    let F2 : Fs := ⟨st.fsv σ, []⟩
    let qs := queriesOf (192 / lv.depth) lv.depth (F2.squeezeN lv.squeezes).1 lv.queries
    σ (.n (bLam c lvl lv st)) = (F2.squeezeN lv.squeezes).2.squeeze.1 ∧
    (bSq c lvl lv st).fsv σ = (F2.squeezeN lv.squeezes).2.squeeze.2.cap ∧
    PadOk σ (bSq c lvl lv st).pad ∧ (bSq c lvl lv st).fs.length = 5 ∧
    qs.length = lv.queries ∧ (∀ k < lv.queries, qs.getD k 0 < 2 ^ lv.depth) ∧
    (∀ k < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + k) (eOfNat (qs.getD k 0))) ∧
    σ (.n (bLamN c lvl lv st)) = σ (.n (bLam c lvl lv st)) ^ lv.queries ∧
    σ (.n (bLam c lvl lv st)) ≠ 0 ∧
    LoadHolds rd (σ (.n osMus)) lvl (σ (.n (bLam c lvl lv st)))⁻¹ ∧
    MatsOk σ (bS1 c lvl lv st).mats ∧
    ∃ (os : List Opening) (ic0 ic2 : E), os = bOs c lvl lv st rd σ V W ∧ os.length = lv.queries ∧
      (∀ k (hk : k < qs.length) (ho : k < os.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root lv.depth
          (if lvl = 0 then lv.interleave else 3 * lv.interleave) qs[k] os[k]) = true) ∧
      σ (.n (bQ c lvl lv st).2.2.1) = enforcedSum ((os.map (·.leaf)).map (specRow lvl)) lf
        (powers (σ (.n (bLam c lvl lv st))) lv.queries) ∧
      ReadsAt rd (st.cur σ) [ic0, ic2] ∧ σ (.n (bQ c lvl lv st).2.2.2.2.1) = ic0 ∧
      σ (.n (bQ c lvl lv st).2.2.2.2.2.2) = ic2 ∧
      σ (.n (bQ c lvl lv st).2.2.2.2.2.1) = σ (.n (bQ c lvl lv st).2.2.1) + ic2 ∧
      os.map Opening.leafIndex = qs := by
  intro F2 qs
  obtain ⟨hdepth, hqq, hq2, hqd, hper, hsqz, hdig, hpo, hsq0, hsqo, hsq5, hrow, hcd, hcd8, hcdd,
    hbo⟩ := hcfg
  obtain ⟨D, hlam, hfsv, hpad', hfs', hmsq⟩ :=
    osPositions_sound hsq (fun a r h hw ↦ hcal.lp a r (hle _ _ _ h) hw)
      hrate hwt hpo hfs hpad hmats
  obtain ⟨hl0, hmu'⟩ := osMu_sound hmu
  have hdec' : ∀ jj < lv.squeezes, MeaningDecodeQueryWindows lv.depth lv.capDepth rd
      [(F2.squeezeN lv.squeezes).1.getD jj 0,
        σ (.n osQpos) * gen ^ (lv.posOff + jj * (192 / lv.depth)),
        σ (.n osQbp) * gen ^ (lv.posOff + jj * (192 / lv.depth)), σ (.n osWin)] [] := by
    intro jj hjj
    rw [squeezeN_getD _ _ _ hjj]
    exact D jj hjj
  have hqle : lv.queries ≤ lv.squeezes * (192 / lv.depth) := by
    rw [hsqz]; exact le_ceilDiv_mul hper
  have tab := positions_of_decodes hper hqle _ hdec'
  have hqlt : ∀ k < lv.queries, qs.getD k 0 < 2 ^ lv.depth := by
    intro k hk
    simp only [qs, queriesOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some]
    exact Nat.mod_lt _ (by positivity)
  obtain ⟨ic0, ic2, hol, hop, hsum, hlamN, hrd, e0, e2, e1, hmq, hidx⟩ :=
    osQueries_sound hle hU hq (by simpa using hmsq) hrate hcal.lq hqd hrow hcd hcd8 hcdd hcal.rw
      hcal.cap W hQW hlf hfch hr0 hr1 qs (by simp [qs, queriesOf]) hqlt (fun k hk ↦ (tab k hk).2) hbo
  refine ⟨hlam, hfsv, hpad', hfs', by simp [qs, queriesOf], hqlt, fun k hk ↦ (tab k hk).1, hlamN,
    hl0, hmu', hmq, _, ic0, ic2, rfl, hol, hop, hsum, ?_, e0, e2, e1, hidx⟩
  exact hrd

theorem specRows_eq (lvl : ℕ) (words : List (List K)) :
    (if lvl = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow) =
      words.map (specRow lvl) := by
  by_cases h : lvl = 0 <;> simp [specRow, h]

/-- **The Spec's `levelRest`** from a sponge with nothing waiting: the positions of `nsq`
squeezes, the batching challenge, the openings, the intro's two words. -/
theorem levelRest_run {ml lvl : ℕ} {level : Whir.Level} {lf : List E} {ws : WhirStateT}
    {pending : List (E × List E × (List E → E))} {F : Fs} {d nsq : ℕ}
    (hd : ml + level.logInvRate = d) (hper : 1 ≤ 192 / d)
    (hn : nsq = ceilDiv level.queries (192 / d)) {R : List (Digest × ℕ × ℕ)} {root : Digest}
    {height width : ℕ} (hR : R[lvl]? = some (root, height, width)) (os : List Opening)
    (hol : os.length = (queriesOf (192 / d) d (F.squeezeN nsq).1 level.queries).length)
    (hop : ∀ k (hk : k < (queriesOf (192 / d) d (F.squeezeN nsq).1 level.queries).length)
      (ho : k < os.length), Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width
        (queriesOf (192 / d) d (F.squeezeN nsq).1 level.queries)[k] os[k]) = true)
    (hidx : os.map Opening.leafIndex = queriesOf (192 / d) d (F.squeezeN nsq).1 level.queries)
    (ic0 ic2 : E) :
    let qs := queriesOf (192 / d) d (F.squeezeN nsq).1 level.queries
    let lam := (F.squeezeN nsq).2.squeeze.1
    let enf := enforcedSum ((os.map (·.leaf)).map (specRow lvl)) lf (powers lam qs.length)
    RunsWith (levelRest ml lvl level lf ws pending) F [ic0, ic2] [os] R
      (glueT lam ws (pending ++ [(enf, [ic0, enf + ic2, ic2],
        fun x ↦ inducedWeight ml qs (powers lam qs.length) x)]))
      ⟨(F.squeezeN nsq).2.squeeze.2.cap, [(ic0, dsObserve), (ic2, dsObserve)]⟩ R := by
  subst hn
  intro qs lam enf
  have h1 : RunsWith (sampleQueries (ml + level.logInvRate) level.queries) F [] [] R qs
      (F.squeezeN (ceilDiv level.queries (192 / d))).2 R := by
    rw [hd]
    unfold sampleQueries
    exact RunsTo.withRoots
      (sampleQueriesAux_run d hper level.queries level.queries F (ceilDiv_le hper)) R
  set nsq := ceilDiv level.queries (192 / d)
  have h2 := RunsTo.withRoots (runsTo_sampleE (F.squeezeN nsq).2) R
  have h3 := runsWith_queryP (F.squeezeN nsq).2.squeeze.2 R hR qs os hol hop hidx
  have h4 := RunsTo.withRoots (runsTo_round3 (F.squeezeN nsq).2.squeeze.2 enf ic0 ic2) R
  have hF4 : (((F.squeezeN nsq).2.squeeze.2.absorb ic0 dsObserve).absorbAll [ic2] dsObserve) =
      ⟨(F.squeezeN nsq).2.squeeze.2.cap, [(ic0, dsObserve), (ic2, dsObserve)]⟩ := by
    simp [Fs.absorbAll, Fs.absorb, Fs.squeeze, rateScalars]
  rw [hF4] at h4
  have e : levelRest ml lvl level lf ws pending =
      (sampleQueries (ml + level.logInvRate) level.queries).bind fun queries ↦
        VerifierProgram.sampleChallenge.bind fun lam ↦ (VerifierProgram.queryOpenings lvl
            queries).bind fun words ↦
          (sumcheckRoundPoly 3 (enforcedSum (words.map (specRow lvl)) lf
            (powers lam queries.length)) none).bind fun intro ↦
            VerifierProgram.ret (glueT lam ws (pending ++ [(enforcedSum (words.map (specRow lvl)) lf
              (powers lam queries.length), intro,
              fun x ↦ inducedWeight ml queries (powers lam queries.length) x)])) := by
    simp only [levelRest, specRows_eq, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  rw [e]
  refine RunsWith.of_eq (RunsWith.bind' h1 (RunsWith.bind' h2 (RunsWith.bind' h3 (RunsWith.bind' h4
    (runsWith_ret _ _ _))))) rfl (by simp) (by simp) rfl rfl rfl rfl

/-- **A level's queries and glue.** -/
theorem osLevelB_sound {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) {V : FrameMap}
    (hU : UnfoldsV rd C V) {c : OsCfg}
    {lvl : ℕ} {lv : OsLv} {st : OsSt} {level : Whir.Level}
    {ml : ℕ} (hcfg : LvB c lvl lv level ml)
    (hok : AllOk C rd σ (osLevelB c lvl lv st).1)
    (hcal : LvQCallees rd lvl lv) (hrate : LvRate σ c lvl lv)
    (hwt : WinTabs rd (σ (.n osWin)))
    (W : List E → List E → List QW) (hQW : LvQW rd C lvl lv W)
    (hfs : st.fs.length = 5) (hpad : PadOk σ st.pad) (hmats : MatsOk σ st.mats)
    {ws : WhirStateT} (hquad : ws.quad = st.quad σ) (ht : ws.target = σ (.n st.t))
    {lf : List E} (hlf : lf.length = lv.folds)
    (hfch : ∀ j < lv.folds, LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j) (lf.getD j 0))
    {R : List (Digest × ℕ × ℕ)} {root : Digest}
    (hR : R[lvl]? = some (root, lv.depth, if lvl = 0 then lv.interleave else 3 * lv.interleave))
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestHalves root).1)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestHalves root).2)
    {pending : List (E × List E × (List E → E))} (hpend : PendOk rd σ c lvl pending) :
    ∃ (xs : List E) (os : List Opening) (ws' : WhirStateT) (lam : E) (qs : List ℕ),
      os = bOs c lvl lv st rd σ V W ∧ ReadsAt rd (st.cur σ) xs ∧ xs.length = 2 ∧
      RunsWith (levelRest ml lvl level lf ws pending) ⟨st.fsv σ, []⟩ xs [os] R ws'
        ((osLevelB c lvl lv st).2.F σ) R ∧
      ws'.quad = (osLevelB c lvl lv st).2.quad σ ∧ ws'.target = σ (.n (osLevelB c lvl lv st).2.t) ∧
      (∃ (enf : E) (intro : List E), ws' = glueT lam ws (pending ++
        [(enf, intro, fun x ↦ inducedWeight ml qs (powers lam qs.length) x)])) ∧
      LvRec rd σ c lvl lv lam qs ∧
      (osLevelB c lvl lv st).2.fs.length = 5 ∧ PadOk σ (osLevelB c lvl lv st).2.pad ∧
      (osLevelB c lvl lv st).2.cb = st.cb ∧ (osLevelB c lvl lv st).2.co = st.co + 2 ∧
      MatsOk σ (osLevelB c lvl lv st).2.mats := by
  have hsqc : (bSq c lvl lv st).c = st.c ∧ (bSq c lvl lv st).b = st.b ∧
      (bSq c lvl lv st).a = st.a ∧ (bSq c lvl lv st).t = st.t ∧ (bSq c lvl lv st).cb = st.cb ∧
      (bSq c lvl lv st).co = st.co := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [osLevelB_eq] at hok ⊢
  by_cases hfin : lvl = c.yrLevel
  · have hc : (lvl = c.yrLevel) = True := eq_true hfin
    simp only [hc, ↓reduceIte] at hok ⊢
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hok
    obtain ⟨⟨⟨⟨hsq, hmu⟩, hq⟩, hbm, hbeta⟩, hgl⟩ := hok
    have hpend' : pending = [] := by
      have := hpend; unfold PendOk at this; simpa only [hc, ↓reduceIte] using this
    subst hpend'
    obtain ⟨hlam, hfsv, hpad', hfs', hqlen, hqlt, hpos, hlamN, hl0, hmu, hmq, os, ic0, ic2, hos, hol,
      hop, hsum, hrd, e0, e2, e1, hidx⟩ := osLevelB_common hle hU hcfg hsq hmu
      hq hcal hrate hwt W hQW hfs hpad hmats hlf hfch hr0 hr1
    obtain ⟨gq, gt⟩ := osGlue_sound hgl
    rw [hbm, hlamN] at hbeta
    have hd := hcfg.depth.symm
    have hqq := hcfg.queries
    have hrun := levelRest_run (F := ⟨st.fsv σ, []⟩) (ws := ws) (lf := lf) (pending := [])
      (nsq := lv.squeezes) hd hcfg.per (by rw [hqq]; exact hcfg.squeezes) hR os
      (by simp [hol, hqq, queriesOf]) (by rw [hqq]; exact hop) (by rw [hqq]; exact hidx) ic0 ic2
    rw [hqq] at hrun
    have hql : (queriesOf (192 / lv.depth) lv.depth
        (Fs.squeezeN lv.squeezes ⟨st.fsv σ, []⟩).1 lv.queries).length = lv.queries := by
      simp [queriesOf]
    refine ⟨_, os, _, _, _, hos, hrd, rfl, RunsWith.of_eq hrun rfl rfl rfl rfl rfl ?_ rfl, ?_, ?_,
      ⟨_, _, rfl⟩, ⟨hqlen, hqlt, hpos, by rw [← hlam]; exact hl0, by rw [← hlam]; exact hmu,
        by simp only [hc, ↓reduceIte]; rw [← hlam]; exact hbeta, fun h ↦ absurd hfin h⟩, hfs',
      hpad', rfl, rfl, hmq⟩
    · show _ = (⟨(bSq c lvl lv st).fsv σ, [(σ (.n (bQ c lvl lv st).2.2.2.2.1), dsObserve),
        (σ (.n (bQ c lvl lv st).2.2.2.2.2.2), dsObserve)]⟩ : Fs)
      rw [hfsv, e0, e2]
    · rw [gq, hql]
      simp only [List.nil_append, glue_one, hquad, OsSt.quad, List.zipWith_cons_cons,
        List.zipWith_nil_left, one_mul]
      rw [e0, e1, e2, hsum, hlam]
      simp only [hsqc.1, hsqc.2.1, hsqc.2.2.1]
    · rw [gt, hql]
      simp only [List.nil_append, glue_one, ht, one_mul]
      rw [hsum, hlam]
      simp only [hsqc.2.2.2.1]
  · have hc : (lvl = c.yrLevel) = False := eq_false hfin
    simp only [hc, ↓reduceIte] at hok ⊢
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hok
    obtain ⟨⟨⟨⟨⟨hsq, hmu⟩, hq⟩, hog⟩, hbm, hbeta⟩, hgl⟩ := hok
    obtain ⟨y, c0, c2, z, hpe, hy, hc0, hc2⟩ : ∃ (y c0 c2 : E) (z : List E),
        pending = [(y, [c0, y + c2, c2], fun x ↦ eqEval z x)] ∧
        LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y ∧
        LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0 ∧
        LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2 := by
      have := hpend; unfold PendOk at this; simpa only [hc, ↓reduceIte] using this
    subst hpe
    obtain ⟨hlam, hfsv, hpad', hfs', hqlen, hqlt, hpos, hlamN, hl0, hmu, hmq, os, ic0, ic2, hos, hol,
      hop, hsum, hrd, e0, e2, e1, hidx⟩ := osLevelB_common hle hU hcfg hsq hmu
      hq hcal hrate hwt W hQW hfs hpad hmats hlf hfch hr0 hr1
    obtain ⟨y', c0', c2', hy', hc0', hc2', hlo, oq, ot, ob⟩ := osOodGlue_sound hog
    rw [hbm, hlamN] at hbeta
    rw [loadHolds_unique hy' hy] at oq ot
    rw [loadHolds_unique hc0' hc0] at oq
    rw [loadHolds_unique hc2' hc2] at oq
    obtain ⟨gq, gt⟩ := osGlue_sound hgl
    simp only [OsSt.quad, List.cons.injEq, and_true] at oq
    obtain ⟨oc, obb, oa⟩ := oq
    have hd := hcfg.depth.symm
    have hqq := hcfg.queries
    have hrun := levelRest_run (F := ⟨st.fsv σ, []⟩) (ws := ws) (lf := lf)
      (pending := [(y, [c0, y + c2, c2], fun x ↦ eqEval z x)])
      (nsq := lv.squeezes) hd hcfg.per (by rw [hqq]; exact hcfg.squeezes) hR os
      (by simp [hol, hqq, queriesOf]) (by rw [hqq]; exact hop) (by rw [hqq]; exact hidx) ic0 ic2
    rw [hqq] at hrun
    have hql : (queriesOf (192 / lv.depth) lv.depth
        (Fs.squeezeN lv.squeezes ⟨st.fsv σ, []⟩).1 lv.queries).length = lv.queries := by
      simp [queriesOf]
    refine ⟨_, os, _, _, _, hos, hrd, rfl, RunsWith.of_eq hrun rfl rfl rfl rfl rfl ?_ rfl, ?_, ?_,
      ⟨_, _, rfl⟩, ⟨hqlen, hqlt, hpos, by rw [← hlam]; exact hl0, by rw [← hlam]; exact hmu,
        by simp only [hc, ↓reduceIte]; rw [← hlam, ← ob]; exact hbeta,
        fun _ ↦ by rw [← hlam]; exact hlo⟩, hfs', hpad', rfl, rfl, hmq⟩
    · show _ = (⟨(bSq c lvl lv st).fsv σ, [(σ (.n (bQ c lvl lv st).2.2.2.2.1), dsObserve),
        (σ (.n (bQ c lvl lv st).2.2.2.2.2.2), dsObserve)]⟩ : Fs)
      rw [hfsv, e0, e2]
    · rw [gq, hql]
      simp only [List.singleton_append, glue_two, hquad, OsSt.quad, List.zipWith_cons_cons,
        List.zipWith_nil_left, one_mul]
      rw [oc, obb, oa, ob, e0, e1, e2, hsum, hlam]
      simp only [hsqc.1, hsqc.2.1, hsqc.2.2.1]
    · rw [gt, ot, hql]
      simp only [List.singleton_append, glue_two, ht, one_mul]
      rw [ob, hsum, hlam]
      simp only [hsqc.2.2.2.1]

end
end LeanVM.Guest.B1.Whir
