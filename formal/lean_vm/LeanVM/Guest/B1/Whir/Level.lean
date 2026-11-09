/-
  LeanVM.Guest.B1.Whir.Level

  One level of `open_stacked` runs the Spec's level head (`levelHead`): folds, claims, proof of
  work, queries and glue.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.LevelB
public import LeanVM.Guest.B1.Whir.Final

/-!
# A level (G:1488-1646)

`osLevel_nonfinal_sound`, `osLevel_final_sound`: from the guest's state at a level's start against
the Spec's (`LvIn`: the sponge it carries, the claim and the quadratic, the fold challenges stored,
the level's root committed and stored), the level's template runs `levelHead`, reads the words at
the cursor and the openings, and leaves the next level's start (`LvIn`, the next commitment
appended) or the residual; the claims it glues are `recClaims` of its record (`OsRec`), whose
values the terminal's weights reread from the buffers (`RecStored`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

theorem levelHead_eq (logN index : ℕ) (level : Whir.Level) (rest : List Whir.Level)
    (s : WhirStateT) :
    levelHead logN index level rest s =
      (foldRoundsT level.fold s []).bind fun p ↦
        (do
          let r ← levelMid (logN - p.1.folds.length) rest
          VerifierProgram.grindProofOfWork Whir.queryGrindingBits
          pure r).bind fun r ↦
          (levelRest (logN - p.1.folds.length) index level p.2 p.1 r.2).bind fun s' ↦
            VerifierProgram.ret (r.1, logN - p.1.folds.length, s') := by
  simp only [levelHead, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

theorem osFolds_state (p : ℕ) : ∀ (n off : ℕ) (st : OsSt),
    (osFolds p off n st).2.pad = st.pad ∧ (osFolds p off n st).2.k ≥ st.k
  | 0, _, _ => ⟨rfl, le_rfl⟩
  | n + 1, off, st => by
    obtain ⟨h1, h2⟩ := osFolds_state p n (off + 1) (osFold p off st).2
    refine ⟨h1, le_trans ?_ h2⟩
    simp only [osFold]
    have := osMat_next st.cb st.co st.k
    omega

/-! ## Records -/

/-- What a level glues, for the terminal: its batching challenge, its query positions, the
out-of-domain point of the commitment it read (none at the last level), the folds before its
claims and the message log there. -/
structure OsRec where
  lam : E
  qs : List ℕ
  z : Option (List E)
  F : ℕ
  ml : ℕ

/-- The claims a level glues (V:1775-1783, 1745-1760). -/
def recClaims (r : OsRec) : List GluedClaim :=
  match r.z with
  | some z => [⟨1 * r.lam, r.F, fun x ↦ eqEval z x⟩,
      ⟨1 * r.lam * r.lam, r.F, fun x ↦ inducedWeight r.ml r.qs (powers r.lam r.qs.length) x⟩]
  | none => [⟨1 * r.lam, r.F, fun x ↦ inducedWeight r.ml r.qs (powers r.lam r.qs.length) x⟩]

/-- What the terminal's weights reread of a level: its record's values in the buffers. -/
structure RecStored (rd : Reader) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (r : OsRec) :
    Prop where
  rq : LvRec rd σ c lvl lv r.lam r.qs
  z : (lvl = c.yrLevel → r.z = none) ∧ (lvl ≠ c.yrLevel → r.z ≠ none) ∧
    ∀ z, r.z = some z → z.length = lv.logCols ∧
    ∀ t (ht : t < z.length), LoadHolds rd (σ (.n osOodz)) ((lvl + 1) * ligColsCap + t) z[t]
  F : r.F = lv.foldsOff + lv.folds
  ml : r.ml = lv.logCols

/-! ## A level's start -/

/-- The width of a level's rows in `K` words. -/
def lvWidth (lvl : ℕ) (lv : OsLv) : ℕ := if lvl = 0 then lv.interleave else 3 * lv.interleave

/-- **A level's start**: the guest's state against the Spec's: the sponge, the claim and the
quadratic, the fold challenges so far in `fold_challenges`, the commitments so far, the level's
root stored in `level_roots`. -/
structure LvIn (rd : Reader) (σ : Val) (lvl : ℕ) (lv : OsLv) (st : OsSt) (ws : WhirStateT)
    (R : List (Digest × ℕ × ℕ)) (root : Digest) : Prop where
  fs : st.fs.length = 5
  co : st.co ≤ 8
  pad : PadOk σ st.pad
  quad : ws.quad = st.quad σ
  t : ws.target = σ (.n st.t)
  folds : ws.folds.length = lv.foldsOff
  fch : ∀ j (h : j < ws.folds.length), LoadHolds rd (σ (.n osFch)) j ws.folds[j]
  rlen : R.length = lvl + 1
  R : R[lvl]? = some (root, lv.depth, lvWidth lvl lv)
  r0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestHalves root).1
  r1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestHalves root).2
  mats : MatsOk σ st.mats

/-- The callees a level's template calls, by their meanings. -/
structure LvCallees (rd : Reader) (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Prop where
  fold : ∀ args rets, coreProgram.Rel rd "opening_fold" args rets → MeaningOpeningFold rd args rets
  can : ∀ args rets, coreProgram.Rel rd "assert_canonical" args rets →
    MeaningAssertCanonical args rets
  ood : lvl ≠ c.yrLevel → ∀ args rets,
    coreProgram.Rel rd ("opening_ood_point__L" ++ natStr lv.logCols) args rets →
      MeaningOpeningOodPoint lv.logCols rd args rets
  fm : ∀ args rets, coreProgram.Rel rd ("opening_final_message__L" ++ natStr c.yrLen) args rets →
    MeaningOpeningFinalMessage c.yrLen rd args rets
  grind : ∀ args rets, coreProgram.Rel rd ("grind_check__L" ++ natStr lv.grind) args rets →
    MeaningGrindCheck Whir.queryGrindingBits args rets
  loop : FnIs (c.sqLoop lvl) (osParams 6) (sqLoopBody lv (c.sqLoop lvl))
  dec : ∀ args rets, WinTabs rd (args.getD 3 0) →
    coreProgram.Rel rd ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
      args rets → MeaningDecodeQueryWindows lv.depth lv.capDepth rd args rets
  rw : ∀ args rets, coreProgram.Rel rd ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
    natStr (if lvl = 0 then 1 else 0)) args rets →
      MeaningOpeningRowWeights lv.folds (if lvl = 0 then 1 else 0) rd args rets
  cap : ∀ args rets, coreProgram.Rel rd ("verify_merkle_cap__L" ++ natStr lv.capDepth) args rets →
    MeaningVerifyMerkleCap lv.capDepth rd args rets

/-- A level's `opening_queries` calls of `C`, sound with their queries `W` at the call's words. -/
def LvQW (rd : Reader) (C : CallRel) (lvl : ℕ) (lv : OsLv) (W : List E → List E → List QW) :
    Prop :=
  ∀ args rets, C (osQueriesName lvl lv) args rets →
    args.getD 6 0 = gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0)) →
    lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG → lv.capDepth ≤ lv.depth →
    (∀ N, args.getD 6 0 = gen ^ N → N < ordG → QueryWinsOk rd (args.getD 4 0)
      (oqCount (lv.queries % 2 * (if lvl = 0 then 1 else 0)) (if lvl = 0 then 1 else 0) N)
      lv.depth lv.capDepth) →
    MeaningOpeningQueriesW (lv.queries % 2 * (if lvl = 0 then 1 else 0))
      (if lvl = 0 then 1 else 0) lv.interleave lv.depth lv.capDepth rd (W args rets) args rets

/-- **A level that is not the last.** -/
theorem osLevel_nonfinal_sound {c : OsCfg} {lvl : ℕ} {lv lv' : OsLv} {logN : ℕ}
    {level next : Whir.Level} {rest : List Whir.Level}
    {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) {W : List E → List E → List QW}
    (hQW : LvQW rd C lvl lv W)
    (hcb : LvCallees rd c lvl lv) (hcfg : LvB c lvl lv level lv.logCols)
    (hfold : level.fold = lv.folds) (h4 : 1 ≤ lv.folds)
    (hml : logN - (lv.foldsOff + lv.folds) = lv.logCols) (hm : 1 ≤ lv.logCols)
    (hlvl : (lvl + 1) * ligColsCap < u128Bound) (hnf : lvl ≠ c.yrLevel)
    (hoff' : lv'.foldsOff = lv.foldsOff + lv.folds)
    (hshape : levelShape lv.logCols next (3 * 2 ^ next.fold) = (lv'.depth, lvWidth (lvl + 1) lv'))
    {st : OsSt} {ws : WhirStateT} {R : List (Digest × ℕ × ℕ)} {root : Digest}
    (hin : LvIn rd σ lvl lv st ws R root) (hwt : WinTabs rd (σ (.n osWin)))
    (hok : AllOk C rd σ (osLevel c lvl lv st).1) :
    ∃ (xs : List E) (os : List Opening) (ws' : WhirStateT) (root' : Digest) (r : OsRec),
      ReadsAt rd (st.cur σ) xs ∧
      RunsWith (levelHead logN lvl level (next :: rest) ws) (st.F σ) xs [os] R
        ([], lv.logCols, ws') ((osLevel c lvl lv st).2.F σ) (R ++ [(root', lv'.depth, lvWidth (lvl + 1) lv')]) ∧
      LvIn rd σ (lvl + 1) lv' (osLevel c lvl lv st).2 ws' (R ++ [(root', lv'.depth, lvWidth (lvl + 1) lv')])
        root' ∧
      ws'.glued = ws.glued ++ recClaims r ∧ RecStored rd σ c lvl lv r ∧
      (osLevel c lvl lv st).2.cur σ = st.cur σ * gen ^ xs.length ∧
      os = lvOpenings rd σ lv W (osQCall c lvl lv st) ∧ xs.length = 2 * lv.folds + 6 + 2 := by
  have hc : (lvl = c.yrLevel) = False := eq_false hnf
  rw [osLevel_split] at hok ⊢
  rw [allOk_append] at hok
  obtain ⟨hA, hB⟩ := hok
  simp only [osLevelA, hc, ↓reduceIte] at hA hB ⊢
  rw [allOk_append, allOk_append] at hA
  obtain ⟨⟨hF, hC⟩, hG⟩ := hA
  -- the folds
  obtain ⟨xs1, chs, hx1, hcl, hrd1, hrun1, hcur1, hfs1, hco1, hch⟩ :=
    osFolds_sound hcb.fold osFch lv.folds lv.foldsOff st ws [] hin.fs
      (by have := hin.co; unfold u128Bound; omega) hin.quad hin.t (allOk_mono hle hF)
  set st1 := (osFolds osFch lv.foldsOff lv.folds st).2
  have hco1' : st1.co = 0 := hco1.resolve_left (by omega)
  -- the commitment
  obtain ⟨ra, rb, y, c0, c2, nonce, d, z, F', hrd2, hco, hrun2⟩ :=
    osCommit_sound hcb.can (hcb.ood hnf) hcb.grind hfs1
      (by rw [osFolds_mats]; exact hin.mats) hm hlvl
      (allOk_mono hle (allOk_append.mpr ⟨hC, hG⟩)) next rest R
  set st2 := (osCommit c.plan lvl lv st1).2.1
  have hpad2 : st2.pad = st.pad := (osFolds_state osFch lv.folds lv.foldsOff st).1
  have hR2 : (R ++ [(d, levelShape lv.logCols next (3 * 2 ^ next.fold))])[lvl]? =
      some (root, lv.depth, if lvl = 0 then lv.interleave else 3 * lv.interleave) := by
    rw [List.getElem?_append_left (by rw [hin.rlen]; omega)]
    exact hin.R
  obtain ⟨xs3, os, ws', lam, qs, hos, hrd3, hxl3, hrun3, hq3, ht3, ⟨enf, intro, hws'⟩, hrec, hfs3, hpad3,
      hcb3, hco3, hmats3⟩ :=
    osLevelB_sound hle (lf := [] ++ chs) (ws := { ws with
        target := σ (.n st1.t)
        quad := st1.quad σ
        folds := ws.folds ++ chs })
      (pending := [(y, [c0, y + c2, c2], fun x ↦ eqEval z x)])
      hcfg hB hcb.loop hcb.dec hwt hcb.rw hcb.cap W hQW hco.fs (by rw [hpad2]; exact hin.pad) hco.mats
      rfl rfl (by simpa using hcl) (fun j hj ↦ by
        have := hch j (by rw [hcl]; exact hj)
        rw [List.nil_append, List.getD_eq_getElem _ _ (by rw [hcl]; exact hj)]
        exact this) hR2 hin.r0 hin.r1
      (by unfold PendOk; simp only [hc, ↓reduceIte]
          exact ⟨y, c0, c2, z, rfl, hco.oy, hco.oc0, hco.oc2⟩)
  have hfl : (ws.folds ++ chs).length = lv.foldsOff + lv.folds := by
    rw [List.length_append, hin.folds, hcl]
  have hml' : logN - (ws.folds ++ chs).length = lv.logCols := by rw [hfl, hml]
  rw [List.singleton_append, glue_two] at hws'
  have hwf : ws'.folds = ws.folds ++ chs := by rw [hws']
  have hwg : ws'.glued = ws.glued ++ [⟨1 * lam, (ws.folds ++ chs).length, fun x ↦ eqEval z x⟩,
      ⟨1 * lam * lam, (ws.folds ++ chs).length,
        fun x ↦ inducedWeight lv.logCols qs (powers lam qs.length) x⟩] := by rw [hws']
  rw [levelHead_eq]
  have r1 := RunsTo.withRoots hrun1 R
  rw [← hfold] at r1
  have r2 : RunsWith (do
        let r ← levelMid (logN - (ws.folds ++ chs).length) (next :: rest)
        VerifierProgram.grindProofOfWork Whir.queryGrindingBits
        pure r) (st1.F σ) [ra, rb, y, c0, c2, nonce] [] R
      ([], [(y, [c0, y + c2, c2], fun x ↦ eqEval z x)]) F'
      (R ++ [(d, levelShape lv.logCols next (3 * 2 ^ next.fold))]) := by
    rw [hml']; exact hrun2
  have r3 : RunsWith (levelRest (logN - (ws.folds ++ chs).length) lvl level ([] ++ chs)
      { ws with
        target := σ (.n st1.t)
        quad := st1.quad σ
        folds := ws.folds ++ chs }
      [(y, [c0, y + c2, c2], fun x ↦ eqEval z x)]) F' xs3 [os]
      (R ++ [(d, levelShape lv.logCols next (3 * 2 ^ next.fold))]) ws'
      ((osLevelB c lvl lv st2).2.F σ)
      (R ++ [(d, levelShape lv.logCols next (3 * 2 ^ next.fold))]) := by
    rw [hml', hco.sponge]; exact hrun3
  refine ⟨xs1 ++ ([ra, rb, y, c0, c2, nonce] ++ (xs3 ++ [])), os, ws', d,
    ⟨lam, qs, some z, lv.foldsOff + lv.folds, lv.logCols⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine readsAt_append hrd1 (readsAt_append ?_ ?_)
    · rw [hx1, ← hcur1]; exact hrd2
    · rw [List.append_nil, hx1, ← hcur1, show [ra, rb, y, c0, c2, nonce].length = 6 from rfl,
        ← hco.cur]
      exact hrd3
  · refine RunsWith.of_eq (RunsWith.bind' r1 (RunsWith.bind' r2 (RunsWith.bind' r3
      (runsWith_ret _ _ _)))) rfl rfl rfl rfl ?_ rfl ?_
    · simp only [hml']
    · rw [hshape]
  · refine ⟨hfs3, ?_, hpad3, hq3, ht3, ?_, ?_, by simp [hin.rlen], ?_, ?_, ?_, hmats3⟩
    · rw [hco3]; simp [st2, osCommit, hco1']
    · rw [hwf, hfl, hoff']
    · intro j hj
      simp only [hwf] at hj ⊢
      rcases Nat.lt_or_ge j ws.folds.length with h | h
      · rw [List.getElem_append_left h]; exact hin.fch j h
      · rw [List.getElem_append_right h]
        have := hch (j - ws.folds.length) (by simp at hj; omega)
        have e : lv.foldsOff + (j - ws.folds.length) = j := by rw [← hin.folds]; omega
        rwa [e] at this
    · simp [hin.rlen]
    · rw [← hco.root, show 2 * (lvl + 1) = 2 * lvl + 2 by ring]; exact hco.rootA
    · rw [← hco.root, show 2 * (lvl + 1) + 1 = 2 * lvl + 3 by ring]; exact hco.rootB
  · rw [hwg, hfl]; rfl
  · exact ⟨hrec, ⟨fun h ↦ absurd h hnf, fun _ ↦ by simp, fun z' hz ↦ by
      cases hz; exact ⟨hco.zlen, hco.zat⟩⟩, rfl, rfl⟩
  · simp only [OsSt.cur, hcb3, hco3, List.length_append, List.length_cons, List.length_nil, hxl3]
    have := hco.cur
    simp only [OsSt.cur] at this hcur1
    rw [pow_add, ← mul_assoc, this, hcur1, hx1]
    ring
  · rw [hos]
    simp only [bOs, osQCall, hc, ↓reduceIte]
    rfl
  · simp only [List.length_append, hx1, hxl3, List.length_cons, List.length_nil]

/-- **The last level**: it runs its head, reads the final message (the residual, stored in
`final_msg`). -/
theorem osLevel_final_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {logN : ℕ} {level : Whir.Level}
    {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) {W : List E → List E → List QW}
    (hQW : LvQW rd C lvl lv W)
    (hcb : LvCallees rd c lvl lv) (hcfg : LvB c lvl lv level lv.logCols)
    (hfold : level.fold = lv.folds) (h4 : 1 ≤ lv.folds)
    (hml : logN - (lv.foldsOff + lv.folds) = lv.logCols) (hlen : 2 ^ lv.logCols = c.yrLen)
    (hfin : lvl = c.yrLevel)
    {st : OsSt} {ws : WhirStateT} {R : List (Digest × ℕ × ℕ)} {root : Digest}
    (hin : LvIn rd σ lvl lv st ws R root) (hwt : WinTabs rd (σ (.n osWin)))
    (hok : AllOk C rd σ (osLevel c lvl lv st).1) :
    ∃ (xs : List E) (os : List Opening) (ws' : WhirStateT) (ms : List E) (r : OsRec),
      ReadsAt rd (st.cur σ) xs ∧
      RunsWith (levelHead logN lvl level [] ws) (st.F σ) xs [os] R
        (ms, lv.logCols, ws') ((osLevel c lvl lv st).2.F σ) R ∧
      ms.length = c.yrLen ∧ ReadsAt rd (σ (.n osFmsg)) ms ∧
      ws'.glued = ws.glued ++ recClaims r ∧ RecStored rd σ c lvl lv r ∧
      ws'.folds.length = lv.foldsOff + lv.folds ∧
      (∀ j (h : j < ws'.folds.length), LoadHolds rd (σ (.n osFch)) j ws'.folds[j]) ∧
      ws'.quad = (osLevel c lvl lv st).2.quad σ ∧ ws'.target = σ (.n (osLevel c lvl lv st).2.t) ∧
      (osLevel c lvl lv st).2.fs.length = 5 ∧ PadOk σ (osLevel c lvl lv st).2.pad ∧
      (osLevel c lvl lv st).2.co ≤ 8 ∧
      (osLevel c lvl lv st).2.cur σ = st.cur σ * gen ^ xs.length ∧
      os = lvOpenings rd σ lv W (osQCall c lvl lv st) ∧ xs.length = 2 * lv.folds + (c.yrLen + 1) + 2 := by
  have hc : (lvl = c.yrLevel) = True := eq_true hfin
  rw [osLevel_split] at hok ⊢
  rw [allOk_append] at hok
  obtain ⟨hA, hB⟩ := hok
  simp only [osLevelA, hc, ↓reduceIte] at hA hB ⊢
  rw [allOk_append, allOk_append] at hA
  obtain ⟨⟨hF, hC⟩, hG⟩ := hA
  obtain ⟨xs1, chs, hx1, hcl, hrd1, hrun1, hcur1, hfs1, hco1, hch⟩ :=
    osFolds_sound hcb.fold osFch lv.folds lv.foldsOff st ws [] hin.fs
      (by have := hin.co; unfold u128Bound; omega) hin.quad hin.t (allOk_mono hle hF)
  set st1 := (osFolds osFch lv.foldsOff lv.folds st).2
  have hco1' : st1.co = 0 := hco1.resolve_left (by omega)
  obtain ⟨ms, nonce, hmsl, hrd2, hfm, hrun2, hcur2, hfs2⟩ :=
    osFinal_sound hlen hcb.fm hcb.grind hfs1 (by rw [hco1']; unfold u128Bound; norm_num)
      (allOk_mono hle (allOk_append.mpr ⟨hC, hG⟩))
  set st2 := (osFinal c st1).2.1
  have hpad2 : st2.pad = st.pad := (osFolds_state osFch lv.folds lv.foldsOff st).1
  obtain ⟨xs3, os, ws', lam, qs, hos, hrd3, hxl3, hrun3, hq3, ht3, ⟨enf, intro, hws'⟩, hrec, hfs3, hpad3,
      hcb3, hco3, -⟩ :=
    osLevelB_sound hle (lf := [] ++ chs) (ws := { ws with
        target := σ (.n st1.t)
        quad := st1.quad σ
        folds := ws.folds ++ chs })
      (pending := []) (R := R)
      hcfg hB hcb.loop hcb.dec hwt hcb.rw hcb.cap W hQW hfs2 (by rw [hpad2]; exact hin.pad)
      (by show MatsOk σ st1.mats; rw [osFolds_mats]; exact hin.mats)
      rfl rfl (by simpa using hcl) (fun j hj ↦ by
        have := hch j (by rw [hcl]; exact hj)
        rw [List.nil_append, List.getD_eq_getElem _ _ (by rw [hcl]; exact hj)]
        exact this) hin.R hin.r0 hin.r1
      (by unfold PendOk; simp only [hc, ↓reduceIte])
  have hfl : (ws.folds ++ chs).length = lv.foldsOff + lv.folds := by
    rw [List.length_append, hin.folds, hcl]
  have hml' : logN - (ws.folds ++ chs).length = lv.logCols := by rw [hfl, hml]
  rw [List.nil_append, glue_one] at hws'
  have hwf : ws'.folds = ws.folds ++ chs := by rw [hws']
  have hwg : ws'.glued = ws.glued ++ [⟨1 * lam, (ws.folds ++ chs).length,
      fun x ↦ inducedWeight lv.logCols qs (powers lam qs.length) x⟩] := by rw [hws']
  rw [levelHead_eq]
  have r1 := RunsTo.withRoots hrun1 R
  rw [← hfold] at r1
  have r2 : RunsWith (do
        let r ← levelMid (logN - (ws.folds ++ chs).length) []
        VerifierProgram.grindProofOfWork Whir.queryGrindingBits
        pure r) (st1.F σ) (ms ++ [nonce]) [] R (ms, []) ⟨st2.fsv σ, []⟩ R := by
    rw [hml']; exact RunsTo.withRoots hrun2 R
  have r3 : RunsWith (levelRest (logN - (ws.folds ++ chs).length) lvl level ([] ++ chs)
      { ws with
        target := σ (.n st1.t)
        quad := st1.quad σ
        folds := ws.folds ++ chs } []) ⟨st2.fsv σ, []⟩ xs3 [os] R ws'
      ((osLevelB c lvl lv st2).2.F σ) R := by
    rw [hml']; exact hrun3
  refine ⟨xs1 ++ ((ms ++ [nonce]) ++ (xs3 ++ [])), os, ws', ms,
    ⟨lam, qs, none, lv.foldsOff + lv.folds, lv.logCols⟩, ?_, ?_, hmsl, hfm, ?_, ?_, ?_, ?_, hq3,
    ht3, hfs3, hpad3, ?_, ?_, ?_, ?_⟩
  · refine readsAt_append hrd1 (readsAt_append ?_ ?_)
    · rw [hx1, ← hcur1]; exact hrd2
    · rw [List.append_nil, hx1, ← hcur1, List.length_append, hmsl, show [nonce].length = 1 from rfl,
        ← hcur2]
      exact hrd3
  · refine RunsWith.of_eq (RunsWith.bind' r1 (RunsWith.bind' r2 (RunsWith.bind' r3
      (runsWith_ret _ _ _)))) rfl rfl rfl rfl ?_ rfl rfl
    simp only [hml']
  · rw [hwg, hfl]; rfl
  · exact ⟨hrec, ⟨fun _ ↦ rfl, fun h ↦ absurd hfin h, fun z' hz ↦ by cases hz⟩, rfl, rfl⟩
  · rw [hwf, hfl]
  · intro j hj
    simp only [hwf] at hj ⊢
    rcases Nat.lt_or_ge j ws.folds.length with h | h
    · rw [List.getElem_append_left h]; exact hin.fch j h
    · rw [List.getElem_append_right h]
      have := hch (j - ws.folds.length) (by simp at hj; omega)
      have e : lv.foldsOff + (j - ws.folds.length) = j := by rw [← hin.folds]; omega
      rwa [e] at this
  · rw [hco3]; simp [st2, osFinal]
  · simp only [OsSt.cur, hcb3, hco3, List.length_append, List.length_cons, List.length_nil, hxl3,
      hmsl]
    have := hcur2
    simp only [OsSt.cur] at this hcur1
    rw [pow_add, ← mul_assoc, this, hcur1, hx1]
    ring
  · rw [hos]
    simp only [bOs, osQCall, hc, ↓reduceIte]
    rfl
  · simp only [List.length_append, hx1, hxl3, hmsl, List.length_cons, List.length_nil]; omega

end
end LeanVM.Guest.B1.Whir
