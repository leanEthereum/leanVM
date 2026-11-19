module

public import NativeVm.Equiv.WhirPure

/-!
# Phase 7b: the stacked opening, the model against the statement

`Sim.sampleQueries`: the query positions are the statement's as numbers (`depth ≤ 64`).
`Sim.foldRound`, `Sim.foldRounds`: the fold rounds, the level loop's state related by
`WhirStateW.Rel` and the rounds' challenges equal. `Sim.whirLevels`: every level from related
states, each level's depth `μ + ν` at most `64` (`ladder_depth`: the ladder's rates are at most
`34` and the stack at most `30` variables). `Sim.verifyWhir` and `Sim.verifyStackedOpening`: the
phase, from stack claims related by `StackClaimW.Rel`, the batching scales and claims (`BasisW`)
evaluating as the statement's `evaluateBasis`.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## Query positions -/

theorem Sim.sampleQueriesAux {depth : ℕ} (hd : depth ≤ 64) : ∀ fuel remaining : ℕ,
    Sim (Model.sampleQueriesAux depth fuel remaining) (Verifier.sampleQueriesAux depth fuel remaining)
      fun a b ↦ a.toList.map UInt64.toNat = b
  | 0, _ => Sim.pure rfl
  | fuel + 1, remaining => by
    unfold Model.sampleQueriesAux Verifier.sampleQueriesAux
    by_cases h : remaining = 0
    · simp only [h, ite_true]
      exact Sim.pure rfl
    · simp only [h, ite_false]
      refine Sim.bind Sim.sampleChallenge fun c c' hc ↦ ?_
      refine Sim.bind (Sim.sampleQueriesAux hd fuel _) fun rest rest' hr ↦ Sim.pure ?_
      subst hc hr
      simp [Function.comp_def, queryBits_toNat _ _ hd]

theorem Sim.sampleQueries {depth : ℕ} (hd : depth ≤ 64) (count : ℕ) :
    Sim (Model.sampleQueries depth count) (Verifier.sampleQueries depth count)
      fun a b ↦ a.toList.map UInt64.toNat = b :=
  Sim.sampleQueriesAux hd count count

/-! ## Fold rounds -/

theorem Sim.foldRound {s : WhirStateW} {s' : Verifier.WhirState} (h : s.Rel s') :
    Sim (Model.foldRound s) (Verifier.foldRound s') fun a b ↦ a.1.Rel b.1 ∧ a.2.toSpec = b.2 := by
  unfold Model.foldRound Verifier.foldRound
  refine Sim.bind Sim.readScalar fun u0 u0' hu ↦ ?_
  refine Sim.bind Sim.readScalar fun w w' hw ↦ ?_
  refine Sim.bind Sim.readScalar fun c0 c0' h0 ↦ ?_
  refine Sim.bind Sim.readScalar fun c1 c1' h1 ↦ ?_
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind Sim.sampleChallenge fun al al' ha ↦ ?_
  refine Sim.bind Sim.sampleChallenge fun be be' hb ↦ Sim.pure ⟨⟨?_, ?_, h.glued⟩, ?_⟩
  · simp only [EW.toE_add, EW.toE_mul, hu, hw, h0, h1, ha, hb, h.claim]
  · simp [h.alphas, ha]
  · simp [FoldRoundW.toSpec, ha, hb]

theorem Sim.foldRounds_aux
    {step : WhirStateW × Array FoldRoundW → ℕ → VM (WhirStateW × Array FoldRoundW)}
    (hstep : ∀ acc x, step acc x = Model.foldRound acc.1 >>= fun p ↦ Pure.pure (p.1, acc.2.push p.2)) :
    ∀ (l : List ℕ) {s : WhirStateW} {s' : Verifier.WhirState} (acc : Array FoldRoundW)
      (acc' : List Verifier.FoldRound), s.Rel s' → acc.toList.map FoldRoundW.toSpec = acc' →
      Sim (l.foldlM step (s, acc)) (Verifier.foldRounds l.length s')
        fun a b ↦ a.1.Rel b.1 ∧ a.2.toList.map FoldRoundW.toSpec = acc' ++ b.2
  | [], _, _, _, _, hs, hacc => Sim.pure ⟨hs, by simpa using hacc⟩
  | x :: l, s, s', acc, acc', hs, hacc => by
    rw [List.foldlM_cons, hstep, bind_assoc, List.length_cons, Verifier.foldRounds]
    refine Sim.bind (Sim.foldRound hs) fun ⟨s1, r⟩ ⟨s1', r'⟩ ⟨h1, hr⟩ ↦ ?_
    simp only [pure_bind]
    rw [← bind_pure (List.foldlM step (s1, acc.push r) l)]
    refine Sim.bind (Sim.foldRounds_aux hstep l (acc' := acc' ++ [r']) (acc.push r) h1
      (by simp [hacc, hr])) fun a ⟨b1, b2⟩ hab ↦ Sim.pure ⟨hab.1, ?_⟩
    simp [hab.2]

theorem Sim.foldRounds (n : ℕ) {s : WhirStateW} {s' : Verifier.WhirState} (h : s.Rel s') :
    Sim (Model.foldRounds n s) (Verifier.foldRounds n s')
      fun a b ↦ a.1.Rel b.1 ∧ a.2.toList.map FoldRoundW.toSpec = b.2 := by
  have := Sim.foldRounds_aux (fun _ _ ↦ rfl) (List.range n) #[] [] h rfl
  rw [List.length_range] at this
  exact Sim.mono this fun _ _ h ↦ ⟨h.1, by simpa using h.2⟩

/-! ## A level's pure steps -/

theorem toList_map_lanes (index : ℕ) (row : Array UInt64) :
    (if index = 0 then row.reverse.map EW.ofK else Model.extRow row).toList.map EW.toE =
      if index = 0 then (row.toList.map K.ofLane).reverse.map ofK
      else Verifier.extRow (row.toList.map K.ofLane) := by
  split
  · simp [Function.comp_def]
  · exact toList_map_extRow row

theorem glueLevel_rel {s : WhirStateW} {s' : Verifier.WhirState} (h : s.Rel s') {lam : EW} {lam' : E}
    (hl : lam.toE = lam') (mu : ℕ) {oodPoint : Array EW} {oodPoint' : List E}
    (hp : oodPoint.toList.map EW.toE = oodPoint') {oodValue : EW} {oodValue' : E}
    (hv : oodValue.toE = oodValue') {queries : Array UInt64} {queries' : List ℕ}
    (hq : queries.toList.map UInt64.toNat = queries') {queryWeights : Array EW}
    {queryWeights' : List E} (hw : queryWeights.toList.map EW.toE = queryWeights')
    {batched : EW} {batched' : E} (hb : batched.toE = batched') :
    (Model.glueLevel s lam mu oodPoint oodValue queries queryWeights batched).Rel
      (Verifier.glueLevel s' lam' mu oodPoint' oodValue' queries' queryWeights' batched') := by
  have hsize : s.alphas.size = s'.alphas.length := by
    rw [← h.alphas, List.length_map, Array.length_toList]
  refine ⟨?_, h.alphas, ?_⟩
  · simp [Model.glueLevel, Verifier.glueLevel, h.claim, hl, hv, hb]
  · simp only [Model.glueLevel, Verifier.glueLevel, Array.toList_append]
    refine List.rel_append h.glued (.cons ⟨hl, hsize, ?_⟩ (.cons ⟨?_, hsize, ?_⟩ .nil))
    · subst hp
      exact GluedWeight.rel_eq oodPoint
    · simp [hl]
    · subst hq hw
      exact GluedWeight.rel_induced mu queries queryWeights

/-! ## The ladder's depths -/

theorem levelsFrom_rate : ∀ (fuel remaining prevFold prevRate reduction : ℕ),
    ∀ g ∈ Whir.levelsFrom fuel remaining prevFold prevRate reduction,
      g.2 ≤ prevRate + prevFold + remaining
  | 0, _, _, _, _, g, hg => by simp [Whir.levelsFrom] at hg
  | fuel + 1, remaining, prevFold, prevRate, reduction, g, hg => by
    rw [Whir.levelsFrom] at hg
    split at hg
    · simp at hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · simp only; omega
      · have := levelsFrom_rate fuel _ _ _ _ g hg
        simp only [Whir.subsequentFold] at this ⊢
        omega

theorem mem_zipWith_level {geometry : List (ℕ × ℕ)} {queries : List ℕ} {l : Whir.Level}
    (hl : l ∈ List.zipWith (fun (g : ℕ × ℕ) q ↦ (⟨g.1, g.2, q⟩ : Whir.Level)) geometry queries) :
    ∃ g ∈ geometry, l.logInvRate = g.2 := by
  induction geometry generalizing queries with
  | nil => simp at hl
  | cons g gs ih =>
    cases queries with
    | nil => simp at hl
    | cons q qs =>
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ⟨g, List.mem_cons_self .., rfl⟩
      · obtain ⟨g', hg', h⟩ := ih hl
        exact ⟨g', List.mem_cons_of_mem _ hg', h⟩

/-- Every level of the ladder queries positions of at most `64` bits: `μ + ν ≤ 30 + 34`. -/
theorem ladder_depth {logN logInvRate : ℕ} {config : List Whir.Level}
    (h : Whir.ladder logN logInvRate = some config) : ∀ l ∈ config, logN + l.logInvRate ≤ 64 := by
  intro l hl
  unfold Whir.ladder at h
  split at h
  · rename_i hadm
    obtain ⟨h16, h30, -, h4⟩ := hadm
    dsimp only at h
    split at h
    · cases h
      obtain ⟨g, hg, hr⟩ := mem_zipWith_level hl
      rw [hr]
      unfold Whir.ladderShape at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp only; simp only [Whir.minLogStack, Whir.maxLogStack] at h16 h30; omega
      · have := levelsFrom_rate _ _ _ _ _ g hg
        simp only [Whir.initialFold, Whir.minLogStack, Whir.maxLogStack] at this h16 h30
        omega
    · cases h
  · cases h

/-! ## The level loop -/

/-- **The level loop**: from related states, every level of the ladder. -/
theorem Sim.whirLevels {logN laneFolds : ℕ} {basis : BasisW} {evaluateBasis : List E → E}
    (hb : basis.Rel evaluateBasis) :
    ∀ (levels : List Whir.Level) (index : ℕ) {s : WhirStateW} {s' : Verifier.WhirState},
      (∀ l ∈ levels, logN + l.logInvRate ≤ 64) → s.Rel s' →
      Sim (Model.whirLevels logN laneFolds basis index levels s)
        (Verifier.whirLevels logN laneFolds evaluateBasis index levels s') fun _ _ ↦ True
  | [], _, _, _, _, _ => Sim.reject
  | level :: rest, index, s, s', hdepth, hs => by
    rw [Model.whirLevels, Verifier.whirLevels]
    refine Sim.bind (Sim.foldRounds _ hs) fun ⟨s1, rounds⟩ ⟨s1', rounds'⟩ ⟨h1, hr⟩ ↦ ?_
    have hmu : s1.alphas.size = s1'.alphas.length := by
      rw [← h1.alphas, List.length_map, Array.length_toList]
    have hd : logN - s1'.alphas.length + level.logInvRate ≤ 64 := by
      have := hdepth level List.mem_cons_self
      omega
    dsimp only
    rw [hmu]
    cases rest with
    | nil =>
      refine Sim.bind (Sim.readScalars _) fun folded folded' ⟨hf, _⟩ ↦ ?_
      refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
      refine Sim.bind (Sim.sampleQueries hd _) fun queries queries' hq ↦ ?_
      refine Sim.bind (Sim.queryOpenings _ hq) fun words words' hw ↦ ?_
      refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ ?_
      · rw [← Array.all_toList, Array.toList_zip, ← hq, ← hw, List.zip_map, List.all_map]
        refine Eq.to_iff (congrArg (· = true) (congrArg (List.all _) (funext fun x ↦ ?_)))
        rcases x with ⟨q, row⟩
        rw [Function.comp_apply, Prod.map_apply, Bool.eq_iff_iff, EW.beq_iff_toE, ← subspaceAt,
          toE_foldRow, toE_novelEval, toList_map_lanes, toList_map_subspaceAt, ofBits_toNat, hr, hf,
          decide_eq_true_iff]
      refine Sim.bind (Sim.sumcheckPlain h1.claim 3 _) fun ⟨tail, claim⟩ ⟨tail', claim'⟩ ⟨ht, hc⟩ ↦ ?_
      refine Sim.require ?_
      have hpoint : (s1.alphas ++ tail).toList.map EW.toE = s1'.alphas ++ tail' := by
        rw [Array.toList_append, List.map_append, h1.alphas, ht]
      rw [EW.beq_iff_toE, EW.toE_mul, toE_multilinearEval, toList_extract_zero, List.map_take, hf, ht,
        hc, ← Array.foldl_toList, foldl_forall₂ EW.toE (Q := GluedClaimW.Rel)
          (f' := fun weight glued ↦ weight + glued.scalar *
            glued.weightAt ((s1'.alphas ++ tail').drop glued.foldStart)) ?_ h1.glued, hb,
        Array.toList_append, toList_extract_end, toList_extract_zero, List.map_append,
        List.map_drop, List.map_take, hpoint]
      intro weight g g' hg
      rw [EW.toE_add, EW.toE_mul, hg.scalar, hg.weight, toList_extract_end, List.map_drop, hpoint,
        hg.foldStart]
    | cons next rest =>
      simp only [Model.levelShape, Verifier.levelShape]
      refine Sim.bind (Sim.readCommitment _ _) fun _ _ _ ↦ ?_
      refine Sim.bind (Sim.readScalars _) fun high high' ⟨hh, _⟩ ↦ ?_
      refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
      refine Sim.bind (Sim.sampleChallenges _) fun oodPoint oodPoint' ⟨hp, _⟩ ↦ ?_
      refine Sim.bind Sim.readScalar fun oodValue oodValue' hv ↦ ?_
      refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
      refine Sim.bind (Sim.sampleQueries hd _) fun queries queries' hq ↦ ?_
      refine Sim.bind Sim.sampleChallenge fun lam lam' hl ↦ ?_
      refine Sim.bind (Sim.queryOpenings _ hq) fun words words' hw ↦ ?_
      have hsize : queries.size = queries'.length := by
        rw [← hq, List.length_map, Array.length_toList]
      refine Sim.whirLevels hb (next :: rest) (index + 1)
        (fun l hl ↦ hdepth l (List.mem_cons_of_mem _ hl))
        (glueLevel_rel h1 hl _ hp hv hq (by rw [toList_map_powers, hl, hsize]) ?_)
      rw [toE_sumE, Array.toList_zipWith, Array.toList_zip, List.map_zipWith, ← hq, ← hw,
        List.length_map, Array.length_toList, ← hl, ← toList_map_powers, List.zip_map,
        List.zipWith_map]
      refine congrArg Verifier.sumE
        (congrArg (fun F ↦ List.zipWith F _ _) (funext fun x ↦ funext fun qw ↦ ?_))
      rcases x with ⟨q, row⟩
      simp only [Prod.map_apply]
      rw [EW.toE_mul, EW.toE_add, EW.toE_scale, toE_foldRow, toE_novelEval, toList_map_lanes, hr, hh,
        ← subspaceAt, toList_map_subspaceAt, ofBits_toNat, getD_map K.ofLane, K_ofLane_zero,
        toList_map_subspaceAt, mul_comm (ofK _)]

/-! ## The phase -/

theorem Sim.verifyWhir {logN logInvRate : ℕ} {target : EW} {target' : E} (ht : target.toE = target')
    {basis : BasisW} {evaluateBasis : List E → E} (hb : basis.Rel evaluateBasis) :
    Sim (Model.verifyWhir logN logInvRate target basis)
      (Verifier.verifyWhir logN logInvRate target' evaluateBasis) fun _ _ ↦ True := by
  unfold Model.verifyWhir Verifier.verifyWhir
  refine Sim.bind (Sim.liftOpt (R := fun c c' ↦ c = c' ∧ Whir.ladder logN logInvRate = some c) ?_)
    fun config config' ⟨hc, hl⟩ ↦ ?_
  · cases h : Whir.ladder logN logInvRate
    · exact .none
    · exact .some ⟨rfl, rfl⟩
  subst hc
  exact Sim.whirLevels hb config 0 (ladder_depth hl) ⟨ht, rfl, .nil⟩

/-- **Phase 7b.** -/
theorem Sim.verifyStackedOpening (stackLog logInvRate : ℕ) {claims : Array StackClaimW}
    {claims' : List Verifier.StackClaim} (hc : List.Forall₂ StackClaimW.Rel claims.toList claims') :
    Sim (Model.verifyStackedOpening stackLog logInvRate claims)
      (Verifier.verifyStackedOpening stackLog logInvRate claims') fun _ _ ↦ True := by
  unfold Model.verifyStackedOpening Verifier.verifyStackedOpening
  have hsize : claims.size = claims'.length := by
    rw [← hc.length_eq, Array.length_toList]
  refine Sim.bind (Sim.require (by rw [hsize, decide_eq_true_iff])) fun _ _ _ ↦ ?_
  refine Sim.bind Sim.sampleChallenge fun c c' hcc ↦ ?_
  have hs : (powers c claims.size).toList.map EW.toE = Verifier.powers c' claims'.length := by
    rw [toList_map_powers, hcc, hsize]
  refine Sim.verifyWhir ?_ (BasisW.rel_mk hs hc)
  rw [toE_dot, hs, Array.toList_map, List.map_map]
  congr 1
  clear hs hsize
  generalize claims.toList = l at hc ⊢
  induction hc with
  | nil => rfl
  | cons h _ ih => exact congrArg₂ _ h.2 ih

end NativeVm.Equiv
