/-
  LeanVM.Guest.B1.Whir.CInvLast

  The final level after its folds (`levelLast`) and its closing rounds, read backwards from an
  accepting run.
-/

module

public import LeanVM.Guest.B1.Whir.CInvLevel
public import LeanVM.Guest.B1.Whir.LastRun

/-!
# The final level, backwards

`sumcheck_inv`: `n` plain rounds of `sumcheck _ 3` read their words `tailWords pairs`, every
challenge nonzero; they return `tailRun`'s.

`FinW`: what the final level reads after its folds: the lane, the query nonce, the phase, the
closing rounds' words; `FinW.qS`, `qs`, `F3`, `tail`, `wend`. `FinOk`: `levelLast_run`'s
hypotheses at it, the tail challenges nonzero. `levelLast_inv`: an accepting run of `levelLast`
read a `FinW` with `FinOk`, and returns `levelLast_run`'s.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none)

@[expose] public section

/-! ## The closing rounds -/

theorem tailRun_cons (c0 c2 : E) (rest : List (E × E)) (cap : List E) (claim : E) :
    tailRun ((c0, c2) :: rest) cap claim =
      let s := (⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve
      let t := tailRun rest s.squeeze.2.cap (c0 + s.squeeze.1 * (claim + (1 + s.squeeze.1) * c2))
      (s.squeeze.1 :: t.1, t.2.1, t.2.2) := rfl

/-- **`n` plain closing rounds, backwards.** -/
theorem sumcheck_inv : ∀ (n : ℕ) {claim : E} {cap xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : List E × E} {st1 : TSt},
    (∃ sp, (⟨cap, []⟩ : Fs).Carries sp) →
    runTz (sumcheck claim 3 (List.replicate n none)) ⟨⟨cap, []⟩, none, xs, os, R⟩ = some (a, st1) →
    ∃ pairs xs', pairs.length = n ∧ xs = tailWords pairs ++ xs' ∧
      (∀ c ∈ (tailRun pairs cap claim).1, c ≠ 0) ∧
      a = ((tailRun pairs cap claim).1, (tailRun pairs cap claim).2.1) ∧
      st1 = ⟨⟨(tailRun pairs cap claim).2.2, []⟩, none, xs', os, R⟩
  | 0, claim, cap, xs, os, R, a, st1, _, h => by
    have e := runTz_ret_inv (α := List E × E) h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨[], xs, rfl, rfl, by simp [tailRun], rfl, rfl⟩
  | n + 1, claim, cap, xs, os, R, a, st1, hc, h => by
    rw [List.replicate_succ] at h
    unfold sumcheck at h
    obtain ⟨msg, st2, h1, h2⟩ := runTz_bind_some h
    have h1c := h1
    unfold sumcheckRoundPoly at h1
    obtain ⟨c0, xs1, hs1, -, h1⟩ := runTz_readE h1
    obtain ⟨tl, xs2, htl, hs2, -⟩ := runTz_readScalars (3 - 2) _ _ rfl h1
    obtain ⟨c2, rfl⟩ : ∃ c2, tl = [c2] := by
      match tl, htl with
      | [c2], _ => exact ⟨c2, rfl⟩
    simp only at hs1 hs2
    have hxs : xs = [c0, c2] ++ xs2 := by rw [hs1, hs2]; rfl
    rw [hxs] at h1c
    have hf := runsTo_roundPolyNone ⟨cap, []⟩ claim c0 [c2] 3 rfl (by decide)
    obtain ⟨emsg, est2⟩ := runTz_detTo h1c hf hc
    subst emsg est2
    set s := (⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve with hs
    have es : ((⟨cap, []⟩ : Fs).absorb c0 dsObserve).absorbAll [c2] dsObserve = s := rfl
    rw [es] at h2
    obtain ⟨hr, h3⟩ := runTz_sampleE_none h2 rfl
    obtain ⟨p, st3, h4, h5⟩ := runTz_bind_some h3
    have hc1 : ∃ sp, (⟨s.squeeze.2.cap, []⟩ : Fs).Carries sp := ⟨⟨s.perm, [], none⟩, rfl, rfl, rfl⟩
    have h4' : runTz (sumcheck (polyEval [c0, claim + sumE [c2], c2] s.squeeze.1) 3
        (List.replicate n none)) ⟨⟨s.squeeze.2.cap, []⟩, none, xs2, os, R⟩ = some (p, st3) := h4
    rw [← tail_eval] at h4'
    obtain ⟨pairs, xs', hl, hx, hnz, ea, est⟩ := sumcheck_inv n hc1 h4'
    subst ea est
    have e := runTz_ret_inv h5
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨(c0, c2) :: pairs, xs', by simp [hl], by rw [hxs, hx]; rfl, ?_, ?_, ?_⟩
    · rw [tailRun_cons]
      intro c hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · exact hr
      · exact hnz c hc'
    · rw [tailRun_cons]
    · rw [tailRun_cons]


/-! ## What the final level reads -/

/-- **The final level's reads after its folds**: the lane, the query nonce, the phase of openings,
the closing rounds' words. -/
structure FinW where
  fold : List E
  nn : E
  phase : List Opening
  pairs : List (E × E)

namespace FinW

variable (W : FinW) (F : Fs) (d Q : ℕ)

/-- Its words, in stream order. -/
def words : List E := W.fold ++ [W.nn] ++ tailWords W.pairs

/-- The query grind's permutation. -/
def qS : KeccakState := (F.absorbAll W.fold dsObserve).nonceState W.nn

/-- The positions. -/
def qs : List ℕ := sqPositions d (sqSample (challengeOf (W.qS F)) (capOf (W.qS F))) Q

/-- The sponge after the positions' squeezes. -/
def F3 : Fs := ((⟨capOf (W.qS F), []⟩ : Fs).squeezeN (sqCount (128 / d) Q - 1)).2

/-- The closing rounds from the claim `claim`: challenges, final claim, capacity. -/
def tail (claim : E) : List E × E × List E := tailRun W.pairs (W.F3 F d Q).cap claim

end FinW

/-- What `levelLast_run` returns. -/
def FinW.wend (W : FinW) (logN laneFolds : ℕ) (level : Whir.Level) (s : WhirState) (F : Fs) :
    WhirEnd :=
  let mu := logN - s.alphas.length
  let T := W.tail F (mu + level.logInvRate) level.queries s.claim
  ⟨(s.alphas ++ T.1).drop laneFolds ++ (s.alphas ++ T.1).take laneFolds,
    s.glued.foldl (fun weight glued ↦ weight + glued.scalar *
      glued.weightAt ((s.alphas ++ T.1).drop glued.foldStart)) 0,
    multilinearEval (W.fold.take (2 ^ mu)) T.1, T.2.1⟩

/-- **`levelLast_run`'s hypotheses at what the final level read**, and its closing challenges
nonzero. -/
structure FinOk (logN index : ℕ) (level : Whir.Level) (s : WhirState) (rounds : List FoldRound)
    (F : Fs) (R : List (Digest × ℕ × ℕ)) (W : FinW) : Prop where
  root : ∃ root height width, R[index]? = some (root, height, width) ∧
    (∀ k (hk : k < (W.qs F (logN - s.alphas.length + level.logInvRate) level.queries).length)
        (ho : k < W.phase.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width
        (W.qs F (logN - s.alphas.length + level.logInvRate) level.queries)[k] W.phase[k]) = true)
  flen : W.fold.length = 2 ^ (logN - s.alphas.length) + level.fold
  ok1 : powOk Whir.queryGrindingBits (Keccak.lane (W.qS F) 2) = true
  plen : W.phase.length = (W.qs F (logN - s.alphas.length + level.logInvRate) level.queries).length
  idx : W.phase.map Opening.leafIndex = W.qs F (logN - s.alphas.length + level.logInvRate)
    level.queries
  req : ∀ k (hk : k < (W.qs F (logN - s.alphas.length + level.logInvRate) level.queries).length)
      (ho : k < W.phase.length),
    foldRow (specLanes index W.phase[k].leaf)
        (K.ofBits (W.qs F (logN - s.alphas.length + level.logInvRate) level.queries)[k]) rounds =
      novelEval W.fold (subspaceAt (logN - s.alphas.length)
        (K.ofBits (W.qs F (logN - s.alphas.length + level.logInvRate) level.queries)[k]))
  plen2 : W.pairs.length = logN - s.alphas.length
  tnz : ∀ c ∈ (W.tail F (logN - s.alphas.length + level.logInvRate) level.queries s.claim).1, c ≠ 0

/-- The checks of an accepted `require` over the zipped queries, pointwise. -/
theorem zip_all_get {qs : List ℕ} {rows : List (List K)} {P : ℕ × List K → Bool}
    (h : (List.zip qs rows).all P = true) :
    ∀ k (hk : k < qs.length) (ho : k < rows.length), P (qs[k], rows[k]) = true := by
  intro k hk ho
  have hz : k < (List.zip qs rows).length := by simp [hk, ho]
  have := List.all_eq_true.mp h _ (List.getElem_mem hz)
  simpa [List.getElem_zip] using this

/-- **The final level after its folds, backwards.** -/
theorem levelLast_inv {logN laneFolds index : ℕ} {level : Whir.Level} {s : WhirState}
    {rounds : List FoldRound} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : WhirEnd} {st1 : TSt}
    (hc : ∃ sp, F.Carries sp)
    (hP : 1 ≤ 128 / (logN - s.alphas.length + level.logInvRate)) (hQ : 0 < level.queries)
    (h : runTz (levelLast logN laneFolds index level s rounds) ⟨F, none, xs, os, R⟩ = some (a, st1)) :
    ∃ (W : FinW) (xs' : List E) (orest : List (List Opening)),
      xs = W.words ++ xs' ∧ os = W.phase :: orest ∧ FinOk logN index level s rounds F R W ∧
      a = W.wend logN laneFolds level s F ∧
      st1 = ⟨⟨(W.tail F (logN - s.alphas.length + level.logInvRate) level.queries s.claim).2.2, []⟩,
        none, xs', orest, R⟩ := by
  have h0 := h
  set mu := logN - s.alphas.length with hmu
  set d := mu + level.logInvRate with hd
  unfold levelLast at h
  obtain ⟨fold, xs1, hfl, hs1, h⟩ := runTz_readScalars (2 ^ mu + level.fold) _ _ rfl h
  obtain ⟨nn, xs2, hs2, -, hp1, h⟩ := runTz_grindPoW (by decide) h
  obtain ⟨qs', st2, hq1, h⟩ := runTz_bind_some h
  simp only at hs1 hs2
  set W0 : FinW := ⟨fold, nn, [], []⟩ with hW0
  have eS : (F.absorbAll fold dsObserve).nonceState nn = W0.qS F := rfl
  have hq2 := runTz_runT _ _ _ hq1
  rw [show xs2 = [] ++ xs2 from rfl] at hq2
  have hcq : ∃ sp, Fs.CarriesGround (capOf (W0.qS F)) (challengeOf (W0.qS F)) sp :=
    ⟨⟨W0.qS F, [], some (challengeOf (W0.qS F))⟩, rfl, rfl, rfl⟩
  have hfq := runT_of_runsFromG (sampleQueries_runG d level.queries hP hQ (capOf (W0.qS F))
    (challengeOf (W0.qS F))) hcq xs2 os R
  rw [eS] at hq2
  rw [hq2] at hfq
  simp only [Option.some.injEq, Prod.mk.injEq] at hfq
  obtain ⟨eqs, est2⟩ := hfq
  subst eqs est2
  have hqs : sqPositions d (fun j ↦ if j = 0 then challengeOf (W0.qS F) else
      ((⟨capOf (W0.qS F), []⟩ : Fs).squeezeN (j - 1)).2.squeeze.1) level.queries =
      W0.qs F d level.queries := rfl
  rw [hqs] at h
  obtain ⟨root, height, width, phase, orest, rows, hroot, hos, hop, h⟩ := runTz_queryB h
  simp only at hos hroot
  obtain ⟨hl, hopen, hidx, hrows⟩ := phase_of_some hop
  obtain ⟨hreq0, h⟩ := runTz_require h
  obtain ⟨p, st3, h4, -⟩ := runTz_bind_some h
  have e3 := squeezeN_mk (capOf (W0.qS F)) (sqCount (128 / d) level.queries - 1)
  have hc3 : ∃ sp, (⟨((⟨capOf (W0.qS F), []⟩ : Fs).squeezeN (sqCount (128 / d) level.queries - 1)).2.cap,
      []⟩ : Fs).Carries sp := by
    rw [eS] at hq1
    obtain ⟨sp, hsp⟩ := runTz_carries hq1
      ⟨⟨W0.qS F, [], some (challengeOf (W0.qS F))⟩, rfl, rfl, rfl⟩
    rw [e3] at hsp
    exact ⟨sp, tcar_none.mp hsp⟩
  have h4' : runTz (sumcheck s.claim 3 (List.replicate mu none))
      ⟨⟨((⟨capOf (W0.qS F), []⟩ : Fs).squeezeN (sqCount (128 / d) level.queries - 1)).2.cap, []⟩,
        none, xs2, orest, R⟩ = some (p, st3) := by
    rw [← e3]; exact h4
  obtain ⟨pairs, xs', hpl, hx, htnz, -, -⟩ := sumcheck_inv mu hc3 h4'
  set W : FinW := ⟨fold, nn, phase, pairs⟩ with hW
  have hxs : xs = W.words ++ xs' := by
    rw [hs1, hs2, hx]; simp [FinW.words, hW]
  have hreq : ∀ k (hk : k < (W.qs F d level.queries).length) (ho : k < phase.length),
      foldRow (specLanes index phase[k].leaf) (K.ofBits (W.qs F d level.queries)[k]) rounds =
        novelEval fold (subspaceAt mu (K.ofBits (W.qs F d level.queries)[k])) := by
    intro k hk ho
    have hr := zip_all_get (rows := rows) hreq0 k hk (by rw [hrows, List.length_map]; exact ho)
    simp only [hrows, List.getElem_map, decide_eq_true_eq] at hr
    exact hr
  have hfw := levelLast_run logN laneFolds index level s rounds F R hroot fold hfl nn (by decide) hP hQ
    hp1 (W.qs F d level.queries) rfl (W.F3 F d level.queries) rfl phase hl hopen hidx hreq pairs hpl
  rw [hxs, hos, show phase :: orest = [phase] ++ orest from rfl] at h0
  obtain ⟨ea, est⟩ := runTz_det h0 hfw hc
  exact ⟨W, xs', orest, hxs, hos, ⟨⟨root, height, width, hroot, hopen⟩, hfl, hp1, hl, hidx, hreq, hpl,
    htnz⟩, ea, est⟩

end
end LeanVM.Guest.B1.Whir
