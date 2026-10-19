/-
  LeanVM.Guest.B1.Tables.GkrTrace

  The GKR walk's run, read back as the honest trace `verify_bus_gkr` follows: the two roots, the
  odd layer, each pair step's rounds and children.
-/

module

public import LeanVM.Guest.B1.Tables.GkrPair

/-!
# The honest trace

`RunsTo.gkrPhase_inv`: the two roots, the count root nonzero, the layers' run. `odd_data`: the
odd step's six children. `exists_trace`: the whole walk as a `GkrTrace`, its facts `GkrTrace.Ok`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The GKR phase's run, inverted.** -/
theorem RunsTo.gkrPhase_inv {depth : ℕ} {cv cv' : Digest} {xs : List E} {r : E × List E × List E}
    (h : RunsTo (gkrPhase depth) cv xs r cv') :
    ∃ (x0 cnt : E) (ys : List E) (s : GkrState), xs = x0 :: cnt :: ys ∧ cnt ≠ 0 ∧
      RunsTo (gkrLayers depth ⟨[x0, x0, cnt], []⟩) (obsCv (obsCv cv x0) cnt) ys s cv' ∧
      r = (cnt, s.point, s.values) := by
  unfold gkrPhase at h
  obtain ⟨x1, x2, r1, cv1, rfl, h1, h⟩ := RunsTo.bind_inv' h
  have h' : RunsTo (Prog.require (r1.1 ≠ 0) >>= fun _ => (pure r1 : Prog (E × List E × List E))) cv1 x2 r
    cv' := h
  obtain ⟨x3, x4, u, cv3, hx34, h3, hk⟩ := RunsTo.bind_inv' h'
  obtain ⟨hne, hx3, hc3⟩ := RunsTo.require_inv h3
  obtain ⟨hx4, hr, hc'⟩ := RunsTo.ret_inv hk
  subst hx3 hx4 hr hc3 hc'
  simp only [List.append_nil] at hx34
  subst hx34
  unfold verifyGkrGrandProducts at h1
  obtain ⟨y1, y2, x0, c1, rfl, g1, h1⟩ := RunsTo.bind_inv' h1
  obtain ⟨rfl, rfl⟩ := RunsTo.readE_inv g1
  obtain ⟨y3, y4, cnt, c3, rfl, g3, h1⟩ := RunsTo.bind_inv' h1
  obtain ⟨rfl, rfl⟩ := RunsTo.readE_inv g3
  obtain ⟨y5, y6, s, c5, rfl, g5, h1⟩ := RunsTo.bind_inv' h1
  obtain ⟨rfl, rfl, rfl⟩ := RunsTo.ret_inv h1
  exact ⟨x0, cnt, y5, s, by simp, hne, g5, rfl⟩

theorem l10cv_six (cvT : Digest) (a0 a1 b0 b1 d0 d1 : E) :
    l10cv cvT (fun i => ([a0, a1, b0, b1, d0, d1] : List E).getD i 0) 6 =
      obsAll (obsAll (obsAll cvT [a0, a1]) [b0, b1]) [d0, d1] := rfl

/-- **The odd step's run, read back**: from a state with no point, six children. -/
theorem odd_data {s s' : GkrState} {cv cv' : Digest} {ys : List E}
    (h : RunsTo (gkrStep 1 s) cv ys s' cv') (hp : s.point = []) :
    ∃ oes : ℕ → E, ys = (List.range 6).map oes ∧
      polyEval s.values (challengeOf (sqCv cv)) = oes 0 * oes 1 + challengeOf (sqCv cv) *
        (oes 2 * oes 3 + challengeOf (sqCv cv) * (oes 4 * oes 5)) ∧
      s'.point = [challengeOf (sqCv (l10cv (sqCv cv) oes 6))] ∧
      s'.values = [oes 0 + challengeOf (sqCv (l10cv (sqCv cv) oes 6)) * (oes 0 + oes 1),
        oes 2 + challengeOf (sqCv (l10cv (sqCv cv) oes 6)) * (oes 2 + oes 3),
        oes 4 + challengeOf (sqCv (l10cv (sqCv cv) oes 6)) * (oes 4 + oes 5)] ∧
      cv' = sqCv (l10cv (sqCv cv) oes 6) := by
  obtain ⟨ws, chs, cl, cvS, c0, c1, c2, hsc, h0, h1, h2, hreq, rfl, rfl, rfl⟩ := RunsTo.gkrStep_inv h
  rw [hp] at hsc
  obtain ⟨cl', cvr, wsr, ch, hc0, hcv0, -, hws, hpt, hfin, hcvS⟩ := RunsTo.sumcheck_inv _ _ _ _ _ _ _ hsc
  simp only [List.map_nil, List.length_nil, List.range_zero, List.flatMap_nil, List.map_nil] at hws hpt hfin hcvS
  subst hws hpt
  have e2 : ∀ (l : List E), l.length = 2 → ∃ a b, l = [a, b] := fun l hl => by
    match l, hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨a0, a1, rfl⟩ := e2 c0 h0
  obtain ⟨b0, b1, rfl⟩ := e2 c1 h1
  obtain ⟨d0, d1, rfl⟩ := e2 c2 h2
  refine ⟨fun i => ([a0, a1, b0, b1, d0, d1] : List E).getD i 0, rfl, ?_, ?_, ?_, ?_⟩
  · rw [← hc0, ← hfin, hreq, polyEval_three]
    simp [prodE]
  · rw [hcvS, hcv0]; rfl
  · rw [hcvS, hcv0, l10cv_six]
    simp [sqAll, multilinearEval, foldPairs]
    refine ⟨by ring, by ring, by ring⟩
  · rw [hcvS, hcv0]; rfl

/-! ## The trace -/

/-- The layer of pair `i`, after the odd layer when `sh = 1`. -/
def gL (sh i : ℕ) : ℕ := 2 * i + sh

/-- Pair `i`'s first round slot. -/
def gPos (sh : ℕ) : ℕ → ℕ
  | 0 => sh
  | i + 1 => gPos sh i + gL sh i + 1

/-- The cursor's offset at pair `i`. -/
def gCur (sh : ℕ) : ℕ → ℕ
  | 0 => 2 + 6 * sh
  | i + 1 => gCur sh i + 4 * gL sh i + 12

/-- What `odd_data` says of the odd step from `s` to `s'`. -/
def OddOk (s s' : GkrState) (cv cv' : Digest) (oes : ℕ → E) : Prop :=
  polyEval s.values (challengeOf (sqCv cv)) = oes 0 * oes 1 + challengeOf (sqCv cv) *
      (oes 2 * oes 3 + challengeOf (sqCv cv) * (oes 4 * oes 5)) ∧
    s'.point = [challengeOf (sqCv (l10cv (sqCv cv) oes 6))] ∧
    s'.values = [oes 0 + challengeOf (sqCv (l10cv (sqCv cv) oes 6)) * (oes 0 + oes 1),
      oes 2 + challengeOf (sqCv (l10cv (sqCv cv) oes 6)) * (oes 2 + oes 3),
      oes 4 + challengeOf (sqCv (l10cv (sqCv cv) oes 6)) * (oes 4 + oes 5)] ∧
    cv' = sqCv (l10cv (sqCv cv) oes 6)

/-- What `pair_data` says of a pair step from `s` (of `L` coordinates) to `s'` reading `ys`. -/
def PairOk (s s' : GkrState) (cv cv' : Digest) (ys : List E) (L : ℕ) (cl : ℕ → E)
    (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch es : ℕ → E) : Prop :=
  cl 0 = polyEval s.values (challengeOf (sqCv cv)) ∧ cvr 0 = sqCv cv ∧
    (∀ r < L, (wsr r).length = 4 ∧ RunsTo (roundPoly 5 (cl r) (some (s.point.getD r 0))) (cvr r)
      (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) ∧
    ys = (List.range L).flatMap wsr ++ (List.range 12).map es ∧
    cl L = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCv cv) * (es 4 * es 5 * es 6 * es 7 +
      challengeOf (sqCv cv) * (es 8 * es 9 * es 10 * es 11)) ∧
    s'.point = [challengeOf (sqCv (l10cv (cvr L) es 12)),
      challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))] ++ (List.range L).map ch ∧
    s'.values = [l10Next es 0 (challengeOf (sqCv (l10cv (cvr L) es 12)))
        (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))),
      l10Next es 4 (challengeOf (sqCv (l10cv (cvr L) es 12)))
        (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))),
      l10Next es 8 (challengeOf (sqCv (l10cv (cvr L) es 12)))
        (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12))))] ∧
    cv' = sqCv (sqCv (l10cv (cvr L) es 12))

theorem pair_ok {s s' : GkrState} {cv cv' : Digest} {ys : List E} {L : ℕ}
    (h : RunsTo (gkrStep 2 s) cv ys s' cv') (hL : s.point.length = L) :
    ∃ (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch es : ℕ → E),
      PairOk s s' cv cv' ys L cl cvr wsr ch es := pair_data h hL

/-- **The pairs' facts**, from the first state's point length. -/
theorem pairs_facts {m sh : ℕ} {P : ℕ → GkrState} {C : ℕ → Digest} {Y : ℕ → List E}
    (h0 : (P 0).point.length = sh)
    (hs : ∀ i < m, RunsTo (gkrStep 2 (P i)) (C i) (Y i) (P (i + 1)) (C (i + 1))) :
    (∀ i ≤ m, (P i).point.length = gL sh i) ∧
      ∃ (CL : ℕ → ℕ → E) (CVR : ℕ → ℕ → Digest) (WSR : ℕ → ℕ → List E) (CH ES : ℕ → ℕ → E),
        ∀ i < m, PairOk (P i) (P (i + 1)) (C i) (C (i + 1)) (Y i) (gL sh i) (CL i) (CVR i) (WSR i)
          (CH i) (ES i) := by
  have hlen : ∀ i ≤ m, (P i).point.length = gL sh i := by
    intro i hi
    induction i with
    | zero => simpa [gL] using h0
    | succ i ih =>
      obtain ⟨_, _, _, _, _, -, -, -, -, -, hpt, -, -⟩ := pair_ok (hs i (by omega)) (ih (by omega))
      rw [hpt]; simp [gL]; omega
  refine ⟨hlen, ?_⟩
  have : ∀ i, ∃ (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch es : ℕ → E), i < m →
      PairOk (P i) (P (i + 1)) (C i) (C (i + 1)) (Y i) (gL sh i) cl cvr wsr ch es := by
    intro i
    by_cases hi : i < m
    · obtain ⟨cl, cvr, wsr, ch, es, h⟩ := pair_ok (hs i hi) (hlen i (by omega))
      exact ⟨cl, cvr, wsr, ch, es, fun _ => h⟩
    · exact ⟨fun _ => 0, fun _ => default, fun _ => [], fun _ => 0, fun _ => 0, fun h => absurd h hi⟩
  choose CL CVR WSR CH ES hP using this
  exact ⟨CL, CVR, WSR, CH, ES, fun i hi => hP i hi⟩

/-- The honest trace of the GKR walk. -/
structure GkrTrace where
  x0 : E
  cnt : E
  oes : ℕ → E
  P : ℕ → GkrState
  C : ℕ → Digest
  Y : ℕ → List E
  CL : ℕ → ℕ → E
  CVR : ℕ → ℕ → Digest
  WSR : ℕ → ℕ → List E
  CH : ℕ → ℕ → E
  ES : ℕ → ℕ → E

/-- **The trace's facts** for a run of `gkrPhase μ` from `cv` reading `xs` to `r`, `cv'`. -/
structure GkrTrace.Ok (T : GkrTrace) (μ : ℕ) (cv : Digest) (xs : List E) (r : E × List E × List E)
    (cv' : Digest) : Prop where
  hxs : xs = T.x0 :: T.cnt :: ((if μ % 2 = 1 then (List.range 6).map T.oes else []) ++
    (List.range (μ / 2)).flatMap T.Y)
  hcnt : T.cnt ≠ 0
  even : μ % 2 = 0 → T.P 0 = ⟨[T.x0, T.x0, T.cnt], []⟩ ∧ T.C 0 = obsCv (obsCv cv T.x0) T.cnt
  odd : μ % 2 = 1 → OddOk ⟨[T.x0, T.x0, T.cnt], []⟩ (T.P 0) (obsCv (obsCv cv T.x0) T.cnt) (T.C 0) T.oes
  pair : ∀ i < μ / 2, PairOk (T.P i) (T.P (i + 1)) (T.C i) (T.C (i + 1)) (T.Y i) (gL (μ % 2) i)
    (T.CL i) (T.CVR i) (T.WSR i) (T.CH i) (T.ES i)
  hlen : ∀ i ≤ μ / 2, (T.P i).point.length = gL (μ % 2) i
  hr : r = (T.cnt, (T.P (μ / 2)).point, (T.P (μ / 2)).values)
  hcv : cv' = T.C (μ / 2)

/-- **A run of the GKR phase has an honest trace.** -/
theorem exists_trace {μ : ℕ} {cv cv' : Digest} {xs : List E} {r : E × List E × List E}
    (h : RunsTo (gkrPhase μ) cv xs r cv') : ∃ T : GkrTrace, T.Ok μ cv xs r cv' := by
  obtain ⟨x0, cnt, ys, s, rfl, hne, hL, rfl⟩ := RunsTo.gkrPhase_inv h
  rcases Nat.mod_two_eq_zero_or_one μ with hsh | hsh
  · have hμ : μ = 2 * (μ / 2) := by omega
    rw [hμ, gkrLayers_even] at hL
    obtain ⟨P, C, Y, h0, hc0, hs, hys, rfl, rfl⟩ := RunsTo.gkrPairs_inv _ _ _ _ _ _ hL
    obtain ⟨hlen, CL, CVR, WSR, CH, ES, hP⟩ := pairs_facts (sh := 0) (by rw [h0]; rfl) hs
    refine ⟨⟨x0, cnt, fun _ => 0, P, C, Y, CL, CVR, WSR, CH, ES⟩, ⟨?_, hne, fun _ => ⟨h0, hc0⟩,
      fun h => by omega, ?_, ?_, rfl, rfl⟩⟩
    · simp only [hsh, ite_neg' (by omega : ¬ (0 = 1)), List.nil_append, hys]
    · rw [hsh]; exact hP
    · rw [hsh]; exact hlen
  · have hμ : μ = 2 * (μ / 2) + 1 := by omega
    rw [hμ, gkrLayers_odd] at hL
    obtain ⟨y1, y2, s1, cv1, rfl, h1, hL2⟩ := RunsTo.bind_inv' hL
    obtain ⟨oes, rfl, hc, hpt, hv, hcv⟩ := odd_data h1 rfl
    obtain ⟨P, C, Y, h0, hc0, hs, hys, rfl, rfl⟩ := RunsTo.gkrPairs_inv _ _ _ _ _ _ hL2
    obtain ⟨hlen, CL, CVR, WSR, CH, ES, hP⟩ := pairs_facts (sh := 1) (by rw [h0, hpt]; rfl) hs
    refine ⟨⟨x0, cnt, oes, P, C, Y, CL, CVR, WSR, CH, ES⟩, ⟨?_, hne, fun h => by omega,
      fun _ => ?_, ?_, ?_, rfl, rfl⟩⟩
    · simp only [hsh, hys, ↓reduceIte]
    · show OddOk _ (P 0) _ (C 0) oes
      rw [h0, hc0]; exact ⟨hc, hpt, hv, hcv⟩
    · rw [hsh]; exact hP
    · rw [hsh]; exact hlen

end
end LeanVM.Guest.B1.VerifySub
