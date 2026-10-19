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

end
end LeanVM.Guest.B1.VerifySub
