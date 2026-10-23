/-
  LeanVM.Guest.B1.Tables.GkrInv

  The GKR walk's run, inverted: a run of a step, of a sumcheck, of the layers, read back as the
  runs `runsTo_gkrStep`, `runsTo_sumcheck` compose.
-/

module

public import LeanVM.Guest.B1.Tables.GkrRunInv

/-!
# The GKR run, inverted

From a run of `gkrStep` its sumcheck, its three children and its check (`RunsTo.gkrStep_inv`); of
a sumcheck its rounds (`RunsTo.sumcheck_inv`); of the layers each step in turn
(`RunsTo.gkrPairs_inv`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem RunsTo.bind_inv' {α β : Type} {p : Prog α} {f : α → Prog β} {cv cv'' : Digest}
    {xs : List E} {b : β} (h : RunsTo (p >>= f) cv xs b cv'') :
    ∃ (xs1 xs2 : List E) (a : α) (cv1 : Digest), xs = xs1 ++ xs2 ∧ RunsTo p cv xs1 a cv1 ∧
      RunsTo (f a) cv1 xs2 b cv'' := RunsTo.bind_inv h

theorem RunsTo.ret_inv {α : Type} {a b : α} {cv cv' : Digest} {xs : List E}
    (h : RunsTo (pure a : Prog α) cv xs b cv') : xs = [] ∧ b = a ∧ cv' = cv :=
  (runsTo_ret a cv).det_nil h

theorem RunsTo.require_inv {c : Prop} [Decidable c] {cv cv' : Digest} {xs : List E} {u : Unit}
    (h : RunsTo (Prog.require c) cv xs u cv') : c ∧ xs = [] ∧ cv' = cv := by
  by_cases hc : c
  · obtain ⟨h1, -, h3⟩ := (runsTo_require hc cv).det_nil h
    exact ⟨hc, h1, h3⟩
  · have := h [] [] []
    simp [Prog.require, hc, runId, Compile.run] at this

theorem RunsTo.sampleE_inv {cv cv' : Digest} {xs : List E} {a : E}
    (h : RunsTo Prog.sampleE cv xs a cv') : xs = [] ∧ a = challengeOf (sqCv cv) ∧ cv' = sqCv cv :=
  (runsTo_sampleE cv).det_nil h

theorem RunsTo.sampleN_inv {n : ℕ} {cv cv' : Digest} {xs a : List E}
    (h : RunsTo (Prog.sampleN n) cv xs a cv') : xs = [] ∧ a = (sqAll n cv).1 ∧ cv' = (sqAll n cv).2 :=
  (runsTo_sampleN n cv).det_nil h

/-- **A step's run, inverted**: its sumcheck, its three children of `2^step` words, its check. -/
theorem RunsTo.gkrStep_inv {step : ℕ} {s s' : GkrState} {cv cv' : Digest} {ys : List E}
    (h : RunsTo (gkrStep step s) cv ys s' cv') :
    ∃ (ws chs : List E) (cl : E) (cvS : Digest) (c0 c1 c2 : List E),
      RunsTo (sumcheck (polyEval s.values (challengeOf (sqCv cv))) (2 ^ step + 1)
        (s.point.map some)) (sqCv cv) ws (chs, cl) cvS ∧
      c0.length = 2 ^ step ∧ c1.length = 2 ^ step ∧ c2.length = 2 ^ step ∧
      cl = polyEval [prodE c0, prodE c1, prodE c2] (challengeOf (sqCv cv)) ∧
      ys = ws ++ (c0 ++ (c1 ++ c2)) ∧
      s' = ⟨[c0, c1, c2].map (multilinearEval ·
          (sqAll step (obsAll (obsAll (obsAll cvS c0) c1) c2)).1),
        (sqAll step (obsAll (obsAll (obsAll cvS c0) c1) c2)).1 ++ chs⟩ ∧
      cv' = (sqAll step (obsAll (obsAll (obsAll cvS c0) c1) c2)).2 := by
  unfold gkrStep at h
  obtain ⟨x1, y1, comb, cv1, rfl, h1, h⟩ := RunsTo.bind_inv' h
  obtain ⟨rfl, rfl, rfl⟩ := RunsTo.sampleE_inv h1
  obtain ⟨ws, y2, ⟨chs, cl⟩, cvS, rfl, hsc, h⟩ := RunsTo.bind_inv' h
  obtain ⟨c0, y3, c0', cv3, rfl, h3, h⟩ := RunsTo.bind_inv' h
  obtain ⟨hl0, rfl, rfl⟩ := RunsTo.readN_inv h3
  obtain ⟨c1, y4, c1', cv4, rfl, h4, h⟩ := RunsTo.bind_inv' h
  obtain ⟨hl1, rfl, rfl⟩ := RunsTo.readN_inv h4
  obtain ⟨c2, y5, c2', cv5, rfl, h5, h⟩ := RunsTo.bind_inv' h
  obtain ⟨hl2, rfl, rfl⟩ := RunsTo.readN_inv h5
  obtain ⟨y6, y7, u, cv6, rfl, h6, h⟩ := RunsTo.bind_inv' h
  obtain ⟨hreq, rfl, rfl⟩ := RunsTo.require_inv h6
  obtain ⟨y8, y9, yy, cv8, rfl, h8, h⟩ := RunsTo.bind_inv' h
  obtain ⟨rfl, rfl, rfl⟩ := RunsTo.sampleN_inv h8
  obtain ⟨rfl, rfl, rfl⟩ := RunsTo.ret_inv h
  refine ⟨ws, chs, cl, cvS, c0', c1', c2', hsc, hl0, hl1, hl2, ?_, by simp, rfl, rfl⟩
  simpa using hreq

theorem RunsTo.readE_inv {cv cv' : Digest} {xs : List E} {a : E}
    (h : RunsTo Prog.readE cv xs a cv') : xs = [a] ∧ cv' = obsCv cv a := by
  match xs, h with
  | [], h =>
    obtain ⟨e1, -, -⟩ := (runsTo_readE cv 0).det h ⟨[0], Or.inr rfl⟩
    simp at e1
  | y :: ys, h =>
    obtain ⟨e1, e2, e3⟩ := (runsTo_readE cv y).det h ⟨ys, Or.inl rfl⟩
    rw [← e1, ← e2]
    exact ⟨rfl, e3.symm⟩

/-- **A sumcheck's run, inverted**, round by round. -/
theorem RunsTo.sumcheck_inv {count : ℕ} : ∀ (es : List (Option E)) (claim : E) (cv cv2 : Digest)
    (ws pt : List E) (fin : E), RunsTo (sumcheck claim count es) cv ws (pt, fin) cv2 →
    ∃ (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch : ℕ → E), cl 0 = claim ∧ cvr 0 = cv ∧
      (∀ r (hr : r < es.length),
        RunsTo (roundPoly count (cl r) es[r]) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) ∧
      ws = (List.range es.length).flatMap wsr ∧ pt = (List.range es.length).map ch ∧
      fin = cl es.length ∧ cv2 = cvr es.length
  | [], claim, cv, cv2, ws, pt, fin, h => by
    have h' : RunsTo (pure ([], claim) : Prog (List E × E)) cv ws (pt, fin) cv2 := h
    obtain ⟨hx, he, hc⟩ := RunsTo.ret_inv h'
    simp only [Prod.mk.injEq] at he
    exact ⟨fun _ => claim, fun _ => cv, fun _ => [], fun _ => 0, rfl, rfl,
      fun r hr => absurd hr (by simp), by simp [hx], by simp [he.1], he.2, hc⟩
  | e :: es, claim, cv, cv2, ws, pt, fin, h => by
    rw [sumcheck_cons_eq] at h
    obtain ⟨w1, y1, ⟨claim', c⟩, cv1, rfl, h1, h⟩ := RunsTo.bind_inv' h
    obtain ⟨w2, y2, ⟨pt', fin'⟩, cv3, rfl, h2, h⟩ := RunsTo.bind_inv' h
    obtain ⟨rfl, he, rfl⟩ := RunsTo.ret_inv h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨cl, cvr, wsr, ch, h0, hc0, hr, hw, hp, hf, hcv⟩ :=
      RunsTo.sumcheck_inv es claim' cv1 cv2 w2 pt' fin h2
    refine ⟨fun k => if k = 0 then claim else cl (k - 1), fun k => if k = 0 then cv else cvr (k - 1),
      fun k => if k = 0 then w1 else wsr (k - 1), fun k => if k = 0 then c else ch (k - 1),
      rfl, rfl, fun r hr' => ?_, ?_, ?_, ?_, ?_⟩
    · match r with
      | 0 => simpa [h0, hc0] using h1
      | r + 1 =>
        have := hr r (by simpa using hr')
        simpa using this
    · rw [hw, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp
    · rw [hp, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [Function.comp_def]
    · simp [hf]
    · simp [hcv]

/-- **The pairs' run, inverted**, step by step. -/
theorem RunsTo.gkrPairs_inv : ∀ (m : ℕ) (s : GkrState) (cv : Digest) (xs : List E) (s' : GkrState)
    (cv' : Digest), RunsTo (gkrPairs m s) cv xs s' cv' →
    ∃ (st : ℕ → GkrState) (cvs : ℕ → Digest) (ys : ℕ → List E), st 0 = s ∧ cvs 0 = cv ∧
      (∀ i < m, RunsTo (gkrStep 2 (st i)) (cvs i) (ys i) (st (i + 1)) (cvs (i + 1))) ∧
      xs = (List.range m).flatMap ys ∧ s' = st m ∧ cv' = cvs m
  | 0, s, cv, xs, s', cv', h => by
    have h' : RunsTo (pure s : Prog GkrState) cv xs s' cv' := h
    obtain ⟨hx, hs, hc⟩ := RunsTo.ret_inv h'
    exact ⟨fun _ => s, fun _ => cv, fun _ => [], rfl, rfl, fun i hi => absurd hi (by omega),
      by simp [hx], hs, hc⟩
  | m + 1, s, cv, xs, s', cv', h => by
    rw [gkrPairs_succ'] at h
    obtain ⟨y1, y2, s1, cv1, rfl, h1, h⟩ := RunsTo.bind_inv' h
    obtain ⟨st, cvs, ys, h0, hc0, hs, hx, hst, hcv⟩ := RunsTo.gkrPairs_inv m s1 cv1 y2 s' cv' h
    refine ⟨fun k => if k = 0 then s else st (k - 1), fun k => if k = 0 then cv else cvs (k - 1),
      fun k => if k = 0 then y1 else ys (k - 1), rfl, rfl, fun i hi => ?_, ?_, by simp [hst],
      by simp [hcv]⟩
    · match i with
      | 0 => simpa [h0, hc0] using h1
      | i + 1 => simpa using hs i (by omega)
    · rw [hx, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp

end
end LeanVM.Guest.B1.VerifySub
