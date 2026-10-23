/-
  LeanVM.Guest.B1.Whir.StackedC10

  `open_stacked`'s tail rounds at their honest values.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC9

/-!
# The tail, honestly (TRIAGE #36)

`os_tail_inv`: `tailRounds (n + 1)` is `foldRounds n` and a closing squeeze. `osTail_complete`: the
tail's fold rounds into `tail_challenges`, the closing squeeze, the final claim and the zeroed
entries at their honest values `osTailVals`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **The tail rounds, inverted**: `n + 1` tail rounds are `n` fold rounds from any state of the
quadratic, then the closing challenge. -/
theorem os_tail_inv : ∀ (n : ℕ) (t : E) (q : List E) (st : St) (r : List E × E) (st' : St),
    Runs (tailRounds (n + 1) t q) st r st' → ∀ (w : WhirState) (lf : List E), w.quad = q →
      ∃ (w1 : WhirState) (chs : List E) (st1 : St), Runs (foldRounds n w lf) st (w1, lf ++ chs) st1 ∧
        r = (chs ++ [challengeOf (sqCv st1.cv)], polyEval w1.quad (challengeOf (sqCv st1.cv))) ∧
        st' = { st1 with cv := sqCv st1.cv } := by
  intro n
  induction n with
  | zero =>
    intro t q st r st' h w lf hq
    simp only [tailRounds] at h
    obtain ⟨ch, s1, h1, h2⟩ := os_inv_bind h
    obtain ⟨rfl, rfl⟩ := os_inv_sampleE h1
    simp only [↓reduceIte] at h2
    obtain ⟨rfl, rfl⟩ := os_inv_pure h2
    refine ⟨w, [], st, ?_, by rw [List.nil_append, hq], rfl⟩
    rw [List.append_nil]
    exact Runs.ret (w, lf) st
  | succ n ih =>
    intro t q st r st' h w lf hq
    rw [tailRounds] at h
    obtain ⟨ch, s1, h1, h2⟩ := os_inv_bind h
    obtain ⟨rfl, rfl⟩ := os_inv_sampleE h1
    rw [ite_neg' (by omega)] at h2
    obtain ⟨q', s2, h3, h4⟩ := os_inv_bind h2
    obtain ⟨⟨rest, tg⟩, s3, h5, h6⟩ := os_inv_bind h4
    obtain ⟨rfl, rfl⟩ := os_inv_pure h6
    obtain ⟨c0, c2, rr, hs, rfl, rfl⟩ := os_inv_roundPoly3 h3
    obtain ⟨w1, chs, st1, hr1, he, hs'⟩ := ih _ _ _ _ _ h5
      ⟨polyEval w.quad (challengeOf (sqCv st.cv)), [c0, polyEval w.quad (challengeOf (sqCv st.cv)) + c2, c2],
        w.folds ++ [challengeOf (sqCv st.cv)], w.glued⟩ (lf ++ [challengeOf (sqCv st.cv)]) (by rw [hq])
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨w1, challengeOf (sqCv st.cv) :: chs, st1, ?_, by rw [List.cons_append], hs'⟩
    rw [foldRounds_succ]
    refine Runs.bind (s1 := ⟨obsCv (obsCv (sqCv st.cv) c0) c2, rr, st.openings, st.roots⟩) (a := (challengeOf (sqCv st.cv), polyEval w.quad (challengeOf (sqCv st.cv)),
      [c0, polyEval w.quad (challengeOf (sqCv st.cv)) + c2, c2])) ?_ ?_
    · simp only [foldStep]
      refine Runs.bind (os_runs_sampleE _) ?_
      refine Runs.bind (s1 := ⟨obsCv (obsCv (sqCv st.cv) c0) c2, rr, st.openings, st.roots⟩) ?_ (Runs.ret _ _)
      have := os_runs_roundPoly3 (sqCv st.cv) (polyEval w.quad (challengeOf (sqCv st.cv))) c0 c2 rr st.openings
        st.roots
      simp only at hs
      rw [← hs] at this
      exact this
    · rw [List.append_assoc, List.singleton_append] at hr1
      exact hr1

theorem os_polyEval_three (c b a x : E) : polyEval [c, b, a] x = c + x * b + x * x * a := by
  simp only [polyEval, List.foldr]; ring

/-- The values of `osTail` from its first: the buffer's size and pointer `tchv`, the fold rounds',
the closing squeeze's, the final claim's, the zeroed entries. -/
def osTailVals (yrLog : ℕ) (xs : List E) (cv : Digest) (p : ℕ) (q : List E) (cbv : E) (co : ℕ) (tchv : E)
    (w1 : WhirState) (cv1 : Digest) : List E :=
  let last := challengeOf (sqCv cv1)
  let c := w1.quad.getD 0 0
  let b := w1.quad.getD 1 0
  let a := w1.quad.getD 2 0
  [osGw 5, tchv] ++ osFoldsVals xs (yrLog - 1) cv p q cbv co ++ (List.range 14).map (sqVals cv1) ++
    [last * b, c + last * b, last * last, last * last * a, c + last * b + last * last * a] ++
    List.replicate (5 - yrLog) 0

/-- **The tail** at its honest values (G:1216-1228). -/
theorem osTail_complete {yrLog : ℕ} {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) (hcop : s.co ≤ p) (hco : s.co ≤ 8) {xs : List E} {osp : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {w : WhirState} (hw : w.folds = [])
    (hq : w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) {w1 : WhirState} {chs : List E} {cv1 : Digest}
    (hrun : Runs (foldRounds (yrLog - 1) w []) ⟨cv, xs.drop p, osp, roots⟩ (w1, chs)
      ⟨cv1, xs.drop (p + 2 * (yrLog - 1)), osp, roots⟩) {tchv : E}
    (htch : ∀ j < yrLog - 1, LoadHolds rd tchv j (chs.getD j 0))
    (hlast : LoadHolds rd tchv (yrLog - 1) (challengeOf (sqCv cv1)))
    (hz : ∀ j < 5 - yrLog, LoadHolds rd tchv (yrLog + j) 0) {kret : List E → Prop}
    (hcf : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      C "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRets xs cv' p' q' (cur * gen ^ p')))
    (hv : ∀ j < (osTailVals yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).length,
      σ (.n (s.k + j)) = (osTailVals yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).getD j 0) :
    Stmt.HoldsList C rd σ (osTail yrLog s).1 True kret ∧
      σ (.n (osTail yrLog s).2.1.t) = polyEval w1.quad (challengeOf (sqCv cv1)) ∧
      σ (.n (osTail yrLog s).2.2.1) = tchv ∧
      (osTail yrLog s).2.1.k = s.k + (osTailVals yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).length := by
  have hcb := os_cb_of_at hat hcop
  set F := osFoldsVals xs (yrLog - 1) cv p w.quad (cur * gen ^ (p - s.co)) s.co with hF
  set Q := (List.range 14).map (sqVals cv1) with hQ
  set last := challengeOf (sqCv cv1)
  set T : List E := [last * w1.quad.getD 1 0, w1.quad.getD 0 0 + last * w1.quad.getD 1 0, last * last,
    last * last * w1.quad.getD 2 0, w1.quad.getD 0 0 + last * w1.quad.getD 1 0 + last * last * w1.quad.getD 2 0]
    with hT
  have hV : osTailVals yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1 =
      [osGw 5, tchv] ++ F ++ Q ++ T ++ List.replicate (5 - yrLog) 0 := rfl
  rw [hV] at hv ⊢
  obtain ⟨hv4, gZ⟩ := os_look_app hv
  obtain ⟨hv3, gT⟩ := os_look_app hv4
  obtain ⟨hv2, gQ⟩ := os_look_app hv3
  obtain ⟨gH, gF⟩ := os_look_app hv2
  have h0 : σ (.n s.k) = osGw 5 := by simpa using gH 0 (by simp)
  have h1 : σ (.n (s.k + 1)) = tchv := by simpa using gH 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.length_append] at gF gQ gT gZ
  have hQl : Q.length = 14 := by simp [hQ]
  have hTl : T.length = 5 := rfl
  set s2 : OsSt := { s with k := s.k + 2 }
  have hat2 : OsAt σ s2 cv cur p := ⟨hat.fs, hat.cursor⟩
  obtain ⟨hFh, hatF, hsp, hqF, -, -, -, -, -, hkF⟩ := osFolds_complete (rd := rd) (σ := σ) (fch := s.k + 1)
    (kret := kret) hcf (yrLog - 1) 0 s2 cv p w [] osp roots (w1, chs) _ hat2 (by show s.co < _; omega) hq hrun
    (fun j hj => by
      show σ (.n (s.k + 2 + j)) = _
      rw [show (σ (.n s2.cb)) = cur * gen ^ (p - s.co) from hcb] at hj ⊢
      exact gF j hj)
    (fun j hj => by
      obtain ⟨chs', hf1, hf2, -⟩ := (os_foldRounds_folds hrun)
      have hf1' : w1.folds = w.folds ++ chs' := hf1
      have hf2' : chs = chs' := by simpa using hf2
      subst hf2'
      show LoadHolds rd (σ (.n (s.k + 1))) (0 + j) (w1.folds.getD (w.folds.length + j) 0)
      simp only [h1, hf1', hw, List.nil_append, List.length_nil, Nat.zero_add]
      exact htch j hj)
  simp only at hatF hqF hkF
  rw [show (σ (.n s2.cb)) = cur * gen ^ (p - s.co) from hcb, ← hF] at hkF
  set f := osFolds (s.k + 1) 0 (yrLog - 1) s2 with hfd
  have hbb : f.2.k = s.k + (2 + F.length) := by rw [hkF]; simp only [s2]; ring
  have eQ : ∀ j < 14, σ (.n (f.2.k + j)) = sqVals cv1 j := fun j hj => by
    rw [hbb, gQ j (by rw [hQl]; exact hj), hQ]
    simp [List.getD_eq_getElem?_getD, hj]
  have eT : ∀ j < 5, σ (.n (f.2.k + 14 + j)) = T.getD j 0 := fun j hj => by
    rw [hbb, show s.k + (2 + F.length) + 14 = s.k + (2 + F.length + Q.length) by rw [hQl]; ring]
    exact gT j (by rw [hTl]; exact hj)
  have eZ : ∀ j < 5 - yrLog, σ (.n (f.2.k + 14 + 5 + j)) = 0 := fun j hj => by
    rw [hbb, show s.k + (2 + F.length) + 14 + 5 = s.k + (2 + F.length + Q.length + T.length) by
      rw [hQl, hTl]; ring]
    rw [gZ j (by simp; exact hj)]
    simp [List.getD_eq_getElem?_getD, hj]
  have e13 : σ (.n (f.2.k + 13)) = last := eQ 13 (by omega)
  have t0 := eT 0 (by omega); have t1 := eT 1 (by omega); have t2 := eT 2 (by omega)
  have t3 := eT 3 (by omega); have t4 := eT 4 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t0 t1 t2 t3 t4
  have hq0 : w1.quad.getD 0 0 = σ (.n f.2.c) := by rw [hqF]; rfl
  have hq1 : w1.quad.getD 1 0 = σ (.n f.2.b) := by rw [hqF]; rfl
  have hq2 : w1.quad.getD 2 0 = σ (.n f.2.a) := by rw [hqF]; rfl
  unfold osTail
  dsimp only
  rw [← hfd]
  refine ⟨?_, ?_, h1, ?_⟩
  · simp only [holdsList_append]
    refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, (holdsList_noRet _ (osFolds_noRet _ _ _ _) _ _).mpr ⟨hFh,
      (holdsList_noRet _ (by simp [squeezeT, squeezeStateT, challengeT, Stmt.noRetList, Stmt.noRet]) _ _).mpr
      ⟨?_, (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩⟩⟩⟩
    · simp only [osHeap, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact h0
    · exact (holds_squeezeT _ _ _ True _).mpr ⟨⟨cv1, hatF.fs, eQ⟩, trivial⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨by rw [e13, h1]; exact hlast, by rw [t0, e13, hq1], by rw [t1, t0, hq0], by rw [t2, e13],
        by rw [t3, t2, hq2], by rw [t4, t1, t3]⟩
    · rw [holdsList_range_flatten _ _ (fun _ => rfl)]
      refine ⟨fun j hj => ?_, trivial⟩
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      have := eZ j hj
      rw [show f.2.k + 14 + 5 + j = f.2.k + 14 + 5 + j from rfl] at this
      refine ⟨by rw [this, word_zero], by rw [this, h1]; exact hz j hj⟩
  · show σ (.n (f.2.k + 14 + 4)) = _
    rw [t4, hqF, os_polyEval_three]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · show f.2.k + 14 + 5 + (5 - yrLog) = _
    rw [hbb]; simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate, hQl, hTl]
    ring

end
end LeanVM.Guest.B1
