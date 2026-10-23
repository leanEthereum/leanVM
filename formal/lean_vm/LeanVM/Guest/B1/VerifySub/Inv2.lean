/-
  LeanVM.Guest.B1.VerifySub.Inv2

  Runs of the reading and sampling primitives, backward, and Flock's run: its output's shape and
  its run at every evaluation of the matrices that takes the claimed value.
-/

module

public import LeanVM.Guest.B1.VerifySub.Inv1

/-!
# Primitive runs and Flock, backward

* `runs_ret_inv`, `runs_require_inv`, `runs_sampleE_inv`, `runs_readN_inv`, `runs_sumcheck_inv`:
  what a run of each primitive returns and leaves;
* `vs_flock_inv`: a run of `verifyFlock` at the claimed values returns the lincheck's reversed point,
  the zerocheck's point past it and the slices, of the deployed lengths, at the claimed values'
  points, and runs the same at every evaluation that takes the claimed matrices' value there.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem runs_bind_inv' {α β : Type} {p : Prog α} {f : α → Prog β} {s s'' : St} {b : β}
    (h : Runs (p >>= f) s b s'') : ∃ a s', Runs p s a s' ∧ Runs (f a) s' b s'' :=
  runs_bind_inv h

theorem Runs.bind_m {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : St} {a : α} {b : β}
    (h1 : Runs p s a s1) (h2 : Runs (f a) s1 b s2) : Runs (p >>= f) s b s2 := Runs.bind h1 h2

theorem runs_ret_inv {α : Type} {a b : α} {s s' : St} (h : Runs (Prog.ret a) s b s') :
    b = a ∧ s' = s := by
  unfold Runs at h
  simp only [runId, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem runs_pure_inv {α : Type} {a b : α} {s s' : St} (h : Runs (pure a : Prog α) s b s') :
    b = a ∧ s' = s := runs_ret_inv h

theorem runs_require_inv {c : Prop} [Decidable c] {s s' : St} {u : Unit}
    (h : Runs (Prog.require c) s u s') : c ∧ s' = s := by
  unfold Prog.require at h
  split at h
  · exact ⟨by assumption, (runs_ret_inv h).2⟩
  · cases h

theorem runs_sampleE_inv {s s' : St} {x : E} (h : Runs Prog.sampleE s x s') :
    x = challengeOf (sqCv s.cv) ∧ s' = { s with cv := sqCv s.cv } := by
  unfold Runs at h
  simp only [runId, Compile.run, Prog.sampleE, bind, pure, Option.some.injEq,
    Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem runs_readE_inv {s s' : St} {x : E} (h : Runs Prog.readE s x s') :
    s.stream = x :: s'.stream ∧ s'.cv = obsCv s.cv x ∧ s'.openings = s.openings ∧
      s'.roots = s.roots := by
  obtain ⟨cv, xs, os, roots⟩ := s
  match xs, h with
  | [], h => cases h
  | y :: ys, h =>
    unfold Runs at h
    simp only [runId, Compile.run, Prog.readE, bind, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem runs_readN_inv : ∀ {n : ℕ} {s s' : St} {xs : List E}, Runs (Prog.readN n) s xs s' →
    xs.length = n ∧ s.stream = xs ++ s'.stream ∧ s'.cv = obsAll s.cv xs ∧
      s'.openings = s.openings ∧ s'.roots = s.roots
  | 0, s, s', xs, h => by
    obtain ⟨rfl, rfl⟩ := runs_ret_inv h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, s, s', xs, h => by
    unfold Prog.readN at h
    obtain ⟨x, s1, h1, h2⟩ := runs_bind_inv' h
    obtain ⟨ys, s2, h3, h4⟩ := runs_bind_inv' h2
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h4
    obtain ⟨hl, hs, hc, ho, hr⟩ := runs_readN_inv h3
    obtain ⟨e1, e2, e3, e4⟩ := runs_readE_inv h1
    refine ⟨by simp [hl], by rw [e1, hs]; rfl, ?_, by rw [ho, e3], by rw [hr, e4]⟩
    rw [hc, e2]; rfl

theorem runs_sampleN_inv : ∀ {n : ℕ} {s s' : St} {xs : List E}, Runs (Prog.sampleN n) s xs s' →
    xs.length = n
  | 0, s, s', xs, h => by
    obtain ⟨rfl, rfl⟩ := runs_ret_inv h
    rfl
  | n + 1, s, s', xs, h => by
    unfold Prog.sampleN at h
    obtain ⟨x, s1, -, h2⟩ := runs_bind_inv' h
    obtain ⟨ys, s2, h3, h4⟩ := runs_bind_inv' h2
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h4
    simp [runs_sampleN_inv h3]

theorem runs_sumcheck_inv {count : ℕ} : ∀ {eqs : List (Option E)} {claim : E} {s s' : St}
    {r : List E × E}, Runs (sumcheck claim count eqs) s r s' → r.1.length = eqs.length
  | [], _, s, s', r, h => by
    unfold sumcheck at h
    obtain ⟨rfl, -⟩ := runs_pure_inv h
    rfl
  | e :: es, claim, s, s', r, h => by
    unfold sumcheck at h
    obtain ⟨m, s1, -, h2⟩ := runs_bind_inv' h
    obtain ⟨x, s2, -, h4⟩ := runs_bind_inv' h2
    obtain ⟨⟨pt, f⟩, s3, h5, h6⟩ := runs_bind_inv' h4
    obtain ⟨rfl, -⟩ := runs_pure_inv h6
    have := runs_sumcheck_inv h5
    simp only [List.length_cons] at this ⊢
    omega

/-! ## Flock -/

theorem fixedChallenges_length : fixedChallenges.length = 7 := rfl

/-- **Flock's run, backward**: at the claimed values, the output is the lincheck's reversed point,
then the zerocheck's point past its first `8` coordinates, and the slices; the zerocheck's point
has `log_n - 6` coordinates, the lincheck's `8`, the slices `64`; the claimed values' points are
these; and the run is the same at every evaluation of the matrices taking the claimed value
there. -/
theorem vs_flock_inv {c : FixedClaims} {logN : ℕ} {s s' : St} {out : List E × List E}
    (h : Runs (verifyFlock (.claimed c) logN) s out s') :
    ∃ (zSkip : E) (chi rc : List E), out = (rc.reverse ++ chi.drop flockNumLincheckRounds, c.slices) ∧
      chi.length = 7 + (logN - flockKSkip - 7) ∧ rc.length = flockNumLincheckRounds ∧
      c.slices.length = kBits ∧ zSkip = c.zSkip ∧ chi.take flockNumLincheckRounds = c.rowPoint ∧
      rc.reverse = c.columnPoint ∧
      ∀ ev, MatricesAt ev c.alpha c.zSkip c.rowPoint c.columnPoint c.slices c.matrixValue →
        Runs (verifyFlock ev logN) s out s' := by
  unfold verifyFlock at h
  obtain ⟨zc, s1, hz, hl⟩ := runs_bind_inv' h
  -- the zerocheck
  have hzc : zc.chi.length = 7 + (logN - flockKSkip - 7) := by
    unfold verifyFlockZerocheck at hz
    obtain ⟨sm, z1, hsm0, hz⟩ := runs_bind_inv' hz
    obtain ⟨pc, z2, -, hz⟩ := runs_bind_inv' hz
    obtain ⟨zs, z3, -, hz⟩ := runs_bind_inv' hz
    obtain ⟨⟨chi, run⟩, z4, hs, hz⟩ := runs_bind_inv' hz
    obtain ⟨va, z5, -, hz⟩ := runs_bind_inv' hz
    obtain ⟨vb, z6, -, hz⟩ := runs_bind_inv' hz
    obtain ⟨rfl, -⟩ := runs_pure_inv hz
    have := runs_sumcheck_inv hs
    have hsm : sm.length = logN - flockKSkip - 7 := runs_sampleN_inv hsm0
    simp only [List.length_map, List.length_append, fixedChallenges_length] at this
    simp only
    omega
  unfold verifyFlockLincheck at hl
  obtain ⟨alpha, t1, ha, hl⟩ := runs_bind_inv' hl
  obtain ⟨⟨rc, rLc⟩, t2, hsc, hl⟩ := runs_bind_inv' hl
  obtain ⟨sl, t3, hsl, hl⟩ := runs_bind_inv' hl
  obtain ⟨mv, t4, hmv, hl⟩ := runs_bind_inv' hl
  obtain ⟨u, t5, hreq, hl⟩ := runs_bind_inv' hl
  obtain ⟨hout, rfl⟩ := runs_pure_inv hl
  unfold Evaluations.claimed at hmv
  obtain ⟨u', t6, hr2, hmv2⟩ := runs_bind_inv' hmv
  obtain ⟨⟨e1, e2, e3, e4, e5⟩, rfl⟩ := runs_require_inv hr2
  obtain ⟨rfl, rfl⟩ := runs_pure_inv hmv2
  subst e1 e5
  have hrc : rc.length = flockNumLincheckRounds := by
    have := runs_sumcheck_inv hsc; simpa using this
  refine ⟨zc.zSkip, zc.chi, rc, hout, hzc, hrc, (runs_readN_inv hsl).1, e2, e3, e4,
    fun ev hev => ?_⟩
  unfold verifyFlock verifyFlockLincheck
  exact Runs.bind_m hz (Runs.bind_m ha (Runs.bind_m hsc (Runs.bind_m hsl (Runs.bind_m
    (by rw [e2, e3, e4]; exact hev _) (Runs.bind_m hreq (by rw [hout]; exact Runs.ret _ _))))))

end
end LeanVM.Guest.B1.VerifySub
