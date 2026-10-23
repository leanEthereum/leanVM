/-
  LeanVM.Guest.B1.Tables.GkrRunInv

  A run reading exactly its words splits at every bind: the first program reads a prefix.
-/

module

public import LeanVM.Guest.B1.Tables.GkrBase

/-!
# Splitting a run at a bind

`runId_roots_mono`: a run only appends roots. `runId_frame`: a run from no openings and no roots
ending with no roots reads a prefix `k` of its stream, and runs the same on any stream continuing
that prefix, from any openings and roots (it neither commits nor opens). So `RunsTo.bind_inv`: a
run of `p >>= f` is a run of `p` on a prefix and of `f` on the rest.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile

@[expose] public section

theorem runId_read_cons {α : Type} (k : E → Prog α) (cv : Digest) (x : E) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runId (.read k) ⟨cv, x :: xs, os, roots⟩ = runId (k x) ⟨obsCv cv x, xs, os, roots⟩ := rfl

theorem runId_read_nil {α : Type} (k : E → Prog α) (cv : Digest) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) : runId (.read k) ⟨cv, [], os, roots⟩ = none := rfl

theorem runId_sample {α : Type} (k : E → Prog α) (cv : Digest) (xs : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    runId (.sample k) ⟨cv, xs, os, roots⟩ = runId (k (challengeOf (sqCv cv))) ⟨sqCv cv, xs, os, roots⟩ :=
  rfl

theorem runId_grind_cons {α : Type} (b : ℕ) (k : Prog α) (cv : Digest) (n : E) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runId (.grind b k) ⟨cv, n :: xs, os, roots⟩ =
      if powOk b n (blake2sBytes (digestBytes (blake2sBytes (digestBytes cv ++ blockOf 0 3)) ++
        blockOf n 4)) then runId k ⟨blake2sBytes (digestBytes cv ++ blockOf n 4), xs, os, roots⟩
      else none := rfl

theorem runId_grind_nil {α : Type} (b : ℕ) (k : Prog α) (cv : Digest) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) : runId (.grind b k) ⟨cv, [], os, roots⟩ = none := rfl

theorem runId_commit {α : Type} (hh w : ℕ) (k : Prog α) (cv : Digest) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runId (.commit hh w k) ⟨cv, xs, os, roots⟩ = match xs with
      | x0 :: x1 :: xs => match digestOfScalars (x0, x1) with
        | some root => runId k ⟨obsCv (obsCv cv x0) x1, xs, os, roots ++ [(root, hh, w)]⟩
        | none => none
      | _ => none := by
  match xs with
  | [] => rfl
  | [_] => rfl
  | x0 :: x1 :: xs =>
    show (match digestOfScalars (x0, x1) with
      | some root => runId k ⟨obsCv (obsCv cv x0) x1, xs, os, roots ++ [(root, hh, w)]⟩
      | none => none) = _
    rfl

theorem runId_roots_mono {α : Type} : ∀ (p : Prog α) (s : St) (a : α) (s' : St),
    runId p s = some (a, s') → ∃ l, s'.roots = s.roots ++ l
  | .ret _, _, _, _, h => by cases h; exact ⟨[], by simp⟩
  | .fail, _, _, _, h => by cases h
  | .read k, ⟨cv, xs, os, roots⟩, a, s', h => by
    match xs, h with
    | [], h => rw [runId_read_nil] at h; cases h
    | x :: xs, h =>
      rw [runId_read_cons] at h; exact runId_roots_mono (k x) ⟨obsCv cv x, xs, os, roots⟩ a s' h
  | .sample k, ⟨cv, xs, os, roots⟩, a, s', h => by
    rw [runId_sample] at h
    exact runId_roots_mono _ ⟨sqCv cv, xs, os, roots⟩ a s' h
  | .grind b k, ⟨cv, xs, os, roots⟩, a, s', h => by
    match xs, h with
    | [], h => rw [runId_grind_nil] at h; cases h
    | n :: xs, h =>
      rw [runId_grind_cons] at h
      split at h
      · exact runId_roots_mono k ⟨_, xs, os, roots⟩ a s' h
      · cases h
  | .commit hh w k, ⟨cv, xs, os, roots⟩, a, s', h => by
    rw [runId_commit] at h
    match xs, h with
    | [], h => cases h
    | [_], h => cases h
    | x0 :: x1 :: xs, h =>
      simp only at h
      split at h
      · rename_i root _
        obtain ⟨l, hl⟩ := runId_roots_mono k ⟨_, xs, os, roots ++ [(root, hh, w)]⟩ a s' h
        exact ⟨(root, hh, w) :: l, by rw [hl]; simp⟩
      · cases h
  | .query i ps k, ⟨cv, xs, os, roots⟩, a, s', h => by
    simp only [runId, Compile.run] at h
    split at h
    · cases h
    · simp only [bind] at h
      split at h
      · rename_i rows rest _
        exact runId_roots_mono (k rows) ⟨cv, xs, rest, roots⟩ a s' h
      · cases h

/-- **A run that commits nothing reads a prefix**, the same on any continuation of it. -/
theorem runId_frame {α : Type} : ∀ (p : Prog α) (cv : Digest) (xs : List E) (a : α) (s' : St),
    runId p ⟨cv, xs, [], []⟩ = some (a, s') → s'.roots = [] →
      ∃ k, s'.stream = xs.drop k ∧ s'.openings = [] ∧ ∀ ys os roots,
        runId p ⟨cv, xs.take k ++ ys, os, roots⟩ = some (a, ⟨s'.cv, ys, os, roots⟩)
  | .ret _, cv, xs, _, s', h, _ => by
    cases h
    exact ⟨0, by simp, rfl, fun ys os roots => by simp; rfl⟩
  | .fail, _, _, _, _, h, _ => by cases h
  | .read k, cv, xs, a, s', h, hr => by
    match xs, h with
    | [], h => rw [runId_read_nil] at h; cases h
    | x :: xs, h =>
      rw [runId_read_cons] at h
      obtain ⟨k0, h1, h2, h3⟩ := runId_frame (k x) _ xs a s' h hr
      refine ⟨k0 + 1, by simpa using h1, h2, fun ys os roots => ?_⟩
      rw [List.take_succ_cons, List.cons_append, runId_read_cons]
      exact h3 ys os roots
  | .sample k, cv, xs, a, s', h, hr => by
    rw [runId_sample] at h
    obtain ⟨k0, h1, h2, h3⟩ := runId_frame _ _ xs a s' h hr
    exact ⟨k0, h1, h2, fun ys os roots => by rw [runId_sample]; exact h3 ys os roots⟩
  | .grind b k, cv, xs, a, s', h, hr => by
    match xs, h with
    | [], h => rw [runId_grind_nil] at h; cases h
    | n :: xs, h =>
      rw [runId_grind_cons] at h
      split at h
      · rename_i hpow
        obtain ⟨k0, h1, h2, h3⟩ := runId_frame k _ xs a s' h hr
        refine ⟨k0 + 1, by simpa using h1, h2, fun ys os roots => ?_⟩
        rw [List.take_succ_cons, List.cons_append, runId_grind_cons, ite_pos' hpow]
        exact h3 ys os roots
      · cases h
  | .commit hh w k, cv, xs, a, s', h, hr => by
    exfalso
    rw [runId_commit] at h
    match xs, h with
    | [], h => cases h
    | [_], h => cases h
    | x0 :: x1 :: xs, h =>
      simp only at h
      split at h
      · obtain ⟨l, hl⟩ := runId_roots_mono _ _ a s' h
        rw [hr] at hl
        simp at hl
      · cases h
  | .query i ps k, cv, xs, a, s', h, _ => by
    simp [runId, Compile.run] at h

/-- **A run of a bind splits**: `p` reads a prefix, `f` the rest. -/
theorem RunsTo.bind_inv {α β : Type} {p : Prog α} {f : α → Prog β} {cv cv'' : Digest}
    {xs : List E} {b : β} (h : RunsTo (p.bind f) cv xs b cv'') :
    ∃ (xs1 xs2 : List E) (a : α) (cv1 : Digest), xs = xs1 ++ xs2 ∧ RunsTo p cv xs1 a cv1 ∧
      RunsTo (f a) cv1 xs2 b cv'' := by
  have h0 := h [] [] []
  rw [List.append_nil, run_bind] at h0
  obtain ⟨⟨a, s1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h0
  obtain ⟨l, hl⟩ := runId_roots_mono (f a) s1 b _ h2
  have hr1 : s1.roots = [] := by
    have := congrArg List.length hl; simp at this; exact List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨k, hk1, hk2, hk3⟩ := runId_frame p cv xs a s1 h1 hr1
  obtain ⟨cv1, st1, os1, rs1⟩ := s1
  simp only at hk1 hk2 hr1 hk3
  subst hk1 hk2 hr1
  have h2' : runId (f a) ⟨cv1, xs.drop k, [], []⟩ = some (b, ⟨cv'', [], [], []⟩) := h2
  obtain ⟨k', hk1', -, hk3'⟩ := runId_frame (f a) cv1 (xs.drop k) b _ h2' rfl
  simp only at hk1'
  refine ⟨xs.take k, xs.drop k, a, cv1, (List.take_append_drop k xs).symm, fun ys os roots => hk3 ys os roots,
    fun ys os roots => ?_⟩
  have := hk3' ys os roots
  have hd : (xs.drop k).take k' = xs.drop k := by
    have hl' : ((xs.drop k).drop k').length = 0 := by rw [← hk1']; rfl
    simp only [List.length_drop] at hl'
    exact List.take_of_length_le (by simp; omega)
  rw [hd] at this
  exact this

/-- **Two runs on one stream agree**: when one run's words extend the other's, they read the same
words, to the same value and state. -/
theorem RunsTo.det {α : Type} {p : Prog α} {cv c0 c : Digest} {xs0 xs : List E} {a0 a : α}
    (h0 : RunsTo p cv xs0 a0 c0) (h : RunsTo p cv xs a c)
    (hp : ∃ t, xs = xs0 ++ t ∨ xs0 = xs ++ t) : xs0 = xs ∧ a0 = a ∧ c0 = c := by
  obtain ⟨t, ht | ht⟩ := hp
  · have e1 := h0 t [] []
    have e2 := h [] [] []
    rw [List.append_nil, ht, e1] at e2
    simp only [Option.some.injEq, Prod.mk.injEq, St.mk.injEq] at e2
    obtain ⟨ha, hc, rfl, -, -⟩ := e2
    exact ⟨by simp [ht], ha, hc⟩
  · have e1 := h t [] []
    have e2 := h0 [] [] []
    rw [List.append_nil, ht, e1] at e2
    simp only [Option.some.injEq, Prod.mk.injEq, St.mk.injEq] at e2
    obtain ⟨ha, hc, rfl, -, -⟩ := e2
    exact ⟨by simp [ht], ha.symm, hc.symm⟩

/-- A run of a program that reads nothing reads nothing. -/
theorem RunsTo.det_nil {α : Type} {p : Prog α} {cv c0 c : Digest} {xs : List E} {a0 a : α}
    (h0 : RunsTo p cv [] a0 c0) (h : RunsTo p cv xs a c) : xs = [] ∧ a = a0 ∧ c = c0 := by
  obtain ⟨h1, h2, h3⟩ := h0.det h ⟨xs, Or.inl rfl⟩
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- A run of `readN n` reads its `n` words. -/
theorem RunsTo.readN_inv {n : ℕ} {cv c : Digest} {xs a : List E}
    (h : RunsTo (Prog.readN n) cv xs a c) : xs.length = n ∧ a = xs ∧ c = obsAll cv xs := by
  set ys := (xs ++ List.replicate n 0).take n
  have hy : ys.length = n := by simp [ys]
  have h0 := VerifySub.runsTo_readN_of_length cv hy
  have hp : ∃ t, xs = ys ++ t ∨ ys = xs ++ t := by
    rcases le_total n xs.length with hn | hn
    · exact ⟨xs.drop n, Or.inl (by
        simp only [ys, List.take_append_of_le_length hn, List.take_append_drop])⟩
    · refine ⟨List.replicate (n - xs.length) 0, Or.inr ?_⟩
      simp only [ys, List.take_append, List.take_of_length_le hn, List.take_replicate]
      congr 2; omega
  obtain ⟨e1, e2, e3⟩ := h0.det h hp
  rw [← e1]
  exact ⟨hy, e2.symm, e3.symm⟩

end
end LeanVM.Guest.B1
