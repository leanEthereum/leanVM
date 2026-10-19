/-
  LeanVM.Guest.B1.Whir.StackedInv

  Runs of the stacked opening's pieces, backward: what a run of each piece read and computed.
-/

module

public import LeanVM.Guest.B1.Whir.StackedRun
public import LeanVM.Guest.B1.VerifySub.Inv0

/-!
# The stacked opening's runs, backward (TRIAGE #36)

The specification's side of `open_stacked`'s completeness: from a run of a piece of
`whirLevelsOpen`, the words it read and the values it computed, the state it ends in.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem os_inv_bind {α β : Type} {p : Prog α} {f : α → Prog β} {s s'' : St} {b : β}
    (h : Runs (p >>= f) s b s'') : ∃ a s', Runs p s a s' ∧ Runs (f a) s' b s'' := runs_bind_inv h

theorem os_inv_ret {α : Type} {a b : α} {s s' : St} (h : Runs (Prog.ret a) s b s') : b = a ∧ s' = s := by
  unfold Runs at h
  simp only [runId, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem os_inv_pure {α : Type} {a b : α} {s s' : St} (h : Runs (pure a : Prog α) s b s') : b = a ∧ s' = s :=
  os_inv_ret h

/-- A run is the forward run it is known to be. -/
theorem os_runs_det {α : Type} {p : Prog α} {s s' : St} {a a0 : α} {cv0 : Digest} {ys rest : List E}
    (h : Runs p s a s') (hf : RunsTo p s.cv ys a0 cv0) (hs : s.stream = ys ++ rest) :
    a = a0 ∧ s' = ⟨cv0, rest, s.openings, s.roots⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  simp only at hs
  subst hs
  have := hf rest os roots
  unfold Runs at h
  rw [this] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem os_inv_sampleE {s s' : St} {x : E} (h : Runs Prog.sampleE s x s') :
    x = challengeOf (sqCv s.cv) ∧ s' = ⟨sqCv s.cv, s.stream, s.openings, s.roots⟩ :=
  os_runs_det (rest := s.stream) h (runsTo_sampleE s.cv) rfl

theorem os_inv_readE {s s' : St} {x : E} (h : Runs Prog.readE s x s') :
    ∃ rest, s.stream = x :: rest ∧ s' = ⟨obsCv s.cv x, rest, s.openings, s.roots⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  match xs, h with
  | [], h => cases h
  | y :: ys, h =>
    obtain ⟨rfl, rfl⟩ := os_runs_det (rest := ys) h (runsTo_readE cv y) rfl
    exact ⟨ys, rfl, rfl⟩

theorem os_inv_readN : ∀ {n : ℕ} {s s' : St} {ys : List E}, Runs (Prog.readN n) s ys s' →
    ys.length = n ∧ ∃ rest, s.stream = ys ++ rest ∧ s' = ⟨obsAll s.cv ys, rest, s.openings, s.roots⟩
  | 0, s, s', ys, h => by
    obtain ⟨rfl, rfl⟩ := os_inv_ret h
    exact ⟨rfl, _, (List.nil_append _).symm, rfl⟩
  | n + 1, s, s', ys, h => by
    unfold Prog.readN at h
    obtain ⟨x, s1, h1, h2⟩ := os_inv_bind h
    obtain ⟨zs, s2, h3, h4⟩ := os_inv_bind h2
    obtain ⟨rfl, rfl⟩ := os_inv_pure h4
    obtain ⟨r1, hs1, rfl⟩ := os_inv_readE h1
    obtain ⟨hl, r2, hs2, rfl⟩ := os_inv_readN h3
    refine ⟨by simp [hl], r2, by rw [hs1]; simp only at hs2; rw [hs2]; rfl, rfl⟩

theorem os_inv_sampleN {n : ℕ} {s s' : St} {ys : List E} (h : Runs (Prog.sampleN n) s ys s') :
    ys = (sqAll n s.cv).1 ∧ s' = ⟨(sqAll n s.cv).2, s.stream, s.openings, s.roots⟩ :=
  os_runs_det (rest := s.stream) h (runsTo_sampleN n s.cv) rfl

theorem os_inv_roundPoly3 {claim : E} {s s' : St} {q : List E} (h : Runs (sumcheckRoundPoly 3 claim none) s q s') :
    ∃ c0 c2 rest, s.stream = c0 :: c2 :: rest ∧ q = [c0, claim + c2, c2] ∧
      s' = ⟨obsCv (obsCv s.cv c0) c2, rest, s.openings, s.roots⟩ := by
  simp only [sumcheckRoundPoly] at h
  obtain ⟨c0, s1, h1, h2⟩ := os_inv_bind h
  obtain ⟨tl, s2, h3, h4⟩ := os_inv_bind h2
  obtain ⟨rfl, rfl⟩ := os_inv_pure h4
  obtain ⟨r1, hs1, rfl⟩ := os_inv_readE h1
  obtain ⟨hl, r2, hs2, rfl⟩ := os_inv_readN h3
  match tl, hl with
  | [c2], _ =>
    refine ⟨c0, c2, r2, by rw [hs1]; simp only at hs2; rw [hs2]; rfl, by simp [sumE], rfl⟩

theorem os_inv_grindP {b : ℕ} {s s' : St} {u : Unit} (h : Runs (Prog.grindP b) s u s') :
    ∃ n rest, s.stream = n :: rest ∧ powOk b n (gcDigest s.cv n) = true ∧
      s' = ⟨absorbCv s.cv n 4, rest, s.openings, s.roots⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  match xs, h with
  | [], h => cases h
  | n :: rest, h =>
    unfold Runs Prog.grindP at h
    rw [inv_grind_cons] at h
    split at h
    · rename_i hpow
      have := os_inv_ret h
      exact ⟨n, rest, rfl, hpow, this.2⟩
    · cases h

theorem os_inv_commitP {hh ww : ℕ} {s s' : St} {u : Unit} (h : Runs (Prog.commitP hh ww) s u s') :
    ∃ x0 x1 rest root, s.stream = x0 :: x1 :: rest ∧ digestOfScalars (x0, x1) = some root ∧
      s' = ⟨obsCv (obsCv s.cv x0) x1, rest, s.openings, s.roots ++ [(root, hh, ww)]⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  match xs, h with
  | [], h => cases h
  | [_], h => cases h
  | x0 :: x1 :: rest, h =>
    unfold Runs Prog.commitP at h
    simp only [runId, Compile.run] at h
    split at h
    · rename_i root hroot
      have := os_inv_ret h
      exact ⟨x0, x1, rest, root, rfl, hroot, this.2⟩
    · cases h

theorem os_inv_queryP {i : ℕ} {ps : List ℕ} {s s' : St} {rows : List (List K)}
    (h : Runs (Prog.queryP i ps) s rows s') :
    ∃ root hh ww rest, s.roots[i]? = some (root, hh, ww) ∧
      openAll (m := Id) blake2sBytes root hh ww ps s.openings = some (rows, rest) ∧
      s' = ⟨s.cv, s.stream, rest, s.roots⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  unfold Runs Prog.queryP at h
  simp only [runId, Compile.run] at h
  split at h
  · cases h
  · rename_i root hh ww hr
    simp only [bind] at h
    split at h
    · rename_i rows' rest hoa
      have := os_inv_ret h
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨root, hh, ww, rest, hr, hoa, rfl⟩
    · cases h

end
end LeanVM.Guest.B1
