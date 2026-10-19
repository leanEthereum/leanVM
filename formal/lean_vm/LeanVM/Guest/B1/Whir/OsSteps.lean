/-
  LeanVM.Guest.B1.Whir.OsSteps

  The query steps of a run: through a bind, and of the programs without a query.
-/

module

public import LeanVM.Guest.B1.Whir.StackedInv
public import LeanVM.Guest.B1.Whir.CapAgrees
public import LeanVM.Guest.B1.Whir.StackedRun

/-!
# The query steps of a run (TRIAGE #36)

`os_queriesOf_bind`: a bind's query steps are the first program's, then the continuation's from
where the first ends; `os_queriesOf_noQ`: a program without a query step has none.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **A bind's query steps**: the first program's, then the continuation's. -/
theorem os_queriesOf_bind {α β : Type} (p : Prog α) (f : α → Prog β) :
    ∀ (s : St) {a : α} {s' : St}, Runs p s a s' → queriesOf (p.bind f) s = queriesOf p s ++ queriesOf (f a) s' := by
  induction p with
  | ret a0 =>
    intro s a s' h
    obtain ⟨rfl, rfl⟩ := os_inv_ret h
    rfl
  | fail => intro s a s' h; cases h
  | read k ih =>
    intro s a s' h
    obtain ⟨cv, xs, os, roots⟩ := s
    cases xs with
    | nil => cases h
    | cons x xs =>
      have h' : Runs (k x) ⟨absorbBlock (m := Id) blake2sBytes cv (blockOf x 1), xs, os, roots⟩ a s' := h
      exact ih x _ h'
  | sample k ih =>
    intro s a s' h
    exact ih _ _ h
  | grind b k ih =>
    intro s a s' h
    obtain ⟨cv, xs, os, roots⟩ := s
    cases xs with
    | nil => cases h
    | cons n xs =>
      unfold Runs at h
      simp only [runId, Compile.run, bind, pure] at h
      simp only [queriesOf, Prog.bind]
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih _ h
      · cases h
  | commit hh ww k ih =>
    intro s a s' h
    obtain ⟨cv, xs, os, roots⟩ := s
    match xs, h with
    | [], h => cases h
    | [_], h => cases h
    | x0 :: x1 :: xs, h =>
      unfold Runs at h
      simp only [runId, Compile.run, bind] at h
      simp only [queriesOf, Prog.bind]
      split at h
      · rename_i root hr
        rw [hr]
        exact ih _ h
      · cases h
  | query i ps k ih =>
    intro s a s' h
    unfold Runs at h
    simp only [runId, Compile.run] at h
    simp only [queriesOf, Prog.bind]
    split at h
    · cases h
    · rename_i root hh ww hr
      rw [hr]
      simp only [bind] at h
      split at h
      · rename_i rows rest hoa
        simp only [hoa, List.cons_append]
        exact congrArg _ (ih rows _ h)
      · cases h

/-- A program without a query step. -/
def osNoQ {α : Type} : Prog α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, osNoQ (k x)
  | .sample k => ∀ x, osNoQ (k x)
  | .grind _ k => osNoQ k
  | .commit _ _ k => osNoQ k
  | .query .. => False

theorem os_queriesOf_noQ {α : Type} : ∀ (p : Prog α), osNoQ p → ∀ s, queriesOf p s = []
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, h, s => by
    simp only [queriesOf]; split
    · rfl
    · exact os_queriesOf_noQ _ (h _) _
  | .sample k, h, s => os_queriesOf_noQ _ (h _) _
  | .grind _ k, h, s => by
    simp only [queriesOf]; split
    · rfl
    · split
      · exact os_queriesOf_noQ k h _
      · rfl
  | .commit _ _ k, h, s => by
    simp only [queriesOf]; split
    · split
      · exact os_queriesOf_noQ k h _
      · rfl
    · rfl
  | .query .., h, _ => h.elim

theorem os_noQ_bind {α β : Type} : ∀ (p : Prog α) (f : α → Prog β), osNoQ p → (∀ a, osNoQ (f a)) →
    osNoQ (p.bind f)
  | .ret a, _, _, hf => hf a
  | .fail, _, _, _ => trivial
  | .read k, f, h, hf => fun x => os_noQ_bind (k x) f (h x) hf
  | .sample k, f, h, hf => fun x => os_noQ_bind (k x) f (h x) hf
  | .grind _ k, f, h, hf => os_noQ_bind k f h hf
  | .commit _ _ k, f, h, hf => os_noQ_bind k f h hf
  | .query .., _, h, _ => h.elim

theorem os_noQ_readN : ∀ n, osNoQ (Prog.readN n)
  | 0 => trivial
  | n + 1 => by
    simp only [Prog.readN, prog_bind_eq]
    exact os_noQ_bind _ _ (fun _ => trivial) fun x => os_noQ_bind _ _ (os_noQ_readN n) fun _ => trivial

theorem os_noQ_sampleN : ∀ n, osNoQ (Prog.sampleN n)
  | 0 => trivial
  | n + 1 => by
    simp only [Prog.sampleN, prog_bind_eq]
    exact os_noQ_bind _ _ (fun _ => trivial) fun x => os_noQ_bind _ _ (os_noQ_sampleN n) fun _ => trivial

theorem os_noQ_roundPoly3 (claim : E) : osNoQ (sumcheckRoundPoly 3 claim none) := by
  simp only [sumcheckRoundPoly, prog_bind_eq]
  exact os_noQ_bind _ _ (fun _ => trivial) fun _ => os_noQ_bind _ _ (os_noQ_readN _) fun _ => trivial

theorem os_noQ_foldRounds : ∀ (n : ℕ) (w : WhirState) (lf : List E), osNoQ (foldRounds n w lf)
  | 0, _, _ => trivial
  | n + 1, w, lf => by
    simp only [foldRounds, prog_bind_eq]
    exact os_noQ_bind _ _ (fun _ => trivial) fun _ =>
      os_noQ_bind _ _ (os_noQ_roundPoly3 _) fun _ => os_noQ_foldRounds n _ _

theorem os_noQ_sampleQueriesAux (depth : ℕ) : ∀ fuel rem, osNoQ (sampleQueriesAux depth fuel rem)
  | 0, _ => trivial
  | fuel + 1, rem => by
    simp only [sampleQueriesAux]
    split
    · trivial
    · simp only [prog_bind_eq]
      exact os_noQ_bind _ _ (fun _ => trivial) fun _ =>
        os_noQ_bind _ _ (os_noQ_sampleQueriesAux depth fuel _) fun _ => trivial

theorem os_noQ_tailRounds : ∀ (n : ℕ) (t : E) (q : List E), osNoQ (tailRounds n t q)
  | 0, _, _ => trivial
  | n + 1, t, q => by
    rw [tailRounds]
    simp only [prog_bind_eq]
    refine os_noQ_bind _ _ (fun _ => trivial) fun ch => ?_
    split
    · trivial
    · exact os_noQ_bind _ _ (os_noQ_roundPoly3 _) fun _ =>
        os_noQ_bind _ _ (os_noQ_tailRounds n _ _) fun _ => trivial

/-- A query step's own steps. -/
theorem os_queriesOf_queryP {i : ℕ} {ps : List ℕ} {s : St} {root : Digest} {hh ww : ℕ}
    {rows : List (List K)} {rest : List Opening} (hr : s.roots[i]? = some (root, hh, ww))
    (ho : openAll (m := Id) blake2sBytes root hh ww ps s.openings = some (rows, rest)) :
    queriesOf (Prog.queryP i ps) s = [(hh, ps.zip s.openings)] := by
  simp only [Prog.queryP, queriesOf, hr, ho]

end
end LeanVM.Guest.B1
