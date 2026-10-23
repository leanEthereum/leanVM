/-
  LeanVM.Guest.B1.VerifySub.Inv0

  Runs of the specification's programs, backward: a run reads a prefix of the stream and of the
  openings, the same on any continuation, and a program that neither commits nor opens reads
  the same from any openings and roots.
-/

module

public import LeanVM.Guest.B1.VerifySub.Run

/-!
# Runs, backward

* `runs_bind_inv`: a run of `p >>= f` is a run of `p`, then of `f` from its end;
* `runs_frame`: a run reads a prefix of the stream and of the openings, and runs the same on any
  continuation of both (`RunsWith`);
* `QFree`: a program with no `commit` and no `query`; `qfree_frame`: its run reads a prefix of the
  stream, the same from any openings and roots (`RunsTo`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem runs_bind_inv {α β : Type} {p : Prog α} {f : α → Prog β} {s s'' : St} {b : β}
    (h : Runs (p.bind f) s b s'') : ∃ a s', Runs p s a s' ∧ Runs (f a) s' b s'' := by
  unfold Runs at *
  rw [run_bind] at h
  match hp : runId p s, h with
  | some (a, s'), h => exact ⟨a, s', rfl, h⟩

/-! ## The steps -/

theorem inv_grind_cons {α : Type} (b : ℕ) (k : Prog α) (cv : Digest) (n : E) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runId (.grind b k) ⟨cv, n :: xs, os, roots⟩ =
      if powOk b n (blake2sBytes (digestBytes (blake2sBytes (digestBytes cv ++ blockOf 0 3)) ++
        blockOf n 4)) then runId k ⟨blake2sBytes (digestBytes cv ++ blockOf n 4), xs, os, roots⟩
      else none := rfl

/-! ## The openings -/

/-- `openAll` reads a prefix of the openings, the same on any continuation. -/
theorem openAll_frame (root : Digest) (hh w : ℕ) : ∀ (qs : List ℕ) (os rest : List Opening)
    (rows : List (List K)), Compile.openAll (m := Id) blake2sBytes root hh w qs os = some (rows, rest) →
    ∃ os1, os = os1 ++ rest ∧ ∀ orest,
      Compile.openAll (m := Id) blake2sBytes root hh w qs (os1 ++ orest) = some (rows, orest)
  | [], os, rest, rows, h => by
    simp only [Compile.openAll] at h
    cases h
    exact ⟨[], rfl, fun _ => rfl⟩
  | _ :: _, [], _, _, h => by simp [Compile.openAll] at h
  | q :: qs, o :: os, rest, rows, h => by
    simp only [Compile.openAll, bind] at h
    split at h
    · rename_i hok
      match hr : Compile.openAll (m := Id) blake2sBytes root hh w qs os, h with
      | some (rows', rest'), h =>
        simp only [Option.map_some] at h
        cases h
        obtain ⟨os1, rfl, h1⟩ := openAll_frame root hh w qs os _ _ hr
        refine ⟨o :: os1, rfl, fun orest => ?_⟩
        simp only [List.cons_append, Compile.openAll, bind, hok, ↓reduceIte, h1 orest]
        rfl
    · cases h

/-! ## Any program -/

/-- **A run reads a prefix** of the stream and of the openings, and runs the same on any
continuation of both. -/
theorem runs_frame {α : Type} (p : Prog α) : ∀ (cv : Digest) (xs : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (a : α) (s' : St),
    runId p ⟨cv, xs, os, roots⟩ = some (a, s') →
    ∃ ys os1, xs = ys ++ s'.stream ∧ os = os1 ++ s'.openings ∧
      RunsWith p cv ys os1 roots a s'.cv s'.roots := by
  induction p with
  | ret b =>
    intro cv xs os roots a s' h
    cases h
    exact ⟨[], [], rfl, rfl, fun _ _ => rfl⟩
  | fail => intro _ _ _ _ _ _ h; cases h
  | read k ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => cases h
    | x :: xs, h =>
      obtain ⟨ys, os1, h1, h2, h3⟩ := ih x _ xs os roots a s' h
      exact ⟨x :: ys, os1, by rw [h1]; rfl, h2, fun rest orest => h3 rest orest⟩
  | sample k ih =>
    intro cv xs os roots a s' h
    obtain ⟨ys, os1, h1, h2, h3⟩ := ih _ _ xs os roots a s' h
    exact ⟨ys, os1, h1, h2, fun rest orest => h3 rest orest⟩
  | grind b k ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => cases h
    | n :: xs, h =>
      rw [inv_grind_cons] at h
      split at h
      · rename_i hpow
        obtain ⟨ys, os1, h1, h2, h3⟩ := ih _ xs os roots a s' h
        refine ⟨n :: ys, os1, by rw [h1]; rfl, h2, fun rest orest => ?_⟩
        rw [List.cons_append, inv_grind_cons]
        simp only [hpow, ↓reduceIte]
        exact h3 rest orest
      · cases h
  | commit hh w k ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => cases h
    | [_], h => cases h
    | x0 :: x1 :: xs, h =>
      simp only [runId, Compile.run] at h
      split at h
      · rename_i root hroot
        obtain ⟨ys, os1, h1, h2, h3⟩ := ih _ xs os _ a s' h
        refine ⟨x0 :: x1 :: ys, os1, by rw [h1]; rfl, h2, fun rest orest => ?_⟩
        simp only [runId, Compile.run, List.cons_append, hroot]
        exact h3 rest orest
      · cases h
  | query i ps k ih =>
    intro cv xs os roots a s' h
    simp only [runId, Compile.run] at h
    split at h
    · cases h
    · rename_i root hh w hi
      simp only [bind] at h
      split at h
      · rename_i rows rest hoa
        obtain ⟨os1, rfl, hf⟩ := openAll_frame root hh w ps os rest rows hoa
        obtain ⟨ys, os2, h1, h2, h3⟩ := ih rows _ xs rest roots a s' h
        refine ⟨ys, os1 ++ os2, h1, by rw [h2, List.append_assoc], fun R O => ?_⟩
        simp only [runId, Compile.run, hi, bind, List.append_assoc, hf (os2 ++ O)]
        exact h3 R O
      · cases h

/-! ## Programs that neither commit nor open -/

/-- A program with no `commit` and no `query`. -/
inductive QFree {α : Type} : Prog α → Prop where
  | ret (a : α) : QFree (.ret a)
  | fail : QFree .fail
  | read (k : E → Prog α) (h : ∀ x, QFree (k x)) : QFree (.read k)
  | sample (k : E → Prog α) (h : ∀ x, QFree (k x)) : QFree (.sample k)
  | grind (b : ℕ) (k : Prog α) (h : QFree k) : QFree (.grind b k)

/-- **A run of a program that neither commits nor opens** reads a prefix of the stream, the same
from any openings and roots. -/
theorem qfree_frame {α : Type} {p : Prog α} (hq : QFree p) :
    ∀ (cv : Digest) (xs : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)) (a : α)
      (s' : St), runId p ⟨cv, xs, os, roots⟩ = some (a, s') →
      ∃ ys, xs = ys ++ s'.stream ∧ s'.openings = os ∧ s'.roots = roots ∧ RunsTo p cv ys a s'.cv := by
  induction hq with
  | ret b =>
    intro cv xs os roots a s' h
    cases h
    exact ⟨[], rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | fail => intro _ _ _ _ _ _ h; cases h
  | read k _ ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => cases h
    | x :: xs, h =>
      obtain ⟨ys, h1, h2, h3, h4⟩ := ih x _ xs os roots a s' h
      exact ⟨x :: ys, by rw [h1]; rfl, h2, h3, fun rest os roots => h4 rest os roots⟩
  | sample k _ ih =>
    intro cv xs os roots a s' h
    obtain ⟨ys, h1, h2, h3, h4⟩ := ih _ _ xs os roots a s' h
    exact ⟨ys, h1, h2, h3, fun rest os roots => h4 rest os roots⟩
  | grind b k _ ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => cases h
    | n :: xs, h =>
      rw [inv_grind_cons] at h
      split at h
      · rename_i hpow
        obtain ⟨ys, h1, h2, h3, h4⟩ := ih _ xs os roots a s' h
        refine ⟨n :: ys, by rw [h1]; rfl, h2, h3, fun rest os roots => ?_⟩
        rw [List.cons_append, inv_grind_cons]
        simp only [hpow, ↓reduceIte]
        exact h4 rest os roots
      · cases h

theorem QFree.bind {α β : Type} {p : Prog α} {f : α → Prog β} (hp : QFree p)
    (hf : ∀ a, QFree (f a)) : QFree (p.bind f) := by
  induction hp with
  | ret a => exact hf a
  | fail => exact .fail
  | read k _ ih => exact .read _ ih
  | sample k _ ih => exact .sample _ ih
  | grind b k _ ih => exact .grind _ _ ih

theorem QFree.bind' {α β : Type} {p : Prog α} {f : α → Prog β} (hp : QFree p)
    (hf : ∀ a, QFree (f a)) : QFree (p >>= f) := hp.bind hf

theorem QFree.pure {α : Type} (a : α) : QFree (pure a : Prog α) := .ret a

theorem qfree_readE : QFree Prog.readE := .read _ fun x => .ret x

theorem qfree_sampleE : QFree Prog.sampleE := .sample _ fun x => .ret x

theorem qfree_readN : ∀ n, QFree (Prog.readN n)
  | 0 => .ret _
  | n + 1 => qfree_readE.bind fun _ => (qfree_readN n).bind fun _ => .ret _

theorem qfree_sampleN : ∀ n, QFree (Prog.sampleN n)
  | 0 => .ret _
  | n + 1 => qfree_sampleE.bind fun _ => (qfree_sampleN n).bind fun _ => .ret _

theorem qfree_require (c : Prop) [Decidable c] : QFree (Prog.require c) := by
  unfold Prog.require; split
  · exact .ret _
  · exact .fail

theorem qfree_grindP (b : ℕ) : QFree (Prog.grindP b) := .grind _ _ (.ret _)

theorem qfree_liftOption {α : Type} : ∀ o : Option α, QFree (Verifier.liftOption o)
  | none => .fail
  | some a => .ret a

end
end LeanVM.Guest.B1.VerifySub
