/-
  LeanVM.Guest.B1.VerifySub.H.WhirPoint

  An accepted run of the stacked opening up to its terminal ends on a point of `μ` coordinates.
-/

module

public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Common.Run

/-!
# The terminal point has `μ` coordinates

`Post p P`: every successful run of `p` returns a value satisfying `P` (`post_bind`, `post_mono`,
`post_true`, `post_ret`). Each fold round adds one fold (`foldRoundsT_post`), the tail rounds
return as many challenges as asked (`tailRoundsT_post`), gluing keeps the folds (`glueT_folds`),
so the levels of a ladder whose folds sum below `μ` end on `μ` coordinates
(`whirLevelsOpen_post`), and so does `whirOpen` (`whirOpen_post`, `whir_point_length`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Every successful run of `p` returns a value satisfying `P`. -/
def Post {α : Type} (p : VerifierProgram α) (P : α → Prop) : Prop :=
  ∀ st a st', runId p st = some (a, st') → P a

theorem post_true {α : Type} (p : VerifierProgram α) : Post p fun _ ↦ True :=
  fun _ _ _ _ ↦ trivial

theorem post_mono {α : Type} {p : VerifierProgram α} {P Q : α → Prop} (h : Post p P)
    (hPQ : ∀ a, P a → Q a) : Post p Q :=
  fun st a st' hr ↦ hPQ a (h st a st' hr)

theorem post_ret {α : Type} {a : α} {P : α → Prop} (h : P a) : Post (VerifierProgram.ret a) P := by
  intro st b st' hr
  simp only [runId, Compile.runWithHash] at hr
  cases hr
  exact h

theorem post_fail {α : Type} (P : α → Prop) : Post (VerifierProgram.fail : VerifierProgram α) P := by
  intro st b st' hr
  simp [runId, Compile.runWithHash] at hr

theorem post_bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {Q : α → Prop} {P : β → Prop} (hp : Post p Q) (hf : ∀ a, Q a → Post (f a) P) :
    Post (p >>= f) P := by
  intro st b st'' hr
  rw [prog_bind_eq, run_bind] at hr
  obtain ⟨⟨a, st'⟩, h1, h2⟩ := Option.bind_eq_some_iff.1 hr
  exact hf a (hp st a st' h1) _ _ _ h2

theorem post_liftOption {α : Type} (o : Option α) : Post (liftOption o) fun a ↦ o = some a := by
  cases o with
  | none => exact post_fail _
  | some a => exact post_ret rfl

/-- **Each fold round adds one fold.** -/
theorem foldRoundsT_post : ∀ (n : ℕ) (s : WhirStateT) (l : List E),
    Post (foldRoundsT n s l) fun r ↦ r.1.folds.length = s.folds.length + n
  | 0, s, l => post_ret rfl
  | n + 1, s, l => by
    simp only [foldRoundsT]
    refine post_bind (post_true _) fun c _ ↦
      post_bind (post_true _) fun q _ ↦ post_mono (foldRoundsT_post n _ _) fun r hr ↦ ?_
    rw [hr, List.length_append, List.length_singleton]
    omega

/-- **The tail rounds return as many challenges as asked.** -/
theorem tailRoundsT_post : ∀ (n : ℕ) (t : E) (q : List E),
    Post (tailRoundsT n t q) fun r ↦ r.1.length = n
  | 0, t, q => post_ret rfl
  | n + 1, t, q => by
    simp only [tailRoundsT]
    refine post_bind (post_true _) fun c _ ↦ ?_
    split
    · rename_i hn
      subst hn
      exact post_ret rfl
    · refine post_bind (post_true _) fun q' _ ↦ post_bind (tailRoundsT_post n _ _) fun r hr ↦ ?_
      obtain ⟨rest, tg⟩ := r
      exact post_ret (by simp only [List.length_cons]; simp only at hr; omega)

/-- **Gluing keeps the folds.** -/
theorem glueT_folds (lam : E) (s : WhirStateT) (pending : List (E × List E × (List E → E))) :
    (glueT lam s pending).folds = s.folds := by
  unfold glueT
  show _ = (s, (1 : E)).1.folds
  generalize (s, (1 : E)) = acc
  induction pending generalizing acc with
  | nil => rfl
  | cons x rest ih => rw [List.foldl_cons, ih]

/-- **The levels end on `logN` coordinates**, when their folds and the folds so far are at most
`logN`. -/
theorem whirLevelsOpen_post (logN lane : ℕ) : ∀ (index : ℕ) (levels : List Whir.Level)
    (s : WhirStateT), s.folds.length + (levels.map (·.fold)).sum ≤ logN →
    Post (B1.Whir.whirLevelsOpen logN lane index levels s) fun w ↦ w.point.length = logN
  | _, [], _, _ => post_fail _
  | index, level :: rest, s, hsum => by
    simp only [List.map_cons, List.sum_cons] at hsum
    simp only [B1.Whir.whirLevelsOpen]
    refine post_bind (foldRoundsT_post _ _ _) fun r hr ↦ ?_
    obtain ⟨s1, lf⟩ := r
    simp only at hr
    cases rest with
    | nil =>
      dsimp only
      iterate 7 refine post_bind (post_true _) fun _ _ ↦ ?_
      refine post_bind (tailRoundsT_post _ _ _) fun t ht ↦ post_ret ?_
      simp only [List.length_append, List.length_drop, List.length_take, glueT_folds, ht]
      simp only [List.map_nil, List.sum_nil, add_zero] at hsum
      omega
    | cons l2 tail =>
      dsimp only
      iterate 10 refine post_bind (post_true _) fun _ _ ↦ ?_
      refine whirLevelsOpen_post logN lane (index + 1) _ _ ?_
      rw [glueT_folds, hr]
      simp only [List.map_cons, List.sum_cons] at hsum ⊢
      omega

/-- **`whirOpen` ends on `μ` coordinates.** -/
theorem whirOpen_post (μ r : ℕ) (target : E) :
    Post (B1.Whir.whirOpen μ r target) fun w ↦ w.point.length = μ := by
  simp only [B1.Whir.whirOpen]
  refine post_bind (post_liftOption _) fun cfg hcfg ↦ post_bind (post_true _) fun _ _ ↦ ?_
  exact whirLevelsOpen_post μ _ 0 cfg _ (by
    have := WhirTarget.ladder_sum_lt hcfg
    simp only [List.length_nil, zero_add]
    omega)

/-- **An accepted opening's terminal point has `μ` coordinates.** -/
theorem whir_point_length {μ r : ℕ} {S : KeccakState} {root : Digest} {target : E} {xs : List E}
    {os : List (List Opening)} {w : B1.Whir.WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : B1.Whir.RunsWith (B1.Whir.whirOpen μ r target) ⟨capOf S, []⟩ xs os
      [(root, B1.Whir.stackShape μ r)] w s' roots') : w.point.length = μ := by
  obtain ⟨sp', -, hr⟩ := hrun ⟨S, []⟩ ⟨rfl, rfl⟩ [] []
  exact whirOpen_post μ r target _ _ _ hr

end
end LeanVM.Guest.B1.VerifySub
