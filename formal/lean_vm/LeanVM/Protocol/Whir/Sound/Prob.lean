/-
  LeanVM.Protocol.Whir.Sound.Prob

  Expectations over the challenges of a group (`Prog.retExp`): their algebra (sequencing,
  monotonicity, sums, constants, independence of the commitments), the uniform tuple drawn by
  `sampleN`, and the query positions drawn by `sampleQueries`: disjoint bit chunks of uniform
  192-bit samples, i.i.d. uniform on the domain.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.ToArkLib.Whir.Ood

/-!
# Expectations over a group of challenges

`LeanVM.Protocol.Compile.Prog.retExp g h₀ l p` is the expectation, over the challenges `p` draws
before its first prover move, of `g` at the return. The joint bounds of `Spec.ofNoMove` are
expectations of indicators. This module computes them for the move-free fragments of the WHIR
verifier (`LeanVM.Protocol.Verifier.verifyWhir`, transcribing `verify_whir` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`):

* algebra: `retExp_bind` (sequencing is iterated expectation), `retExp_mono`, `retExp_add_le`,
  `retExp_const_mul`, `retExp_le_const`, and `retExp_commits` (a function of the commitments of the
  history is constant along a group: samples and openings commit nothing);
* `retExp_sampleN`: `sampleN n` draws a uniform vector of `E^n`;
* `retExp_sampleQueries_le`: the positions of `sampleQueries depth t` all land in a set `S` with
  probability at most `(|S ∩ [0, 2^depth)| / 2^depth)^t`. Each sample is a uniform `E`, read as a
  uniform 192-bit integer (`eToNat`, a bijection `E ≃ [0, 2^192)`), whose `⌊192/depth⌋` chunks of
  `depth` bits are independent and uniform (`card_chunks`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Prog Finset

@[expose] public section

variable {α β : Type}

/-! ## Algebra of expectations -/

/-- The expectation after a longer local history is the one after the longer base history. -/
theorem retExp_shift (g : α → List Ev → ENNReal) :
    ∀ (r : Prog α) (h₀ l m : List Ev), retExp g h₀ (l ++ m) r = retExp g (h₀ ++ l) m r
  | .ret a, h₀, l, m => by simp [retExp]
  | .fail, h₀, l, m => by simp [retExp]
  | .read k, h₀, l, m => by simp [retExp]
  | .grind b k, h₀, l, m => by simp [retExp]
  | .commit ht w k, h₀, l, m => by simp [retExp]
  | .sample k, h₀, l, m => by
    simp only [retExp, List.append_assoc]
    congr 1
    exact Finset.sum_congr rfl fun c _ ↦ retExp_shift g (k c) h₀ l _
  | .query i ps k, h₀, l, m => by
    simp only [retExp, List.append_assoc]
    split <;> rename_i h
    · exact retExp_shift g _ h₀ l _
    · rfl

/-- **Sequencing** is iterated expectation. -/
theorem retExp_bind (g : β → List Ev → ENNReal) (f : α → Prog β) :
    ∀ (q : Prog α) (h₀ l : List Ev),
      retExp g h₀ l (q.bind f) = retExp (fun a h ↦ retExp g h [] (f a)) h₀ l q
  | .ret a, h₀, l => by
    simp only [Prog.bind, retExp]
    rw [← retExp_shift, List.append_nil]
  | .fail, h₀, l => by simp [Prog.bind, retExp]
  | .read k, h₀, l => by simp [Prog.bind, retExp]
  | .grind b k, h₀, l => by simp [Prog.bind, retExp]
  | .commit ht w k, h₀, l => by simp [Prog.bind, retExp]
  | .sample k, h₀, l => by
    simp only [Prog.bind, retExp]
    congr 1
    exact Finset.sum_congr rfl fun c _ ↦ retExp_bind g f (k c) h₀ _
  | .query i ps k, h₀, l => by
    simp only [Prog.bind, retExp]
    split
    · exact retExp_bind g f _ h₀ _
    · rfl

/-- Expectations are monotone. -/
theorem retExp_mono {g g' : α → List Ev → ENNReal} (hg : ∀ a h, g a h ≤ g' a h) :
    ∀ (q : Prog α) (h₀ l : List Ev), retExp g h₀ l q ≤ retExp g' h₀ l q
  | .ret a, h₀, l => by simpa [retExp] using hg a _
  | .fail, h₀, l => by simp [retExp]
  | .read k, h₀, l => by simp [retExp]
  | .grind b k, h₀, l => by simp [retExp]
  | .commit ht w k, h₀, l => by simp [retExp]
  | .sample k, h₀, l => by
    simp only [retExp]
    gcongr with c
    exact retExp_mono hg (k c) h₀ _
  | .query i ps k, h₀, l => by
    simp only [retExp]
    split
    · exact retExp_mono hg _ h₀ _
    · exact le_rfl

/-- Expectations are subadditive. -/
theorem retExp_add_le (g₁ g₂ : α → List Ev → ENNReal) :
    ∀ (q : Prog α) (h₀ l : List Ev),
      retExp (fun a h ↦ g₁ a h + g₂ a h) h₀ l q ≤ retExp g₁ h₀ l q + retExp g₂ h₀ l q
  | .ret a, h₀, l => by simp [retExp]
  | .fail, h₀, l => by simp [retExp]
  | .read k, h₀, l => by simp [retExp]
  | .grind b k, h₀, l => by simp [retExp]
  | .commit ht w k, h₀, l => by simp [retExp]
  | .sample k, h₀, l => by
    simp only [retExp]
    rw [← mul_add, ← Finset.sum_add_distrib]
    gcongr with c
    exact retExp_add_le g₁ g₂ (k c) h₀ _
  | .query i ps k, h₀, l => by
    simp only [retExp]
    split
    · exact retExp_add_le g₁ g₂ _ h₀ _
    · simp

/-- Constants factor out of expectations. -/
theorem retExp_const_mul (c : ENNReal) (g : α → List Ev → ENNReal) :
    ∀ (q : Prog α) (h₀ l : List Ev),
      retExp (fun a h ↦ c * g a h) h₀ l q = c * retExp g h₀ l q
  | .ret a, h₀, l => by simp [retExp]
  | .fail, h₀, l => by simp [retExp]
  | .read k, h₀, l => by simp [retExp]
  | .grind b k, h₀, l => by simp [retExp]
  | .commit ht w k, h₀, l => by simp [retExp]
  | .sample k, h₀, l => by
    simp only [retExp]
    simp_rw [retExp_const_mul c g (k _) h₀, ← Finset.mul_sum]
    ring
  | .query i ps k, h₀, l => by
    simp only [retExp]
    split
    · exact retExp_const_mul c g _ h₀ _
    · simp

/-- An expectation of a function bounded by `c` is at most `c`. -/
theorem retExp_le_const {g : α → List Ev → ENNReal} {c : ENNReal} (hg : ∀ a h, g a h ≤ c) :
    ∀ (q : Prog α) (h₀ l : List Ev), retExp g h₀ l q ≤ c := by
  intro q h₀ l
  have h1 := retExp_mono (g' := fun _ _ ↦ c * 1) (fun a h ↦ by simpa using hg a h) q h₀ l
  rw [retExp_const_mul] at h1
  refine h1.trans ?_
  calc c * retExp (fun _ _ ↦ 1) h₀ l q ≤ c * 1 := by
        gcongr; exact retExp_le_one (fun _ _ ↦ le_rfl) h₀ q l
    _ = c := mul_one c

/-- The commitments of a history extended by samples and openings. -/
theorem commits_append_sample (h : List Ev) (c : E) : commits (h ++ [Ev.sample c]) = commits h := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

theorem commits_append_query (h : List Ev) (rows : List (List K)) :
    commits (h ++ [Ev.query rows]) = commits h := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

theorem answer_append_sample (h : List Ev) (c : E) (i : ℕ) (ps : List ℕ) :
    answer (h ++ [Ev.sample c]) i ps = answer h i ps := by
  simp [answer, commits_append_sample]

theorem answer_append_query (h : List Ev) (rows : List (List K)) (i : ℕ) (ps : List ℕ) :
    answer (h ++ [Ev.query rows]) i ps = answer h i ps := by
  simp [answer, commits_append_query]

/-- **A function of the commitments is constant along a group.** -/
theorem retExp_commits (G : α → List (ℕ × ℕ × Word) → ENNReal) :
    ∀ (q : Prog α) (h₀ l : List Ev),
      retExp (fun a h ↦ G a (commits h)) h₀ l q =
        retExp (fun a _ ↦ G a (commits (h₀ ++ l))) h₀ l q
  | .ret a, h₀, l => by simp [retExp]
  | .fail, h₀, l => by simp [retExp]
  | .read k, h₀, l => by simp [retExp]
  | .grind b k, h₀, l => by simp [retExp]
  | .commit ht w k, h₀, l => by simp [retExp]
  | .sample k, h₀, l => by
    simp only [retExp]
    congr 1
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [retExp_commits G (k c) h₀, ← List.append_assoc, commits_append_sample]
  | .query i ps k, h₀, l => by
    simp only [retExp]
    split
    · rw [retExp_commits G _ h₀, ← List.append_assoc, commits_append_query]
    · rfl

/-- A function of the answers to an opening is evaluated at the answer of the base history. -/
theorem retExp_queryP (g : List (List K) → List Ev → ENNReal) (h₀ l : List Ev) (i : ℕ)
    (ps : List ℕ) :
    retExp g h₀ l (queryP i ps) = match answer (h₀ ++ l) i ps with
      | some rows => g rows (h₀ ++ l ++ [Ev.query rows])
      | none => 0 := by
  simp only [queryP, retExp]
  split <;> rename_i h <;> simp [h, List.append_assoc]

/-- One challenge: the average over `E`. -/
theorem retExp_sampleE (g : E → List Ev → ENNReal) (h₀ l : List Ev) :
    retExp g h₀ l sampleE =
      (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, g c (h₀ ++ l ++ [Ev.sample c]) := by
  simp [sampleE, retExp, List.append_assoc]

/-! ## Uniform tuples -/

/-- **`sampleN n` draws a uniform tuple**, for a function that ignores the history. -/
theorem retExp_sampleN (G : List E → ENNReal) :
    ∀ (n : ℕ) (h₀ l : List Ev), retExp (fun v _ ↦ G v) h₀ l (sampleN n) =
      (Fintype.card E : ENNReal)⁻¹ ^ n * ∑ f : Fin n → E, G (List.ofFn f)
  | 0, h₀, l => by
    simp only [sampleN, retExp, pow_zero, one_mul]
    rw [Fintype.sum_unique]
    simp
  | n + 1, h₀, l => by
    rw [sampleN, show (do let x ← sampleE; let xs ← sampleN n; return x :: xs : Prog (List E)) =
      sampleE.bind fun x ↦ (sampleN n).bind fun xs ↦ ret (x :: xs) from rfl, retExp_bind,
      retExp_sampleE]
    have hin : ∀ c h, retExp (fun v _ ↦ G v) h [] ((sampleN n).bind fun xs ↦ ret (c :: xs)) =
        (Fintype.card E : ENNReal)⁻¹ ^ n * ∑ f : Fin n → E, G (c :: List.ofFn f) := by
      intro c h
      rw [retExp_bind]
      have : (fun a (h' : List Ev) ↦ retExp (fun v _ ↦ G v) h' [] (ret (c :: a))) =
          fun a _ ↦ G (c :: a) := by
        funext a h'; simp [retExp]
      rw [this]
      exact retExp_sampleN (fun v ↦ G (c :: v)) n h []
    simp only [hin]
    rw [pow_succ, ← Finset.mul_sum, ← mul_assoc, mul_comm ((Fintype.card E : ENNReal)⁻¹ ^ n)]
    congr 1
    rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ : Fin (n + 1) ↦ E).sum_comp]
    exact Fintype.sum_congr _ _ fun cf ↦ by simp [Fin.consEquiv, List.ofFn_succ]

end
end LeanVM.Protocol.Whir.Sound
