/-
  LeanVM.Protocol.Compile.Rom.IdealCalc

  A calculus for the ideal failure probability `Strategy.failFrom`: expectations along a run,
  sequencing, an inserted check, every zero challenge refused, and a strategy that wins.
-/

module

public import LeanVM.Protocol.Compile.Rom.Ideal
public import LeanVM.Protocol.Compile.Cost
public import LeanVM.Protocol.Verifier.Deferred
public import Statement.LeanVmGuestCompleteness

/-!
# Calculating the ideal failure probability

`S.exp0 A h g C`: the expectation of `C` at the end of the ideal run of `A` (every challenge
uniform and independent), a failure counting `0`. It is linear (`exp0_add`, `exp0_const_mul`),
monotone, at most a constant's value for a constant (`exp0_const_le`), and sequences
(`exp0_bind`).

* `failFrom_bind_le`: two programs sharing their first part fail at most as often as each other
  plus the expected difference of their continuations.
* `failFrom_require_bind_le`: a check inserted fails with at most the probability that it does
  not hold.
* `failFrom_refusingZero_le`: refusing every zero challenge adds at most `2^-128` per sample of
  the program, a quarter of its cost.
* `failFrom_eq_zero`: a strategy that wins every interactive run never fails.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol
open scoped ENNReal

@[expose] public section

namespace Strategy

variable (S : Strategy)

open Classical in
/-- **The expectation of `C` at the end of the ideal run of a program**, a failure counting
`0`. -/
noncomputable def exp0 {α : Type} : VerifierProgram α → List Ev → Option E →
    (α → List Ev → Option E → ℝ≥0∞) → ℝ≥0∞
  | .ret a, h, g, C => C a h g
  | .fail, _, _, _ => 0
  | .read k, h, g, C => if g.isSome then 0 else
      exp0 (k (S.msg h)) (h ++ [Ev.read (S.msg h)]) none C
  | .sample k, h, g, C => match g with
    | some c => exp0 (k c) (h ++ [Ev.sample c]) none C
    | none => avgE fun c ↦ exp0 (k c) (h ++ [Ev.sample c]) none C
  | .grind b k, h, g, C => if g.isSome then 0 else
      avgE fun c ↦ exp0 k (h ++ [Ev.grind b]) (some c) C
  | .commit ht w k, h, g, C => if g.isSome ∨ ¬ WellShaped w (S.word h) then 0 else
      exp0 k (h ++ [Ev.commit ht w (S.word h)]) none C
  | .query i ps k, h, g, C => match answer h i ps with
    | some rows => exp0 (k rows) (h ++ [Ev.query rows]) g C
    | none => 0

variable {S}

theorem avg_le_const {γ : Type} [Fintype γ] [Nonempty γ] {f : γ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x, f x ≤ c) : (∑ x, f x) / Fintype.card γ ≤ c := by
  have hc : (Fintype.card γ : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.div_le_iff hc (ENNReal.natCast_ne_top _)]
  calc ∑ x, f x ≤ ∑ _x : γ, c := Finset.sum_le_sum fun x _ ↦ h x
    _ = c * Fintype.card γ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

theorem avgE_add (f f' : E → ℝ≥0∞) : avgE (fun c ↦ f c + f' c) = avgE f + avgE f' := by
  unfold avgE
  rw [Finset.sum_add_distrib, ENNReal.add_div]

theorem avgE_mono {f f' : E → ℝ≥0∞} (h : ∀ c, f c ≤ f' c) : avgE f ≤ avgE f' := by
  unfold avgE
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun c _ ↦ h c) _

theorem avgE_le_const {f : E → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, f x ≤ c) : avgE f ≤ c := by
  unfold avgE
  exact avg_le_const h

theorem avgE_const (x : ℝ≥0∞) : avgE (fun _ ↦ x) = x := by
  unfold avgE
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, ENNReal.mul_div_cancel_right
    (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]

theorem avgE_mul_const (c : ℝ≥0∞) (f : E → ℝ≥0∞) : avgE (fun x ↦ c * f x) = c * avgE f := by
  unfold avgE
  rw [← Finset.mul_sum, mul_div_assoc]

/-- The average of the indicator of `0` over `E`. -/
theorem avgE_ind_zero : avgE (fun c ↦ if c = 0 then 1 else 0) = epsE := by
  unfold avgE epsE
  rw [Finset.sum_ite_eq' Finset.univ (0 : E)]
  simp only [Finset.mem_univ, ↓reduceIte, one_div]

/-- `exp0` is additive. -/
theorem exp0_add {α : Type} (C C' : α → List Ev → Option E → ℝ≥0∞) :
    ∀ (A : VerifierProgram α) (h : List Ev) (g : Option E),
      S.exp0 A h g (fun a h' g' ↦ C a h' g' + C' a h' g') = S.exp0 A h g C + S.exp0 A h g C' := by
  intro A
  induction A with
  | ret a => intros; rfl
  | fail => intros; simp [exp0]
  | read k ih =>
    intro h g
    simp only [exp0]
    split <;> simp [ih]
  | sample k ih =>
    intro h g
    rcases g with _ | c
    · simp only [exp0, ih, avgE_add]
    · simp only [exp0, ih]
  | grind b k ih =>
    intro h g
    simp only [exp0]
    split
    · simp
    · simp only [ih, avgE_add]
  | commit ht w k ih =>
    intro h g
    simp only [exp0]
    split <;> simp [ih]
  | query i ps k ih =>
    intro h g
    simp only [exp0]
    split <;> simp [ih]

/-- `exp0` is monotone. -/
theorem exp0_mono {α : Type} {C C' : α → List Ev → Option E → ℝ≥0∞}
    (hC : ∀ a h g, C a h g ≤ C' a h g) :
    ∀ (A : VerifierProgram α) (h : List Ev) (g : Option E), S.exp0 A h g C ≤ S.exp0 A h g C' := by
  intro A
  induction A with
  | ret a => intro h g; exact hC a h g
  | fail => intros; simp [exp0]
  | read k ih =>
    intro h g
    simp only [exp0]
    split
    · exact le_rfl
    · exact ih _ _ _
  | sample k ih =>
    intro h g
    rcases g with _ | c
    · simp only [exp0]
      exact avgE_mono fun c ↦ ih _ _ _
    · exact ih _ _ _
  | grind b k ih =>
    intro h g
    simp only [exp0]
    split
    · exact le_rfl
    · exact avgE_mono fun c ↦ ih _ _
  | commit ht w k ih =>
    intro h g
    simp only [exp0]
    split
    · exact le_rfl
    · exact ih _ _
  | query i ps k ih =>
    intro h g
    simp only [exp0]
    split
    · exact ih _ _ _
    · exact le_rfl

/-- `exp0` of a constant is at most the constant. -/
theorem exp0_const_le {α : Type} (c : ℝ≥0∞) :
    ∀ (A : VerifierProgram α) (h : List Ev) (g : Option E),
      S.exp0 A h g (fun _ _ _ ↦ c) ≤ c := by
  intro A
  induction A with
  | ret a => intros; exact le_rfl
  | fail => intros; simp [exp0]
  | read k ih =>
    intro h g
    simp only [exp0]
    split
    · exact bot_le
    · exact ih _ _ _
  | sample k ih =>
    intro h g
    rcases g with _ | c'
    · exact avgE_le_const fun _ ↦ ih _ _ _
    · exact ih _ _ _
  | grind b k ih =>
    intro h g
    simp only [exp0]
    split
    · exact bot_le
    · exact avgE_le_const fun _ ↦ ih _ _
  | commit ht w k ih =>
    intro h g
    simp only [exp0]
    split
    · exact bot_le
    · exact ih _ _
  | query i ps k ih =>
    intro h g
    simp only [exp0]
    split
    · exact ih _ _ _
    · exact bot_le

/-- `exp0` sequences. -/
theorem exp0_bind {α β : Type} (f : α → VerifierProgram β) (C : β → List Ev → Option E → ℝ≥0∞) :
    ∀ (A : VerifierProgram α) (h : List Ev) (g : Option E),
      S.exp0 (A.bind f) h g C = S.exp0 A h g (fun a h' g' ↦ S.exp0 (f a) h' g' C) := by
  intro A
  induction A with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro h g
    simp only [VerifierProgram.bind, exp0]
    split
    · rfl
    · exact ih _ _ _
  | sample k ih =>
    intro h g
    rcases g with _ | c
    · simp only [VerifierProgram.bind, exp0, ih]
    · simp only [VerifierProgram.bind, exp0, ih]
  | grind b k ih =>
    intro h g
    simp only [VerifierProgram.bind, exp0]
    split
    · rfl
    · simp only [ih]
  | commit ht w k ih =>
    intro h g
    simp only [VerifierProgram.bind, exp0]
    split
    · rfl
    · exact ih _ _
  | query i ps k ih =>
    intro h g
    simp only [VerifierProgram.bind, exp0]
    split
    · exact ih _ _ _
    · rfl

/-- **Two programs sharing their first part**: the first fails at most as often as the second
plus the expected difference of their continuations. -/
theorem failFrom_bind_le {α : Type} {f' f : α → VerifierProgram Bool}
    {D : α → List Ev → Option E → ℝ≥0∞}
    (hf : ∀ a h g, S.failFrom (f' a) h g ≤ S.failFrom (f a) h g + D a h g) :
    ∀ (A : VerifierProgram α) (h : List Ev) (g : Option E),
      S.failFrom (A.bind f') h g ≤ S.failFrom (A.bind f) h g + S.exp0 A h g D := by
  intro A
  induction A with
  | ret a => intro h g; exact hf a h g
  | fail => intros; simp [VerifierProgram.bind, failFrom]
  | read k ih =>
    intro h g
    simp only [VerifierProgram.bind, failFrom, exp0]
    split
    · simp
    · exact ih _ _ _
  | sample k ih =>
    intro h g
    rcases g with _ | c
    · simp only [VerifierProgram.bind, failFrom, exp0]
      rw [← avgE_add]
      exact avgE_mono fun c ↦ ih _ _ _
    · exact ih _ _ _
  | grind b k ih =>
    intro h g
    simp only [VerifierProgram.bind, failFrom, exp0]
    split
    · simp
    · rw [← avgE_add]
      exact avgE_mono fun c ↦ ih _ _
  | commit ht w k ih =>
    intro h g
    simp only [VerifierProgram.bind, failFrom, exp0]
    split
    · simp
    · exact ih _ _
  | query i ps k ih =>
    intro h g
    simp only [VerifierProgram.bind, failFrom, exp0]
    rcases ha : answer h i ps with _ | rows
    · simp
    · exact ih _ _ _

open Classical in
/-- **An inserted check** fails at most with the probability that it does not hold. -/
theorem failFrom_require_bind_le (c : Prop) [Decidable c] (X : VerifierProgram Bool)
    (h : List Ev) (g : Option E) :
    S.failFrom ((VerifierProgram.require c).bind fun _ ↦ X) h g ≤
      (if c then 0 else 1) + S.failFrom X h g := by
  unfold VerifierProgram.require
  split
  · simp [VerifierProgram.bind]
  · simp [VerifierProgram.bind, failFrom]

/-- **Refusing every zero challenge** adds at most `|E|⁻¹` per sample of the program (a quarter
of its cost), and fails at once on a waiting zero challenge. -/
theorem failFrom_refusingZero_le {height : ℕ} :
    ∀ (P : VerifierProgram Bool) (n : ℕ), P.CostLE height n → ∀ (h : List Ev) (g : Option E),
      S.failFrom P.refusingZeroChallenge h g ≤
        S.failFrom P h g + (if g = some 0 then 1 else 0) +
          ((n / 4 : ℕ) : ℝ≥0∞) * epsE := by
  intro P
  induction P with
  | ret a => intros; exact le_self_add.trans le_self_add
  | fail => intros; exact le_self_add.trans le_self_add
  | read k ih =>
    intro n hc h g
    simp only [VerifierProgram.refusingZeroChallenge, failFrom]
    split
    · exact le_self_add.trans le_self_add
    · rename_i hg
      have hg' : g = none := by simpa using hg
      subst hg'
      refine (ih _ (n - 1) (hc.2 _) _ none).trans ?_
      simp only [reduceCtorEq, ↓reduceIte, add_zero]
      gcongr
      exact Nat.sub_le n 1
  | sample k ih =>
    intro n hc h g
    have hn : 4 ≤ n := hc.1
    have hq : (n - 4) / 4 + 1 = n / 4 := by omega
    rcases g with _ | c
    · simp only [VerifierProgram.refusingZeroChallenge, failFrom, reduceCtorEq, ↓reduceIte,
        add_zero]
      calc avgE (fun c ↦ S.failFrom (if c = 0 then VerifierProgram.fail
              else (k c).refusingZeroChallenge) (h ++ [Ev.sample c]) none)
          ≤ avgE (fun c ↦ (if c = 0 then 1 else 0) + (S.failFrom (k c) (h ++ [Ev.sample c]) none +
              (((n - 4) / 4 : ℕ) : ℝ≥0∞) * epsE)) := by
            refine avgE_mono fun c ↦ ?_
            split
            · rename_i hc0
              simp only [failFrom]
              exact le_self_add
            · rename_i hc0
              have := ih c (n - 4) (hc.2 c) (h ++ [Ev.sample c]) none
              simp only [reduceCtorEq, ↓reduceIte, add_zero] at this
              simp only [zero_add]
              exact this
        _ = epsE + (avgE (fun c ↦ S.failFrom (k c) (h ++ [Ev.sample c]) none) +
              (((n - 4) / 4 : ℕ) : ℝ≥0∞) * epsE) := by
            rw [avgE_add, avgE_ind_zero, avgE_add, avgE_const]
        _ = _ := by
            rw [← hq, Nat.cast_add, Nat.cast_one, add_one_mul]
            ring
    · simp only [VerifierProgram.refusingZeroChallenge, failFrom, Option.some.injEq]
      split
      · rename_i hc0
        simp only [failFrom, hc0]
        exact le_add_self.trans le_self_add
      · rename_i hc0
        refine (ih c (n - 4) (hc.2 c) (h ++ [Ev.sample c]) none).trans ?_
        simp only [reduceCtorEq, ↓reduceIte, add_zero]
        gcongr
        exact Nat.sub_le n 4
  | grind b k ih =>
    intro n hc h g
    have hn : 5 ≤ n := hc.1
    simp only [VerifierProgram.refusingZeroChallenge, failFrom]
    split
    · exact le_self_add.trans le_self_add
    · rename_i hg
      have hg' : g = none := by simpa using hg
      subst hg'
      simp only [reduceCtorEq, ↓reduceIte, add_zero]
      calc avgE (fun c ↦ S.failFrom k.refusingZeroChallenge (h ++ [Ev.grind b]) (some c))
          ≤ avgE (fun c ↦ (if c = 0 then 1 else 0) + (S.failFrom k (h ++ [Ev.grind b]) (some c) +
              (((n - 5) / 4 : ℕ) : ℝ≥0∞) * epsE)) := by
            refine avgE_mono fun c ↦ ?_
            have := ih (n - 5) hc.2 (h ++ [Ev.grind b]) (some c)
            simp only [Option.some.injEq] at this
            calc _ ≤ _ := this
              _ = _ := by ring
        _ = epsE + (avgE (fun c ↦ S.failFrom k (h ++ [Ev.grind b]) (some c)) +
              (((n - 5) / 4 : ℕ) : ℝ≥0∞) * epsE) := by
            rw [avgE_add, avgE_ind_zero, avgE_add, avgE_const]
        _ ≤ _ := by
            have hq : (n - 5) / 4 + 1 ≤ n / 4 := by omega
            calc epsE + (avgE (fun c ↦ S.failFrom k (h ++ [Ev.grind b]) (some c)) +
                  (((n - 5) / 4 : ℕ) : ℝ≥0∞) * epsE)
                = avgE (fun c ↦ S.failFrom k (h ++ [Ev.grind b]) (some c)) +
                    ((((n - 5) / 4 + 1 : ℕ) : ℝ≥0∞)) * epsE := by
                  rw [Nat.cast_add, Nat.cast_one, add_one_mul]; ring
              _ ≤ _ := by gcongr
  | commit ht w k ih =>
    intro n hc h g
    simp only [VerifierProgram.refusingZeroChallenge, failFrom]
    split
    · exact le_self_add.trans le_self_add
    · rename_i hg
      have hg' : g = none := by
        rcases g with _ | c
        · rfl
        · exact absurd (Or.inl rfl) hg
      subst hg'
      refine (ih (n - 2) hc.2.2 _ none).trans ?_
      simp only [reduceCtorEq, ↓reduceIte, add_zero]
      gcongr
      exact Nat.sub_le n 2
  | query i ps k ih =>
    intro n hc h g
    simp only [VerifierProgram.refusingZeroChallenge, failFrom]
    rcases ha : answer h i ps with _ | rows
    · exact le_self_add.trans le_self_add
    · refine (ih rows _ (hc.2 rows) _ g).trans ?_
      gcongr
      exact Nat.sub_le _ _

/-- **A strategy that wins every interactive run never fails**, from a history where no
challenge waits or the program samples next. -/
theorem failFrom_eq_zero :
    ∀ (p : VerifierProgram Bool) (h : List Ev) (g : Option E), S.AcceptsFrom p h →
      GrindThenSample p → (g = none ∨ ∃ k, p = .sample k) → S.failFrom p h g = 0 := by
  intro p
  induction p with
  | ret b => intro h g hacc _ _; simp [failFrom, show b = true from hacc]
  | fail => intro h g hacc; exact absurd hacc id
  | read k ih =>
    intro h g hacc hP hg
    obtain rfl : g = none := hg.resolve_right (by simp)
    exact ih _ _ _ hacc (grindThenSample_after hP (l := [Ev.read (S.msg h)])
      (by simp [VerifierProgram.after])) (Or.inl rfl)
  | sample k ih =>
    intro h g hacc hP _
    have hk : ∀ c, S.failFrom (k c) (h ++ [Ev.sample c]) none = 0 := fun c ↦
      ih c _ _ (hacc c) (grindThenSample_after hP (l := [Ev.sample c])
        (by simp [VerifierProgram.after])) (Or.inl rfl)
    rcases g with _ | c
    · simp only [failFrom, hk, avgE_const]
    · exact hk c
  | grind b k ih =>
    intro h g hacc hP hg
    obtain rfl : g = none := hg.resolve_right (by simp)
    obtain ⟨k', rfl⟩ := hP [] b k rfl
    rw [failFrom]
    have : ∀ c, S.failFrom (VerifierProgram.sample k') (h ++ [Ev.grind b]) (some c) = 0 :=
      fun c ↦ ih _ _ hacc (grindThenSample_after hP (l := [Ev.grind b])
        (by simp [VerifierProgram.after])) (Or.inr ⟨k', rfl⟩)
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, this, avgE_const]
  | commit ht w k ih =>
    intro h g hacc hP hg
    obtain rfl : g = none := hg.resolve_right (by simp)
    obtain ⟨hw, hacc⟩ := hacc
    simp only [failFrom, Option.isSome_none, Bool.false_eq_true, hw, not_true_eq_false, or_self,
      ↓reduceIte]
    exact ih _ _ hacc (grindThenSample_after hP (l := [Ev.commit ht w (S.word h)])
      (by simp [VerifierProgram.after])) (Or.inl rfl)
  | query i ps k ih =>
    intro h g hacc hP hg
    obtain rfl : g = none := hg.resolve_right (by simp)
    obtain ⟨rows, hans, hacc⟩ := hacc
    simp only [failFrom, hans]
    exact ih _ _ _ hacc (grindThenSample_after hP (l := [Ev.query rows])
      (by simp [VerifierProgram.after])) (Or.inl rfl)


/-- `exp0` scales. -/
theorem exp0_const_mul {α : Type} (c : ℝ≥0∞) (C : α → List Ev → Option E → ℝ≥0∞) :
    ∀ (A : VerifierProgram α) (h : List Ev) (g : Option E),
      S.exp0 A h g (fun a h' g' ↦ c * C a h' g') = c * S.exp0 A h g C := by
  intro A
  induction A with
  | ret a => intros; rfl
  | fail => intros; simp [exp0]
  | read k ih =>
    intro h g
    simp only [exp0]
    split <;> simp [ih]
  | sample k ih =>
    intro h g
    rcases g with _ | c'
    · simp only [exp0, ih, avgE_mul_const]
    · simp only [exp0, ih]
  | grind b k ih =>
    intro h g
    simp only [exp0]
    split
    · simp
    · simp only [ih, avgE_mul_const]
  | commit ht w k ih =>
    intro h g
    simp only [exp0]
    split <;> simp [ih]
  | query i ps k ih =>
    intro h g
    simp only [exp0]
    split <;> simp [ih]

/-- `exp0` of a finite sum. -/
theorem exp0_sum {α ι : Type} (s : Finset ι) (C : ι → α → List Ev → Option E → ℝ≥0∞)
    (A : VerifierProgram α) (h : List Ev) (g : Option E) :
    S.exp0 A h g (fun a h' g' ↦ ∑ i ∈ s, C i a h' g') = ∑ i ∈ s, S.exp0 A h g (C i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := S.exp0_const_mul 0 (fun _ _ _ ↦ 0) A h g
    simpa using this
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [S.exp0_add (C i) (fun a h' g' ↦ ∑ i ∈ s, C i a h' g') A h g, ih]

/-- `failFrom_bind_le` with a constant difference. -/
theorem failFrom_bind_le_const {α : Type} {f' f : α → VerifierProgram Bool} {c : ℝ≥0∞}
    (hf : ∀ a h g, S.failFrom (f' a) h g ≤ S.failFrom (f a) h g + c) (A : VerifierProgram α)
    (h : List Ev) (g : Option E) : S.failFrom (A >>= f') h g ≤ S.failFrom (A >>= f) h g + c := by
  rw [VerifierProgram.bind_eq, VerifierProgram.bind_eq]
  exact (failFrom_bind_le (D := fun _ _ _ ↦ c) hf A h g).trans
    (add_le_add le_rfl (exp0_const_le c A h g))

/-- **`X'` fails at most `c` more often than `X`**, whatever follows them. -/
def DivLE {α : Type} (S : Strategy) (c : ℝ≥0∞) (X' X : VerifierProgram α) : Prop :=
  ∀ (K : α → VerifierProgram Bool) (h : List Ev) (g : Option E),
    S.failFrom (X' >>= K) h g ≤ S.failFrom (X >>= K) h g + c

theorem DivLE.refl {α : Type} (c : ℝ≥0∞) (X : VerifierProgram α) : DivLE S c X X :=
  fun _ _ _ ↦ le_self_add

/-- A common first part keeps a difference. -/
theorem DivLE.bind_refl {α β : Type} {c : ℝ≥0∞} {f' f : α → VerifierProgram β}
    (hf : ∀ a, DivLE S c (f' a) (f a)) (A : VerifierProgram α) :
    DivLE S c (A >>= f') (A >>= f) := by
  intro K h g
  rw [LawfulMonad.bind_assoc, LawfulMonad.bind_assoc]
  exact failFrom_bind_le_const (fun a h g ↦ hf a K h g) A h g

/-- Differences add along a sequence. -/
theorem DivLE.bind {α β : Type} {c d : ℝ≥0∞} {X' X : VerifierProgram α}
    {f' f : α → VerifierProgram β} (hX : DivLE S c X' X) (hf : ∀ a, DivLE S d (f' a) (f a)) :
    DivLE S (c + d) (X' >>= f') (X >>= f) := by
  intro K h g
  rw [LawfulMonad.bind_assoc, LawfulMonad.bind_assoc]
  calc S.failFrom (X' >>= fun a ↦ f' a >>= K) h g
      ≤ S.failFrom (X >>= fun a ↦ f' a >>= K) h g + c := hX _ h g
    _ ≤ S.failFrom (X >>= fun a ↦ f a >>= K) h g + d + c := by
        gcongr
        exact failFrom_bind_le_const (fun a h g ↦ hf a K h g) X h g
    _ = _ := by ring

theorem DivLE.mono {α : Type} {c d : ℝ≥0∞} {X' X : VerifierProgram α} (h : DivLE S c X' X)
    (hcd : c ≤ d) : DivLE S d X' X :=
  fun K h' g ↦ (h K h' g).trans (add_le_add le_rfl hcd)


/-- A double average of a list sum, term by term. -/
theorem avgE_avgE_list_le {X : Type} (g : X → E → E → ℝ≥0∞) (c : ℝ≥0∞) :
    ∀ L : List X, (∀ x ∈ L, avgE (fun a ↦ avgE fun b ↦ g x a b) ≤ c) →
      avgE (fun a ↦ avgE fun b ↦ (L.map fun x ↦ g x a b).sum) ≤ L.length * c
  | [], _ => by
    have e : avgE (fun a ↦ avgE fun b ↦ (([] : List X).map fun x ↦ g x a b).sum) = 0 := by
      have := congrArg avgE (funext fun _ : E ↦ avgE_const (0 : ℝ≥0∞))
      exact this.trans (avgE_const 0)
    rw [e]
    exact bot_le
  | x :: L, hL => by
    have e : avgE (fun a ↦ avgE fun b ↦ ((x :: L).map fun x ↦ g x a b).sum) =
        avgE (fun a ↦ avgE fun b ↦ g x a b) +
          avgE (fun a ↦ avgE fun b ↦ (L.map fun x ↦ g x a b).sum) := by
      rw [← avgE_add]
      exact congrArg avgE (funext fun a ↦ avgE_add (g x a) fun b ↦ (L.map fun x ↦ g x a b).sum)
    rw [e, List.length_cons, Nat.cast_succ, add_one_mul, add_comm]
    exact add_le_add (avgE_avgE_list_le g c L fun y hy ↦ hL y (List.mem_cons_of_mem x hy))
      (hL x List.mem_cons_self)

end Strategy

end
end LeanVM.Protocol.Compile
