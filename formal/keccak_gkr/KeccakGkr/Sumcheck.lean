import KeccakGkr.Phase
import KeccakGkr.Prob

/-!
# Sumcheck

The verifier holds a context `c` and a target `t`, claimed to be `∑ x ∈ {0,1}ⁿ, f c x` for a
summand `f c` of degree at most `d` in each variable. Each round the prover sends a polynomial
of degree at most `d` in the first remaining variable; the verifier checks that its values at
`0` and `1` add up to the target, samples the variable, and takes the polynomial's value there
as the next target. After `n` rounds the verifier holds the point and a value claimed to be the
summand there.

The protocols of the paper send a round polynomial in a compressed form (two or three field
elements, the rest following from the target and the equality factor); any such message stands
for a polynomial passing the check, so its soundness is that of this protocol.
-/

open Polynomial OracleComp
open scoped ENNReal

namespace KeccakGkr

variable {E : Type} [Field E]

/-- A round message: a polynomial of degree at most `d`. -/
abbrev RoundPoly (E : Type) [Field E] (d : ℕ) := {p : E[X] // p.natDegree ≤ d}

/-- A sumcheck summand for every context. -/
structure Summand (E : Type) [Field E] (C : Type) (n d : ℕ) where
  f : C → (Fin n → E) → E
  deg : ∀ c, IndivDeg d (f c)

namespace Summand

variable {C : Type} {n d : ℕ}

/-- The summand left once the first variable is fixed. -/
def cons (S : Summand E C (n + 1) d) : Summand E (C × E) n d where
  f cr x := S.f cr.1 (Fin.cons cr.2 x)
  deg cr := (S.deg cr.1).cons cr.2

/-- The sum the verifier's target claims. -/
def total (S : Summand E C n d) (c : C) : E := ∑ x : Cube n, S.f c (toPt x)

/-- The honest round polynomial: the summand with all but its first variable summed out. -/
noncomputable def roundPoly (S : Summand E C (n + 1) d) (c : C) : RoundPoly E d :=
  ⟨Classical.choose (S.deg c).round, (Classical.choose_spec (S.deg c).round).1⟩

theorem roundPoly_eval (S : Summand E C (n + 1) d) (c : C) (t : E) :
    (S.roundPoly c).1.eval t = S.cons.total (c, t) :=
  ((Classical.choose_spec (S.deg c).round).2 t).symm

theorem total_eq_roundPoly (S : Summand E C (n + 1) d) (c : C) :
    S.total c = (S.roundPoly c).1.eval 0 + (S.roundPoly c).1.eval 1 := by
  rw [roundPoly_eval, roundPoly_eval, total, sum_cube_cons, Fintype.sum_bool]
  simp only [toPt_cons, bit_true, bit_false, cons, Summand.total]
  ring

/-- The input is true, and the context satisfies `P`. -/
def True' (S : Summand E C n d) (P : C → Prop) : Option (C × E) → Prop
  | none => False
  | some ct => P ct.1 ∧ ct.2 = S.total ct.1

/-- The output is accepted and true, the value being the summand at the point, and the context
satisfies `P`. -/
def Good (S : Summand E C n d) (P : C → Prop) : Option (C × (Fin n → E) × E) → Prop
  | none => False
  | some cpv => P cpv.1 ∧ cpv.2.2 = S.f cpv.1 cpv.2.1

end Summand

open Summand

variable [Fintype E] [DecidableEq E] [SampleableType E] {C : Type} {d : ℕ}

/-- The verifier's check of a round polynomial against the target. -/
def roundCheck (st : Option (C × E)) (p : RoundPoly E d) : Option (C × RoundPoly E d) :=
  st.bind fun ct => if p.1.eval 0 + p.1.eval 1 = ct.2 then some (ct.1, p) else none

/-- One round: receive the polynomial, check it, sample the variable. -/
noncomputable def round {n : ℕ} (S : Summand E C (n + 1) d) :
    Phase (Option (C × E)) (Option ((C × E) × E)) :=
  (Phase.receive (RoundPoly E d) roundCheck fun st =>
      match st with
      | some ct => S.roundPoly ct.1
      | none => ⟨0, by simp⟩).comp
    (Phase.sample E fun st r => st.map fun cp => ((cp.1, r), cp.2.1.eval r))

/-- The sumcheck over `n` variables, binding the first variable first. -/
noncomputable def sumcheck : (n : ℕ) → {C : Type} → Summand E C n d →
    Phase (Option (C × E)) (Option (C × (Fin n → E) × E))
  | 0, _, _ => Phase.compute fun st => st.map fun ct => (ct.1, Fin.elim0, ct.2)
  | n + 1, _, S => (round S).comp ((sumcheck n S.cons).map fun st =>
      st.map fun cpv => (cpv.1.1, Fin.cons cpv.1.2 cpv.2.1, cpv.2.2))

/-- After the round message: it is accepted and the true round polynomial. -/
def RoundGood {n : ℕ} (S : Summand E C (n + 1) d) (P : C → Prop) :
    Option (C × RoundPoly E d) → Prop
  | none => False
  | some cp => P cp.1 ∧ cp.2 = S.roundPoly cp.1

theorem round_sound {n : ℕ} (S : Summand E C (n + 1) d) (P : C → Prop) :
    (round S).Sound (fun st => ¬ S.True' P st) (S.cons.True' fun cr => P cr.1)
      (d / Fintype.card E) := by
  refine (Phase.Sound.comp (Mid := RoundGood S P) ?_ ?_).mono (fun _ h => h) (fun _ h => h)
    (by rw [zero_add])
  · refine Phase.receive_sound fun st hst p => ?_
    rcases st with _ | ⟨c, t⟩
    · simp [roundCheck, RoundGood]
    · simp only [roundCheck, Option.bind_some]
      split_ifs with hc
      · rintro ⟨hP, hp⟩
        apply hst
        refine ⟨hP, ?_⟩
        simp only at hc hp hP ⊢
        rw [← hc, hp, total_eq_roundPoly]
      · simp [RoundGood]
  · refine Phase.sample_sound fun st hst => ?_
    rcases st with _ | ⟨c, p⟩
    · simp [True']
    · by_cases hP : P c
      · have hne : p ≠ S.roundPoly c := fun h => hst ⟨hP, h⟩
        have h := prob_eval_eq_le (fun h => hne (Subtype.ext h)) p.2 (S.roundPoly c).2
        refine le_of_eq_of_le (prEvent_congr _ _ _ fun r => ?_) h
        simp [True', roundPoly_eval, hP]
      · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun r h => ?_) zero_le
        simp only [Option.map_some, True'] at h
        exact hP h.1

omit [Fintype E] in
theorem round_complete {n : ℕ} (S : Summand E C (n + 1) d) (P : C → Prop) :
    (round S).Complete (S.True' P) (S.cons.True' fun cr => P cr.1) := by
  refine Phase.Complete.comp (Mid := RoundGood S P) ?_ ?_
  · refine Phase.receive_complete fun st hst => ?_
    rcases st with _ | ⟨c, t⟩
    · exact hst.elim
    · obtain ⟨hP, hst⟩ := hst
      simp only at hst
      simp [roundCheck, RoundGood, hst, total_eq_roundPoly, hP]
  · refine Phase.sample_complete fun st hst r => ?_
    rcases st with _ | ⟨c, p⟩
    · exact hst.elim
    · obtain ⟨hP, hst⟩ := hst
      simp only at hP hst
      simp [True', hst, roundPoly_eval, hP]

theorem sumcheck_sound : (n : ℕ) → {C : Type} → (S : Summand E C n d) → (P : C → Prop) →
    (sumcheck n S).Sound (fun st => ¬ S.True' P st) (S.Good P) (n * d / Fintype.card E)
  | 0, _, S, P => by
    refine (Phase.compute_sound fun st hst => ?_).mono (fun _ h => h) (fun _ h => h) zero_le
    rcases st with _ | ⟨c, t⟩
    · simp [Good]
    · simp only [True', total, Finset.univ_unique, Finset.sum_singleton] at hst
      simp only [Option.map_some, Good]
      rintro ⟨hP, h⟩
      apply hst
      refine ⟨hP, ?_⟩
      rw [h]
      exact congrArg _ (Subsingleton.elim _ _)
  | n + 1, _, S, P => by
    refine ((round_sound S P).comp (ε₂ := n * d / Fintype.card E) (Phase.Sound.map ?_)).mono
      (fun _ h => h) (fun _ h => h) ?_
    · refine (sumcheck_sound n S.cons fun cr => P cr.1).mono (fun st h => ?_)
        (fun st h => ?_) le_rfl
      · exact h
      · rcases st with _ | ⟨⟨c, r⟩, pt, v⟩
        · exact h
        · exact h
    · rw [Nat.cast_succ, add_mul, one_mul, ENNReal.add_div, add_comm]

omit [Fintype E] in
theorem sumcheck_complete : (n : ℕ) → {C : Type} → (S : Summand E C n d) → (P : C → Prop) →
    (sumcheck n S).Complete (S.True' P) (S.Good P)
  | 0, _, S, P => by
    refine Phase.compute_complete fun st hst => ?_
    rcases st with _ | ⟨c, t⟩
    · exact hst.elim
    · obtain ⟨hP, hst⟩ := hst
      simp only [total, Finset.univ_unique, Finset.sum_singleton] at hst
      simp only [Option.map_some, Good]
      refine ⟨hP, ?_⟩
      rw [hst]
      exact congrArg _ (Subsingleton.elim _ _)
  | n + 1, _, S, P => by
    refine (round_complete S P).comp (Phase.Complete.map ?_)
    refine (sumcheck_complete n S.cons fun cr => P cr.1).mono (fun _ h => h) (fun st h => ?_)
    rcases st with _ | ⟨⟨c, r⟩, pt, v⟩
    · exact h
    · exact h

end KeccakGkr
