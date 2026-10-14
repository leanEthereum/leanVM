import Whir.PCSBCSCallerParserPolynomialBound

/-! Work and actual returned-point cardinality for the counted, factored source
GKR interpreter. Bounds include rejection and every visited nested round. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace Whir.PCSBCSCallerParserCost
open Concrete WHIRCallerClaims

private theorem tick_result {A : Type} (n : Nat) (next : Unit → Parser A)
    (tokens : List CallerToken) :
    ((tick n >>= next) tokens).result = (next () tokens).result := rfl

private theorem accepted_bind {A B : Type} (before : Parser A) (next : A → Parser B)
    (tokens rest : List CallerToken) (output : B)
    (accepted : ((before >>= next) tokens).result = some (output,rest)) :
    ∃ value middle, (before tokens).result = some (value,middle) ∧
      (next value middle).result = some (output,rest) :=
  (bind_success_iff before next tokens output rest).mp accepted

theorem gkrSeed_work_le (mu : Nat) (tokens : List CallerToken) :
    (gkrSeed mu tokens).work ≤ 47 := by
  unfold gkrSeed
  split
  · apply bind_work_le (readScalars 4) _ tokens 38 9 (readScalars_work_le 4 tokens)
    intro _ tail _
    apply bind_work_le drawScalar _ tail 4 5 (drawScalar_work_le tail)
    intro _ tail _
    apply bind_work_le drawScalar _ tail 4 1 (drawScalar_work_le tail)
    intro _ tail _
    rw [tick_bind_work]
    exact Nat.le_refl _
  · exact Nat.zero_le _

theorem gkrSeed_success_length (mu : Nat) (tokens : List CallerToken)
    (point : List E) (rest : List CallerToken)
    (accepted : (gkrSeed mu tokens).result = some (point,rest)) :
    point.length = mu%2 := by
  unfold gkrSeed at accepted
  split at accepted
  · next odd =>
    obtain ⟨_,middle,_,accepted⟩ := accepted_bind _ _ _ _ _ accepted
    obtain ⟨x,middle,_,accepted⟩ := accepted_bind _ _ _ _ _ accepted
    obtain ⟨_,middle,_,accepted⟩ := accepted_bind _ _ _ _ _ accepted
    simp only [tick_result,pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    simpa using odd.symm
  · next even =>
    change some ([],tokens) = some (point,rest) at accepted
    cases accepted
    have small := Nat.mod_lt mu (by decide : 0<2)
    simp only [List.length_nil]
    omega

private def gkrStep (_ : Nat) (point : List E) : Parser (ForInStep (List E)) := do
  let next ← gkrRound point
  pure (.yield next)

private theorem gkrStep_work_le (i : Nat) (point : List E) (tokens : List CallerToken) :
    (gkrStep i point tokens).work ≤ 47*point.length+93 := by
  unfold gkrStep
  simpa only [Nat.add_zero] using bind_work_le (gkrRound point) _ tokens
    (47*point.length+93) 0 (gkrRound_work_le point tokens)
    (by intro _ tail _; exact Nat.le_refl _)

private theorem gkrStep_success (i : Nat) (point : List E) (tokens rest : List CallerToken)
    (step : ForInStep (List E))
    (accepted : (gkrStep i point tokens).result = some (step,rest)) :
    ∃ next, step = .yield next ∧ next.length = point.length+2 := by
  unfold gkrStep at accepted
  obtain ⟨next,middle,roundRead,accepted⟩ := accepted_bind _ _ _ _ _ accepted
  have length := gkrRound_success_length point tokens next middle roundRead
  change some (.yield next,middle) = some (step,rest) at accepted
  cases accepted
  exact ⟨next,rfl,length⟩

private theorem gkrLoop_success_length (xs : List Nat) (initial final : List E)
    (tokens rest : List CallerToken)
    (accepted : (forIn xs initial gkrStep tokens).result = some (final,rest)) :
    final.length = initial.length+2*xs.length := by
  induction xs generalizing initial tokens with
  | nil =>
    simp only [List.forIn_nil] at accepted
    change some (initial,tokens) = some (final,rest) at accepted
    cases accepted
    simp
  | cons i xs ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨step,middle,first,accepted⟩ := accepted_bind _ _ _ _ _ accepted
    obtain ⟨next,rfl,growth⟩ := gkrStep_success i initial tokens middle step first
    have tail := ih next middle accepted
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

private theorem gkrLoop_work_le (n : Nat) (initial : List E) (tokens : List CallerToken)
    (seed : initial.length ≤ 1) :
    (forIn (List.range n) initial gkrStep tokens).work ≤ n*(47*(1+2*n)+93) := by
  have bound := forIn_growth_work_le (List.range n) initial gkrStep List.length 47 93 2
    (by intro i _ point ts; exact gkrStep_work_le i point ts)
    (by
      intro i _ point ts step rest accepted
      obtain ⟨next,rfl,growth⟩ := gkrStep_success i point ts rest step accepted
      simp only [iterationState]
      omega) tokens
  simp only [List.length_range] at bound
  exact bound.trans (Nat.mul_le_mul_left n (by omega))

/-- Unconditional work bound: failures retain only their executed prefix. -/
theorem gkrPoint_work_le (mu : Nat) (tokens : List CallerToken) :
    (gkrPoint mu tokens).work ≤ 94*mu^2+142*mu+62 := by
  have half := Nat.div_le_self mu 2
  have square := Nat.mul_self_le_mul_self half
  unfold gkrPoint
  apply Nat.le_trans
  · apply bind_work_le
    · exact readScalar_work_le _
    · intro _ tail _
      apply bind_work_le
      · exact drawScalar_work_le _
      · intro _ tail _
        apply bind_work_le
        · exact Nat.le_refl _
        · intro _ tail _
          apply bind_work_le
          · exact gkrSeed_work_le _ _
          · intro seed tail parsed
            have length := gkrSeed_success_length mu _ seed _ parsed
            have small := Nat.mod_lt mu (by decide : 0<2)
            apply bind_work_le
            · exact Nat.le_refl _
            · intro _ tail _
              apply bind_work_le
              · exact gkrLoop_work_le (mu/2) seed tail (by omega)
              · intro _ tail _
                rw [tick_bind_work]
                exact Nat.le_refl _
  · nlinarith

/-- Exact length comes from the visited radix-four rounds and parity seed. -/
theorem gkrPoint_success_length (mu : Nat) (tokens : List CallerToken)
    (point : List E) (rest : List CallerToken)
    (accepted : (gkrPoint mu tokens).result = some (point,rest)) :
    point.length = mu := by
  unfold gkrPoint at accepted
  obtain ⟨_,middle,_,accepted⟩ := accepted_bind _ _ _ _ _ accepted
  obtain ⟨_,middle,_,accepted⟩ := accepted_bind _ _ _ _ _ accepted
  simp only [tick_result] at accepted
  obtain ⟨seed,middle,seedRead,accepted⟩ := accepted_bind _ _ _ _ _ accepted
  have seedLength := gkrSeed_success_length mu _ seed _ seedRead
  simp only [tick_result] at accepted
  obtain ⟨final,middle,loopRead,accepted⟩ := accepted_bind _ _ _ _ _ accepted
  have finalLength := gkrLoop_success_length (List.range (mu/2)) seed final _ _ loopRead
  simp only [tick_result,pure,Option.some.injEq,Prod.mk.injEq] at accepted
  rcases accepted with ⟨rfl,rfl⟩
  simp only [List.length_range] at finalLength
  omega

#print axioms gkrSeed_work_le
#print axioms gkrSeed_success_length
#print axioms gkrPoint_work_le
#print axioms gkrPoint_success_length
end Whir.PCSBCSCallerParserCost
