import Whir.PCSBCSCallerParserCost

/-! Compositional work lemmas for the concrete counted caller interpreter.
Bounds concern the declared source-operation counter, including rejection,
not CPU cycles. Concrete nested-loop bounds must be discharged separately. -/
set_option autoImplicit false
namespace Whir.PCSBCSCallerParserCost
open Concrete WHIRCallerClaims

/-- A parser never invents token input. This is useful when bounding later
work by the public input size rather than an arbitrary callback result. -/
def Nonexpanding {A : Type} (parser : Parser A) : Prop :=
  ∀ tokens value rest, (parser tokens).result = some (value,rest) → rest.length ≤ tokens.length


theorem pure_nonexpanding {A : Type} (value : A) :
    Nonexpanding (Pure.pure value : Parser A) := by
  intro tokens output rest found
  have equal := Option.some.inj found
  cases equal
  exact Nat.le_refl _

theorem bind_nonexpanding {A B : Type} (parser : Parser A) (next : A → Parser B)
    (before : Nonexpanding parser) (after : ∀ value, Nonexpanding (next value)) :
    Nonexpanding (parser >>= next) := by
  intro tokens output tail found
  change (bind parser next tokens).result = some (output,tail) at found
  unfold bind at found
  cases result : (parser tokens).result with
  | none => simp only [result] at found; cases found
  | some pair =>
    rcases pair with ⟨value,rest⟩
    simp only [result] at found
    exact (after value rest output tail found).trans (before tokens value rest result)

#print axioms bind_work_le
#print axioms bind_nonexpanding
#print axioms readScalar_work_le
#print axioms drawScalar_work_le
#print axioms check_work_le
#print axioms nonce_work_le

theorem tick_bind_work {A : Type} (n : Nat) (parser : Parser A)
    (tokens : List CallerToken) :
    ((tick n >>= fun _ => parser) tokens).work = n + (parser tokens).work := rfl

theorem pure_work {A : Type} (value : A) (tokens : List CallerToken) :
    ((Pure.pure value : Parser A) tokens).work = 0 := rfl

/-- Both early termination and ordinary iteration retain the same invariant. -/
def iterationState {A : Type} : ForInStep A → A
  | .done value => value
  | .yield value => value

/-- Actual `forIn` work, including a failed body or early `done`, is bounded by
the visited-list capacity. The invariant bounds only source-created state. -/
theorem forIn_work_le {A B : Type} (xs : List A) (initial : B)
    (body : A → B → Parser (ForInStep B)) (invariant : B → Prop) (cap : Nat)
    (initialBound : invariant initial)
    (bodyBound : ∀ a ∈ xs, ∀ state tokens, invariant state → (body a state tokens).work ≤ cap)
    (preserves : ∀ a ∈ xs, ∀ state tokens step rest, invariant state →
      (body a state tokens).result = some (step,rest) → invariant (iterationState step))
    (tokens : List CallerToken) :
    ((forIn xs initial body : Parser B) tokens).work ≤ cap*xs.length := by
  induction xs generalizing initial tokens with
  | nil =>
    simp only [List.forIn_nil,pure_work,List.length_nil,Nat.mul_zero]
    exact Nat.le_refl _
  | cons a xs ih =>
    rw [List.forIn_cons]
    have before := bodyBound a (by simp) initial tokens initialBound
    have bounded := bind_work_le (body a initial)
      (fun step => match step with
        | .done state => (Pure.pure state : Parser B)
        | .yield state => forIn xs state body)
      tokens cap (cap*xs.length) before (by
        intro step rest parsed
        have retained := preserves a (by simp) initial tokens step rest initialBound parsed
        cases step with
        | done state => simp only [pure_work]; exact Nat.zero_le _
        | yield state =>
          apply ih state retained
          · intro next member value tail bound
            exact bodyBound next (by simp [member]) value tail bound
          · intro next member value tail outcome unused bound reached
            exact preserves next (by simp [member]) value tail outcome unused bound reached)
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    convert bounded using 1
    omega

#print axioms forIn_work_le

/-- A failed map still charges its executed stopping prefix. -/
theorem mapM_work_le {A B : Type} (xs : List A) (body : A → Parser B) (cap : Nat)
    (bodyBound : ∀ a ∈ xs, ∀ tokens, (body a tokens).work ≤ cap)
    (tokens : List CallerToken) :
    ((xs.mapM body : Parser (List B)) tokens).work ≤ cap*xs.length := by
  induction xs generalizing tokens with
  | nil =>
    simp only [List.mapM_nil,pure_work,List.length_nil,Nat.mul_zero]
    exact Nat.le_refl _
  | cons a xs ih =>
    rw [List.mapM_cons]
    have bounded := bind_work_le (body a)
      (fun value => xs.mapM body >>= fun values => Pure.pure (value::values))
      tokens cap (cap*xs.length) (bodyBound a (by simp) tokens) (by
        intro value rest parsed
        have tailBound := ih (fun next member tail => bodyBound next (by simp [member]) tail) rest
        have later := bind_work_le (xs.mapM body) (fun values => Pure.pure (value::values))
          rest (cap*xs.length) 0 tailBound (by
            intro values unused result
            simp only [pure_work]
            exact Nat.le_refl _)
        simpa only [Nat.add_zero] using later)
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

#print axioms mapM_work_le


/-- Affine work for a state that grows by at most `delta` per successful round.
A stopping or failing iteration pays only the executed prefix. -/
theorem forIn_growth_work_le {A B : Type} (xs : List A) (initial : B)
    (body : A → B → Parser (ForInStep B)) (size : B → Nat) (a b delta : Nat)
    (bodyBound : ∀ x ∈ xs, ∀ state tokens, (body x state tokens).work ≤ a*size state+b)
    (grows : ∀ x ∈ xs, ∀ state tokens step rest,
      (body x state tokens).result = some (step,rest) →
      size (iterationState step) ≤ size state+delta)
    (tokens : List CallerToken) :
    (forIn xs initial body tokens).work ≤
      xs.length*(a*(size initial+delta*xs.length)+b) := by
  induction xs generalizing initial tokens with
  | nil =>
    simp only [List.forIn_nil,List.length_nil,Nat.mul_zero,Nat.zero_mul,pure_work]
    exact Nat.le_refl _
  | cons x xs ih =>
    rw [List.forIn_cons]
    let cap := a*(size initial+delta*(xs.length+1))+b
    have before : (body x initial tokens).work ≤ cap := by
      apply (bodyBound x (by simp) initial tokens).trans
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left a (Nat.le_add_right _ _)
    have bounded := bind_work_le (body x initial)
      (fun step => match step with
        | .done state => Pure.pure state
        | .yield state => forIn xs state body)
      tokens cap (xs.length*cap) before (by
        intro step rest parsed
        cases step with
        | done state =>
          simp only [pure_work]
          exact Nat.zero_le _
        | yield state =>
          have next := grows x (by simp) initial tokens (.yield state) rest parsed
          have tailBound := ih state
            (fun y member value tail => bodyBound y (by simp [member]) value tail)
            (fun y member value tail outcome unused reached =>
              grows y (by simp [member]) value tail outcome unused reached) rest
          apply tailBound.trans
          apply Nat.mul_le_mul_left xs.length
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_left a
          simp only [iterationState] at next
          simp only [Nat.mul_add,Nat.mul_one]
          omega)
    simp only [List.length_cons]
    convert bounded using 1
    simp only [cap,Nat.add_mul,Nat.one_mul,Nat.add_comm]

#print axioms forIn_growth_work_le

/-- Successful monadic list traversal preserves its exact input cardinality. -/
theorem mapM_success_length {A B : Type} (xs : List A) (f : A → Parser B)
    (tokens : List CallerToken) (ys : List B) (rest : List CallerToken)
    (accepted : (xs.mapM f tokens).result = some (ys,rest)) :
    ys.length = xs.length := by
  induction xs generalizing tokens ys rest with
  | nil =>
    simp only [List.mapM_nil] at accepted
    change some ([],tokens) = some (ys,rest) at accepted
    cases accepted
    rfl
  | cons x xs ih =>
    simp only [List.mapM_cons] at accepted
    change (bind (f x) (fun y => bind (xs.mapM f) (fun tail => pure (y::tail)))
      tokens).result = some (ys,rest) at accepted
    cases first : (f x tokens).result with
    | none => simp [bind,first] at accepted
    | some pair =>
      rcases pair with ⟨y,middle⟩
      cases last : (xs.mapM f middle).result with
      | none => simp [bind,first,last] at accepted
      | some pair =>
        rcases pair with ⟨tail,remaining⟩
        have tailLength := ih middle tail remaining last
        simp only [bind,first,last,pure,Option.some.injEq,Prod.mk.injEq] at accepted
        rcases accepted with ⟨rfl,rfl⟩
        simpa using congrArg Nat.succ tailLength

#print axioms mapM_success_length

/-- The literal nested GKR body has linear work in its entering point. -/
theorem gkrRound_work_le (point : List E) (tokens : List CallerToken) :
    (gkrRound point tokens).work ≤ 47*point.length+93 := by
  let entry : Nat → Parser E := fun _ => do
    tick 2
    let _ ← readScalars 4
    drawScalar
  have entryBound (i : Nat) (ts : List CallerToken) : (entry i ts).work ≤ 44 := by
    dsimp only [entry]
    rw [tick_bind_work]
    have bound := bind_work_le (readScalars 4) (fun _ => drawScalar) ts 38 4
      (readScalars_work_le 4 ts) (by intro values rest parsed; exact drawScalar_work_le rest)
    omega
  have roundsBound (ts : List CallerToken) :
      ((List.range point.length).mapM entry ts).work ≤ 44*point.length := by
    simpa using mapM_work_le (List.range point.length) entry 44
      (fun i _ rest => entryBound i rest) ts
  let finish : List E → Parser (List E) := fun rounds => do
    let _ ← readScalars 8
    let low ← drawScalar
    let high ← drawScalar
    let _ ← drawScalar
    tick 3
    pure (low::high::rounds)
  have finishBound (rounds : List E) (ts : List CallerToken) : (finish rounds ts).work ≤ 89 := by
    dsimp only [finish]
    apply bind_work_le (readScalars 8) _ ts 74 15 (readScalars_work_le 8 ts)
    intro values rest parsed
    apply bind_work_le drawScalar _ rest 4 11 (drawScalar_work_le rest)
    intro low rest parsed
    apply bind_work_le drawScalar _ rest 4 7 (drawScalar_work_le rest)
    intro high rest parsed
    apply bind_work_le drawScalar _ rest 4 3 (drawScalar_work_le rest)
    intro unused rest parsed
    rw [tick_bind_work]
    exact Nat.le_refl _
  have mainBound := bind_work_le ((List.range point.length).mapM entry) finish tokens
    (44*point.length) 89 (roundsBound tokens) (by
      intro rounds rest parsed
      exact finishBound rounds rest)
  change (bind ((List.range point.length).mapM entry) finish tokens).work ≤
    44*point.length+89 at mainBound
  unfold gkrRound
  rw [tick_bind_work]
  change lengthCost point+2*point.length+3+
    (bind ((List.range point.length).mapM entry) finish tokens).work ≤ _
  unfold lengthCost
  omega

#print axioms gkrRound_work_le
/-- Literal successful continuation decomposition, including its cursor. -/
theorem bind_success_iff {A B : Type} (p : Parser A) (f : A → Parser B)
    (tokens : List CallerToken) (value : B) (rest : List CallerToken) :
    (bind p f tokens).result = some (value,rest) ↔
      ∃ before middle, (p tokens).result = some (before,middle) ∧
        (f before middle).result = some (value,rest) := by
  cases hp : (p tokens).result with
  | none => simp [bind,hp]
  | some pair =>
    rcases pair with ⟨before,middle⟩
    simp [bind,hp]

theorem gkrRound_success_length (point : List E) (tokens : List CallerToken)
    (value : List E) (rest : List CallerToken)
    (accepted : (gkrRound point tokens).result = some (value,rest)) :
    value.length = point.length+2 := by
  unfold gkrRound at accepted
  change (bind (tick _) _ tokens).result = some (value,rest) at accepted
  obtain ⟨tickValue,first,started,accepted⟩ := bind_success_iff _ _ _ _ _ |>.mp accepted
  change some ((),tokens) = some (tickValue,first) at started
  cases started
  obtain ⟨rounds,middle,mapped,accepted⟩ := bind_success_iff _ _ _ _ _ |>.mp accepted
  have length := mapM_success_length _ _ _ rounds middle mapped
  obtain ⟨unused,next,read,accepted⟩ := bind_success_iff _ _ _ _ _ |>.mp accepted
  obtain ⟨low,next,drawn,accepted⟩ := bind_success_iff _ _ _ _ _ |>.mp accepted
  obtain ⟨high,next,drawn,accepted⟩ := bind_success_iff _ _ _ _ _ |>.mp accepted
  obtain ⟨unused,next,drawn,accepted⟩ := bind_success_iff _ _ _ _ _ |>.mp accepted
  obtain ⟨tickValue,last,ticked,accepted⟩ := bind_success_iff _ _ _ _ _ |>.mp accepted
  change some ((),next) = some (tickValue,last) at ticked
  cases ticked
  change some (low::high::rounds,next) = some (value,rest) at accepted
  cases accepted
  simpa using congrArg (fun n : Nat => n+2) length

#print axioms gkrRound_success_length


#print axioms readScalars_work_le
#print axioms drawScalars_work_le
end Whir.PCSBCSCallerParserCost
