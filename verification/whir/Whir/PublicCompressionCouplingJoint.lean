import Whir.PublicCompressionCoupling

/-! A finite shared-answer coupling of actual globally memoized adaptive
programs. Each draw here is an independent uniform digest, not a primitive
oracle coordinate. Both marginals are the existing exact lazy-sampling
experiments. Cached requests consume no fresh randomness. -/
namespace Whir.PublicCompressionCouplingJoint
open FiatShamirGame TypedOracleCompiler TypedFiatShamirGame

abbrev Cache (K : Type) := K → Option Digest32
abbrev Draws (R : Type) (n : Nat) := Sampling Unit (fun _ => Digest32) R n
abbrev Computation (K R : Type) (n : Nat) :=
  Sampling K (fun _ => Digest32) R n

variable {A B R S : Type} [DecidableEq A] [DecidableEq B]

noncomputable def joint {n m : Nat} (p : Computation A R n) (pc : Cache A)
    (q : Computation B S m) (qc : Cache B) : Draws ((R × Cache A) × (S × Cache B)) (n+m) :=
  match p,q with
  | .ret r,.ret s => .ret ((r,pc),(s,qc))
  | @Sampling.draw _ _ _ i a nextp,.ret s =>
    match pc a with
    | some answer => Sampling.pad (by omega) (joint (nextp answer) pc (.ret (n:=m) s) qc)
    | none => Sampling.pad (n:=i+m+1) (m:=i+1+m) (by omega)
      (.draw () (fun answer => joint (nextp answer) (put pc a answer) (.ret (n:=m) s) qc))
  | .ret r,@Sampling.draw _ _ _ j b nextq =>
    match qc b with
    | some answer => Sampling.pad (by omega) (joint (.ret (n:=n) r) pc (nextq answer) qc)
    | none => Sampling.pad (n:=n+j+1) (m:=n+(j+1)) (by omega)
      (.draw () (fun answer => joint (.ret (n:=n) r) pc (nextq answer) (put qc b answer)))
  | @Sampling.draw _ _ _ i a nextp,@Sampling.draw _ _ _ j b nextq =>
    match pc a with
    | some answer => Sampling.pad (by omega)
      (joint (nextp answer) pc (.draw b nextq) qc)
    | none => match qc b with
      | some answer => Sampling.pad (by omega)
        (joint (.draw a nextp) pc (nextq answer) qc)
      | none => Sampling.pad (n:=i+j+1) (m:=i+1+(j+1)) (by omega)
        (.draw () (fun answer =>
          joint (nextp answer) (put pc a answer) (nextq answer) (put qc b answer)))
termination_by n+m

theorem joint_first {n m : Nat} (p : Computation A R n) (pc : Cache A)
    (q : Computation B S m) (qc : Cache B) (payoff : R × Cache A → ℚ) :
    Sampling.expectation (fun pair => payoff pair.1) (joint p pc q qc) =
      Sampling.expectation payoff (RawOracleCoupling.memo p pc) := by
  suffices aux : ∀ size n m, n+m=size →
      ∀ (p : Computation A R n) (pc : Cache A) (q : Computation B S m) (qc : Cache B),
      Sampling.expectation (fun pair => payoff pair.1) (joint p pc q qc) =
        Sampling.expectation payoff (RawOracleCoupling.memo p pc) by
    exact aux (n+m) n m rfl p pc q qc
  intro size
  induction size using Nat.strong_induction_on with
  | h size ih =>
    intro n m h p pc q qc
    cases p with
    | ret r =>
      cases q with
      | ret s => simp only [joint,RawOracleCoupling.memo,Sampling.expectation]
      | @draw j b nextq =>
        cases hit : qc b with
        | some answer =>
          simp only [joint,hit,Sampling.expectation_pad]
          exact ih (n+j) (by omega) _ _ rfl _ _ _ _
        | none =>
          simp only [joint,hit,Sampling.expectation_pad,Sampling.expectation]
          have eq (answer : Digest32) :=
            ih (n+j) (by omega) n j rfl (.ret r) pc (nextq answer) (put qc b answer)
          simp only [eq,RawOracleCoupling.memo,Sampling.expectation]
          exact average_const _
    | @draw i a nextp =>
      cases q with
      | ret s =>
        cases hit : pc a with
        | some answer =>
          simp only [joint,RawOracleCoupling.memo,hit,Sampling.expectation_pad]
          exact ih (i+m) (by omega) _ _ rfl _ _ _ _
        | none =>
          simp only [joint,RawOracleCoupling.memo,hit,Sampling.expectation_pad,Sampling.expectation]
          apply congrArg average
          funext answer
          exact ih (i+m) (by omega) _ _ rfl _ _ _ _
      | @draw j b nextq =>
        cases hp : pc a with
        | some answer =>
          simp only [joint,RawOracleCoupling.memo,hp,Sampling.expectation_pad]
          exact ih (i+(j+1)) (by omega) _ _ rfl _ _ _ _
        | none =>
          cases hq : qc b with
          | some answer =>
            simp only [joint,hp,hq,Sampling.expectation_pad]
            exact ih (i+1+j) (by omega) _ _ rfl _ _ _ _
          | none =>
            simp only [joint,RawOracleCoupling.memo,hp,hq,Sampling.expectation_pad,Sampling.expectation]
            apply congrArg average
            funext answer
            exact ih (i+j) (by omega) _ _ rfl _ _ _ _

theorem joint_second {n m : Nat} (p : Computation A R n) (pc : Cache A)
    (q : Computation B S m) (qc : Cache B) (payoff : S × Cache B → ℚ) :
    Sampling.expectation (fun pair => payoff pair.2) (joint p pc q qc) =
      Sampling.expectation payoff (RawOracleCoupling.memo q qc) := by
  suffices aux : ∀ size n m, n+m=size →
      ∀ (p : Computation A R n) (pc : Cache A) (q : Computation B S m) (qc : Cache B),
      Sampling.expectation (fun pair => payoff pair.2) (joint p pc q qc) =
        Sampling.expectation payoff (RawOracleCoupling.memo q qc) by
    exact aux (n+m) n m rfl p pc q qc
  intro size
  induction size using Nat.strong_induction_on with
  | h size ih =>
    intro n m h p pc q qc
    cases p with
    | ret r =>
      cases q with
      | ret s => simp only [joint,RawOracleCoupling.memo,Sampling.expectation]
      | @draw j b nextq =>
        cases hit : qc b with
        | some answer =>
          simp only [joint,RawOracleCoupling.memo,hit,Sampling.expectation_pad]
          exact ih (n+j) (by omega) _ _ rfl _ _ _ _
        | none =>
          simp only [joint,RawOracleCoupling.memo,hit,Sampling.expectation_pad,Sampling.expectation]
          apply congrArg average
          funext answer
          exact ih (n+j) (by omega) _ _ rfl _ _ _ _
    | @draw i a nextp =>
      cases q with
      | ret s =>
        cases hit : pc a with
        | some answer =>
          simp only [joint,hit,Sampling.expectation_pad]
          exact ih (i+m) (by omega) _ _ rfl _ _ _ _
        | none =>
          simp only [joint,hit,Sampling.expectation_pad,Sampling.expectation]
          have eq (answer : Digest32) :=
            ih (i+m) (by omega) i m rfl (nextp answer) (put pc a answer) (.ret s) qc
          simp only [eq,RawOracleCoupling.memo,Sampling.expectation]
          exact average_const _
      | @draw j b nextq =>
        cases hp : pc a with
        | some answer =>
          simp only [joint,hp,Sampling.expectation_pad]
          exact ih (i+(j+1)) (by omega) _ _ rfl _ _ _ _
        | none =>
          cases hq : qc b with
          | some answer =>
            simp only [joint,RawOracleCoupling.memo,hp,hq,Sampling.expectation_pad]
            exact ih (i+1+j) (by omega) _ _ rfl _ _ _ _
          | none =>
            simp only [joint,RawOracleCoupling.memo,hp,hq,Sampling.expectation_pad,Sampling.expectation]
            apply congrArg average
            funext answer
            exact ih (i+j) (by omega) _ _ rfl _ _ _ _

#print axioms joint_second
#print axioms joint_first
end Whir.PublicCompressionCouplingJoint
