module

public import LeanDa.ForkCollapse

@[expose] public section

/-!
# Answering an extra oracle by a fixed function, through simulations

`col c` (`LeanDa.ForkCollapse`) answers the queries of an extra oracle `X` by a fixed function `c`
and forwards the others. A computation that uses `c` as a function is, when `c` is reached only
through queries, `col c` of a computation that queries `X`: this file moves `col c` through the
simulations that build Benedikt Wagner's reductions (a stateful simulation of the other oracles,
`run_simulateQ_col_ext`, `run_simulateQ_col_of`; a stateless one, `simulateQ_col_extI`), and
computations of the other oracles alone (`liftL`, `simulateQ_col_liftL`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA: it bounds the
collision terms of his reductions.
-/

set_option linter.unusedSectionVars false

open PFunctor OracleSpec OracleComp

namespace LeanDa.Fork

section Lift

variable {ι κ : Type} {Ψ : OracleSpec ι} {X : OracleSpec κ} {α β : Type}

/-- A computation of `Ψ` among the oracles `Ψ + X`. -/
def liftL (z : OracleComp Ψ α) : OracleComp (Ψ + X) α :=
  simulateQ (fun i ↦ FreeM.lift (P := (Ψ + X).toPFunctor) (.inl i)) z

theorem liftL_bind (z : OracleComp Ψ α) (f : α → OracleComp Ψ β) :
    liftL (X := X) (z >>= f) = liftL z >>= fun a ↦ liftL (f a) :=
  simulateQ_bind _ z f

theorem liftL_pure (a : α) : liftL (X := X) (pure a : OracleComp Ψ α) = pure a := rfl

theorem liftL_map (f : α → β) (z : OracleComp Ψ α) :
    liftL (X := X) (f <$> z) = f <$> liftL z :=
  simulateQ_map _ z f

/-- **A computation of the other oracles is unchanged.** -/
theorem simulateQ_col_liftL (c : (x : κ) → X.Range x) :
    (z : OracleComp Ψ α) → simulateQ (col c) (liftL (X := X) z) = z
  | .pure _ => rfl
  | .liftBind i k => by
    change FreeM.liftBind i (fun u ↦ simulateQ (col c) (liftL (k u))) = _
    congr 1
    funext u
    exact simulateQ_col_liftL c (k u)

theorem simulateQ_col_query_inl (c : (x : κ) → X.Range x) (i : ι) :
    simulateQ (col c) (FreeM.lift (P := (Ψ + X).toPFunctor) (.inl i)) =
      FreeM.lift (P := Ψ.toPFunctor) i := rfl

theorem simulateQ_col_query_inr (c : (x : κ) → X.Range x) (x : κ) :
    simulateQ (col (Ψ := Ψ) c) (FreeM.lift (P := (Ψ + X).toPFunctor) (.inr x)) = pure (c x) :=
  rfl

end Lift

section Stateful

variable {ι κ ιs : Type} {Ψ : OracleSpec ι} {X : OracleSpec κ} {spec : OracleSpec ιs}
  {σ α : Type}

/-- A simulation of `spec` into `Ψ`, extended by `X` passed through. -/
def extImpl (impl : QueryImpl spec (StateT σ (OracleComp Ψ))) :
    QueryImpl (spec + X) (StateT σ (OracleComp (Ψ + X)))
  | .inl t => StateT.mk fun s ↦ liftL ((impl t).run s)
  | .inr x => StateT.mk fun s ↦ (·, s) <$> FreeM.lift (P := (Ψ + X).toPFunctor) (.inr x)

/-- **A simulation of an adversary whose extra oracle is answered by `c`** is the extended
simulation of the adversary with the extra oracle, answered by `c`. -/
theorem run_simulateQ_col_ext (c : (x : κ) → X.Range x)
    (impl : QueryImpl spec (StateT σ (OracleComp Ψ))) (A : OracleComp (spec + X) α) (s : σ) :
    (simulateQ impl (simulateQ (col c) A)).run s =
      simulateQ (col c) ((simulateQ (extImpl impl) A).run s) := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with t | x
    · change ((impl t).run s >>= fun p ↦ (simulateQ impl (simulateQ (col c) (k p.1))).run p.2) =
        simulateQ (col c) (liftL ((impl t).run s) >>= fun p ↦
          (simulateQ (extImpl impl) (k p.1)).run p.2)
      rw [simulateQ_bind, simulateQ_col_liftL]
      congr 1
      funext p
      exact ih p.1 p.2
    · change (simulateQ impl (simulateQ (col c) (k (c x)))).run s =
        simulateQ (col c) (((·, s) <$> FreeM.lift (P := (Ψ + X).toPFunctor) (.inr x)) >>= fun p ↦
          (simulateQ (extImpl impl) (k p.1)).run p.2)
      rw [ih (c x) s]
      rfl

/-- **A simulation into `Ψ + X` answered by `c`** is a simulation into `Ψ`, when every step is. -/
theorem run_simulateQ_col_of (c : (x : κ) → X.Range x)
    (impl : QueryImpl spec (StateT σ (OracleComp Ψ)))
    (impl' : QueryImpl spec (StateT σ (OracleComp (Ψ + X))))
    (h : ∀ t s, simulateQ (col c) ((impl' t).run s) = (impl t).run s)
    (Z : OracleComp spec α) (s : σ) :
    simulateQ (col c) ((simulateQ impl' Z).run s) = (simulateQ impl Z).run s := by
  induction Z using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ (col c) ((impl' t).run s >>= fun p ↦ (simulateQ impl' (k p.1)).run p.2) =
      (impl t).run s >>= fun p ↦ (simulateQ impl (k p.1)).run p.2
    rw [simulateQ_bind, h]
    congr 1
    funext p
    exact ih p.1 p.2

end Stateful

section Stateless

variable {ι κ ιs : Type} {Ψ : OracleSpec ι} {X : OracleSpec κ} {spec : OracleSpec ιs} {α : Type}

/-- A stateless simulation of `spec` into `Ψ`, extended by `X` passed through. -/
def extI (I : QueryImpl spec (OracleComp Ψ)) : QueryImpl (spec + X) (OracleComp (Ψ + X))
  | .inl t => liftL (I t)
  | .inr x => FreeM.lift (P := (Ψ + X).toPFunctor) (.inr x)

/-- **A stateless simulation commutes with answering the extra oracle by `c`.** -/
theorem simulateQ_col_extI (c : (x : κ) → X.Range x) (I : QueryImpl spec (OracleComp Ψ))
    (A : OracleComp (spec + X) α) :
    simulateQ I (simulateQ (col c) A) = simulateQ (col c) (simulateQ (extI I) A) := by
  induction A using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with t | x
    · change (I t >>= fun u ↦ simulateQ I (simulateQ (col c) (k u))) =
        simulateQ (col c) (liftL (I t) >>= fun u ↦ simulateQ (extI I) (k u))
      rw [simulateQ_bind, simulateQ_col_liftL]
      congr 1
      funext u
      exact ih u
    · change simulateQ I (simulateQ (col c) (k (c x))) =
        simulateQ (col c) (FreeM.lift (P := (Ψ + X).toPFunctor) (.inr x) >>= fun u ↦
          simulateQ (extI I) (k u))
      rw [ih (c x)]
      rfl

end Stateless

end LeanDa.Fork
