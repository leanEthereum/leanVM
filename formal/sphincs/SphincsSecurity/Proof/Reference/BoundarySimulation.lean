import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.FixedHashBoundary
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_writer_compose {ι₁ ι₂ α ω : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m] [Monoid ω]
    (first : QueryImpl spec₁ (WriterT ω (OracleComp spec₂))) (second : QueryImpl spec₂ m)
    (combined : QueryImpl spec₁ (WriterT ω m))
    (hquery : ∀ input, simulateQ second (first input).run = (combined input).run)
    (computation : OracleComp spec₁ α) :
    simulateQ second (simulateQ first computation).run = (simulateQ combined computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query, simulateQ_map, hquery]
      apply bind_congr
      rintro ⟨output, trace⟩
      rw [ih]

theorem simulateQ_writerAppend_compose {ι₁ ι₂ α ω : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m] [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (first : QueryImpl spec₁ (WriterT ω (OracleComp spec₂))) (second : QueryImpl spec₂ m)
    (combined : QueryImpl spec₁ (WriterT ω m))
    (hquery : ∀ input, simulateQ second (first input).run = (combined input).run)
    (computation : OracleComp spec₁ α) :
    simulateQ second (simulateQ first computation).run = (simulateQ combined computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query, simulateQ_map, hquery]
      apply bind_congr
      rintro ⟨output, trace⟩
      rw [ih]

noncomputable def boundaryComputation {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) : OracleComp OracleWorld (α × SigningBoundaryTrace) :=
  (simulateQ ((QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter)) computation).run

theorem simulateQ_boundaryComputation {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (parameter : PublicParameter) (impl : QueryImpl OracleWorld m) (computation : OracleComp OracleWorld α) :
    simulateQ impl (boundaryComputation parameter computation) =
      (simulateQ (impl.withTrace (signingBoundaryTrace parameter)) computation).run := by
  apply simulateQ_writer_compose
  intro input
  simp [QueryImpl.withTrace_apply]

theorem boundaryRun_fst_eq_boundaryComputation {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Prod.fst <$> boundaryRun parameter computation cache =
      (simulateQ romImpl (boundaryComputation parameter computation)).run' cache := by
  rw [simulateQ_boundaryComputation, StateT.run'_eq]
  rfl

theorem fixedBoundaryRun_eq_boundaryComputation {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld α) :
    fixedBoundaryRun parameter f computation =
      simulateQ (fixedHashWorld f) (boundaryComputation parameter computation) :=
  (simulateQ_boundaryComputation parameter (fixedHashWorld f) computation).symm

end SphincsSecurity.Concrete
