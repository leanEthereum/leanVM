import SphincsFors.SecurityPrefixErasedKeygen

/-! The fixed-function cost world (`fixedWorldCost`: private draws are free, hash queries cost one
each), and how mapping the base monad commutes with query logging and with lifting. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete Completeness SeedModel PreparedScheme MaterialGameCoupling
open SeedCoupling
open SphincsBase.QueryCap

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000
attribute [local irreducible] PreparedScheme.sign PreparedScheme.keygen
  Randomized.sign digestAttemptLimit encodingAttemptLimit erasedMaterialSign
  preparedOracle answer

noncomputable def fixedWorldCost (f : QueryImpl HashSpec Id) :
    QueryImpl OracleWorld (AddWriterT Nat PMF) :=
  (fixedHashWorld f).withAddCost (fun | .inl _ => 0 | .inr _ => 1)

theorem map_logging_query {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (outer : QueryImpl target m) (inner : QueryImpl spec (OracleComp target)) (input : I) :
    (outer.writerTMapBase inner.withLogging) input =
      (QueryImpl.withLogging (spec := spec) (fun t => simulateQ outer (inner t))) input := by
  apply WriterT.ext
  simp only [QueryImpl.writerTMapBase, QueryImpl.run_withLogging_apply]
  change simulateQ outer (inner input >>= fun output =>
    pure (output, (show QueryLog spec from [⟨input, output⟩]))) = _
  simp only [simulateQ_bind, simulateQ_pure]

theorem map_lift_query {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {log : Type} [EmptyCollection log] [Append log]
    (outer : QueryImpl target m) (inner : QueryImpl spec (OracleComp target)) (input : I) :
    (outer.writerTMapBase (inner.liftTarget (WriterT log (OracleComp target)))) input =
      (liftM (simulateQ outer (inner input)) : WriterT log m (spec.Range input)) := by
  apply WriterT.ext
  change simulateQ outer ((fun output => (output, (∅ : log))) <$> inner input) = _
  rw [simulateQ_map]
  rfl

end SphincsFors.Security.Prefix
