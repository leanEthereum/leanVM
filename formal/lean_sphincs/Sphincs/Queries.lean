module

public import FORS.CrateShort
public import Common.StaticSwap

@[expose] public section

/-!
# The honest algorithms query a finite part of the random oracle

The honest part of the random oracle that `Common.SufCma.StaticSwap` samples in advance: the
inputs of at most `FORS.Security.Short.bound = 2084` bytes (`Honest`, a finite set). Key generation
and the signer of FORS's model (`FORS.Seeded.keygen`, `FORS.Seeded.sign`) and of the crate
(`FORS.Crate.keygen`, `FORS.Crate.sign`) only query it (`queriesIn_*`), from FORS's short-input
facts (`FORS.Security.Short.Only`; the crate's in `FORS/CrateShort.lean`).
-/

open OracleComp OracleSpec Common.SufCma

namespace Sphincs.Queries

/-- The honest inputs: at most `2084` bytes. -/
def Honest (input : List UInt8) : Prop := input.length ≤ FORS.Security.Short.bound

instance : DecidablePred Honest := fun input =>
  inferInstanceAs (Decidable (input.length ≤ FORS.Security.Short.bound))

noncomputable instance : Fintype {input // Honest input} :=
  Set.Finite.fintype (s := {input : List UInt8 | input.length ≤ FORS.Security.Short.bound})
    (List.finite_length_le UInt8 _)

variable [FORS.Params]

/-- A computation of FORS's hash monad whose queries are short only queries honest inputs. -/
theorem queriesIn_of_only {α : Type} (X : OracleComp FORS.HashSpec α)
    (h : FORS.Security.Short.Only X) : QueriesIn Honest (X : OracleComp SchemeHashSpec α) := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
      rw [FORS.Security.Short.Only, isQueryBoundP_query_bind_iff] at h
      have hs : FORS.Security.Short.IsShort t := by
        rcases h.1 with h1 | h1
        · exact not_not.mp h1
        · omega
      refine ⟨hs, fun u => ih u ?_⟩
      have := h.2 u
      rwa [ite_eq_right (not_not.mpr hs)] at this

theorem queriesIn_seededKeygen (seed : FORS.MasterSeed) :
    QueriesIn Honest ((FORS.Seeded.keygen seed : OracleComp FORS.HashSpec _) :
      OracleComp SchemeHashSpec _) :=
  queriesIn_of_only _ (FORS.Security.Short.Seeded.Only.keygen seed)

theorem queriesIn_seededSign (sk : FORS.Seeded.SecretKey) (message : FORS.Message) :
    QueriesIn Honest ((FORS.Seeded.sign sk message : OracleComp FORS.HashSpec _) :
      OracleComp SchemeHashSpec _) :=
  queriesIn_of_only _ (FORS.Security.Det.Only.seededSign sk message)

theorem queriesIn_crateKeygen (seed : FORS.MasterSeed) :
    QueriesIn Honest ((FORS.Crate.keygen seed : OracleComp FORS.HashSpec _) :
      OracleComp SchemeHashSpec _) :=
  queriesIn_of_only _ (FORS.Crate.Only.keygen seed)

theorem queriesIn_crateSign (seed : FORS.MasterSeed) (message : FORS.Message) :
    QueriesIn Honest ((FORS.Crate.sign seed message : OracleComp FORS.HashSpec _) :
      OracleComp SchemeHashSpec _) :=
  queriesIn_of_only _ (FORS.Crate.Only.sign seed message)

end Sphincs.Queries
