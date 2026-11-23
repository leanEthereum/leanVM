module

public import XmssSecurity.Proof.EvalDistEq
public import XmssSecurity.Proof.Seeded.StoppedRun
public import XmssSecurity.Proof.ConsistentQueryBound

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open Common.RomTable

theorem hashQueryBound_after_preparation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound computation cache q) (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ romImpl preparation).run cache)) :
    HashQueryBound computation prepared.2 q := by
  intro result hresult
  apply hbound result
  rw [OracleComp.support_eq_of_evalDistEq
    (evalDist_presample_computation romImpl rfl (countHashQueries computation) preparation cache),
    mem_support_bind_iff]
  exact ⟨prepared, hprepared, hresult⟩

end XmssSecurity.Seeded
