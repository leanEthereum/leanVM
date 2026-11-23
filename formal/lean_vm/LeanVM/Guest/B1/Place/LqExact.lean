/-
  LeanVM.Guest.B1.Place.LqExact

  `level_queries` complete placed by a tree of exactly `lqN` words, at every entry of `lqTable`.
-/

module

public import LeanVM.Guest.B1.Place.LqProofP

/-!
# `level_queries`, by exactly `lqN` words

`lq_placedE`: `lq_placedEP` forgetting its pops, so `LqAtE`. `level_queries_completeAtB`: frames
below `2^32`, each entry of `lqTable` is `LqAtO` at every words bound of its trees (`lqAtO_of_E`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **`level_queries` at an entry, by exactly `lqN` words.** -/
theorem lq_placedE (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {name : String}
    {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hlq : FnIs name (osParams 6) (lqBody q base folds leaf d cd mu nhs hbits fin))
    (hoq : (lqOqN base folds leaf d cd mu nhs hbits fin,
      oqLoopOf (lqOqN base folds leaf d cd mu nhs hbits fin),
      oqShapeOf (lqOqN base folds leaf d cd mu nhs hbits fin)) ∈ openingQueriesLoops)
    (hQ : oqCount (Whir.lqOdd q base) (lqOqS base folds leaf d cd mu nhs hbits fin).base
      (lqIters q base) = q)
    (hN : lqIters q base + 1 < ordG)
    (hodd : Whir.lqOdd q base ≤ (lqOqS base folds leaf d cd mu nhs hbits fin).base)
    (hcd1 : 1 ≤ cd) (hcd8 : cd ≤ 8)
    (hK : osKindOf ("verify_merkle_cap__L" ++ natStr cd) = some (.cap cd))
    (hpw : digitsVal (osPowDigits q) 1 = q) :
    LqAtE fs cert κ name q base folds leaf d cd mu nhs hbits fin :=
  (lq_placedEP fs cert hlq hoq hQ hN hodd hcd1 hcd8 hK hpw).toE

/-- **`level_queries` within every words bound of its trees**, frames below `2^32`. -/
theorem level_queries_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (hfs : ∀ f, fs f < 2 ^ 32) :
    ∀ e ∈ lqTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
      Arm.LqAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
        e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 (some B) := by
  intro e he B hT
  obtain ⟨hoq, hQ, hN, hodd, hcd1, hcd8, hK, hpw⟩ := lqTable_facts e he
  exact lqAtO_of_E (lq_placedE fs cert (κ := κ) (lqTable_ok e he) (oq_mem_of_entry hoq) hQ hN hodd hcd1
    hcd8 hK hpw) hfs (lqTable_small e he) hT

end
end LeanVM.Guest.B1
