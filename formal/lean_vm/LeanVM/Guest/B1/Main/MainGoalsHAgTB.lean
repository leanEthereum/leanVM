/-
  LeanVM.Guest.B1.Main.MainGoalsHAgTB

  `main`'s honest `aggregate_claims` call, by a tree of honest shape (`aggHonest`), within its
  bound before the memory (`aggB`): `mainGoalAgT` (same proof) with `aggregate_claims_completeAtTB`.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHAg
public import LeanVM.Guest.B1.Main.AggAtTB
public import LeanVM.Guest.Batch.Node
public import LeanVM.Guest.AcceptableChild

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits)
open LeanVM.Guest.B1 (CompleteAtDT CompleteAtDTB CompleteAtD Returns bufL)

@[expose] public section

variable (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness)
variable {seed s w}

/-- **`main`'s honest `aggregate_claims` call is complete within `aggB`, by a tree of honest shape**: under `NodeRelation` and `Limits`, for a
bytecode of `2^bytecodeVars` words. -/
theorem mainGoalAgTB (cert : String → V → ℕ) (SB SK : String → ℕ) (hBS : agg_batch_sumcheck_Spec)
    (hGr : CompleteRelB fs cert 16 "grind_check__L2" aggGrindPre (SB "grind_check__L2"))
    (h25 : TotalLeOn coreProgram fs "__loop33" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop33" + fs "__loop33"))
    (h26 : TotalLeOn coreProgram fs "__loop34" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop34" + fs "__loop34"))
    (h27 : TotalLeOn coreProgram fs "__loop35" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop35" + fs "__loop35"))
    (hbs : TotalLe coreProgram fs "batch_sumcheck__L23" (fun _ => SB "batch_sumcheck__L23"))
    {bytecode : List K}
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hrel : NodeRelation bytecode seed s w)
    (hl : DeployedLimits s w) : (hm fs fp seed s w).nc ≠ 0 →
      CompleteAtDTB fs cert 16 "aggregate_claims" (hLmain fs fp seed s w)
        [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
          (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
          (hm fs fp seed s w).et * word 133823759239872512 0] (Returns [])
        (aggHonest (hm fs fp seed s w).nc) (aggB fs SB SK (hm fs fp seed s w).nc) := by
  intro hnc
  have hnc' : w.children.length ≠ 0 := hnc
  have hne : w.children ≠ [] := fun h => hnc' (by rw [h, List.length_nil])
  have hb := (nodeRel_iff.mp hrel).2.2.2.2
  simp only [hne, ↓reduceIte] at hb
  have hlog : Nat.log2 bytecode.length = bytecodeVars := by rw [hbl, Nat.log2_two_pow]
  have hrl : w.batchingHints.sumcheckMessages.length = 23 := by
    have hpt : s.deferredClaim.bytecodePoint.length = 23 := by rw [hrel.hasBytecodeShape, hlog]
    rw [(batch_out hb).1, aggOut, aggRun, aggBsRun_len] at hpt
    exact hpt
  have hdst := mem_hLmain fs fp seed s w (i := 9) (by omega)
  simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at hdst
  have := aggregate_claims_completeAtTB fs cert SB SK hBS hGr h25 h26 h27 hbs
    (m := w.children.length) (by omega) hl.atMostSixteenChildren (cs := hKids seed w)
    (by rw [List.length_map]) hrl hb (fun rd hM => hkids_words fs fp hbl hrel hM)
    (fun rd _ hM => hLmain_winTabs fs fp hM) hdst
  exact this

end
end LeanVM.Guest.B1.Main
