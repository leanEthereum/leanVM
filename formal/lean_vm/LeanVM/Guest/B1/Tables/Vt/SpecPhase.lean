/-
  LeanVM.Guest.B1.Tables.Vt.SpecPhase

  The specification's table phase and public input phase as runs: the batching challenge, the
  table sumcheck, the per-table loop and its final check; the public input's challenge.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Tables.Vt.SpecTotals
public import LeanVM.Guest.B1.Sumcheck.Run

/-!
# The table phase and the public input phase

* `vt_tableSumcheck_run`: when the sumcheck of `n` rounds (the tables' largest height) runs to
  the challenges `pts` and the claim `claimN`, and the per-table loop over the evaluations `evs`
  ends at `claimN`, `tableSumcheck` reads the sumcheck's words and the evaluations and returns the
  loop's claims;
* `vt_tablePhase_run`: the batching challenge first;
* `vt_publicInputPhase_run`: one challenge, nothing read.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure)

@[expose] public section

/-- The rows the table loop walks. -/
def vtRows (heights : List ℕ) (busForms : List (List Form)) (eqPoint pts : List E) :
    List (Table × ℕ × List Form × E) :=
  List.zip tables (List.zip heights (List.zip busForms (tableWeights heights eqPoint pts.reverse)))

theorem vt_flatMap_snd {α : Type} : ∀ l : List (α × List E), l.flatMap (·.2) = (l.map (·.2)).flatten
  | [] => rfl
  | q :: l => by simp [List.flatMap_cons, vt_flatMap_snd l]

/-- **`tableSumcheck` as a run.** -/
theorem vt_tableSumcheck_run (heights : List ℕ) (busForms : List (List Form))
    (cp fp eqPoint : List E) (target : E) {n : ℕ} (hn : heights.foldl max 0 = n) {s s1 : Fs}
    {xs pts : List E} {claimN : E}
    (hsc : RunsTo (sumcheck target 4 (List.replicate n none)) s xs (pts, claimN) s1)
    (evs : List (List E)) (hlen : evs.length = (vtRows heights busForms eqPoint pts).length)
    (hw : ∀ p ∈ List.zip (vtRows heights busForms eqPoint pts) evs, p.2.length = p.1.1.width)
    (hfin : (termsPure cp fp pts.reverse (List.zip (vtRows heights busForms eqPoint pts) evs) 0 0
      []).1 = claimN) :
    RunsTo (tableSumcheckClaims heights busForms cp fp eqPoint target) s (xs ++ evs.flatten)
      (termsPure cp fp pts.reverse (List.zip (vtRows heights busForms eqPoint pts) evs) 0 0 []).2
      (s1.absorbAll evs.flatten dsObserve) := by
  set pairs := List.zip (vtRows heights busForms eqPoint pts) evs
  have hfst : pairs.map (·.1) = vtRows heights busForms eqPoint pts :=
    List.map_fst_zip (by omega)
  have hflat : pairs.flatMap (·.2) = evs.flatten := by
    rw [vt_flatMap_snd, List.map_snd_zip (by omega)]
  have ht := vt_runsTo_tableTerms cp fp pts.reverse pairs 0 0 [] s1 hw
  rw [hfst, hflat] at ht
  rcases hT : termsPure cp fp pts.reverse pairs 0 0 [] with ⟨fin, cl⟩
  rw [hT] at ht hfin
  simp only at hfin ⊢
  have hr := tb_runsTo_require hfin (s1.absorbAll evs.flatten dsObserve)
  have h3 := hr.bind (f := fun _ ↦ (pure cl : VerifierProgram (List ColumnClaim))) (runsTo_ret _ _)
  unfold tableSumcheckClaims
  rw [hn]
  refine RunsTo.of_eq (hsc.bind (ht.bind h3)) rfl (by simp) rfl rfl

/-- **`tablePhase` as a run.** -/
theorem vt_tablePhase_run (layout : Layout) (bus : BusResult) (s0 : Fs) {n : ℕ}
    (hn : layout.tableLogHeights.foldl max 0 = n) {s1 : Fs} {xs pts : List E} {claimN : E}
    (hsc : RunsTo (sumcheck (dot ((powers s0.squeeze.1
        ((tables.map Table.nConstraints).sum + 3)).drop (tables.map Table.nConstraints).sum)
        bus.totals) 4 (List.replicate n none)) s0.squeeze.2 xs (pts, claimN) s1)
    (evs : List (List E))
    (hlen : evs.length = (vtRows layout.tableLogHeights bus.forms bus.point pts).length)
    (hw : ∀ p ∈ List.zip (vtRows layout.tableLogHeights bus.forms bus.point pts) evs,
      p.2.length = p.1.1.width)
    (hfin : (termsPure ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) pts.reverse
      (List.zip (vtRows layout.tableLogHeights bus.forms bus.point pts) evs) 0 0 []).1 = claimN) :
    RunsTo (tablePhaseClaims layout bus) s0 (xs ++ evs.flatten)
      (bus.claims ++ (termsPure ((powers s0.squeeze.1
          ((tables.map Table.nConstraints).sum + 3)).take (tables.map Table.nConstraints).sum)
        ((powers s0.squeeze.1 ((tables.map Table.nConstraints).sum + 3)).drop
          (tables.map Table.nConstraints).sum) pts.reverse
        (List.zip (vtRows layout.tableLogHeights bus.forms bus.point pts) evs) 0 0 []).2)
      (s1.absorbAll evs.flatten dsObserve) := by
  have h0 := runsTo_grind0 (bits := grindingBits ((tables.map Table.nConstraints).sum + nTrees - 1))
    (by decide) s0
  have h1 := runsTo_sampleE s0
  have h2 := vt_tableSumcheck_run layout.tableLogHeights bus.forms _ _ bus.point _ hn hsc evs
    hlen hw hfin
  have h3 := h2.bind (f := fun c ↦ (pure (bus.claims ++ c) : VerifierProgram (List ColumnClaim)))
    (runsTo_ret _ _)
  unfold tablePhaseClaims
  exact RunsTo.of_eq (h0.bind (h1.bind h3)) rfl (by simp) rfl rfl

/-- **`publicInputPhase` as a run.** -/
theorem vt_publicInputPhase_run (layout : Layout) (pi : Digest) (s : Fs) :
    RunsTo (publicInputPhase layout pi) s []
      (List.zipWith (fun column value ↦ ⟨column, s.squeeze.1 ::
        List.replicate ((layout.placement memory0).variableCount - 1) 0, value⟩)
        [memory0, memory1] (([0, 1] : List (Fin 2)).map fun limb ↦
          multilinearEval [ofK ((digestHalves pi).1.limb limb),
            ofK ((digestHalves pi).2.limb limb)] [s.squeeze.1])) s.squeeze.2 := by
  have h1 := runsTo_sampleE s
  unfold publicInputPhase
  exact RunsTo.of_eq (h1.bind (runsTo_ret _ _)) rfl (by simp) rfl rfl

end
end LeanVM.Guest.B1.Tables
