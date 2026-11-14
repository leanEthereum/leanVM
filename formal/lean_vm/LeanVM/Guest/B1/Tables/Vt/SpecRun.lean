/-
  LeanVM.Guest.B1.Tables.Vt.SpecRun

  Runs of the specification's table loop and of programs that read nothing: `tableTerms` reads
  each table's evaluations in turn and returns what `termsPure` computes.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Tables.Vt.SpecWeights
public import LeanVM.Guest.B1.Gkr.Spec
public import LeanVM.Protocol.EndToEnd.Complete.Table

/-!
# Runs of the table loop

* `vt_runsTo_const`: a program that leaves every state as it is and returns `a` runs to `a`,
  reading nothing (the check of the bytecode's value, `BytecodeAt`);
* `vt_runsTo_tableTerms`: `tableTerms` over tables with their evaluations reads the evaluations
  in turn and returns `termsPure`'s terminal value and claims.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure)

@[expose] public section

/-- A program that keeps every state and returns `a`. -/
theorem vt_runsTo_const {α : Type} {p : VerifierProgram α} {a : α} (h : ∀ st, runId p st = some
    (a, st))
    (s : Fs) : RunsTo p s [] a s :=
  fun sp hs rest os roots ↦ ⟨sp, hs, by rw [List.nil_append]; exact h _⟩

theorem vt_absorbAll_append (s : Fs) (a b : List E) (t : ℕ) :
    s.absorbAll (a ++ b) t = (s.absorbAll a t).absorbAll b t := by
  simp [Fs.absorbAll, List.foldl_append]

/-- **The table loop as a run.** -/
theorem vt_runsTo_tableTerms (cp fp point : List E) :
    ∀ (pairs : List ((Table × ℕ × List Form × E) × List E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim) (s : Fs), (∀ p ∈ pairs, p.2.length = p.1.1.width) →
      RunsTo (tableTermsClaims cp fp point (pairs.map (·.1)) cursor final claims) s
        (pairs.flatMap (·.2)) (termsPure cp fp point pairs cursor final claims)
        (s.absorbAll (pairs.flatMap (·.2)) dsObserve)
  | [], cursor, final, claims, s, _ => by
    simp only [List.map_nil, tableTermsClaims, List.flatMap_nil, termsPure]
    exact runsTo_ret _ _
  | ((table, height, forms, weight), ev) :: rest, cursor, final, claims, s, h => by
    have hev : ev.length = table.width := h ((table, height, forms, weight), ev) (by simp)
    have ih := vt_runsTo_tableTerms cp fp point rest (cursor + table.nConstraints)
      (final + weight * (dot ((cp.drop cursor).take table.nConstraints) (table.constraints ev) +
        dot fp (forms.map (·.evaluate (ev.getD · 0)))))
      (claims ++ ev.zipIdx.map fun (value, column) ↦
        ⟨globalColumnBases.getD table.opcode 0 + column, point.take height, value⟩)
      (s.absorbAll ev dsObserve) fun p hp ↦ h p (by simp [hp])
    have hr := runsTo_readN s ev
    rw [hev] at hr
    have hb := hr.bind (f := fun evaluations ↦ tableTermsClaims cp fp point (rest.map (·.1))
      (cursor + table.nConstraints)
      (final + weight * (dot ((cp.drop cursor).take table.nConstraints)
        (table.constraints evaluations) + dot fp (forms.map (·.evaluate (evaluations.getD · 0)))))
      (claims ++ evaluations.zipIdx.map fun (value, column) ↦
        ⟨globalColumnBases.getD table.opcode 0 + column, point.take height, value⟩)) ih
    simp only [List.map_cons, tableTermsClaims, List.flatMap_cons, termsPure]
    rw [vt_absorbAll_append]
    exact hb

end
end LeanVM.Guest.B1.Tables
