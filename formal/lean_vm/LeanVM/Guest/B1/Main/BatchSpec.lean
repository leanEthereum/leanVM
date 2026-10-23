/-
  LeanVM.Guest.B1.Main.BatchSpec

  `Node.batch` (N:261) run on the chain: the transcript, the lambdas, the two sumchecks and the
  final check as explicit functions of the chaining value.
-/

module

public import LeanVM.Guest.B1.Main.AggregateSpec

/-!
# `Node.batch`, run

`batch_spec` unfolds `Node.batch`'s `StateM` program: the transcript is `obsAll` of the count and
of every child's cells (`childCells`), the lambdas are two (`sq2`) and three (`sq3`) squeezes per
child, between them the two `batchRounds`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- The cells a child's claims are absorbed as: its public input's two, its fresh claims, its
carried claim. -/
def childCells (c : ChildClaims) : List E :=
  [(digestScalars c.publicInput).1, (digestScalars c.publicInput).2] ++ fixedCells c.fresh ++
    c.carried.cells

/-- Two squeezes per child: the lambdas and the state after them. -/
def sq2 : ℕ → Digest → List (E × E) × Digest
  | 0, cv => ([], cv)
  | n + 1, cv => ((challengeOf (sqCv cv), challengeOf (sqCv (sqCv cv))) ::
      (sq2 n (sqCv (sqCv cv))).1, (sq2 n (sqCv (sqCv cv))).2)

/-- Three squeezes per child. -/
def sq3 : ℕ → Digest → List (E × E × E) × Digest
  | 0, cv => ([], cv)
  | n + 1, cv => ((challengeOf (sqCv cv), challengeOf (sqCv (sqCv cv)),
      challengeOf (sqCv (sqCv (sqCv cv)))) :: (sq3 n (sqCv (sqCv (sqCv cv)))).1,
      (sq3 n (sqCv (sqCv (sqCv cv)))).2)

theorem observe_run (x : E) (cv : Digest) : (observe x).run cv = ((), obsCv cv x) := rfl

theorem squeeze_run (cv : Digest) : squeeze.run cv = (challengeOf (sqCv cv), sqCv cv) := rfl

theorem forIn_unit_run {α : Type} (l : List α) (f : α → Chain PUnit) (cv : Digest) :
    (forIn l PUnit.unit (fun a _ => do f a; pure (ForInStep.yield PUnit.unit))).run cv =
      ((), l.foldl (fun cv a => ((f a).run cv).2) cv) := by
  induction l generalizing cv with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    rw [← ih]
    rfl

theorem forIn_observe_run (xs : List E) (cv : Digest) :
    (forIn xs PUnit.unit (fun x _ => do observe x; pure (ForInStep.yield PUnit.unit))).run cv =
      ((), obsAll cv xs) := by
  rw [forIn_unit_run]
  rfl

theorem forIn_sq2_run {α : Type} (l : List α) (acc : List (E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc => do
        let lf ← squeeze
        let lc ← squeeze
        pure (ForInStep.yield (acc ++ [(lf, lc)])))).run cv =
      (acc ++ (sq2 l.length cv).1, (sq2 l.length cv).2) := by
  induction l generalizing acc cv with
  | nil => simp [sq2]; rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons, sq2]
    rw [← List.singleton_append, ← List.append_assoc, ← ih]
    rfl

theorem forIn_sq3_run {α : Type} (l : List α) (acc : List (E × E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc => do
        let lf ← squeeze
        let la ← squeeze
        let lb ← squeeze
        pure (ForInStep.yield (acc ++ [(lf, la, lb)])))).run cv =
      (acc ++ (sq3 l.length cv).1, (sq3 l.length cv).2) := by
  induction l generalizing acc cv with
  | nil => simp [sq3]; rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons, sq3]
    rw [← List.singleton_append, ← List.append_assoc, ← ih]
    rfl

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

theorem obsAll_flatMap {α : Type} (g : α → List E) :
    ∀ (l : List α) (cv : Digest), obsAll cv (l.flatMap g) = l.foldl (fun cv a => obsAll cv (g a)) cv
  | [], _ => rfl
  | a :: l, cv => by
    rw [List.flatMap_cons, List.foldl_cons, ← obsAll_flatMap g l]
    simp [obsAll, List.foldl_append]

theorem child_run (c : ChildClaims) (cv : Digest) :
    ((do
        observe (digestScalars c.publicInput).1
        observe (digestScalars c.publicInput).2
        forIn (fixedCells c.fresh ++ c.carried.cells) PUnit.unit fun x _ => do
          observe x
          pure (ForInStep.yield PUnit.unit) : Chain PUnit)).run cv =
      ((), obsAll cv (childCells c)) := by
  simp only [StateT.run_bind, observe_run, forIn_observe_run]
  rfl

theorem forIn_children_run (cs : List ChildClaims) (cv : Digest) :
    (forIn cs PUnit.unit fun c _ => do
        observe (digestScalars c.publicInput).1
        observe (digestScalars c.publicInput).2
        forIn (fixedCells c.fresh ++ c.carried.cells) PUnit.unit fun x _ => do
          observe x
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit) : Chain PUnit).run cv =
      ((), obsAll cv (cs.flatMap childCells)) := by
  induction cs generalizing cv with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.forIn_cons, StateT.run_bind, observe_run, forIn_observe_run]
    rw [List.flatMap_cons, show obsAll cv (childCells c ++ cs.flatMap childCells) =
      obsAll (obsAll cv (childCells c)) (cs.flatMap childCells) by simp [obsAll, List.foldl_append],
      ← ih]
    rfl

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

/-- **`Node.batch`, run** on the chain: the transcript, the two sumchecks between the lambdas,
the final check. -/
theorem batch_spec (cs : List ChildClaims) (h : BatchHints) :
    batch cs h =
      let cvA := obsAll (obsCv (blake2sBytes batchLabel) (ofK (Parameters.gpow cs.length)))
        (cs.flatMap childCells)
      let lB := (sq2 cs.length cvA).1
      let rb := (batchRounds (sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.bytecodeValue +
        l.2 * c.carried.bytecodeValue) cs lB)) h.bytecodeRounds).run (sq2 cs.length cvA).2
      let lM := (sq3 cs.length rb.2).1
      let rm := (batchRounds (sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.matrixValue +
        l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB) cs lM)) h.matrixRounds).run
        (sq3 cs.length rb.2).2
      if rb.1.2 = h.bytecodeValue * sumE (List.zipWith (fun c l ↦
            l.1 * eqEval c.fresh.bytecodePoint rb.1.1 + l.2 * eqEval c.carried.bytecodePoint rb.1.1)
            cs lB) ∧
          rm.1.2 = h.matrixA * sumE (List.zipWith (fun c l ↦ l.1 * freshWeight c.fresh rm.1.1 +
            l.2.1 * eqEval c.carried.matrixPoint rm.1.1) cs lM) +
            h.matrixB * sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.alpha * freshWeight c.fresh rm.1.1 +
              l.2.2 * eqEval c.carried.matrixPoint rm.1.1) cs lM) then
        some ⟨rb.1.1, h.bytecodeValue, rm.1.1, h.matrixA, h.matrixB⟩
      else none := by
  rw [show batch cs h = ((batch.go cs h).run (blake2sBytes batchLabel)).1 from rfl]
  unfold batch.go
  simp only [StateT.run_bind, observe_run, forIn_children_run, forIn_sq2_run, forIn_sq3_run,
    List.nil_append, id_bind]
  split_ifs <;> rfl

end
end LeanVM.Guest.B1.Main
