module

public import NativeVm.Math.Roots
public import NativeVm.Equiv.Transcript

/-!
# The roots read by fold rounds and queries
-/

@[expose] public section

namespace NativeVm.Math.Whir

open NativeVm.Model LeanVM.Parameters

theorem foldRound_roots (s : WhirStateW) : KeepsRoots (foldRound s) := by
  unfold foldRound
  refine KeepsRoots.readScalar.bind fun _ ↦ KeepsRoots.readScalar.bind fun _ ↦
    KeepsRoots.readScalar.bind fun _ ↦ KeepsRoots.readScalar.bind fun _ ↦
    (KeepsRoots.grind _).bind fun _ ↦ KeepsRoots.sampleChallenge.bind fun _ ↦
    KeepsRoots.sampleChallenge.bind fun _ ↦ KeepsRoots.pure _

theorem foldRounds_roots (n : Nat) (s : WhirStateW) : KeepsRoots (foldRounds n s) :=
  KeepsRoots.foldlM (fun _ _ ↦ (foldRound_roots _).bind fun x ↦ by
    obtain ⟨_, _⟩ := x; exact KeepsRoots.pure _) _ _

theorem sampleQueriesAux_keepsRoots (depth : Nat) :
    ∀ fuel rem, KeepsRoots (sampleQueriesAux depth fuel rem)
  | 0, _ => KeepsRoots.pure _
  | fuel + 1, rem => by
    unfold sampleQueriesAux
    split
    · exact KeepsRoots.pure _
    · exact KeepsRoots.bind KeepsRoots.sampleChallenge fun _ ↦
        KeepsRoots.bind (sampleQueriesAux_keepsRoots depth fuel _) fun _ ↦ KeepsRoots.pure _

theorem sampleQueries_keepsRoots (depth count : Nat) : KeepsRoots (sampleQueries depth count) :=
  sampleQueriesAux_keepsRoots depth count count

/-- A query that returned kept the roots. -/
theorem qy_roots {t t' : TState} {i : Nat} {ps : Array UInt64} {rows : Array (Array UInt64)}
    (h : (Model.queryOpenings i ps).run t = some (rows, t')) : t'.roots = t.roots := by
  rw [Equiv.queryOpenings_run] at h
  split at h
  · rename_i r ph _ _
    cases ho : Model.openPhase r.digest r.height r.width ps ph with
    | none => rw [ho] at h; cases h
    | some rows' =>
      rw [ho] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rfl
  · cases h

theorem queryOpenings_keeps (i : Nat) (ps : Array UInt64) : KeepsRoots (queryOpenings i ps) :=
  ⟨fun _ _ _ h ↦ qy_roots h⟩

end NativeVm.Math.Whir
