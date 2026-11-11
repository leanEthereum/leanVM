/-
  LeanVM.Guest.B1.Main.MainGoalsHAg

  `main`'s honest `aggregate_claims` call: complete at `main`'s words (`MainGoalAg`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHBase
public import LeanVM.Guest.B1.Main.AggAt
public import LeanVM.Protocol.Verifier.DeferredShape
public import LeanVM.Guest.Batch.Node
public import LeanVM.Guest.AcceptableChild

/-!
# `aggregate_claims` on an honest run

`hkids_words`: `main`'s words hold each
child's words where `aggregate_claims` reads them. `mainGoalAg`: the children's batching is the
statement's deferred claim, which `main`'s words hold at `defer_stmt`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.B1 (CompleteAtD Returns bufL)

@[expose] public section

variable (fs : String → ℕ) (fp : ℕ) {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-- The children's claims as `aggregate_claims` batches them. -/
abbrev hKids (seed : Digest) (w : NodeWitness) : List ChildClaims :=
  w.children.map fun c ↦ ⟨statementDigest seed c.statement, c.freshClaim, c.statement.deferredClaim⟩

/-- **`main`'s words hold every child's words** where `aggregate_claims` reads them. -/
theorem hkids_words {bytecode : List K} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (hrel : NodeRelation bytecode seed s w) {rd : Reader}
    (hM : B1.Main.MemL rd (hLmain fs fp seed s w)) :
    ∀ c (hc : c < (hKids seed w).length), ChildWordsAt rd (hm fs fp seed s w).a394
      (hm fs fp seed s w).a400 (hm fs fp seed s w).a406 c (hKids seed w)[c] := by
  have hsh := kid_shapes hbl hrel
  have hb : bytecodeVars = 23 := rfl
  intro c hc
  rw [List.length_map] at hc
  have hmem := List.getElem_mem hc
  obtain ⟨hf, hd⟩ := hsh _ hmem
  have r6 := reads_hLmain fs fp seed s w hM (i := 5) (by omega)
  have r7 := reads_hLmain fs fp seed s w hM (i := 6) (by omega)
  have r8 := reads_hLmain fs fp seed s w hM (i := 7) (by omega)
  simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at r6 r7 r8
  have p6 := readsAt_flatMap_of (w := 2) w.children (fun _ _ => rfl) r6 c hc
  have p7 := readsAt_flatMap_of (w := 24) w.children
    (fun a ha => by simp [DeferredClaim.cells, (hsh a ha).1, hb]) r7 c hc
  have p8 := readsAt_flatMap_of (w := 24) w.children
    (fun a ha => by simp [DeferredClaim.cells, (hsh a ha).2, hb]) r8 c hc
  simp only [hKids, List.getElem_map]
  refine ⟨hf, hd, ?_, ?_, p7, p8⟩
  · have := p6 0 (by simp [B1.Digest.digestCells])
    rwa [loadHolds_mul_gen_pow, Nat.add_zero] at this
  · have := p6 1 (by simp [B1.Digest.digestCells])
    rwa [loadHolds_mul_gen_pow] at this
