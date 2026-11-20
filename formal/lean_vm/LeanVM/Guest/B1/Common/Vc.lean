/-
  LeanVM.Guest.B1.Common.Vc

  What B1's proofs by `vc` share: a found function's relation as its core function's, and the
  rules naming the sponge's cells.
-/

module

public import LeanVM.Guest.VcTactic
public import LeanVM.Guest.B1.Common.Sponge

/-!
# Proofs by `vc`

A function's statement `P.Rel rd name args rets ↔ Meaning` is proved by `rw [rel_iff_fnSem h]`
(`h` its `find?`, at `coreProgram` `coreProgram_find?_at (j := idx% «name») rfl`), a case split
on the arguments the meaning matches on, `vc [rules]`, and rewriting the meaning to the condition.
`keccakF_cells` names a permutation in the even layouts `permOf`; `scalarCells_eq` and
`word_dsObserve` write a waiting scalar's cells as the guest's constants.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- **A found function's relation is its core function's.** -/
theorem rel_iff_fnSem {P : Program} {rd : Reader} {n : String} {f : Fn} (h : P.find? n = some f)
    (args rets : List E) : P.Rel rd n args rets ↔ f.Sem (P.Rel rd) rd args rets := by
  rw [rel_iff, h]
  simp only [Option.some.injEq, exists_eq_left']

/-- The same at a finite depth: the body's calls one level shallower. -/
theorem relN_succ_iff_fnSem {P : Program} {rd : Reader} {n : String} {f : Fn}
    (h : P.find? n = some f) (d : ℕ) (args rets : List E) :
    P.relN rd (d + 1) n args rets ↔ f.Sem (P.relN rd d) rd args rets := by
  simp only [Program.relN, h, Option.some.injEq, exists_eq_left']

/-- A `KECCAK` in the even layouts permutes into `permOf` of the cells it reads. -/
theorem keccakF_cells (l : List E) : keccakF1600 (stateOfCells (cells13 l) false) = permOf l := rfl

/-- A waiting scalar's two rate cells, as the guest's constants. -/
theorem scalarCells_eq (x : E) (t : ℕ) : Value.Keccak.scalarCells x t = (x, word 0 t) := rfl

theorem word_dsObserve : word 0 Protocol.Compile.dsObserve = word 0 1 := rfl

end
end LeanVM.Guest.B1
