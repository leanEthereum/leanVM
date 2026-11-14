/-
  LeanVM.Guest.B1.Place.ArmXT

  The predicate an arm of `open_stacked` asks of its callees' trees for exactness, and the callees it holds of for
  free.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.Budget.Bounded

/-!
# The arms' callees' exactness predicate

`armXT rd t`: `t` is exact at every node on `rd` when it is an `armExactS` callee's. `CompleteAtDTBR.monoN`:
`CompleteAtDTBR.mono` knowing the tree's name. A `level_queries`', a `level_residual`'s and a named callee other than
`opening_round` and the grind checks (`OsKind.exactS`) are not `armExactS` (by the kernel, over the tables), so any of
their trees satisfies `armXT`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout)

@[expose] public section

/-- **`CompleteAtDTBR.mono` knowing the tree's name.** -/
theorem CompleteAtDTBR.monoN {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : Layout}
    {args : List E} {Out : List E → Layout → Prop} {T T' : Reader → Tree → Prop} {B B' : ℕ}
    (h : CompleteAtDTBR fs cert k f Lin args Out T B) (hB : B ≤ B')
    (hT : ∀ rd t, t.name = f → T rd t → T' rd t) : CompleteAtDTBR fs cert k f Lin args Out T' B' := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn.trans hB, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT'⟩ := hr rd hl hm
    ⟨t, ht, hT rd t ht.1 hT'⟩⟩

end

namespace Arm

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **An `armExactS` callee's tree is exact at every node on `rd`.** -/
def armXT (rd : Reader) (t : Tree) : Prop :=
  armExactS t.name = true → t.Every (ExactAt coreProgram rd)

/-- The named kinds whose callees are `armExactS`: `opening_round` and the grind checks. -/
def _root_.LeanVM.Guest.B1.OsKind.exactS : OsKind → Bool
  | .round => true
  | .grind _ => true
  | _ => false

theorem lq_not_exactS : lqTable.all (fun e ↦ !armExactS e.1) = true := by decide +kernel

theorem lr_not_exactS : lrTable.all (fun e ↦ !armExactS e.1) = true := by decide +kernel

theorem kind_not_exactS : osKindTable.all (fun e ↦ e.2.exactS || !armExactS e.1) = true := by decide +kernel

theorem armExactS_lq {e : String × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (he : e ∈ lqTable) :
    armExactS e.1 = false := by
  simpa using List.all_eq_true.mp lq_not_exactS e he

theorem armExactS_lr {e : String × ℕ × ℕ × ℕ × ℕ × String × String} (he : e ∈ lrTable) :
    armExactS e.1 = false := by
  simpa using List.all_eq_true.mp lr_not_exactS e he

theorem armExactS_kind {f : String} {K : OsKind} (hK : osKindOf f = some K) (hx : K.exactS = false) :
    armExactS f = false := by
  have := List.all_eq_true.mp kind_not_exactS _ (os_mem_of_lookup _ hK)
  simpa [hx] using this

theorem armXT_of_not {rd : Reader} {t : Tree} (h : armExactS t.name = false) : armXT rd t :=
  fun h' ↦ absurd (h.symm.trans h') Bool.false_ne_true

end
end Arm
end LeanVM.Guest.B1
