/-
  LeanVM.Guest.B1.Place.ArmExactDef

  The check that an arm of `open_stacked` has its own computed hints pinned by the next atom and calls only
  `level_positions`, `opening_round`, a grind check or functions exact for free, and what it gives.
-/

module

public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.Exact.Kids
public import LeanVM.Guest.B1.Bits.MeaningP

/-!
# The arms' exactness check

* `armExactS g`: `g` is `opening_round`, a deployed grind check or an entry of `lpTable`: the callees whose exactness
  the arm's composition carries;
* `armExactOk name j`: function `j` is named `name`, its computed hints are pinned by the next atom, and each of its
  callees is `armExactS` or exact for free (`exactCallee j`), decided by the kernel per arm (`ArmExactA`, `ArmExactB`);
* `armExact_find`: such a function's paths that hold are exact, and its callees not `armExactS` exact for free;
  `armExact_every`: so a valid node of it whose `armExactS` callees' predicates give `Every` exact is exact at every
  node.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

/-- `opening_round`, a deployed grind check, or an entry of `lpTable`. -/
def armExactS (g : String) : Bool :=
  g == "opening_round" || grindBitsDeployed.any (fun b => grindCheckName b == g) || lpTable.any (·.1 == g)

/-- **Function `j`, named `name`, has its computed hints pinned by the next atom and calls `armExactS` functions or
functions exact for free.** -/
noncomputable def armExactOk (name : String) (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => fn.name == name && Stmt.blockNextOk isComputed pinsInverse fn.body &&
      (Stmt.blockCallees fn.body).all fun g => armExactS g || exactCallee j g
  | none => false

theorem armExact_find {name : String} {j : ℕ} (h : armExactOk name j = true) :
    ∃ fn, coreProgram.find? name = some fn ∧ Stmt.blockNextOk isComputed pinsInverse fn.body = true ∧
      ∀ g ∈ Stmt.blockCallees fn.body, armExactS g = true ∨ ExactFreeG g := by
  unfold armExactOk at h
  split at h
  · next fn hj =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨hn, hp⟩, hc⟩ := h
    exact ⟨fn, coreProgram_find?_at hj hn, hp, fun g hg ↦ (hc g hg).imp id exactFreeG_of_callee⟩
  · exact absurd h Bool.false_ne_true

/-- **A valid node of an arm passing the check is exact at every node** when each entered `armExactS` callee's
predicate gives `Every` exact on its valid trees. -/
theorem armExact_every {name : String} {j : ℕ} (h : armExactOk name j = true) {rd : Reader} {σ : Val}
    {bufs : List ℕ} {ks : List Tree} {args rets : List E} {Ts : List (Memory.Tree → Prop)}
    (hv : (Memory.Tree.node name σ bufs ks).Valid coreProgram rd args rets)
    (hT : ∀ fn es vs, coreProgram.find? name = some fn → walk σ fn.body = .ret es vs →
      (calls es).length ≤ Ts.length ∧ KidsT (calls es) Ts ks ∧
      ∀ c T, (c, T) ∈ (calls es).zip Ts → c.taken = true → armExactS c.f = true → ∀ t : Memory.Tree, t.name = c.f →
        t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ) → T t → t.Every (ExactAt coreProgram rd)) :
    (Memory.Tree.node name σ bufs ks).Every (ExactAt coreProgram rd) := by
  obtain ⟨fn, hf, hp, hc⟩ := armExact_find h
  obtain ⟨fn', hf', -, es, vs, hw, -, hes, hkv⟩ := hv
  rw [hf] at hf'
  cases hf'
  obtain ⟨hlen, hK, hE⟩ := hT fn es vs hf hw
  refine Tree.every_node.mpr ⟨exactAt_of_walk hf hw (exact_of_pinned hp hw hes rd),
    everyKids_of_kidsT hkv hlen hK fun c T hcT ht t hn htv hTt => ?_⟩
  have hcal : c.f ∈ Stmt.blockCallees fn.body :=
    walk_callees (σ := σ) fn.body (by rw [hw]; exact (List.of_mem_zip hcT).1)
  rcases hc c.f hcal with hs | hfree
  · exact hE c T hcT ht hs t hn htv hTt
  · exact every_exact_of_free hfree htv hn rd

end
end LeanVM.Guest.B1.Arm
