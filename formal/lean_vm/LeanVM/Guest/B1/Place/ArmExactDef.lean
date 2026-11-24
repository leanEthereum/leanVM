/-
  LeanVM.Guest.B1.Place.ArmExactDef

  The check that an arm of `open_stacked` has its own computed hints but its window hints pinned by the next atom and
  calls only `is_zero`, `level_positions` or functions exact for free, and what it gives.
-/

module

public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.Exact.Kids
public import LeanVM.Guest.B1.Bits.MeaningP
public import LeanVM.Guest.B1.Place.ArmRoots

/-!
# The arms' exactness check

* `armExactS g`: `g` is `is_zero` or an entry of `lpTable`: the callees whose exactness the arm's composition carries;
* `isWinHint`: a `windowsExp` hint, as the inlined grind checks (`gcInlineT`) write, pinned by no next atom: their
  exactness comes from the honest valuation (`Whir.WinEx`, from `gcInline_exact_of_vals`), not from the check;
* `armExactOk name j`: function `j` is an arm named `name`, its computed hints but the window hints are pinned by the
  next atom, and its callees have indices, decided by the kernel per arm (`ArmOkA`, `ArmOkB`);
* `exLoc`: `exactJ`'s own step (`exactJ_succ`); `ExRootsOk`: every root (`armRoots`) is `armExactS` by name or
  exact for free, from the groups' checks (`exRootsOk_of`);
* `armExact_find`: so an arm's callees not `armExactS` are exact for free;
  `armExact_every`: so a valid node of it whose window hints are exact and whose `armExactS` callees' predicates give
  `Every` exact is exact at every node.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

/-- `is_zero` or an entry of `lpTable`. -/
def armExactS (g : String) : Bool :=
  g == "is_zero" || lpTable.any (·.1 == g)

/-- A `windowsExp` hint. -/
def isWinHint : Atom → Bool
  | .hint (.windowsExp ..) => true
  | _ => false

/-- A computed hint but a window hint. -/
def isComputedNW (a : Atom) : Bool := isComputed a && !isWinHint a

/-- **Function `j`, named `name`, is an arm, has its computed hints but the window hints pinned by the next atom,
and its callees have indices** (each `armExactS` or exact for free, `armExact_find`, by the roots' check). -/
noncomputable def armExactOk (name : String) (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => fn.name == name && armIdxs.contains j && Stmt.blockNextOk isComputedNW pinsInverse fn.body &&
      (Stmt.blockCallees fn.body).all fun g => (calleeIdx j g).isSome
  | none => false

/-- `exactJ`'s own step on function `j`: its body's computed hints pinned locally, its callees indexed. -/
noncomputable def exLoc (j : ℕ) : Bool :=
  match coreAt j with
  | some fn => Stmt.blockNextOk isComputed pinsInverse fn.body &&
      (Stmt.blockCallees fn.body).all (fun g => (calleeIdx j g).isSome)
  | none => false

theorem exactJ_succ (d j : ℕ) :
    exactJ (d + 1) j = (exLoc j && (Data.calleesJ j).all fun k ↦ k == j || exactJ d k) := by
  rw [exactJ, exLoc, coreAt_eq]
  cases coreProgram[j]? <;> rfl

/-- Root `k`'s name is `armExactS`. -/
noncomputable def exRootS (k : ℕ) : Bool := armExactS ((Data.nameT.find k).getD "")

/-- **Each root's name is `armExactS` or it is exact for free**, from the groups' checks (`ArmFree0` to
`ArmFree5`). -/
def ExRootsOk : Prop := ∀ k ∈ armRoots, exRootS k = true ∨ ∃ d, exactJ d k = true

theorem exRootsOk_of (e0 : armGrpOk exLoc exRootS 0 = true) (e1 : armGrpOk exLoc exRootS 1 = true)
    (e2 : armGrpOk exLoc exRootS 2 = true) (e3 : armGrpOk exLoc exRootS 3 = true)
    (e4 : armGrpOk exLoc exRootS 4 = true) (e5 : armGrpOk exLoc exRootS 5 true = true) : ExRootsOk :=
  have s := fun {i last} (e : armGrpOk exLoc exRootS i last = true) ↦
    armGrpOk_sound (J := exactJ) (fun _ ↦ rfl) exactJ_succ e
  armRoots_all (s e0) (s e1) (s e2) (s e3) (s e4) (s e5)

theorem armExact_find (hR : ExRootsOk) {name : String} {j : ℕ} (h : armExactOk name j = true) :
    ∃ fn, coreProgram.find? name = some fn ∧ Stmt.blockNextOk isComputedNW pinsInverse fn.body = true ∧
      ∀ g ∈ Stmt.blockCallees fn.body, armExactS g = true ∨ ExactFreeG g := by
  unfold armExactOk at h
  split at h
  · next fn hj =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true] at h
    obtain ⟨⟨⟨hn, hA⟩, hp⟩, hc⟩ := h
    refine ⟨fn, coreProgram_find?_at hj hn, hp, fun g hg ↦ ?_⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hc g hg)
    obtain ⟨hr, hnk⟩ := calleeIdx_root hA hk
    rcases hR k hr with hs | ⟨d, hd⟩
    · left
      rwa [exRootS, hnk, Option.getD_some] at hs
    · exact .inr ⟨d, k, calleeIdx_spec hk, hd⟩
  · exact absurd h Bool.false_ne_true

/-- **A valid node of an arm passing the check is exact at every node** when its window hints are exact and each
entered `armExactS` callee's predicate gives `Every` exact on its valid trees. -/
theorem armExact_every (hR : ExRootsOk) {name : String} {j : ℕ} (h : armExactOk name j = true) {rd : Reader} {σ : Val}
    {bufs : List ℕ} {ks : List Tree} {args rets : List E} {Ts : List (Memory.Tree → Prop)}
    (hv : (Memory.Tree.node name σ bufs ks).Valid coreProgram rd args rets)
    (hW : ∀ fn es vs, coreProgram.find? name = some fn → walk σ fn.body = .ret es vs →
      ∀ a, Ev.atom a ∈ es → isWinHint a = true → a.Exact rd σ)
    (hT : ∀ fn es vs, coreProgram.find? name = some fn → walk σ fn.body = .ret es vs →
      (calls es).length ≤ Ts.length ∧ KidsT (calls es) Ts ks ∧
      ∀ c T, (c, T) ∈ (calls es).zip Ts → c.taken = true → armExactS c.f = true → ∀ t : Memory.Tree, t.name = c.f →
        t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ) → T t → t.Every (ExactAt coreProgram rd)) :
    (Memory.Tree.node name σ bufs ks).Every (ExactAt coreProgram rd) := by
  obtain ⟨fn, hf, hp, hc⟩ := armExact_find hR h
  obtain ⟨fn', hf', -, es, vs, hw, -, hes, hkv⟩ := hv
  rw [hf] at hf'
  cases hf'
  obtain ⟨hlen, hK, hE⟩ := hT fn es vs hf hw
  refine Tree.every_node.mpr ⟨exactAt_of_walk hf hw (exact_of_pinned_except (p2 := isWinHint) hp hw hes
    (hW fn es vs hf hw)),
    everyKids_of_kidsT hkv hlen hK fun c T hcT ht t hn htv hTt => ?_⟩
  have hcal : c.f ∈ Stmt.blockCallees fn.body :=
    walk_callees (σ := σ) fn.body (by rw [hw]; exact (List.of_mem_zip hcT).1)
  rcases hc c.f hcal with hs | hfree
  · exact hE c T hcT ht hs t hn htv hTt
  · exact every_exact_of_free hfree htv hn rd

end
end LeanVM.Guest.B1.Arm
