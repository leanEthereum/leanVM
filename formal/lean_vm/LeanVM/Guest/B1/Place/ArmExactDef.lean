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
public import LeanVM.Guest.B1.Place.FreeMaskData

/-!
# The arms' exactness check

* `armExactS g`: `g` is `is_zero` or an entry of `lpTable`: the callees whose exactness the arm's composition carries;
* `isWinHint`: a `windowsExp` hint, as the inlined grind checks (`gcInlineT`) write, pinned by no next atom: their
  exactness comes from the honest valuation (`Whir.WinEx`, from `gcInline_exact_of_vals`), not from the check;
* `armExactOk name j`: function `j` is named `name`, its computed hints but the window hints are pinned by the next atom, and each of its
  callees is one of the arms' (its bit in `armCalleeMask`), decided by the kernel per arm (`ArmExact0` to `ArmExact5`, `ArmExactB`, `ArmExactC`);
* `armExact_find`: the arms' callees being `armExactS` or exact for free (`ArmExactNeedOk`, decided once), such a
  function's callees not `armExactS` are exact for free;
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

/-- **Function `j`, named `name`, has its computed hints but the window hints pinned by the next atom and calls
`armExactS` functions or functions exact for free.** -/
noncomputable def armExactOk (name : String) (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => fn.name == name && Stmt.blockNextOk isComputedNW pinsInverse fn.body &&
      (Stmt.blockCallees fn.body).all (maskCallee armCalleeMask j)
  | none => false

/-- The arms' callees' facts the exactness check reads, decided once (`Place/FreeExactOk`, `Place/FreeLp`). -/
def ArmExactNeedOk : Prop :=
  (∀ k ∈ armExactNeed, exactJ 8 k = true) ∧ ∀ k ∈ armLpNeed, (Data.nameT.find k).all armExactS = true

theorem armExact_find (hN : ArmExactNeedOk) {name : String} {j : ℕ} (h : armExactOk name j = true) :
    ∃ fn, coreProgram.find? name = some fn ∧ Stmt.blockNextOk isComputedNW pinsInverse fn.body = true ∧
      ∀ g ∈ Stmt.blockCallees fn.body, armExactS g = true ∨ ExactFreeG g := by
  unfold armExactOk at h
  split at h
  · next fn hj =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hn, hp⟩, hc⟩ := h
    refine ⟨fn, coreProgram_find?_at hj hn, hp, fun g hg ↦ ?_⟩
    obtain ⟨k, hk, hk', hg'⟩ := maskCallee_mem armCalleeMask_exact (hc g hg)
    rcases List.mem_append.mp hk with hk | hk
    · exact .inr ⟨8, k, hk', hN.1 k hk⟩
    · exact .inl (by simpa [hg'] using hN.2 k hk)
  · exact absurd h Bool.false_ne_true

/-- **A valid node of an arm passing the check is exact at every node** when its window hints are exact and each
entered `armExactS` callee's predicate gives `Every` exact on its valid trees. -/
theorem armExact_every (hN : ArmExactNeedOk) {name : String} {j : ℕ} (h : armExactOk name j = true)
    {rd : Reader} {σ : Val}
    {bufs : List ℕ} {ks : List Tree} {args rets : List E} {Ts : List (Memory.Tree → Prop)}
    (hv : (Memory.Tree.node name σ bufs ks).Valid coreProgram rd args rets)
    (hW : ∀ fn es vs, coreProgram.find? name = some fn → walk σ fn.body = .ret es vs →
      ∀ a, Ev.atom a ∈ es → isWinHint a = true → a.Exact rd σ)
    (hT : ∀ fn es vs, coreProgram.find? name = some fn → walk σ fn.body = .ret es vs →
      (calls es).length ≤ Ts.length ∧ KidsT (calls es) Ts ks ∧
      ∀ c T, (c, T) ∈ (calls es).zip Ts → c.taken = true → armExactS c.f = true → ∀ t : Memory.Tree, t.name = c.f →
        t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ) → T t → t.Every (ExactAt coreProgram rd)) :
    (Memory.Tree.node name σ bufs ks).Every (ExactAt coreProgram rd) := by
  obtain ⟨fn, hf, hp, hc⟩ := armExact_find hN h
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
