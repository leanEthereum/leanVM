/-
  LeanVM.Guest.Memory.NoWitness

  A decidable check that a guest function has no witness hint in its subtree (`noWitness`), and the functions passing it form a call-closed set (`coreProgram_noWitIn`), so every valid tree of one pops nothing.
-/

module

public import LeanVM.Guest.Memory.PopsNil
public import LeanVM.Guest.Memory.CalleeIdx
public import LeanVM.Guest.B1.Common.Find

/-!
# Functions without witness hints

`noWitJ d j`: function `j`'s body has no witness hint, each of its callees has an index (`calleeIdx`), and each callee index (`Data.calleesJ j`, the generated table) is `j` itself (a loop's tail call) or passes `noWitJ (d - 1)`. `noWitness g j` adds that function `j` is named `g`; it is decided by the kernel per function (`by decide +kernel`), its cost the size of the function's subtree. `NoWitG` collects the functions passing it at some depth; it is call-closed (`coreProgram_noWitIn`), so a valid tree of such a function pops `[]` (`pops_nil_of_noWitness`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- **Function `j` and its callees, `d` calls deep, have no witness hint.** -/
noncomputable def noWitJ : ℕ → ℕ → Bool
  | 0, _ => false
  | d + 1, j => match coreProgram[j]? with
    | none => false
    | some fn => Stmt.noWitList fn.body && (Stmt.blockCallees fn.body).all (fun g => (calleeIdx j g).isSome) &&
        (Data.calleesJ j).all fun k => k == j || noWitJ d k

/-- **The check**: function `j` is named `g`, and no witness hint is in its subtree. -/
noncomputable def noWitness (g : String) (j : ℕ) : Bool :=
  decide ((coreProgram[j]?).map Fn.name = some g) && noWitJ 8 j

/-- The functions passing the check at some depth. -/
def NoWitG (g : String) : Prop := ∃ d j, (coreProgram[j]?).map Fn.name = some g ∧ noWitJ d j = true

theorem noWitG_of {g : String} {j : ℕ} (h : noWitness g j = true) : NoWitG g := by
  simp only [noWitness, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨8, j, h.1, h.2⟩

/-- **The functions passing the check are call-closed and have no witness hint.** -/
theorem coreProgram_noWitIn : coreProgram.NoWitIn NoWitG := by
  rintro f ⟨d, j, hn, hj⟩ fn hf
  cases d with
  | zero => simp [noWitJ] at hj
  | succ d =>
    obtain ⟨fn', hfn', rfl⟩ := Option.map_eq_some_iff.mp hn
    have e : fn = fn' := Option.some.inj (hf.symm.trans (coreProgram_find?_at hfn'))
    subst e
    have hj' := hj
    rw [noWitJ, hfn'] at hj'
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hj'
    obtain ⟨⟨hb, hcal⟩, hks⟩ := hj'
    refine ⟨hb, fun g hg => ?_⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hcal g hg)
    have hs := calleeIdx_spec hk
    rcases hks k (List.mem_of_find?_eq_some hk) with rfl | h
    · exact ⟨d + 1, k, hs, hj⟩
    · exact ⟨d, k, hs, h⟩

/-- **A valid tree of a function passing the check pops nothing**, on any memory. -/
theorem pops_nil_of_noWitness {rd : Reader} {g : String} (hg : NoWitG g) {t : Tree} {args rets : List E}
    (hv : t.Valid coreProgram rd args rets) (hn : t.name = g) (rd' : Reader) : t.pops coreProgram rd' = [] :=
  pops_nil_of_noWitIn coreProgram_noWitIn t hv (hn ▸ hg)

end
end LeanVM.Guest.Memory
