/-
  LeanVM.Guest.Lift.RegD

  Leaf callees complete in the uniform placed form, on the regions they load: `CompleteRelRegD`,
  from a callee's `Rel`-level meaning and a kernel check of its body.
-/

module

public import LeanVM.Guest.Memory.LiftPure

/-!
# Leaf callees, placed on their regions

**The form.** `CompleteRelRegD fs cert k f Pre Reg`: for arguments whose loaded words lie in the
caller's words (`Reg args (RegionL Lin)`), and a precondition `Pre` on every memory defined below
`2^k` holding them, `f` is complete placed (`CompleteAtD`) returning `rets`. `RegPtrs spec`: for
each `(j, n) ∈ spec`, the `n` words from argument `j`'s pointer lie in the region.

**The lift** (`completeRelRegD_of_iff`): a function whose body is a leaf (atoms, branches, arms;
nothing placed) loading only `param j` at offsets below `n`, `(j, n) ∈ spec` (`specLoad`), its
parameters `.n 0, .n 1, …` at the spec's indices (`LeafSpecOk`, a kernel check: `leafSpecB`), and
whose relation is its meaning `Pre`, is `CompleteRelRegD … Pre (RegPtrs spec)`: its loads lie in
the caller's words, so `Lift.completeAtD_of_relIn` places it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.Lift (anyAtom)

@[expose] public section

/-- **Complete placed, on the regions the arguments' pointers load.** -/
def CompleteRelRegD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (Reg : List E → (ℕ → Prop) → Prop) : Prop :=
  ∀ args rets Lin, Reg args (RegionL Lin) → (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtD fs cert k f Lin args (Returns rets)

/-- The callee's loads: from argument `j`'s pointer, offsets below `n`, for each `(j, n) ∈ spec`. -/
def RegPtrs (spec : List (ℕ × ℕ)) (args : List E) (R : ℕ → Prop) : Prop :=
  ∀ p ∈ spec, ∀ t < p.2, ∃ i, (args.getD p.1 0).limb 0 * addressOfIndex t = addressOfIndex i ∧ R i

/-- A load of parameter `.n j` at an offset below `n`, `(j, n) ∈ spec`; no other load. -/
def specLoad (spec : List (ℕ × ℕ)) : Atom → Bool
  | .load _ p off => spec.any fun q => decide (p = .n q.1) && decide (off < q.2)
  | _ => true

/-- **The kernel's check of a callee**: found, its parameters `.n j` at the spec's indices, its body
a leaf loading as the spec says. -/
def LeafSpecOk (f : String) (spec : List (ℕ × ℕ)) : Prop :=
  ∃ fn, coreProgram.find? f = some fn ∧ (∀ q ∈ spec, fn.params[q.1]? = some (.n q.1)) ∧
    Lift.Stmt.leafOkList (specLoad spec) fn.body = true

theorem loads_spec {spec : List (ℕ × ℕ)} {σ : Val} {es : List Ev}
    (h : ∀ e ∈ es, Lift.EvLeafOk (specLoad spec) e) :
    ∀ A ∈ loadAddrs σ es, ∃ q ∈ spec, ∃ off < q.2, A = (σ (.n q.1)).limb 0 * addressOfIndex
        off := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      simp only [Lift.EvLeafOk, specLoad, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hok
      obtain ⟨q, hq, rfl, hoff⟩ := hok
      exact ⟨q, hq, off, hoff, hea.symm⟩
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A leaf callee whose relation is its meaning, placed on its regions.** -/
theorem completeRelRegD_of_iff {f : String} {spec : List (ℕ × ℕ)}
    {Pre : Reader → List E → List E → Prop} (hok : LeafSpecOk f spec)
    (hiff : ∀ rd args rets, coreProgram.Rel rd f args rets ↔ Pre rd args rets) (k : ℕ) :
    CompleteRelRegD fs cert k f Pre (RegPtrs spec) := by
  obtain ⟨fn, hf, hpar, hleaf⟩ := hok
  intro args rets Lin hreg hpre
  refine Lift.completeAtD_of_relIn (Lift.pureIn_of_leafOk hf hleaf) (List.mem_singleton_self _)
    fun rd hl hL => Lift.relIn_of_leaf hf hleaf (fun σ es vs hp hw A hA => ?_)
      ((hiff rd args rets).mpr (hpre rd hl hL))
  have hall := Lift.walk_leafOk (σ := σ) fn.body hleaf
  rw [hw] at hall
  obtain ⟨q, hq, off, hoff, rfl⟩ := loads_spec hall A hA
  have hσ : σ (.n q.1) = args.getD q.1 0 := by
    have h1 := hpar q hq
    have h2 : (fn.params.map σ)[q.1]? = args[q.1]? := by rw [hp]
    rw [List.getElem?_map, h1] at h2
    simp only [Option.map_some] at h2
    rw [List.getD_eq_getElem?_getD, ← h2]
    rfl
  rw [hσ]
  exact hreg q hq off hoff

/-! ## The kernel's check -/

/-- `LeafSpecOk`, decided. -/
noncomputable def leafSpecB (f : String) (spec : List (ℕ × ℕ)) : Bool :=
  match coreProgram.find? f with
  | some fn => (spec.all fun q => decide (fn.params[q.1]? = some (.n q.1))) &&
      Lift.Stmt.leafOkList (specLoad spec) fn.body
  | none => false

theorem leafSpecOk_of {f : String} {spec : List (ℕ × ℕ)} (h : leafSpecB f spec = true) :
    LeafSpecOk f spec := by
  unfold leafSpecB at h
  split at h
  · rename_i fn hf
    rw [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨fn, hf, fun q hq => of_decide_eq_true (h.1 q hq), h.2⟩
  · cases h

theorem leafSpecOk_all {names : List (String × ℕ)} {spec : ℕ → List (ℕ × ℕ)}
    (h : (names.all fun p => leafSpecB p.1 (spec p.2)) = true) :
    ∀ p ∈ names, LeafSpecOk p.1 (spec p.2) := fun p hp =>
  leafSpecOk_of (List.all_eq_true.mp h p hp)

end
end LeanVM.Guest.B1
