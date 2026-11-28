/-
  LeanVM.Guest.Budget.HandSame

  `SameOnPath` from a block both valuations walk as they walk the function's body, and on whose
  values they agree: a hand function's virtual parameters off its path are then free.
-/

module

public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.Memory.Retemp

/-!
# Re-valuing off the path

`sameOnPath_of_block`: if `σ` and `σ'` agree on `f`'s parameters, each walks `f`'s body as it walks
a block `b`, and they agree on `b`'s values and temporaries, then `σ'` runs `f`'s path as `σ` does
(`SameOnPath`). `b` is the body with the arms not taken emptied (`walk_ite_zero`, `walk_ite_ne`),
so a value named only there may change.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {σ σ' : Val}

/-- An event's check depends only on the values it names. -/
theorem ev_holds_congr {rd : Reader} {e : Ev} (h : ∀ v ∈ e.uses ++ e.tmps, σ' v = σ v) :
    e.Holds rd σ' ↔ e.Holds rd σ := by
  cases e with
  | atom a => exact atom_holds_congr a h
  | inK c => simp only [Ev.Holds, h c (by simp [Ev.uses])]
  | call _ _ _ => exact Iff.rfl
  | skip _ _ => exact Iff.rfl

/-- An event's allocation depends only on the values it names. -/
theorem ev_alloc_congr {e : Ev} (h : ∀ v ∈ e.uses, σ' v = σ v) : Ev.alloc? σ' e = Ev.alloc? σ e := by
  rcases e with a | _ | _ | _
  · cases a with
    | hint hh =>
        cases hh with
        | allocDyn d s => simp only [Ev.alloc?, h s (by simp [Ev.uses, atomUses, hintUses])]
        | _ => rfl
    | _ => rfl
  all_goals rfl

/-- **`σ'` runs `f`'s path as `σ` does** when they agree on its parameters, each walks its body as
it walks `b`, and they agree on `b`'s values and temporaries. -/
theorem sameOnPath_of_block {P : Core.Program} {f : String} {b : List Stmt}
    (hb : ∀ fn, P.find? f = some fn → fn.params.map σ' = fn.params.map σ ∧
      walk σ fn.body = walk σ b ∧ walk σ' fn.body = walk σ' b)
    (hag : ∀ v ∈ Stmt.usesList b ++ Stmt.tmpsList b, σ' v = σ v) : SameOnPath P f σ σ' := by
  intro fn hfn
  obtain ⟨hp, hw, hw'⟩ := hb fn hfn
  have hu : ∀ v ∈ Stmt.usesList b, σ' v = σ v := fun v hv => hag v (List.mem_append_left _ hv)
  have heq : walk σ' b = walk σ b := walk_congr b hu
  refine ⟨hp, fun es vs hr => ?_⟩
  rw [hw] at hr
  have hwin := walk_within (σ := σ) b
  rw [hr] at hwin
  obtain ⟨h1, h2, h3⟩ := hwin
  have hev : ∀ e ∈ es, ∀ v ∈ e.uses ++ e.tmps, σ' v = σ v := by
    intro e he v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hu v (h1 e he v hv)
    · exact hag v (List.mem_append_right _ (h2.subset (List.mem_flatMap.mpr ⟨e, he, hv⟩)))
  refine ⟨by rw [hw', heq, hr], List.map_congr_left fun v hv => hu v (h3 v hv),
    fun rd e he hh => (ev_holds_congr (hev e he)).mpr hh, ?_, ?_⟩
  · intro c hc
    obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
    have hu' := hev e he
    cases e with
    | call f' args rets =>
        simp only [Ev.call?, Option.some.injEq] at hce
        subst hce
        exact ⟨List.map_congr_left fun v hv => hu' v (by simp [Ev.uses, hv]),
          List.map_congr_left fun v hv => hu' v (by simp [Ev.uses, hv])⟩
    | skip f' args =>
        simp only [Ev.call?, Option.some.injEq] at hce
        subst hce
        exact ⟨List.map_congr_left fun v hv => hu' v (by simp [Ev.uses, hv]), rfl⟩
    | atom _ => simp [Ev.call?] at hce
    | inK _ => simp [Ev.call?] at hce
  · exact filterMap_congr' fun e he =>
      ev_alloc_congr fun v hv => hev e he v (List.mem_append_left _ hv)

/-- At `c = 0` an `if` walks as with its other arm emptied. -/
theorem walk_ite_zero {c : V} {z n n' : List Stmt} (hc : σ c = 0) :
    ∀ (pre post : List Stmt), walk σ (pre ++ .ite c z n :: post) = walk σ (pre ++ .ite c z n' :: post)
  | [], post => by simp only [List.nil_append, walk, walk1, hc, ↓reduceIte]
  | s :: pre, post => by simp only [List.cons_append, walk]; rw [walk_ite_zero hc pre post]

/-- At `c ≠ 0` an `if` walks as with its zero arm emptied. -/
theorem walk_ite_ne {c : V} {z z' n : List Stmt} (hc : σ c ≠ 0) :
    ∀ (pre post : List Stmt), walk σ (pre ++ .ite c z n :: post) = walk σ (pre ++ .ite c z' n :: post)
  | [], post => by simp only [List.nil_append, walk, walk1, hc, ↓reduceIte]
  | s :: pre, post => by simp only [List.cons_append, walk]; rw [walk_ite_ne hc pre post]

/-- `σ` with the values `S` set to `c`. -/
def setVals (σ : Val) (S : List V) (c : E) : Val := fun x => if x ∈ S then c else σ x

theorem setVals_of_not_mem {S : List V} {c : E} {v : V} (hv : v ∉ S) : setVals σ S c v = σ v := by
  simp only [setVals, hv, ↓reduceIte]

theorem setVals_of_mem {S : List V} {c : E} {v : V} (hv : v ∈ S) : setVals σ S c v = c := by
  simp only [setVals, hv, ↓reduceIte]

/-- **Setting values that `b` and the parameters do not name** keeps `f`'s path, when `σ` and the
re-valued `σ` walk `f`'s body as `b`. -/
theorem sameOnPath_setVals {P : Core.Program} {f : String} {b : List Stmt} {S : List V} {c : E}
    (hb : ∀ fn, P.find? f = some fn → fn.params.all (· ∉ S) = true ∧
      walk σ fn.body = walk σ b ∧ walk (setVals σ S c) fn.body = walk (setVals σ S c) b)
    (hS : (Stmt.usesList b ++ Stmt.tmpsList b).all (· ∉ S) = true) : SameOnPath P f σ (setVals σ S c) := by
  refine sameOnPath_of_block (b := b) (fun fn hfn => ?_) fun v hv => setVals_of_not_mem
    (by simpa using List.all_eq_true.mp hS v hv)
  obtain ⟨hp, hw, hw'⟩ := hb fn hfn
  exact ⟨List.map_congr_left fun v hv => setVals_of_not_mem (by simpa using List.all_eq_true.mp hp v hv), hw, hw'⟩

end
end LeanVM.Guest.Budget
