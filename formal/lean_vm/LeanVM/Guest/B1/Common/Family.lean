/-
  LeanVM.Guest.B1.Common.Family

  A family of core functions, one per specialization, checked against its template by one kernel
  evaluation (`coreRunB`, `idxs%`), and a run of functions found by name (`core_find`).
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.KernelLit

/-!
# Families of core functions

A guest function with a compile-time parameter becomes one core function per value,
`f__L{k}`. Their positions in `coreProgram` come from their stable names (`idxs% «f__L» lo hi`, the
list of `idx% «f__L{k}»`, `lo ≤ k < hi`), so no proof assumes they are adjacent. One kernel
evaluation of `coreRunB js name ok` reads each position's function once and compares its name
with `name i` and its parameters and body with the template (`ok i`); `coreRunB_find` then finds
each by its name (`coreProgram_find?_at`): no name is compared with another function's in the
kernel. `coreProgram_indexOf?_run` (`Common/Find.lean`) is the form for a statement that names the
positions `j0 + k` of a contiguous run and wants their `indexOf?`; a family checked against a
template uses `coreRunB`, which assumes no adjacency.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- The functions at positions `js` are, in order, named `name i` and pass `ok i`, `i` the
specialization's place in `js`. -/
noncomputable def coreRunB (js : List ℕ) (name : ℕ → String) (ok : ℕ → Fn → Bool) : Bool :=
  (List.range js.length).all fun i ↦
    (coreProgram[js.getD i 0]?).any fun f ↦ f.name == name i && ok i f

/-- `coreRunB` position by position: a check over large specializations can be one kernel
evaluation each (`interval_cases i <;> decide +kernel`), so that the kernel's cache holds one. -/
theorem coreRunB_iff {js : List ℕ} {name : ℕ → String} {ok : ℕ → Fn → Bool} :
    coreRunB js name ok = true ↔ ∀ i < js.length,
      (coreProgram[js.getD i 0]?).any (fun f ↦ f.name == name i && ok i f) = true := by
  simp only [coreRunB, List.all_eq_true, List.mem_range]

/-- **Each function a passing `coreRunB` checks is found by its name.** -/
theorem coreRunB_find {js : List ℕ} {name : ℕ → String} {ok : ℕ → Fn → Bool}
    (h : coreRunB js name ok = true) {i : ℕ} (hi : i < js.length) :
    ∃ f, coreProgram.find? (name i) = some f ∧ ok i f = true := by
  obtain ⟨f, hf, hok⟩ := (Option.any_eq_true _ _).mp (coreRunB_iff.mp h i hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact ⟨f, coreProgram_find?_at hf hok.1, hok.2⟩

/-- What a specialization's function is: parameters `ps`, body `body i`. -/
def shapeB (ps : List V) (body : ℕ → List Stmt) (i : ℕ) (f : Fn) : Bool :=
  f.params == ps && stmtsEqb f.body (body i)

/-- **Specialization `i` is found by its name, with parameters `ps` and body `body i`.** -/
theorem coreRunB_shape {js : List ℕ} {name : ℕ → String} {ps : List V} {body : ℕ → List Stmt}
    (h : coreRunB js name (shapeB ps body) = true) {i : ℕ} (hi : i < js.length) :
    ∃ f, coreProgram.find? (name i) = some f ∧ f.params = ps ∧ f.body = body i := by
  obtain ⟨f, hf, hok⟩ := coreRunB_find h hi
  simp only [shapeB, Bool.and_eq_true, beq_iff_eq] at hok
  exact ⟨f, hf, hok.1, stmtsEqb_sound hok.2⟩

end

/-! ## Positions by stable name -/

public meta section

open Lean Elab Term Meta

/-- `idxs% «f__L» lo hi`: the list of `idx% «f__L{k}»`, `lo ≤ k < hi`, the positions in
`coreProgram` of a family's specializations by their stable names. -/
elab:max "idxs% " s:ident lo:num hi:num : term => do
  let js ← (List.range' lo.getNat (hi.getNat - lo.getNat)).mapM fun k ↦
    CoreRef.valueOf `I (mkIdentFrom s (s.getId.appendAfter (toString k)))
  mkListLit (mkConst ``Nat) js

/-- `core_find «f₁» … «fₙ»`: for each stable name `f`, the theorem `find_f` (`f` with `__` read
as `_`) that `coreProgram` finds `fn% f` under its name `"f"`, from the private `pos_f`,
`coreProgram[idx% f]? = some fn% f`, which only the kernel checks (`kernel_rfl`). -/
macro "core_find " fs:ident+ : command => do
  let cmds ← fs.flatMapM fun f ↦ do
    let f : Ident := ⟨f⟩
    let s := f.getId.toString (escape := false)
    let base := s.replace "__" "_"
    let thm := mkIdentFrom f (.mkSimple ("find_" ++ base))
    let pos := mkIdentFrom f (.mkSimple ("pos_" ++ base))
    return #[← `(command| private kernel_rfl $pos : coreProgram[idx% $f]? = some fn% $f),
      ← `(command| theorem $thm : coreProgram.find? $(quote s) = some fn% $f :=
        coreProgram_find?_at $pos)]
  return ⟨mkNullNode cmds⟩

end

end LeanVM.Guest.B1
