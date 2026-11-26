/-
  LeanVM.Guest.B1.Whir.DataSpecP

  What the kernel checks of one function's core IR, for any program that finds it: the function
  is a template's instance.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Common.Basic

/-!
# A function's core IR, as a template

`FnIsP P name ps body`: the program `P` holds the function `name` with the parameters `ps` and
the body `body`; `OsDataP P m`: it holds `open_stacked__L{m}` as the template at size `m`.
`Whir/Data{m}.lean` and `Whir/HelperData*.lean` prove them by kernel evaluation of the functions'
own modules (`Guest/Fn/<key>/Core.lean`), for every `P` that finds them (`Finds`);
`Whir/DataSpec.lean` states them for the guest. `scripts/whir-data` writes the data.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The program `P` holds the function `name` with the parameters `ps` and the body `body`. -/
def FnIsP (P : Program) (name : String) (ps : List V) (body : List Stmt) : Prop :=
  ∃ fn, P.find? name = some fn ∧ fn.params = ps ∧ fn.body = body

/-- The parameters `0 .. n - 1`. -/
def osParams (n : Nat) : List V := (List.range n).map V.n

/-- **Size `m`'s function is its template.** -/
def OsDataP (P : Program) (m : Nat) : Prop :=
  FnIsP P ("open_stacked__L" ++ natStr m) (osParams 11) (osBody (osCfg m))

/-- A function found under `name`, with the parameters `ps` and the body `body`. -/
theorem fnIsP_of (P : Program) (name : String) (fn : Fn) [Finds P name fn] {n : String}
    {ps : List V} {body : List Stmt} (hp : fn.params = ps) (hb : fn.body = body)
    (hn : name = n := by rfl) : FnIsP P n ps body :=
  hn ▸ ⟨fn, Finds.find, hp, hb⟩

/-- Two lists agree from `o` on if they agree on the run of `n` from `o` (by `stmtsEqb`) and from
`o + n` on: the data's bodies are checked a run at a time, each run its own kernel evaluation. -/
theorem run_step {a b : List Stmt} (n o : Nat)
    (h : stmtsEqb ((a.drop o).take n) ((b.drop o).take n) = true)
    (h' : a.drop (o + n) = b.drop (o + n)) : a.drop o = b.drop o := by
  rw [← List.take_append_drop n (a.drop o), ← List.take_append_drop n (b.drop o),
    stmtsEqb_sound h, List.drop_drop, List.drop_drop, h']

end
end LeanVM.Guest.B1.Whir
