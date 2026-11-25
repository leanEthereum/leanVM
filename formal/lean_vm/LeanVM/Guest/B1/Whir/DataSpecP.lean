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
`Whir/Data{m}.lean` (a definitional equality the kernel checks) and `Whir/HelperData*.lean` (by
kernel evaluation) prove them from the functions' own modules (`Guest/Fn/<key>/Core.lean`), for
every `P` that finds them (`Finds`); `Whir/DataSpec.lean` states them for the guest.
`scripts/whir-data` writes the data.
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

end
end LeanVM.Guest.B1.Whir
