/-
  LeanVM.Guest.B1.Whir.DataSpec

  What the kernel checks of each size's core IR: `open_stacked__L{m}` is the template at the
  size's configuration.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Common.Find

/-!
# The sizes' core IR, as the templates

`OsData m`: the core IR holds `open_stacked__L{m}` with the parameters `0 .. 10` and the body
`osBody (osCfg m)`. `Whir/Data{m}.lean` prove it for the `ligNSizes` sizes by kernel evaluation
(`stmtsEqb_sound`), `Whir/DataAll.lean` collects them; the helpers' specializations are
`Whir/HelperData*.lean`'s. `scripts/whir-data` writes them.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The core IR holds the function `name` with the parameters `ps` and the body `body`. -/
def FnIs (name : String) (ps : List V) (body : List Stmt) : Prop :=
  ∃ fn, coreProgram.find? name = some fn ∧ fn.params = ps ∧ fn.body = body

/-- The parameters `0 .. n - 1`. -/
def osParams (n : Nat) : List V := (List.range n).map V.n

/-- **Size `m`'s core IR is its template.** -/
def OsData (m : Nat) : Prop :=
  FnIs ("open_stacked__L" ++ natStr m) (osParams 11) (osBody (osCfg m))

/-- **Size `m`'s body is its body at every rate's levels**: the body reads the levels' rate-free
columns alone (the rate's reach the dispatches' names only, through `OsCfg.lvAt`). -/
def OsRate (m : Nat) : Prop :=
  ∀ ri < ligNRates, osBody (osCfg m) = osBody (osCfgR m ri)

/-- Two lists agree from `o` on if they agree on the run of `n` from `o` (by `stmtsEqb`) and from
`o + n` on: the data's bodies are checked a run at a time, each run its own kernel evaluation. -/
theorem run_step {a b : List Stmt} (n o : Nat)
    (h : stmtsEqb ((a.drop o).take n) ((b.drop o).take n) = true)
    (h' : a.drop (o + n) = b.drop (o + n)) : a.drop o = b.drop o := by
  rw [← List.take_append_drop n (a.drop o), ← List.take_append_drop n (b.drop o),
    stmtsEqb_sound h, List.drop_drop, List.drop_drop, h']

/-- Two lists of at most `o` statements agree from `o` on. -/
theorem drop_end {a b : List Stmt} {o : Nat} (ha : a.length ≤ o) (hb : b.length ≤ o) :
    a.drop o = b.drop o := by
  rw [List.drop_eq_nil_of_le ha, List.drop_eq_nil_of_le hb]

end
end LeanVM.Guest.B1.Whir
