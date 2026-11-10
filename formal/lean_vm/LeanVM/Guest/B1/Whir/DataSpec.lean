/-
  LeanVM.Guest.B1.Whir.DataSpec

  What the kernel checks of each size's core IR: `open_stacked__L{m}` is the template at the
  size's configuration.
-/

module

public import LeanVM.Guest.B1.Whir.Template

/-!
# The sizes' core IR, as the templates

`OsData m`: the core IR holds `open_stacked__L{m}` with the parameters `0 .. 9` and the body
`osBody (osCfg m)`. `Whir/Data{m}.lean` prove it for the 14 sizes by kernel evaluation
(`stmtsEqb_sound`), `Whir/DataAll.lean` collects them.
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
  FnIs ("open_stacked__L" ++ natStr m) (osParams 10) (osBody (osCfg m))

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
