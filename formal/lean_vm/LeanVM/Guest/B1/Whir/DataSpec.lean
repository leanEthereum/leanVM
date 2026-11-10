/-
  LeanVM.Guest.B1.Whir.DataSpec

  What the kernel checks of each candidate's core IR: `open_stacked__L{m}` and its loop helpers
  are the templates at the candidate's configuration.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreData

/-!
# The candidates' core IR, as the templates

`OsData m`: the core IR holds `open_stacked__L{m}` with the parameters `0 .. 9` and the body
`osBody (osCfg m)`, each level's squeeze loop and each non-final level's residual loop with their
templates. `Whir/Data{0..27}.lean` prove it for the 28 candidates by kernel evaluation
(`stmtsEqb_sound`), `Whir/DataAll.lean` collects them; `scripts/whir-data` writes them.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The core IR holds the function `name` with the parameters `ps` and the body `body`. -/
def FnIs (name : String) (ps : List V) (body : List Stmt) : Prop :=
  ∃ fn, coreProgram.find? name = some fn ∧ fn.params = ps ∧ fn.body = body

/-- The parameters `0 .. n - 1`. -/
def osParams (n : Nat) : List V := (List.range n).map V.n

/-- **Candidate `m`'s core IR is its template**, with its loop helpers'. -/
def OsData (m : Nat) : Prop :=
  FnIs ("open_stacked__L" ++ natStr m) (osParams 10) (osBody (osCfg m)) ∧
    (∀ lvl < (osCfg m).levels.length,
      FnIs ((osCfg m).sqLoop lvl) (osParams 6) (sqLoopBody (osLv m lvl) ((osCfg m).sqLoop lvl))) ∧
    ∀ lvl < (osCfg m).yrLevel,
      FnIs ((osCfg m).resLoop lvl) (osParams 7) (resLoopBody lvl (osLv m lvl) ((osCfg m).resLoop lvl))

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
