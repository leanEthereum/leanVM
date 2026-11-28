module

public import LeanVM.Guest.Complete.OfRel
public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Memory.NoWitness

/-!
# Callees complete from their relation

A function whose subtree has no witness hint (`NoWitG`) and every computed hint pinned locally
(`ExactFreeG`) completes wherever its relation holds, popping nothing, every node exact
(`callCompletes_free`): any valid tree of it is exact (`every_exact_of_free`) and pops nothing
(`pops_nil_of_noWitness`). Such callees take no words of their own.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

/-- What a callee without witness hints, exact for free, gives: no pops, every node exact. -/
def FreePost (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = [] ∧ t.Every (ExactAt coreProgram rd)

/-- **A callee without witness hints, exact for free, completes where its relation holds.** -/
theorem callCompletes_free (hwf : coreProgram.Wf) {k : ℕ} {f : String} (hw : NoWitG f) (hx : ExactFreeG f) {args rets : List E} {Pre : Reader → Prop}
    (h : ∀ rd, LowDef k rd → Pre rd → coreProgram.Rel rd f args rets) :
    CallCompletes k f args rets Pre FreePost :=
  callCompletes_of_rel hwf fun b => ⟨0, [], wordsIn_nil b, fun rd hl _ hp =>
    ⟨h rd hl hp, fun _t hn hv _ => ⟨pops_nil_of_noWitness hw hv hn rd, every_exact_of_free hx hv hn rd⟩⟩⟩

end
end LeanVM.Guest.Complete
