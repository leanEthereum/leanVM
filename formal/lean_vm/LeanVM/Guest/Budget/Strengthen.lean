/-
  LeanVM.Guest.Budget.Strengthen

  A callee complete by a tree satisfying `T` is complete by one satisfying `T` and any property
  of all its valid trees at its arguments (a static weight or words bound).
-/

module

public import LeanVM.Guest.B1.Main.KidsT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **Strengthening by a property of every valid tree on the memories it runs on**: defined below
`2^k` and holding the caller's words `Lin` (a loop end read from `Lin` is pinned there). -/
theorem CompleteAtDT.and_valid_on {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T Q : Tree → Prop} (h : CompleteAtDT fs cert k f Lin args Out T)
    (hQ : ∀ (rd : Reader), LowDef k rd → MemL rd Lin → ∀ (t : Tree) (rets : List E), t.name = f →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → Q t) :
    CompleteAtDT fs cert k f Lin args Out fun t => T t ∧ Q t := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ⟨hn, hv, hb, hrest⟩, hT⟩ := hr rd hl hm
    ⟨t, ⟨hn, hv, hb, hrest⟩, hT, hQ rd hl (Main.memL_append.mp hm).2 t rets hn hv hb⟩⟩

end
end LeanVM.Guest.B1
