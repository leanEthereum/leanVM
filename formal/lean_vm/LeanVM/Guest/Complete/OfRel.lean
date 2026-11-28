module

public import LeanVM.Guest.Complete.Compose
public import LeanVM.Guest.Memory.PopsNil
public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.Pack.P27.Core

/-!
# Layout-free completeness from the core IR's relation

The archive's completeness theorems end in `coreProgram.Rel rd f args rets`; on a well-formed
program a derivation is a valid tree (`Program.Rel.tree`), so a call whose relation holds on every
memory holding its words completes (`callCompletes_of_rel`). A function with no witness hint in
its subtree pops nothing (`pops_nil_of_noWitIn`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.B1

@[expose] public section

/-- **A call completes when its relation holds** on every memory holding its words and inputs, its
predicate holding of every valid tree. -/
theorem callCompletes_of_rel (hwf : coreProgram.Wf) {k : ℕ} {f : String} {args rets : List E}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    (h : ∀ b, ∃ (n : ℕ) (W : Words), WordsIn W b n ∧ ∀ rd, LowDef k rd → HoldsWords rd W → Pre rd →
      coreProgram.Rel rd f args rets ∧
        ∀ t : Tree, t.name = f → t.Valid coreProgram rd args rets → t.BufsOk coreProgram → Post rd t) :
    CallCompletes k f args rets Pre Post := by
  intro b
  obtain ⟨n, W, hW, hR⟩ := h b
  refine ⟨n, W, hW, fun rd hl hw hp => ?_⟩
  obtain ⟨hr, hpost⟩ := hR rd hl hw hp
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree hwf hr
  exact ⟨t, hn, hv, hb, hpost t hn hv hb⟩

end
end LeanVM.Guest.Complete
