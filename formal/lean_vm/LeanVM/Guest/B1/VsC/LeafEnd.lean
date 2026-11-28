/-
  LeanVM.Guest.B1.VsC.LeafEnd

  A leaf callee placed, its end kept: it ends at its cursor.
-/

module

public import LeanVM.Guest.Complete.TransferA

/-!
# Leaves ending at their cursor

`CallCompletesA` forgets where a callee ends (`∃ e`). `verify_sub`'s oracle holds words that depend on its
callees' cursor (`certify_stack`'s pointers into its own words, `open_stacked`'s buffers), so its windows
pin each callee's end. A leaf ends at its cursor (`block_endA_leaf`): `LeafAtA` keeps that end,
`LeafAtA.completesA` forgets it, `leafAtA_of_callCompletes0_leaf` is `callCompletesA_of_callCompletes0_leaf`
with its end.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Complete

@[expose] public section

/-- **A leaf completes placed at its cursor**: block its frame, ending where it starts, claiming no data. -/
def LeafAtA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (args rets : List E) (R : ℕ → Prop) (Out Pre : Reader → Prop) (Post : Reader → Tree → Prop) : Prop :=
  ∀ fp c, fp + fs f ≤ c → CallAtA fs al cert k f args rets R (fun _ => False) Out Pre Post (fs f) fp c c

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem LeafAtA.completesA {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} (h : LeafAtA fs al cert k f args rets R Out Pre Post) :
    CallCompletesA fs al cert k f args rets R (fun _ _ _ => False) Out Pre Post :=
  ⟨fs f, fun fp c hc => ⟨c, h fp c hc⟩⟩

/-- **A pure leaf placed at its cursor** from its layout-free completeness. -/
theorem leafAtA_of_callCompletes0_leaf {S : List String} (hS : coreProgram.PureIn S) {k : ℕ}
    {f : String} (hf : f ∈ S) (hlp : coreProgram.loop f = false)
    (hnc : ∀ fn σ es vs, coreProgram.find? f = some fn → walk σ fn.body = .ret es vs → calls es = [])
    {args rets : List E} {R : ℕ → Prop} {Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    (h : CallCompletes0 k f args rets Pre Post)
    (hR : ∀ rd t, LowDef k rd → Pre rd → t.name = f → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      Post rd t → t.LoadsR coreProgram R ∧ t.HintsR coreProgram R) :
    LeafAtA fs al cert k f args rets R (fun _ => True) Pre Post :=
  fun _ c _ => callAtA_of_callCompletes0 hS hf le_rfl h fun rd t hl hp hn hv hb hq =>
    let hbe := block_endA_leaf (al := al) hS hf hlp hnc hn hv hb c
    ⟨hbe.1, hbe.2, hR rd t hl hp hn hv hb hq⟩

end

end
end LeanVM.Guest.B1.VsC
