/-
  LeanVM.Guest.B1.VsC.Straight0

  Straight bodies complete with no words of their own (`CallCompletes0`).
-/

module

public import LeanVM.Guest.B1.VsC.Quiet
public import LeanVM.Guest.Complete.Call0

/-!
# Straight bodies, with no words of their own

`callCompletes_straight_ex` (`Quiet.lean`) in the form `CallCompletes0` (`Fwd.lean` has
`callCompletes0_straightRd`), which `callAtA_of_callCompletes0` (`Complete/TransferA.lean`) places: a straight
body's tree reads and writes no word of its own.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

/-- **A straight body with no witness hint completes on a valuation per memory**, given by an
existence, with no words of its own (`CallCompletes0`). -/
theorem callCompletes0_straight_ex {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    {Pre : Reader → Prop} (hfind : coreProgram.find? name = some fn)
    (hck : ((retOf fn.body).isSome && (atomsOf fn.body).all atomQuiet) = true)
    (h : ∀ rd, LowDef k rd → Pre rd → ∃ σ : Val, fn.params.map σ = args ∧
      (∀ vs, retOf fn.body = some vs → vs.map σ = rets) ∧
      ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ ∧ a.Exact rd σ) :
    CallCompletes0 k name args rets Pre PostQuiet := by
  simp only [Bool.and_eq_true] at hck
  obtain ⟨hr, hh⟩ := hck
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ ha
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha =>
    List.all_eq_true.mp hh a (mem_atomsOf' (hmem a (mem_of_mem_atomsOf ha)))
  let P : Reader → Val → Prop := fun rd σ => fn.params.map σ = args ∧
    (∀ vs, retOf fn.body = some vs → vs.map σ = rets) ∧
    ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ ∧ a.Exact rd σ
  refine callCompletes0_straightRd (fun rd => Classical.epsilon (P rd)) hfind hbody hss hq
    fun rd hl hP => ?_
  obtain ⟨hp, hv, ha⟩ := Classical.epsilon_spec (p := P rd) (h rd hl hP)
  exact ⟨hp, hv vs hr, fun a h' => ha a (hmem a h')⟩

end
end LeanVM.Guest.B1.VsC
