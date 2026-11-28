/-
  LeanVM.Guest.B1.VsC.Atoms

  A function whose body is atoms, none a hint, then a `ret`, completes on every memory where its
  atoms hold of a valuation chosen before the memory.
-/

module

public import LeanVM.Guest.Complete.Compose
public import LeanVM.Guest.Complete.Call0
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.B1.VsC.ChunkDC

/-!
# Straight bodies of atoms

`callCompletes_atoms`: a body `as.map .atom ++ [.ret vs]`, no atom a hint, at a valuation `σ`
taking the parameters to the arguments and `vs` to the returns, its atoms holding on every memory
where `Pre` holds: the call completes with no words of its own, its tree popping nothing, exact
(`PostQuiet`). The loads it makes read the caller's words, which `Pre` states.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete

@[expose] public section

/-- An atom is no hint. -/
def noHint : Atom → Bool
  | .hint _ => false
  | _ => true

theorem splice_atoms_quiet {rd : Reader} {σ : Val} :
    ∀ (as : List Atom), as.all noHint = true → ∀ ks, splice rd σ (as.map Ev.atom) ks = []
  | [], _, ks => by cases ks <;> rfl
  | a :: as, h, ks => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, splice]
    rw [splice_atoms_quiet as h.2 ks]
    cases a with
    | hint => simp [noHint] at h
    | _ => rfl

/-- **A straight body of atoms, no hint, completes quietly.** -/
theorem callCompletes_atoms {k : ℕ} {name : String} {fn : Fn} {as : List Atom} {vs : List V}
    {args rets : List E} {Pre : Reader → Prop} (σ : Val)
    (hfind : coreProgram.find? name = some fn) (hbody : fn.body = as.map Stmt.atom ++ [.ret vs])
    (hp : fn.params.map σ = args) (hr : vs.map σ = rets) (hq : as.all noHint = true)
    (hholds : ∀ rd, LowDef k rd → Pre rd → ∀ a ∈ as, a.Holds rd σ) :
    CallCompletes k name args rets Pre PostQuiet := by
  have hw : walk σ fn.body = .ret (as.map Ev.atom) vs := by rw [hbody]; exact walk_atoms σ as vs
  refine callCompletes_node fun b ↦ ⟨0, [], σ, fn, as.map Ev.atom, vs, [], wordsIn_nil b, hfind, hp,
    hw, hr, fun rd hl _ hP ↦ holds_atoms (hholds rd hl hP), ?_, ?_⟩
  · rw [calls_atoms]; show KidsCompl k σ _ [] []; rw [KidsCompl]; trivial
  · intro rd ts _ _ _ hv _
    have hts : ts = [] := by
      cases ts with
      | nil => rfl
      | cons t ts => rw [calls_atoms] at hv; simp [Tree.KidsValid] at hv
    subst hts
    refine ⟨?_, ?_⟩
    · rw [Tree.pops_node hfind hw]
      exact splice_atoms_quiet as hq _
    · rw [Tree.every_node]
      refine ⟨fun e he ↦ ?_, by rw [Tree.EveryKids]; trivial⟩
      have hev : Tree.events coreProgram (.node name σ [] []) = as.map Ev.atom := by
        simp only [Tree.events, Tree.name, Tree.val, hfind, hw]
      rw [hev] at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      have := List.all_eq_true.mp hq a ha
      cases a with
      | hint => simp [noHint] at this
      | _ => trivial

/-- **`callCompletes_atoms` with no words of its own.** -/
theorem callCompletes0_atoms {k : ℕ} {name : String} {fn : Fn} {as : List Atom} {vs : List V}
    {args rets : List E} {Pre : Reader → Prop} (σ : Val)
    (hfind : coreProgram.find? name = some fn) (hbody : fn.body = as.map Stmt.atom ++ [.ret vs])
    (hp : fn.params.map σ = args) (hr : vs.map σ = rets) (hq : as.all noHint = true)
    (hholds : ∀ rd, LowDef k rd → Pre rd → ∀ a ∈ as, a.Holds rd σ) :
    CallCompletes0 k name args rets Pre PostQuiet := by
  have hw : walk σ fn.body = .ret (as.map Ev.atom) vs := by rw [hbody]; exact walk_atoms σ as vs
  refine callCompletes0_node fun rd hl hP ↦ ⟨σ, fn, as.map Ev.atom, vs, [], hfind, hp, hw, hr,
    holds_atoms (hholds rd hl hP), ?_, by rw [Tree.BufsOkKids]; trivial, ?_⟩
  · rw [calls_atoms, Tree.KidsValid]; trivial
  · have hev : ∀ bufs, Tree.events coreProgram (.node name σ bufs []) = as.map Ev.atom := fun _ ↦ by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw]
    refine ⟨?_, ?_⟩
    · rw [Tree.pops_node hfind hw]
      exact splice_atoms_quiet as hq _
    · rw [Tree.every_node]
      refine ⟨fun e he ↦ ?_, by rw [Tree.EveryKids]; trivial⟩
      rw [hev] at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      have := List.all_eq_true.mp hq a ha
      cases a with
      | hint => simp [noHint] at this
      | _ => trivial

end
end LeanVM.Guest.B1.VsC
