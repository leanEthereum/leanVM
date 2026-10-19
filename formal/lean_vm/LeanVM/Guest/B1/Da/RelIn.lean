/-
  LeanVM.Guest.B1.Da.RelIn

  `Program.RelIn` from `Program.Rel` by an invariant on call instances: every instance satisfying
  it loads from the region and passes it to the calls it enters.
-/

module

public import LeanVM.Guest.B1.Da.Atoms

/-!
# Load regions by an invariant

`relIn_of_inv`: if every instance of a function `f` on arguments `args` with `Inv f args`, along
the path its valuation walks, loads only from `R` and enters calls whose arguments satisfy `Inv`,
then `Inv f args` turns `Program.Rel` into `Program.RelIn R`. The invariant is the meaning's view
of the pointers, so a loop's iterations and its callees are covered by one induction on the call
depth.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

theorem mem_calls_taken {es : List Ev} {c : Call} (hc : c ∈ calls es) (ht : c.taken = true) :
    Ev.call c.f c.args c.rets ∈ es := by
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  cases e with
  | call f args rets => simp only [Ev.call?, Option.some.injEq] at hce; subst hce; exact he
  | skip f args => simp only [Ev.call?, Option.some.injEq] at hce; subst hce; simp at ht
  | atom _ => simp [Ev.call?] at hce
  | inK _ => simp [Ev.call?] at hce

/-- **`RelIn` by an invariant on instances.** -/
theorem relIn_of_inv {rd : Reader} {R : ℕ → Prop} (Inv : String → List E → Prop)
    (hinv : ∀ f args σ fn es vs, Inv f args → coreProgram.find? f = some fn → fn.params.map σ = args →
      walk σ fn.body = .ret es vs → (∀ e ∈ es, e.Ok (coreProgram.Rel rd) rd σ) →
      (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i) ∧
        ∀ c ∈ calls es, c.taken = true → Inv c.f (c.args.map σ)) :
    ∀ {f : String} {args rets : List E}, Inv f args → coreProgram.Rel rd f args rets →
      coreProgram.RelIn rd R f args rets := by
  intro f args rets hI hrel
  obtain ⟨n, hn⟩ := hrel
  induction n generalizing f args rets with
  | zero => exact hn.elim
  | succ n ih =>
    obtain ⟨fn, hf, σ, hp, hh⟩ := hn
    have hs := walk_sat (P := coreProgram) fn.body
      (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
    cases hw : walk σ fn.body with
    | fall es => rw [hw] at hs; exact hs.2.elim
    | stuck => rw [hw] at hs; exact hs.elim
    | ret es vs =>
      rw [hw] at hs
      obtain ⟨hok, hr⟩ := hs
      have hok' : ∀ e ∈ es, e.Ok (coreProgram.Rel rd) rd σ := fun e he =>
        ⟨(hok e he).1, fun g a r heq => relN_le_rel coreProgram n _ _ _ ((hok e he).2 g a r heq)⟩
      obtain ⟨hload, hcalls⟩ := hinv f args σ fn es vs hI hf hp hw hok'
      refine relIn_of_walk coreProgram_wf hf hp hw hr (fun e he => (hok e he).1) hload fun c hc ht => ?_
      exact ih (hcalls c hc ht) ((hok _ (mem_calls_taken hc ht)).2 c.f c.args c.rets rfl)

end
end LeanVM.Guest.B1.Digest
