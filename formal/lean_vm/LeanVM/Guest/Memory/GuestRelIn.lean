/-
  LeanVM.Guest.Memory.GuestRelIn

  `Program.RelIn` of the guest from `Program.Rel` by an invariant on call instances: every instance
  satisfying it loads from the region and passes it to the calls it enters; with the words of the
  tree (`RelInT`).
-/

module

public import LeanVM.Guest.Memory.Restrict
public import LeanVM.Guest.Memory.GuestWf

/-!
# Load regions by an invariant

`relIn_of_inv`: if every instance of a function `f` on arguments `args` with `Inv f args`, along
the path its valuation walks, loads only from `R` and enters calls whose arguments satisfy `Inv`,
then `Inv f args` turns `Program.Rel` into `Program.RelIn R`. The invariant is the meaning's view
of the pointers, so a loop's iterations and its callees are covered by one induction on the call
depth. `relInT_of_inv` also gives the tree's words, by a function of the arguments.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

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

/-- The events of a path of a body that holds, hold. -/
theorem holds_of_holdsList {rd : Reader} {σ : Val} {f : String} {fn : Fn} {es : List Ev} {vs : List V}
    {kret : List E → Prop} (hf : coreProgram.find? f = some fn)
    (hh : Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False kret) (hw : walk σ fn.body = .ret es vs) :
    ∀ e ∈ es, e.Holds rd σ := by
  have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at this
  exact fun e he => (this.1 e he).1

/-! ## With the words of the tree -/

section Total
variable (fs : String → ℕ)

/-- **`Program.RelIn` by a tree of `n` words.** -/
def RelInT (rd : Reader) (R : ℕ → Prop) (n : ℕ) (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid coreProgram rd args rets ∧ t.BufsOk coreProgram ∧
    t.LoadsR coreProgram R ∧ t.total fs = n

/-- The words of the frames `cs` sets up: an entered call's by `Tot`, a skipped one's frame. -/
def callsTot (Tot : String → List E → ℕ) (σ : Val) (cs : List Call) : ℕ :=
  (cs.map fun c => if c.taken then Tot c.f (c.args.map σ) else fs c.f).sum

theorem kids_of_relInT {rd : Reader} {σ : Val} {R : ℕ → Prop} (Tot : String → List E → ℕ) :
    ∀ cs : List Call, (∀ c ∈ cs, c.taken = false → coreProgram.Takes c.f c.args.length = true) →
    (∀ c ∈ cs, c.taken = true → ∃ rets, c.rets.map σ = rets ∧
      RelInT fs rd R (Tot c.f (c.args.map σ)) c.f (c.args.map σ) rets) →
    ∃ ks, Tree.KidsValid coreProgram rd σ cs ks ∧ Tree.BufsOkKids coreProgram ks ∧
      Tree.LoadsRKids coreProgram R ks ∧ Tree.totalKids fs ks = callsTot fs Tot σ cs
  | [], _, _ => ⟨[], by simp [Tree.KidsValid], by rw [Tree.BufsOkKids]; trivial,
      by rw [Tree.LoadsRKids]; trivial, by simp [Tree.totalKids, callsTot]⟩
  | c :: cs, hw, hc => by
      obtain ⟨ks, hv, hb, hl, ht⟩ := kids_of_relInT Tot cs (fun c' h => hw c' (List.mem_cons_of_mem _ h))
        (fun c' h => hc c' (List.mem_cons_of_mem _ h))
      by_cases htk : c.taken = true
      · obtain ⟨rets, hrets, k, hn, hkv, hkb, hkl, hkt⟩ := hc c List.mem_cons_self htk
        refine ⟨k :: ks, ⟨hn, by rw [ite_eq_left htk, hrets]; exact hkv, hv⟩,
          by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, by rw [Tree.LoadsRKids]; exact ⟨hkl, hl⟩, ?_⟩
        rw [totalKids_cons, hkt, ht, callsTot, callsTot, List.map_cons, List.sum_cons, ite_eq_left htk]
      · obtain ⟨σ', hph⟩ := phantom_of_takes (P := coreProgram) (f := c.f) (ws := c.args.map σ)
          (by rw [List.length_map]; exact hw c List.mem_cons_self (by simpa using htk))
        refine ⟨.phantom c.f σ' :: ks, ⟨rfl, by rw [ite_eq_right htk]; exact ⟨⟨_, _, rfl⟩, hph⟩, hv⟩,
          by rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, hb⟩,
          by rw [Tree.LoadsRKids, Tree.LoadsR]; exact ⟨trivial, hl⟩, ?_⟩
        rw [totalKids_cons, ht, callsTot, callsTot, List.map_cons, List.sum_cons, ite_eq_right htk]
        rfl

/-- **`RelInT` by an invariant on instances**, the words by `Tot`: each instance's own frame,
`HeapBuf`s and its calls' words. -/
theorem relInT_of_inv {rd : Reader} {R : ℕ → Prop} (Inv : String → List E → Prop)
    (Tot : String → List E → ℕ)
    (hinv : ∀ f args σ fn es vs, Inv f args → coreProgram.find? f = some fn → fn.params.map σ = args →
      walk σ fn.body = .ret es vs → (∀ e ∈ es, e.Ok (coreProgram.Rel rd) rd σ) →
      (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i) ∧
        (∀ c ∈ calls es, c.taken = true → Inv c.f (c.args.map σ)) ∧
        Tot f args = fs f + callsTot fs Tot σ (calls es) + (allocs σ es).sum) :
    ∀ {f : String} {args rets : List E}, Inv f args → coreProgram.Rel rd f args rets →
      RelInT fs rd R (Tot f args) f args rets := by
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
      obtain ⟨hload, hcalls, htot⟩ := hinv f args σ fn es vs hI hf hp hw hok'
      obtain ⟨ks, hkv, hkb, hkl, hkt⟩ := kids_of_relInT fs Tot (calls es)
        (takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw)
        (fun c hc ht => ⟨_, rfl, ih (hcalls c hc ht) ((hok _ (mem_calls_taken hc ht)).2 c.f c.args c.rets rfl)⟩)
      refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, fun e he => (hok e he).1, hkv⟩,
        ?_, ?_, ?_⟩
      · rw [Tree.BufsOk, events_node hf hw]
        exact ⟨rfl, hkb⟩
      · rw [Tree.LoadsR, events_node hf hw]
        exact ⟨hload, hkl⟩
      · rw [total_node, hkt, htot]

variable {fs}

theorem RelInT.relIn {rd : Reader} {R : ℕ → Prop} {n : ℕ} {f : String} {args rets : List E}
    (h : RelInT fs rd R n f args rets) : coreProgram.RelIn rd R f args rets :=
  let ⟨t, hn, hv, hb, hl, _⟩ := h
  ⟨t, hn, hv, hb, hl⟩

/-- **A pure function's `RelInT` is placed anywhere**, of the same words. -/
theorem relAtIn_of_relInT_pure (cert : String → V → ℕ) {S : List String} (hS : coreProgram.PureIn S)
    {rd : Reader} {R : ℕ → Prop} {n : ℕ} {g : String} (hg : g ∈ S) {args rets : List E}
    (h : RelInT fs rd R n g args rets) :
    ∀ fp, RelAtIn coreProgram fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb, hl, ht⟩ := h
  exact fun fp => ⟨t, hn, hv, hb, placed_of_pure hS t hv hb (hn ▸ hg) fp, ht,
    loadsIn_of_loadsR t R fp hl, fun _ h => h.elim⟩

end Total

end
end LeanVM.Guest.Memory
