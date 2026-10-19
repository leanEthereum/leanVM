/-
  LeanVM.Guest.B1.Da.WeightIn

  `RelInT` within weights: the tree a `Rel` proof builds weighs, at every frame weight `θ`, at
  most the words its frame sizes would give at `θ`.
-/

module

public import LeanVM.Guest.B1.Da.RelIn
public import LeanVM.Guest.B1.Main.WeightAt

/-!
# Trees of known words, within weights

`RelInTW fs rd R n f args rets W`: `RelInT` by a tree weighing at most `W θ` at every `θ`.
`relInTW_of_inv`: `relInT_of_inv` with the words given at every frame function, `Tot θ`; the tree
it builds has `Tot fs` words and weighs at most `Tot θ` at `θ`, a skipped call's frame and the
`HeapBuf`s weighing nothing. `relAtInW_of_relInTW_pure`: a pure function's, placed anywhere, as
`RelAtInW` at the weights `id`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Guest.B1.Main (RelAtInW)

@[expose] public section

/-- The weights at every frame function. -/
abbrev wId : (String → ℕ) → String → ℕ := fun θ => θ

variable (fs : String → ℕ)

/-- **`RelInT` within weights.** -/
def RelInTW (rd : Reader) (R : ℕ → Prop) (n : ℕ) (f : String) (args rets : List E)
    (W : (String → ℕ) → ℕ) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid coreProgram rd args rets ∧ t.BufsOk coreProgram ∧
    t.LoadsR coreProgram R ∧ t.total fs = n ∧ ∀ θ, t.weight θ ≤ W θ

theorem kids_of_relInTW {rd : Reader} {σ : Val} {R : ℕ → Prop} (Tot : (String → ℕ) → String → List E → ℕ) :
    ∀ cs : List Call, (∀ c ∈ cs, c.taken = false → coreProgram.Takes c.f c.args.length = true) →
    (∀ c ∈ cs, c.taken = true → ∃ rets, c.rets.map σ = rets ∧
      RelInTW fs rd R (Tot fs c.f (c.args.map σ)) c.f (c.args.map σ) rets fun θ => Tot θ c.f (c.args.map σ)) →
    ∃ ks, Tree.KidsValid coreProgram rd σ cs ks ∧ Tree.BufsOkKids coreProgram ks ∧
      Tree.LoadsRKids coreProgram R ks ∧ Tree.totalKids fs ks = callsTot fs (Tot fs) σ cs ∧
      ∀ θ, Tree.weightKids θ ks ≤ callsTot θ (Tot θ) σ cs
  | [], _, _ => ⟨[], by simp [Tree.KidsValid], by rw [Tree.BufsOkKids]; trivial,
      by rw [Tree.LoadsRKids]; trivial, by simp [Tree.totalKids, callsTot],
      fun θ => by simp [Tree.weightKids, callsTot]⟩
  | c :: cs, hw, hc => by
      obtain ⟨ks, hv, hb, hl, ht, hwt⟩ := kids_of_relInTW Tot cs (fun c' h => hw c' (List.mem_cons_of_mem _ h))
        (fun c' h => hc c' (List.mem_cons_of_mem _ h))
      by_cases htk : c.taken = true
      · obtain ⟨rets, hrets, k, hn, hkv, hkb, hkl, hkt, hkw⟩ := hc c List.mem_cons_self htk
        refine ⟨k :: ks, ⟨hn, by rw [ite_eq_left htk, hrets]; exact hkv, hv⟩,
          by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, by rw [Tree.LoadsRKids]; exact ⟨hkl, hl⟩, ?_, fun θ => ?_⟩
        · rw [totalKids_cons, hkt, ht, callsTot, callsTot, List.map_cons, List.sum_cons, ite_eq_left htk]
        · have := hwt θ
          have := hkw θ
          simp only [Tree.weightKids, callsTot, List.map_cons, List.sum_cons, ite_eq_left htk] at *
          omega
      · obtain ⟨σ', hph⟩ := phantom_of_takes (P := coreProgram) (f := c.f) (ws := c.args.map σ)
          (by rw [List.length_map]; exact hw c List.mem_cons_self (by simpa using htk))
        refine ⟨.phantom c.f σ' :: ks, ⟨rfl, by rw [ite_eq_right htk]; exact ⟨⟨_, _, rfl⟩, hph⟩, hv⟩,
          by rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, hb⟩,
          by rw [Tree.LoadsRKids, Tree.LoadsR]; exact ⟨trivial, hl⟩, ?_, fun θ => ?_⟩
        · rw [totalKids_cons, ht, callsTot, callsTot, List.map_cons, List.sum_cons, ite_eq_right htk]
          rfl
        · have := hwt θ
          simp only [Tree.weightKids, Tree.weight, callsTot, List.map_cons, List.sum_cons, ite_eq_right htk] at *
          omega

/-- **`RelInTW` by an invariant on instances**, the words at every frame function by `Tot`. -/
theorem relInTW_of_inv {rd : Reader} {R : ℕ → Prop} (Inv : String → List E → Prop)
    (Tot : (String → ℕ) → String → List E → ℕ)
    (hinv : ∀ f args σ fn es vs, Inv f args → coreProgram.find? f = some fn → fn.params.map σ = args →
      walk σ fn.body = .ret es vs → (∀ e ∈ es, e.Ok (coreProgram.Rel rd) rd σ) →
      (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i) ∧
        (∀ c ∈ calls es, c.taken = true → Inv c.f (c.args.map σ)) ∧
        ∀ θ, Tot θ f args = θ f + callsTot θ (Tot θ) σ (calls es) + (allocs σ es).sum) :
    ∀ {f : String} {args rets : List E}, Inv f args → coreProgram.Rel rd f args rets →
      RelInTW fs rd R (Tot fs f args) f args rets fun θ => Tot θ f args := by
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
      obtain ⟨ks, hkv, hkb, hkl, hkt, hkw⟩ := kids_of_relInTW fs Tot (calls es)
        (takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw)
        (fun c hc ht => ⟨_, rfl, ih (hcalls c hc ht) ((hok _ (mem_calls_taken hc ht)).2 c.f c.args c.rets rfl)⟩)
      refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, fun e he => (hok e he).1, hkv⟩,
        ?_, ?_, ?_, fun θ => ?_⟩
      · rw [Tree.BufsOk, events_node hf hw]
        exact ⟨rfl, hkb⟩
      · rw [Tree.LoadsR, events_node hf hw]
        exact ⟨hload, hkl⟩
      · rw [total_node, hkt, htot fs]
      · show Tree.weight θ (Memory.Tree.node f σ (allocs σ es) ks) ≤ Tot θ f args
        rw [htot θ]
        have := hkw θ
        simp only [Tree.weight]
        omega

/-- **A pure function's `RelInTW` is placed anywhere**, within the same weights. -/
theorem relAtInW_of_relInTW_pure (cert : String → V → ℕ) {S : List String} (hS : coreProgram.PureIn S)
    {rd : Reader} {R : ℕ → Prop} {n : ℕ} {g : String} (hg : g ∈ S) {args rets : List E}
    {W : (String → ℕ) → ℕ} (h : RelInTW fs rd R n g args rets W) :
    ∀ fp, RelAtInW fs cert wId rd R (fun _ => False) fp n g args rets W := by
  obtain ⟨t, hn, hv, hb, hl, ht, hw⟩ := h
  exact fun fp => ⟨t, hn, hv, hb, placed_of_pure hS t hv hb (hn ▸ hg) fp, ht,
    loadsIn_of_loadsR t R fp hl, fun _ h => h.elim, hw⟩

end
end LeanVM.Guest.B1.Digest
