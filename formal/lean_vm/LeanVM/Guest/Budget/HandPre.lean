/-
  LeanVM.Guest.Budget.HandPre

  Preconditions passed down a valid tree: a fact about a node's arguments that its caller's path
  establishes for every call it enters holds at every node (`every_of_preIn`).
-/

module

public import LeanVM.Guest.Budget.HandPops

/-!
# Preconditions down a tree

A hand fact may need what a caller certifies of its arguments (`verify_keccak`'s table log at least
`4`, the kappas `check_stack_terminal` loads). `PreAt P Pre f σ`: the node's arguments satisfy
`Pre f`. `PreIn P rd H Pre`: at every node whose path is within `H` (`PathIn`) and whose arguments
satisfy `Pre`, every call its path enters gets arguments satisfying `Pre`. Then a valid tree popping
within `H`, its root's arguments satisfying `Pre`, has `PreAt` at every node (`every_of_preIn`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

variable {P : Core.Program} {rd : Reader}

/-- A node of `f` at `σ` whose arguments satisfy `Pre f`. -/
def PreAt (P : Core.Program) (Pre : String → List E → Prop) (f : String) (σ : Val) : Prop :=
  ∀ fn, P.find? f = some fn → Pre f (fn.params.map σ)

/-- **`Pre` passes down paths within `H`**: a node whose path is within `H` and whose arguments
satisfy `Pre` gives every call its path enters arguments satisfying `Pre`. -/
def PreIn (P : Core.Program) (rd : Reader) (H : List Pop) (Pre : String → List E → Prop) : Prop :=
  ∀ f σ, PathIn P rd H f σ → PreAt P Pre f σ → ∀ fn, P.find? f = some fn → ∀ es vs,
    walk σ fn.body = .ret es vs → ∀ c ∈ calls es, c.taken = true → Pre c.f (c.args.map σ)

mutual
/-- **Every node of a valid tree popping within `H` has its arguments in `Pre`**, when its root's
are and `Pre` passes down paths within `H`. -/
theorem every_of_preIn {H : List Pop} {Pre : String → List E → Prop} (hP : PreIn P rd H Pre) :
    ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets → (∀ p ∈ t.pops P rd, p ∈ H) →
      Pre t.name args → t.Every (PreAt P Pre)
  | .node f σ bufs kids, args, rets, hv, hH, hpre => by
      have hv0 := hv
      obtain ⟨fn, hf, hp, es, vs, hw, -, -, hk⟩ := hv
      have hpath : PathIn P rd H f σ := ((Tree.every_node).mp (every_pathIn _ hv0 hH)).1
      have hat : PreAt P Pre f σ := fun fn' hf' => by
        rw [hf] at hf'; cases hf'; rw [hp]; exact hpre
      have hpops := pops_node (rd := rd) (bufs := bufs) (kids := kids) hf hw
      have hl : (calls es).length = (Tree.popsKids P rd kids).length := by
        rw [popsKids_length, kidsValid_length hk]
      have hkid : ∀ k ∈ kids, ∀ p ∈ k.pops P rd, p ∈ H := fun k hk' p hp' =>
        hH p (by rw [hpops]; exact mem_splice_of_kid hl (popsKids_mem hk') hp')
      rw [Tree.every_node]
      exact ⟨hat, everyKids_of_preIn hP σ kids (calls es) hk hkid
        fun c hc ht => hP f σ hpath hat fn hf es vs hw c hc ht⟩
  | .phantom .., _, _, h, _, _ => h.elim

/-- `every_of_preIn` for the callees. -/
theorem everyKids_of_preIn {H : List Pop} {Pre : String → List E → Prop} (hP : PreIn P rd H Pre) :
    ∀ (σ : Val) (ks : List Tree) (cs : List Call), Tree.KidsValid P rd σ cs ks →
      (∀ k ∈ ks, ∀ p ∈ k.pops P rd, p ∈ H) → (∀ c ∈ cs, c.taken = true → Pre c.f (c.args.map σ)) →
        Tree.EveryKids (PreAt P Pre) ks
  | _, [], [], _, _, _ => by rw [Tree.EveryKids]; trivial
  | σ, k :: ks, c :: cs, ⟨hn, hc, hks⟩, hH, hC => by
      rw [Tree.EveryKids]
      refine ⟨?_, everyKids_of_preIn hP σ ks cs hks (fun k' hk' => hH k' (List.mem_cons_of_mem _ hk'))
        fun c' hc' => hC c' (List.mem_cons_of_mem _ hc')⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact every_of_preIn hP k hc (hH k List.mem_cons_self) (by rw [hn]; exact hC c List.mem_cons_self ht)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact Tree.every_phantom
  | _, _ :: _, [], h, _, _ => h.elim
end

/-- **Paths within `H` and arguments in `Pre`** at every node of a valid tree popping within `H`,
its root's arguments in `Pre`. -/
theorem every_pathIn_preAt {H : List Pop} {Pre : String → List E → Prop} (hP : PreIn P rd H Pre)
    {t : Tree} {args rets : List E} (hv : t.Valid P rd args rets) (hH : ∀ p ∈ t.pops P rd, p ∈ H)
    (hpre : Pre t.name args) : t.Every (fun f σ => PathIn P rd H f σ ∧ PreAt P Pre f σ) :=
  (every_pathIn t hv hH).and (every_of_preIn hP t hv hH hpre)

end
end LeanVM.Guest.Budget
