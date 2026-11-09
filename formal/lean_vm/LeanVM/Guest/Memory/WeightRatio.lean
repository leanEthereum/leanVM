/-
  LeanVM.Guest.Memory.WeightRatio

  A call tree's weight within a ratio of its words, when every function its paths reach weighs
  at most that ratio of its frame: `weight_le_ratio`.
-/

module

public import LeanVM.Guest.Memory.SizeTotal

/-!
# Weights within a ratio of the words

If every function of a set `S` closed under calls (`CallsIn`) has `q · ω g ≤ p · fs g`, a valid
tree of a function of `S` has `q · weight ≤ p · total` (`weight_le_ratio`): each instance that
runs contributes its frame to the words and its weight to the weight, a phantom or a `HeapBuf`
only words. `callsIn_of_list` gives `CallsIn` from a list closed under `Stmt.blockCallees`,
decidable for literal lists.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {P : Core.Program} {fs ω : String → ℕ} {S : String → Prop} {rd : Reader} {p q : ℕ}

mutual
/-- **A valid tree's weight within the ratio of its words.** -/
theorem weight_le_ratio (hc : CallsIn P S) (hω : ∀ g, S g → q * ω g ≤ p * fs g) :
    ∀ (t : Tree) {args rets : List E}, S t.name → t.Valid P rd args rets →
      q * t.weight ω ≤ p * t.total fs
  | .node f σ bufs kids, args, rets, hs, hv => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      have hkk := weightKids_le_ratio hc hω kids hk (hc f hs fn hf σ es vs hw)
      have h1 := hω f hs
      rw [Tree.weight, Tree.total]
      nlinarith [Nat.zero_le (p * bufs.sum)]
  | .phantom .., _, _, _, hv => hv.elim

theorem weightKids_le_ratio (hc : CallsIn P S) (hω : ∀ g, S g → q * ω g ≤ p * fs g) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValid P rd σ cs ks →
      (∀ c ∈ cs, S c.f) → q * Tree.weightKids ω ks ≤ p * Tree.totalKids fs ks
  | [], _, [], _, _ => by simp only [Tree.weightKids, Tree.totalKids]; omega
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      have ih := weightKids_le_ratio hc hω ks hv' fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')
      rw [Tree.weightKids, Tree.totalKids]
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        have := weight_le_ratio hc hω k (hn ▸ hs c List.mem_cons_self) hk
        nlinarith
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        rw [Tree.weight]
        nlinarith [Nat.zero_le (p * (Tree.phantom f' σ').total fs)]
end

end
end LeanVM.Guest.Memory
