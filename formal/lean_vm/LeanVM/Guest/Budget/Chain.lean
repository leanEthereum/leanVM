/-
  LeanVM.Guest.Budget.Chain

  A loop helper's iterations of honest shape (`ChainHonest`), and their weight and words: the sum
  of each iteration's bound.
-/

module

public import LeanVM.Guest.Budget.Kids

/-!
# Chains of iterations

A loop helper `f` runs as a chain: iteration `c` is a node of honest shape (`NodeHonest`) whose
calls are its body's `csb σ` and the tail call `tl σ`, the tail's callee the next iteration's
node. `ChainHonest … m c` is `m` iterations from `c`; at `0` it is `False`, so the last
iteration's tail call is not entered (`KidsT`). `ChainHonest.weight_le`: the chain's weight is at
most the sum of its iterations' bounds; `ChainHonest.total_le`: its words too, and the last tail's
phantom frame.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **`m` iterations of the loop helper `f` from iteration `c`, of honest shape**. -/
def ChainHonest (P : Core.Program) (f : String) (Q : ℕ → Val → Prop) (csb : Val → List Call)
    (tl : Val → Call) (bs : Val → List ℕ) (Tsb : ℕ → List (Tree → Prop)) : ℕ → ℕ → Tree → Prop
  | 0, _, _ => False
  | m + 1, c, t => ∃ σ ks, t = .node f σ (bs σ) ks ∧ Q c σ ∧
      (∀ fn es vs, P.find? f = some fn → walk σ fn.body = .ret es vs → calls es = csb σ ++ [tl σ]) ∧
      (csb σ).length = (Tsb c).length ∧
      KidsT (csb σ ++ [tl σ]) (Tsb c ++ [ChainHonest P f Q csb tl bs Tsb m (c + 1)]) ks

/-- The sum of `B` over the `m` iterations from `c`. -/
def iterSum (B : ℕ → ℕ) (c m : ℕ) : ℕ := ((List.range m).map fun i => B (c + i)).sum

theorem iterSum_succ (B : ℕ → ℕ) (c m : ℕ) : iterSum B c (m + 1) = B c + iterSum B (c + 1) m := by
  unfold iterSum
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  congr 2
  congr 1
  funext i
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 i]

variable {P : Core.Program} {rd : Reader}

theorem getElem_append_last {α : Type} (l : List α) (a : α) {i : ℕ} (hi : i < (l ++ [a]).length)
    (hn : ¬ i < l.length) : (l ++ [a])[i] = a := by
  have : i = l.length := by simp at hi; omega
  subst this
  simp

/-- **A chain's weight**: the sum of its iterations' bounds `B c`, each iteration's frame and its
body's calls' bounds `Wb c σ` (by position) within `B c`. -/
theorem ChainHonest.weight_le {f : String} {Q : ℕ → Val → Prop} {csb : Val → List Call}
    {tl : Val → Call} {bs : Val → List ℕ} {Tsb : ℕ → List (Tree → Prop)} (ω : String → ℕ)
    (Wb : ℕ → Val → List ℕ) (B : ℕ → ℕ)
    (hlen : ∀ c σ, Q c σ → (Wb c σ).length = (csb σ).length)
    (hsum : ∀ c σ, Q c σ → ω f + (Wb c σ).sum ≤ B c)
    (hB : ∀ c σ, Q c σ → ∀ i (hi : i < (csb σ).length) (hT : i < (Tsb c).length)
      (hW : i < (Wb c σ).length), (csb σ)[i].taken = true → ∀ (t : Tree) (rets : List E),
        t.name = (csb σ)[i].f → t.Valid P rd ((csb σ)[i].args.map σ) rets → t.BufsOk P →
          (Tsb c)[i] t → t.weight ω ≤ (Wb c σ)[i]) :
    ∀ m c (t : Tree) args rets, ChainHonest P f Q csb tl bs Tsb m c t → t.Valid P rd args rets →
      t.BufsOk P → t.weight ω ≤ iterSum B c m
  | 0, _, _, _, _, h, _, _ => h.elim
  | m + 1, c, t, args, rets, h, hv, hb => by
    obtain ⟨σ, ks, rfl, hQ, hc, hl, hT⟩ := h
    obtain ⟨hk, hbk⟩ := node_kids hv hb hc
    have hWl := hlen c σ hQ
    have hk' := kids_weight_leL ω (csb σ ++ [tl σ]) (Tsb c ++ [ChainHonest P f Q csb tl bs Tsb m (c + 1)])
      (Wb c σ ++ [iterSum B (c + 1) m]) ks hk hbk hT (by simp [hl]) (by simp [hWl])
      (fun i hi hTi hWi ht t' rets' hn hv' hb' hT' => by
        by_cases hlt : i < (csb σ).length
        · have hTl : i < (Tsb c).length := by omega
          have hWlt : i < (Wb c σ).length := by omega
          rw [List.getElem_append_left hlt] at ht hn hv'
          rw [List.getElem_append_left hTl] at hT'
          rw [List.getElem_append_left hWlt]
          exact hB c σ hQ i hlt hTl hWlt ht t' rets' hn hv' hb' hT'
        · rw [getElem_append_last _ _ hi hlt] at ht hn hv'
          rw [getElem_append_last _ _ hTi (by omega)] at hT'
          rw [getElem_append_last _ _ hWi (by omega)]
          exact ChainHonest.weight_le ω Wb B hlen hsum hB m (c + 1) t' _ _ hT' hv' hb')
    rw [Tree.weight, iterSum_succ]
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at hk'
    have := hsum c σ hQ
    omega

/-- **A chain's words**: the sum of its iterations' bounds `B c`, each iteration's frame, its
`HeapBuf`s and its body's calls' bounds `Wb c σ` (by position; a call not entered its callee's
frame) within `B c`, and the last tail call's frame. -/
theorem ChainHonest.total_le {f : String} {Q : ℕ → Val → Prop} {csb : Val → List Call}
    {tl : Val → Call} {bs : Val → List ℕ} {Tsb : ℕ → List (Tree → Prop)} (fs : String → ℕ)
    (Wb : ℕ → Val → List ℕ) (B : ℕ → ℕ)
    (htl : ∀ σ, (tl σ).f = f)
    (hlen : ∀ c σ, Q c σ → (Wb c σ).length = (csb σ).length)
    (hsum : ∀ c σ, Q c σ → fs f + (Wb c σ).sum + (bs σ).sum ≤ B c)
    (hU : ∀ c σ, Q c σ → ∀ i (hi : i < (csb σ).length) (hW : i < (Wb c σ).length),
      (csb σ)[i].taken = false → fs (csb σ)[i].f ≤ (Wb c σ)[i])
    (hB : ∀ c σ, Q c σ → ∀ i (hi : i < (csb σ).length) (hT : i < (Tsb c).length)
      (hW : i < (Wb c σ).length), (csb σ)[i].taken = true → ∀ (t : Tree) (rets : List E),
        t.name = (csb σ)[i].f → t.Valid P rd ((csb σ)[i].args.map σ) rets → t.BufsOk P →
          (Tsb c)[i] t → t.total fs ≤ (Wb c σ)[i]) :
    ∀ m c (t : Tree) args rets, ChainHonest P f Q csb tl bs Tsb m c t → t.Valid P rd args rets →
      t.BufsOk P → t.total fs ≤ iterSum B c m + fs f
  | 0, _, _, _, _, h, _, _ => h.elim
  | m + 1, c, t, args, rets, h, hv, hb => by
    obtain ⟨σ, ks, rfl, hQ, hc, hl, hT⟩ := h
    obtain ⟨hk, hbk⟩ := node_kids hv hb hc
    have hWl := hlen c σ hQ
    have hk' := kids_total_leL fs (csb σ ++ [tl σ]) (Tsb c ++ [ChainHonest P f Q csb tl bs Tsb m (c + 1)])
      (Wb c σ ++ [iterSum B (c + 1) m + fs f]) ks hk hbk hT (by simp [hl]) (by simp [hWl])
      (fun i hi hWi ht => by
        by_cases hlt : i < (csb σ).length
        · have hWlt : i < (Wb c σ).length := by omega
          rw [List.getElem_append_left hlt] at ht ⊢
          rw [List.getElem_append_left hWlt]
          exact hU c σ hQ i hlt hWlt ht
        · rw [getElem_append_last _ _ hi hlt, getElem_append_last _ _ hWi (by omega), htl]
          omega)
      (fun i hi hTi hWi ht t' rets' hn hv' hb' hT' => by
        by_cases hlt : i < (csb σ).length
        · have hTl : i < (Tsb c).length := by omega
          have hWlt : i < (Wb c σ).length := by omega
          rw [List.getElem_append_left hlt] at ht hn hv'
          rw [List.getElem_append_left hTl] at hT'
          rw [List.getElem_append_left hWlt]
          exact hB c σ hQ i hlt hTl hWlt ht t' rets' hn hv' hb' hT'
        · rw [getElem_append_last _ _ hi hlt] at ht hn hv'
          rw [getElem_append_last _ _ hTi (by omega)] at hT'
          rw [getElem_append_last _ _ hWi (by omega)]
          exact ChainHonest.total_le fs Wb B htl hlen hsum hU hB m (c + 1) t' _ _ hT' hv' hb')
    rw [Tree.total, iterSum_succ]
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at hk'
    have := hsum c σ hQ
    omega

end
end LeanVM.Guest.Budget
