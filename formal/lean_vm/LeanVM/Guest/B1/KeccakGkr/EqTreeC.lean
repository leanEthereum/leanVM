/-
  LeanVM.Guest.B1.KeccakGkr.EqTreeC

  `eqtree` on an evaluated valuation: with the point's words and the tree's levels in memory, the
  template holds.
-/

module

public import LeanVM.Guest.B1.Eq.EqTree
public import LeanVM.Guest.B1.KeccakGkr.LayerCBlock

/-!
# `eqtree`, completely

`eqtreeReads`: the template's loads that are not stores (the point's coordinates, the earlier
level's words). `eqtree_complete`: on a valuation satisfying the template's equations (`Fwd.Good`),
none of those loads a store, the point's words at `p` and every level's `eqKernel` entries at `o`
in memory, the template holds (`eqtreeT_complete` on the values the equations give).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The loads of `eqtreeT` that are not stores. -/
def eqtreeReads (p o : V) (po b n : ℕ) : List Atom :=
  .load (.n b) p po :: ((List.range (n - 1)).map fun t' ↦
    .load (.n (eqtreeS b (t' + 1))) p (po + (t' + 1)) ::
      (List.range (2 ^ (t' + 1))).map fun i ↦
        .load (.n (eqtreeS b (t' + 1) + 3 + 3 * i)) o (2 ^ (t' + 1) - 2 + i)).flatten

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- **`eqtree`, completely.** -/
theorem eqtree_complete {p o : V} {po b n : ℕ} (hn : 1 ≤ n)
    (hg : ∀ s ∈ eqtreeT p o po b n, GoodS rd S w σ s)
    (hS : ∀ a ∈ eqtreeReads p o po b n, a ∉ S) {rs : List E} (hrs : rs.length = n)
    (hpt : ∀ t < n, LoadHolds rd (σ p) (po + t) (rs.getD t 0))
    (hout : ∀ t, 1 ≤ t → t ≤ n → ∀ i < 2 ^ t,
      LoadHolds rd (σ o) (2 ^ t - 2 + i) ((eqKernel (rs.take t)).getD i 0)) :
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (eqtreeT p o po b n) next kret := by
  intro next kret hn'
  -- the head
  have gd : ∀ a, Stmt.atom a ∈ eqtreeT p o po b n → Good rd S w σ a := fun a h ↦ hg _ h
  have g0 := gd (.load (.n b) p po) (by simp [eqtreeT])
  have g1 := gd (.const (.n (b + 1)) (word 1 0 0)) (by simp [eqtreeT])
  have g2 := gd (.add (.n (b + 2)) (.n (b + 1)) (.n b)) (by simp [eqtreeT])
  have e0 : σ (.n b) = rs.getD 0 0 :=
    load_val g0 (hS _ (by simp [eqtreeReads])) (by simpa using hpt 0 hn)
  have e1 : σ (.n (b + 1)) = 1 := by rw [show σ (.n (b + 1)) = word 1 0 0 from g1, word_one]
  have e2 : σ (.n (b + 2)) = 1 + rs.getD 0 0 := by
    rw [show σ (.n (b + 2)) = σ (.n (b + 1)) + σ (.n b) from g2, e1, e0]
  have hhead : ∀ k < 3, σ (.n (b + k)) = [rs.getD 0 0, 1, 1 + rs.getD 0 0].getD k 0 := by
    intro k hk
    interval_cases k
    · simpa using e0
    · simpa using e1
    · simpa using e2
  -- the levels
  have hlvl : ∀ t, 1 ≤ t → t < n → ∀ k < 3 + 3 * 2 ^ t,
      σ (.n (eqtreeS b t + k)) = eqtreeLvlVal rs t k := by
    intro t ht1 htn k hk
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have ht' : t' < n - 1 := by omega
    set Sb := eqtreeS b (t' + 1) with hSb
    have memL : ∀ s ∈ eqtreeLevelT p o po b (t' + 1), s ∈ eqtreeT p o po b n := by
      intro s hs
      simp only [eqtreeT, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
      exact Or.inr ⟨_, ⟨t', ht', rfl⟩, hs⟩
    have memR : ∀ a ∈ (Stmt.atom (.load (.n Sb) p (po + (t' + 1)))) ::
        ((List.range (2 ^ (t' + 1))).map fun i ↦
          Stmt.atom (.load (.n (Sb + 3 + 3 * i)) o (2 ^ (t' + 1) - 2 + i))), True := fun _ _ ↦ trivial
    clear memR
    have rd0 : Atom.load (.n Sb) p (po + (t' + 1)) ∉ S := hS _ (by
      simp only [eqtreeReads, List.mem_cons, List.mem_flatten, List.mem_map, List.mem_range]
      exact Or.inr ⟨_, ⟨t', ht', rfl⟩, by simp [hSb]⟩)
    have rdi : ∀ i < 2 ^ (t' + 1),
        Atom.load (.n (Sb + 3 + 3 * i)) o (2 ^ (t' + 1) - 2 + i) ∉ S := fun i hi ↦ hS _ (by
      simp only [eqtreeReads, List.mem_cons, List.mem_flatten, List.mem_map, List.mem_range]
      exact Or.inr ⟨_, ⟨t', ht', rfl⟩, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩)⟩)
    have gl : ∀ a, Stmt.atom a ∈ eqtreeLevelT p o po b (t' + 1) → Good rd S w σ a :=
      fun a h ↦ hg _ (memL _ h)
    have h0 := gl (.load (.n Sb) p (po + (t' + 1))) (by simp [eqtreeLevelT, hSb])
    have h1 := gl (.const (.n (Sb + 1)) (word 1 0 0)) (by simp [eqtreeLevelT, hSb])
    have h2 := gl (.add (.n (Sb + 2)) (.n (Sb + 1)) (.n Sb)) (by simp [eqtreeLevelT, hSb])
    have v0 : σ (.n Sb) = rs.getD (t' + 1) 0 := load_val h0 rd0 (hpt _ htn)
    have v1 : σ (.n (Sb + 1)) = 1 := by rw [show σ (.n (Sb + 1)) = word 1 0 0 from h1, word_one]
    have v2 : σ (.n (Sb + 2)) = 1 + rs.getD (t' + 1) 0 := by
      rw [show σ (.n (Sb + 2)) = σ (.n (Sb + 1)) + σ (.n Sb) from h2, v1, v0]
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · interval_cases k
      · simpa [eqtreeLvlVal] using v0
      · simpa [eqtreeLvlVal] using v1
      · simpa [eqtreeLvlVal] using v2
    · obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 3 ∧ k = 3 + 3 * i + j :=
        ⟨(k - 3) / 3, (k - 3) % 3, Nat.mod_lt _ (by norm_num), by omega⟩
      have hi : i < 2 ^ (t' + 1) := by omega
      have memW : ∀ s ∈ eqtreeWordT o Sb (t' + 1) i, s ∈ eqtreeT p o po b n := fun s hs ↦
        memL s (by
          simp only [eqtreeLevelT, ← hSb, List.mem_append, List.mem_flatten, List.mem_map,
            List.mem_range]
          exact Or.inr ⟨_, ⟨i, hi, rfl⟩, hs⟩)
      have gw : ∀ a, Stmt.atom a ∈ eqtreeWordT o Sb (t' + 1) i → Good rd S w σ a :=
        fun a h ↦ hg _ (memW _ h)
      have w0 := gw (.load (.n (Sb + 3 + 3 * i)) o (2 ^ (t' + 1) - 2 + i)) (by simp [eqtreeWordT])
      have w1 := gw (.mul (.n (Sb + 3 + 3 * i + 1)) (.n (Sb + 3 + 3 * i)) (.n (Sb + 2)))
        (by simp [eqtreeWordT])
      have w2 := gw (.mul (.n (Sb + 3 + 3 * i + 2)) (.n (Sb + 3 + 3 * i)) (.n Sb))
        (by simp [eqtreeWordT])
      have u0 : σ (.n (Sb + 3 + 3 * i)) = (eqKernel (rs.take (t' + 1))).getD i 0 :=
        load_val w0 (rdi i hi) (hout _ (by omega) (by omega) i hi)
      simp only [Good, V.n] at w1 w2
      rw [ite_pos' ⟨by omega, by omega⟩] at w1 w2
      rw [eqtreeLvlVal_word rs (t' + 1) i j hj, show Sb + (3 + 3 * i + j) = Sb + 3 + 3 * i + j by ring]
      interval_cases j
      · simpa using u0
      · simp only [List.getD_cons_succ, List.getD_cons_zero]
        rw [w1, u0, v2]
      · simp only [List.getD_cons_succ, List.getD_cons_zero]
        rw [w2, u0, v0]
  have H := eqtreeT_complete hn hrs hpt hout hhead hlvl
  exact (holdsList_atoms (eqtreeT_atoms p o po b n) next kret).2 ⟨H, hn'⟩

end
end LeanVM.Guest.B1.VerifySub
