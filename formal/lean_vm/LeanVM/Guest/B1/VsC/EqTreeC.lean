/-
  LeanVM.Guest.B1.VsC.EqTreeC

  `eqtree`'s stores hold once its other atoms do, on a memory holding its levels.
-/

module

public import LeanVM.Guest.B1.Link.EqTree

/-!
# `eqtree`, completely

`eqtreeAt_sound` reads the levels off a valuation on which every atom holds, its stores included.
Completeness has the levels in memory first (the caller's own words) and the stores to prove:
`eqtreeAt_complete`, on a memory holding every level `t` of `eqKernel` at `o[oo + 2^t - 2 ..]`, gets
every atom of the template from the atoms that are not stores (`S`, loads only), given that its
reads (`eqReadsAt`: the point's coordinates and each level's words) are not stores. A store's word
is the read word times `1 + r_t` or `r_t`, the next level's entry.

`eqStoresAt` lists the template's stores in order, `eqStoresAt_mem` puts them in the template.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `eqtree`'s reads: the point's coordinates, and each level's words. -/
def eqReadsAt (p o : V) (po oo b n : ℕ) : List Atom :=
  .load (.n b) p po :: ((List.range (n - 1)).map fun t' ↦
    .load (.n (eqtreeS b (t' + 1))) p (po + (t' + 1)) ::
      (List.range (2 ^ (t' + 1))).map fun i ↦
        Atom.load (.n (eqtreeS b (t' + 1) + 3 + 3 * i)) o (oo + (2 ^ (t' + 1) - 2 + i))).flatten

/-- `eqtree`'s stores, in order. -/
def eqStoresAt (o : V) (oo b n : ℕ) : List Atom :=
  [.load (.n (b + 2)) o oo, .load (.n b) o (oo + 1)] ++
    ((List.range (n - 1)).map fun t' ↦ ((List.range (2 ^ (t' + 1))).map fun i ↦
      [Atom.load (.n (eqtreeS b (t' + 1) + 3 + 3 * i + 1)) o (oo + (2 ^ (t' + 1 + 1) - 2 + i)),
        .load (.n (eqtreeS b (t' + 1) + 3 + 3 * i + 2)) o (oo + (2 ^ (t' + 1 + 1) - 2 + 2 ^ (t' + 1) + i))]).flatten).flatten

/-- The atoms of `eqtree`'s template, by position. -/
theorem mem_eqtreeAt {p o : V} {po oo b n : ℕ} {a : Atom} (h : Stmt.atom a ∈ eqtreeAt p o po oo b n) :
    a = .load (.n b) p po ∨ a = .const (.n (b + 1)) (word 1 0) ∨ a = .add (.n (b + 2)) (.n (b + 1)) (.n b) ∨
    a = .load (.n (b + 2)) o oo ∨ a = .load (.n b) o (oo + 1) ∨
    ∃ t, 1 ≤ t ∧ t < n ∧ (a = .load (.n (eqtreeS b t)) p (po + t) ∨
      a = .const (.n (eqtreeS b t + 1)) (word 1 0) ∨
      a = .add (.n (eqtreeS b t + 2)) (.n (eqtreeS b t + 1)) (.n (eqtreeS b t)) ∨
      ∃ i < 2 ^ t, (a = .load (.n (eqtreeS b t + 3 + 3 * i)) o (oo + (2 ^ t - 2 + i)) ∨
        a = .mul (.n (eqtreeS b t + 3 + 3 * i + 1)) (.n (eqtreeS b t + 3 + 3 * i)) (.n (eqtreeS b t + 2)) ∨
        a = .load (.n (eqtreeS b t + 3 + 3 * i + 1)) o (oo + (2 ^ (t + 1) - 2 + i)) ∨
        a = .mul (.n (eqtreeS b t + 3 + 3 * i + 2)) (.n (eqtreeS b t + 3 + 3 * i)) (.n (eqtreeS b t)) ∨
        a = .load (.n (eqtreeS b t + 3 + 3 * i + 2)) o (oo + (2 ^ (t + 1) - 2 + 2 ^ t + i)))) := by
  unfold eqtreeAt at h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inl h))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))]
  obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp h
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hl
  have ht' := List.mem_range.mp ht'
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t' + 1, by omega, by omega, ?_⟩))))
  unfold eqtreeLevelAt at hal
  rcases List.mem_append.mp hal with h | h
  · simp only [List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))]
  obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  refine Or.inr (Or.inr (Or.inr ⟨i, List.mem_range.mp hi, ?_⟩))
  simp only [eqtreeWordAt, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at hal
  exact hal

/-- **The stores are the template's.** -/
theorem eqStoresAt_mem {p o : V} {po oo b n : ℕ} {a : Atom} (h : a ∈ eqStoresAt o oo b n) :
    Stmt.atom a ∈ eqtreeAt p o po oo b n := by
  unfold eqStoresAt at h
  unfold eqtreeAt
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp
  obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp h
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hl
  obtain ⟨l', hl', hal'⟩ := List.mem_flatten.mp hal
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl'
  refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨t', ht', rfl⟩, ?_⟩)
  unfold eqtreeLevelAt
  refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hal'
  rcases hal' with rfl | rfl <;> simp [eqtreeWordAt]

theorem eqKernel_take_one {rs : List E} (h : 1 ≤ rs.length) :
    eqKernel (rs.take 1) = [1 + rs.getD 0 0, rs.getD 0 0] := by
  rcases rs with _ | ⟨r0, rest⟩
  · simp at h
  · simp [eqKernel]

/-- Level `t + 1`'s entries from level `t`'s. -/
theorem eqKernel_take_succ {rs : List E} {t : ℕ} (ht : t < rs.length) (i : ℕ) :
    (eqKernel (rs.take (t + 1))).getD i 0 = if i < 2 ^ t then (eqKernel (rs.take t)).getD i 0 * (1 + rs.getD t 0)
      else (eqKernel (rs.take t)).getD (i - 2 ^ t) 0 * rs.getD t 0 := by
  have htake : rs.take (t + 1) = rs.take t ++ [rs.getD t 0] := by
    rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    simp
  have hlen : (eqKernel (rs.take t)).length = 2 ^ t := by
    rw [length_eqKernel_eq']; simp; omega
  rw [htake, eqKernel_snoc']
  split_ifs with hi
  · rw [List.getD_append _ _ _ _ (by rw [List.length_map, hlen]; exact hi), getD_map_mul_eq']
  · rw [List.getD_append_right _ _ _ _ (by rw [List.length_map, hlen]; omega), List.length_map, hlen,
      getD_map_mul_eq']

/-- **`eqtree` completes**: on a memory holding its levels, every atom holds once those that are not
stores do, its reads not being stores. -/
theorem eqtreeAt_complete {rd : Reader} {σ : Val} {p o : V} {po oo b n : ℕ} (hn : 1 ≤ n) {S : List Atom}
    (hS : ∀ a ∈ S, ∃ d q off, a = Atom.load d q off) (hrd : ∀ a ∈ eqReadsAt p o po oo b n, a ∉ S)
    (hns : ∀ a, Stmt.atom a ∈ eqtreeAt p o po oo b n → a ∉ S → a.Holds rd σ)
    {rs : List E} (hrs : rs.length = n) (hpt : ∀ t < n, LoadHolds rd (σ p) (po + t) (rs.getD t 0))
    (hT : ∀ t, 1 ≤ t → t ≤ n → ∀ i < 2 ^ t,
      LoadHolds rd (σ o) (oo + (2 ^ t - 2 + i)) ((eqKernel (rs.take t)).getD i 0)) :
    ∀ a, Stmt.atom a ∈ eqtreeAt p o po oo b n → a.Holds rd σ := by
  have nl : ∀ {a : Atom}, (∀ d q off, a ≠ .load d q off) → a ∉ S := fun hne hm => by
    obtain ⟨d, q, off, he⟩ := hS _ hm; exact hne d q off he
  have rd0 : Atom.load (.n b) p po ∉ S := hrd _ (by simp [eqReadsAt])
  have rdL : ∀ t, 1 ≤ t → t < n → Atom.load (.n (eqtreeS b t)) p (po + t) ∉ S := fun t h1 h2 =>
    hrd _ (by
      simp only [eqReadsAt, List.mem_cons, List.mem_flatten, List.mem_map, List.mem_range]
      exact Or.inr ⟨_, ⟨t - 1, by omega, rfl⟩, by rw [Nat.sub_add_cancel h1]; simp⟩)
  have rdW : ∀ t, 1 ≤ t → t < n → ∀ i < 2 ^ t,
      Atom.load (.n (eqtreeS b t + 3 + 3 * i)) o (oo + (2 ^ t - 2 + i)) ∉ S := fun t h1 h2 i hi =>
    hrd _ (by
      simp only [eqReadsAt, List.mem_cons, List.mem_flatten, List.mem_map, List.mem_range]
      refine Or.inr ⟨_, ⟨t - 1, by omega, rfl⟩, ?_⟩
      rw [Nat.sub_add_cancel h1]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  have mL : ∀ t, 1 ≤ t → t < n → ∀ a, Stmt.atom a ∈ eqtreeLevelAt p o po oo b t →
      Stmt.atom a ∈ eqtreeAt p o po oo b n := fun t h1 h2 a ha => by
    unfold eqtreeAt
    refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
      ⟨t - 1, List.mem_range.mpr (by omega), ?_⟩, ha⟩)
    rw [Nat.sub_add_cancel h1]
  have mW : ∀ t, 1 ≤ t → t < n → ∀ i < 2 ^ t, ∀ a, Stmt.atom a ∈ eqtreeWordAt o oo (eqtreeS b t) t i →
      Stmt.atom a ∈ eqtreeAt p o po oo b n := fun t h1 h2 i hi a ha =>
    mL t h1 h2 a (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
      ⟨i, List.mem_range.mpr hi, rfl⟩, ha⟩))
  -- the head's values
  have hb : σ (.n b) = rs.getD 0 0 := by
    have := hns _ (by simp [eqtreeAt]) rd0
    exact loadHolds_unique this (by simpa using hpt 0 hn)
  have hb2 : σ (.n (b + 2)) = 1 + rs.getD 0 0 := by
    have a1 := hns (.const (.n (b + 1)) (word 1 0)) (by simp [eqtreeAt]) (nl fun _ _ _ h => by cases h)
    have a2 := hns (.add (.n (b + 2)) (.n (b + 1)) (.n b)) (by simp [eqtreeAt]) (nl fun _ _ _ h => by cases h)
    simp only [Atom.Holds] at a1 a2
    rw [a2, a1, word_one, hb]
  -- a level's values
  have hlev : ∀ t, 1 ≤ t → t < n → σ (.n (eqtreeS b t)) = rs.getD t 0 ∧
      σ (.n (eqtreeS b t + 2)) = 1 + rs.getD t 0 := by
    intro t h1 h2
    have l0 := hns _ (mL t h1 h2 _ (by simp [eqtreeLevelAt])) (rdL t h1 h2)
    have e0 := loadHolds_unique l0 (hpt t h2)
    have a1 := hns (.const (.n (eqtreeS b t + 1)) (word 1 0)) (mL t h1 h2 _ (by simp [eqtreeLevelAt]))
      (nl fun _ _ _ h => by cases h)
    have a2 := hns (.add (.n (eqtreeS b t + 2)) (.n (eqtreeS b t + 1)) (.n (eqtreeS b t)))
      (mL t h1 h2 _ (by simp [eqtreeLevelAt])) (nl fun _ _ _ h => by cases h)
    simp only [Atom.Holds] at a1 a2
    exact ⟨e0, by rw [a2, a1, word_one, e0]⟩
  have hword : ∀ t, 1 ≤ t → t < n → ∀ i < 2 ^ t,
      σ (.n (eqtreeS b t + 3 + 3 * i)) = (eqKernel (rs.take t)).getD i 0 := by
    intro t h1 h2 i hi
    have l0 := hns _ (mW t h1 h2 i hi _ (by simp [eqtreeWordAt])) (rdW t h1 h2 i hi)
    exact loadHolds_unique l0 (hT t h1 h2.le i hi)
  intro a ha
  by_cases haS : a ∈ S
  swap
  · exact hns a ha haS
  obtain ⟨d, q, off, rfl⟩ := hS _ haS
  rcases mem_eqtreeAt ha with h | h | h | h | h | ⟨t, h1, h2, (h | h | h | ⟨i, hi, (h | h | h | h | h)⟩)⟩
  · exact absurd (h ▸ haS) rd0
  · cases h
  · cases h
  · rw [h]
    show LoadHolds rd (σ o) oo (σ (.n (b + 2)))
    have := hT 1 le_rfl hn 0 (by norm_num)
    rw [eqKernel_take_one (by omega)] at this
    simpa [hb2] using this
  · rw [h]
    show LoadHolds rd (σ o) (oo + 1) (σ (.n b))
    have := hT 1 le_rfl hn 1 (by norm_num)
    rw [eqKernel_take_one (by omega)] at this
    simpa [hb] using this
  · exact absurd (h ▸ haS) (rdL t h1 h2)
  · cases h
  · cases h
  · exact absurd (h ▸ haS) (rdW t h1 h2 i hi)
  · cases h
  · rw [h]
    have m := hns (.mul (.n (eqtreeS b t + 3 + 3 * i + 1)) (.n (eqtreeS b t + 3 + 3 * i)) (.n (eqtreeS b t + 2)))
      (mW t h1 h2 i hi _ (by simp [eqtreeWordAt])) (nl fun _ _ _ h => by cases h)
    simp only [Atom.Holds] at m
    show LoadHolds rd (σ o) (oo + (2 ^ (t + 1) - 2 + i)) (σ (.n (eqtreeS b t + 3 + 3 * i + 1)))
    have := hT (t + 1) (by omega) (by omega) i (by rw [pow_succ]; omega)
    rw [eqKernel_take_succ (by omega), ite_eq_left hi] at this
    rwa [m, hword t h1 h2 i hi, (hlev t h1 h2).2]
  · cases h
  · rw [h]
    have m := hns (.mul (.n (eqtreeS b t + 3 + 3 * i + 2)) (.n (eqtreeS b t + 3 + 3 * i)) (.n (eqtreeS b t)))
      (mW t h1 h2 i hi _ (by simp [eqtreeWordAt])) (nl fun _ _ _ h => by cases h)
    simp only [Atom.Holds] at m
    show LoadHolds rd (σ o) (oo + (2 ^ (t + 1) - 2 + 2 ^ t + i)) (σ (.n (eqtreeS b t + 3 + 3 * i + 2)))
    have := hT (t + 1) (by omega) (by omega) (2 ^ t + i) (by rw [pow_succ]; omega)
    rw [eqKernel_take_succ (by omega), ite_eq_right (show ¬2 ^ t + i < 2 ^ t by omega), Nat.add_sub_cancel_left,
      show oo + (2 ^ (t + 1) - 2 + (2 ^ t + i)) = oo + (2 ^ (t + 1) - 2 + 2 ^ t + i) by omega] at this
    rwa [m, hword t h1 h2 i hi, (hlev t h1 h2).1]

end
end LeanVM.Guest.B1.VsC
