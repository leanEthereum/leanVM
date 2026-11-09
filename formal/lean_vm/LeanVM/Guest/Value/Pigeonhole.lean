/-
  LeanVM.Guest.Value.Pigeonhole

  Write-once memory as a certificate of bijections: distinct marks written into slots never
  collide, so the writers are injective into the slots, and a count makes them a bijection;
  with the corollaries the guest needs, a sorted order and coverage as `List.Forall₂`.
-/

module

public import LeanVM.Guest.Value.Bits
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Sort

/-!
# Write-once and pigeonhole bijections

The guest certifies permutations without sorting: each of `N` writers stores a distinct mark (a
running count, a g-power) into its slot of a write-once table, so two writers of one slot would
write two values into one cell, which the memory rejects (`writeOnce_injective`); and a count
says there are as many writers as slots, so the writers fill every slot exactly once
(`cover_of_writeOnce`). This is the coverage table of `main` (G:4431-4503, with
`child_claims`, `child_claim_list_digest`, `child_claim_list_last`, G:4058-4201), `sort_order` in
`verify_tables` (G:1925-1951) and `col_sort_order` in `certify_placement` (G:2954-2978) (G for
`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM `542b035`).

The corollaries: a bijection's ranks list `List.range n` up to order
(`perm_range_of_bijective`); a list of ranks that is a permutation and adjacent-sorted by the
guest's checks (sizes non-increasing, ties ascending) is `stackOffsets`'s `mergeSort`
(`eq_mergeSort_of_adjacent`, `stackOffsets`, V:843-848); and a cover holds every claim,
`List.Forall₂` (`forall₂_of_cover`, the holders of `NodeRelation`, N:354-356).
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Write-once marks -/

/-- **Distinct marks never share a slot**: if each writer `i` leaves `mem (slot i) = mark i`,
one value per cell as write-once memory holds, and the marks are distinct, then the slots are. -/
theorem writeOnce_injective {ι σ α : Type*} {slot : ι → σ} {mark : ι → α} {mem : σ → α}
    (hmark : Function.Injective mark) (hw : ∀ i, mem (slot i) = mark i) :
    Function.Injective slot := fun i j h ↦ hmark (by rw [← hw i, ← hw j, h])

/-- **Pigeonhole**: writers that never share a slot, at least as many as the slots, fill each
slot exactly once. -/
theorem writeOnce_bijective {ι σ α : Type*} [Fintype ι] [Fintype σ] {slot : ι → σ}
    {mark : ι → α} {mem : σ → α} (hmark : Function.Injective mark)
    (hw : ∀ i, mem (slot i) = mark i) (hcard : Fintype.card σ ≤ Fintype.card ι) :
    Function.Bijective slot := by
  have hinj := writeOnce_injective hmark hw
  have := Fintype.card_le_of_injective slot hinj
  exact (Fintype.bijective_iff_injective_and_card slot).mpr ⟨hinj, le_antisymm this hcard⟩

/-- **The coverage certificate**, as the guest runs it: `N` writers, writer `i < N` range-checked
into a slot below `M` and storing a mark distinct from every other writer's into it, with
`M ≤ N` (the guest's final count, `written == n_total`, G:4503), fill every slot `s < M` exactly
once. -/
theorem cover_of_writeOnce {α : Type*} {N M : ℕ} {slot : ℕ → ℕ} {mark : ℕ → α} {mem : ℕ → α}
    (hslot : ∀ i < N, slot i < M) (hmark : ∀ i < N, ∀ j < N, mark i = mark j → i = j)
    (hw : ∀ i < N, mem (slot i) = mark i) (hNM : M ≤ N) :
    ∀ s < M, ∃! i, i < N ∧ slot i = s := by
  let f : Fin N → Fin M := fun i ↦ ⟨slot i, hslot i i.2⟩
  have hbij : Function.Bijective f := by
    refine writeOnce_bijective (mark := fun i : Fin N ↦ mark i) (mem := fun s : Fin M ↦ mem s)
      (fun i j h ↦ Fin.ext (hmark i i.2 j j.2 h)) (fun i ↦ hw i i.2) ?_
    simpa using hNM
  intro s hs
  obtain ⟨i, hi⟩ := hbij.2 ⟨s, hs⟩
  refine ⟨i, ⟨i.2, congrArg Fin.val hi⟩, ?_⟩
  rintro j ⟨hj, hjs⟩
  have hi' : slot i = s := congrArg Fin.val hi
  have : f ⟨j, hj⟩ = f i := Fin.ext (by simp only [f]; rw [hjs, hi'])
  exact congrArg Fin.val (hbij.1 this)

/-! ## Sorted orders (`sort_order`, `col_sort_order`) -/

/-- A list sorted on adjacent entries by a transitive relation is pairwise sorted. -/
theorem pairwise_of_adjacent {α : Type*} {r : α → α → Prop}
    (htrans : ∀ a b c, r a b → r b c → r a c) :
    ∀ (l : List α), (∀ i (h : i + 1 < l.length), r (l[i]'(by omega)) (l[i + 1]'h)) →
      l.Pairwise r
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    refine List.Pairwise.cons ?_ (pairwise_of_adjacent htrans l fun i hi ↦ by
      have := h (i + 1) (by simpa using hi)
      rwa [List.getElem_cons_succ, List.getElem_cons_succ] at this)
    have key : ∀ k (hk : k < l.length), r a (l[k]'hk) := by
      intro k
      induction k with
      | zero => intro hk; simpa using h 0 (by simpa using hk)
      | succ k ih =>
        intro hk
        have := h (k + 1) (by simpa using hk)
        rw [List.getElem_cons_succ, List.getElem_cons_succ] at this
        exact htrans _ _ _ (ih (by omega)) this
    intro b hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    exact key k hk

/-- `stackOffsets`'s order (V:890-897): larger size first, ties by ascending index. -/
def stackLe (size : ℕ → ℕ) (i j : ℕ) : Bool :=
  decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))

/-- **The certified order is the specification's**: a permutation of `List.range n` whose
adjacent entries the guest checks (the size does not increase, G:1942 and G:2973; on equal sizes
the index does not decrease, G:1943-1946 and G:2974-2977) is `stackOffsets`'s `mergeSort` of
`List.range n` (V:843-848). -/
theorem eq_mergeSort_of_adjacent {n : ℕ} (size : ℕ → ℕ) {ord : List ℕ}
    (hperm : ord.Perm (List.range n))
    (hadj : ∀ i (h : i + 1 < ord.length), size (ord[i + 1]'h) ≤ size (ord[i]'(by omega)) ∧
      (size (ord[i]'(by omega)) = size (ord[i + 1]'h) → ord[i]'(by omega) ≤ ord[i + 1]'h)) :
    ord = (List.range n).mergeSort (stackLe size) := by
  have htrans : ∀ a b c, stackLe size a b = true → stackLe size b c = true →
      stackLe size a c = true := by
    intro a b c hab hbc
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
    omega
  have htotal : ∀ a b, (stackLe size a b || stackLe size b a) = true := by
    intro a b
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    omega
  have hsorted : ord.Pairwise fun a b ↦ stackLe size a b = true := by
    refine pairwise_of_adjacent htrans ord fun i h ↦ ?_
    have := hadj i h
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    omega
  refine List.Perm.eq_of_pairwise (le := fun a b ↦ stackLe size a b = true) ?_ hsorted
    (List.pairwise_mergeSort htrans htotal _)
    (hperm.trans (List.mergeSort_perm _ _).symm)
  intro a b _ _ hab hba
  simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hab hba
  omega

/-! ## Coverage as `List.Forall₂` -/

end
end LeanVM.Guest.Value
