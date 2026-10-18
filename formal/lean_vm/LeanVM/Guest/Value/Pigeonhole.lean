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
(`cover_of_writeOnce`). This is the coverage table of `main` (G:3215-3291, with
`child_claims_window`, `child_claims_tail`, `child_claim_list_digest`, G:2802-2880, and
`cover_da_root`, G:3111-3116), `sort_order` in `verify_tables` (G:1496-1523) and
`col_sort_order` in `certify_placement` (G:1966-1997) (TRIAGE #39, #41, #63-65, #76).

The corollaries: a bijection's ranks list `List.range n` up to order
(`perm_range_of_bijective`); a list of ranks that is a permutation and adjacent-sorted by the
guest's checks (sizes non-increasing, ties ascending) is `stackOffsets`'s `mergeSort`
(`eq_mergeSort_of_adjacent`, V:877-884); and a cover holds every claim, `List.Forall₂`
(`forall₂_of_cover`, the holders of `NodeRel`, N:362-365).
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
`M ≤ N` (the guest's final count, `written == n_total`, G:3291), fill every slot `s < M` exactly
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

/-- The guest's marks are g-powers at distinct exponents below the order of `g`. -/
theorem gen_pow_marks {N : ℕ} {e : ℕ → ℕ} (he : ∀ i < N, e i < 2 ^ 64 - 1)
    (hinj : ∀ i < N, ∀ j < N, e i = e j → i = j) :
    ∀ i < N, ∀ j < N, gen ^ e i = gen ^ e j → i = j :=
  fun i hi j hj h ↦ hinj i hi j hj (gen_pow_inj (he i hi) (he j hj) h)

/-! ## Sorted orders (`sort_order`, `col_sort_order`) -/

/-- A bijection's ranks are `List.range n` up to order. -/
theorem perm_range_of_bijective {n : ℕ} {σ : Fin n → Fin n} (h : Function.Bijective σ) :
    (List.ofFn fun r ↦ (σ r : ℕ)).Perm (List.range n) := by
  rw [List.perm_ext_iff_of_nodup]
  · intro a
    simp only [List.mem_ofFn, List.mem_range]
    constructor
    · rintro ⟨r, rfl⟩
      exact (σ r).2
    · intro ha
      obtain ⟨r, hr⟩ := h.2 ⟨a, ha⟩
      exact ⟨r, by rw [hr]⟩
  · exact List.nodup_ofFn.mpr fun i j hij ↦ h.1 (Fin.ext hij)
  · exact List.nodup_range

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

/-- `stackOffsets`'s order (V:877-884): larger size first, ties by ascending index. -/
def stackLe (size : ℕ → ℕ) (i j : ℕ) : Bool :=
  decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))

/-- **The certified order is the specification's**: a permutation of `List.range n` whose
adjacent entries the guest checks (the size does not increase, G:1513 and G:1985; on equal sizes
the index does not decrease, G:1514-1517 and G:1986-1989) is `stackOffsets`'s `mergeSort` of
`List.range n` (V:877-884). -/
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

theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} :
    ∀ (cs : List α) (f : Fin cs.length → β), (∀ s : Fin cs.length, R cs[s] (f s)) →
      List.Forall₂ R cs (List.ofFn f)
  | [], _, _ => List.Forall₂.nil
  | c :: cs, f, h => by
    rw [List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn cs (fun s ↦ f s.succ) fun s ↦ h s.succ)

/-- **A cover holds every claim**: if every slot `s` of the claim list `cs` has a writer
`i < N` with `slot i = s`, and each writer's holder holds the claim in its slot, then there is a
list of holders, one a claim, `List.Forall₂`-related to the claims (as `NodeRel`'s
`List.Forall₂ (XmssHeld …)`, N:362-365, asks). -/
theorem forall₂_of_cover {α β : Type*} {R : α → β → Prop} {cs : List α} {N : ℕ}
    {slot : ℕ → ℕ} (holder : ℕ → β) (hcover : ∀ s < cs.length, ∃ i < N, slot i = s)
    (hR : ∀ i < N, ∀ h : slot i < cs.length, R cs[slot i] (holder i)) :
    ∃ hs : List β, List.Forall₂ R cs hs := by
  choose w hw hws using hcover
  refine ⟨List.ofFn fun s : Fin cs.length ↦ holder (w s s.2), forall₂_ofFn cs _ fun s ↦ ?_⟩
  have := hR (w s s.2) (hw s s.2) (by rw [hws]; exact s.2)
  simpa [hws] using this

end
end LeanVM.Guest.Value
