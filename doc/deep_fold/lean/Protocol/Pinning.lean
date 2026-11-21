/-
Lemma 4.11 of the paper (pinning).

For a finite set `S` of tuples of degree at most `d` (in the paper, the list of the committed
word), the vectors of `s` points at which two distinct members of `S` have equal evaluations at
ALL `s` points form the set `NonSep S ex s`. Its density among the `(q^2)^s` vectors is at most
`C(|S|, 2) ε^s` with `ε = (d + E) / q`, and outside it at most one member of `S` matches any
answer vector.
-/
import Protocol.Lists
import Protocol.Potential

open Polynomial Finset
open scoped Classical

namespace Protocol

open DeepFold

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- (E1) of Lemma 4.4 of the paper for a difference. -/
theorem evL_sub (ex : ι → ℕ) (z : K × K) (U V : ι → K[X]) :
    evL ex z (U - V) = evL ex z U - evL ex z V := by
  simp only [evL, Pi.sub_apply, eval_sub, mul_sub, sum_sub_distrib]

variable [Fintype K]

/-- Two distinct tuples of degree at most `d` have equal evaluations at no more than `(d + E) q`
of the `q^2` points `(θ, ζ)`: probability at most `ε = (d + E) / q` for one uniform point. -/
theorem card_evL_eq_le (ex : ι → ℕ) (hex : Function.Injective ex) {E d : ℕ}
    (hE : ∀ u, ex u ≤ E) {U U' : ι → K[X]} (hne : U ≠ U') (hU : ∀ u, (U u).natDegree ≤ d)
    (hU' : ∀ u, (U' u).natDegree ≤ d) :
    (univ.filter (fun z : K × K => evL ex z U = evL ex z U')).card ≤
      (d + E) * Fintype.card K := by
  have h := card_evL_zero_le ex hex hE (U - U') (sub_ne_zero.mpr hne)
    (fun u => (natDegree_sub_le_of_le (hU u) (hU' u)).trans_eq (max_self d))
  simpa only [evL_sub, sub_eq_zero] using h

/-- Two distinct tuples of degree at most `d` have equal evaluations at all of `s` points for at
most `((d + E) q)^s` of the `(q^2)^s` point vectors. -/
theorem card_evL_eq_all_le (ex : ι → ℕ) (hex : Function.Injective ex) {E d : ℕ}
    (hE : ∀ u, ex u ≤ E) {U U' : ι → K[X]} (hne : U ≠ U') (hU : ∀ u, (U u).natDegree ≤ d)
    (hU' : ∀ u, (U' u).natDegree ≤ d) (s : ℕ) :
    (univ.filter (fun z : Fin s → K × K => ∀ i, evL ex (z i) U = evL ex (z i) U')).card ≤
      ((d + E) * Fintype.card K) ^ s :=
  card_forall_pred_le s _ (card_evL_eq_le ex hex hE hne hU hU')

/-- The vectors of `s` points that do not separate `S`: two distinct members of `S` have equal
evaluations at all `s` points. It depends on `S` and the exponents only, not on answers. -/
noncomputable def NonSep (S : Finset (ι → K[X])) (ex : ι → ℕ) (s : ℕ) :
    Finset (Fin s → K × K) :=
  univ.filter (fun z => ∃ U ∈ S, ∃ U' ∈ S, U ≠ U' ∧ ∀ i, evL ex (z i) U = evL ex (z i) U')

/-- Lemma 4.11 of the paper, counting form: at most `C(|S|, 2) ((d + E) q)^s` of the `(q^2)^s` point
vectors do not separate `S`. -/
theorem card_nonSep_le {S : Finset (ι → K[X])} {ex : ι → ℕ} (hex : Function.Injective ex)
    {E d : ℕ} (hE : ∀ u, ex u ≤ E) (hS : ∀ U ∈ S, ∀ u, (U u).natDegree ≤ d) (s : ℕ) :
    (NonSep S ex s).card ≤ S.card.choose 2 * ((d + E) * Fintype.card K) ^ s := by
  have hsub : NonSep S ex s ⊆ (S.powersetCard 2).biUnion (fun p =>
      univ.filter (fun z : Fin s → K × K =>
        ∃ U ∈ p, ∃ U' ∈ p, U ≠ U' ∧ ∀ i, evL ex (z i) U = evL ex (z i) U')) := by
    intro z hz
    obtain ⟨U, hU, U', hU', hne, heq⟩ := (mem_filter.mp hz).2
    refine mem_biUnion.mpr ⟨{U, U'}, mem_powersetCard.mpr ⟨?_, card_pair hne⟩, ?_⟩
    · intro V hV
      rcases mem_insert.mp hV with rfl | hV
      · exact hU
      · rw [mem_singleton.mp hV]
        exact hU'
    · exact mem_filter.mpr ⟨mem_univ _, U, mem_insert_self _ _, U',
        mem_insert_of_mem (mem_singleton_self _), hne, heq⟩
  calc (NonSep S ex s).card ≤ _ := card_le_card hsub
    _ ≤ ∑ p ∈ S.powersetCard 2, (univ.filter (fun z : Fin s → K × K =>
          ∃ U ∈ p, ∃ U' ∈ p, U ≠ U' ∧ ∀ i, evL ex (z i) U = evL ex (z i) U')).card :=
        card_biUnion_le
    _ ≤ ∑ _p ∈ S.powersetCard 2, ((d + E) * Fintype.card K) ^ s := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpS, hp2⟩ := mem_powersetCard.mp hp
        obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hp2
        have ha : a ∈ S := hpS (mem_insert_self _ _)
        have hb : b ∈ S := hpS (mem_insert_of_mem (mem_singleton_self _))
        refine (card_le_card ?_).trans (card_evL_eq_all_le ex hex hE hab (hS a ha) (hS b hb) s)
        intro z hz
        obtain ⟨U, hU, U', hU', hne, heq⟩ := (mem_filter.mp hz).2
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        rcases mem_insert.mp hU with rfl | hU
        · rcases mem_insert.mp hU' with rfl | hU'
          · exact absurd rfl hne
          · rw [mem_singleton.mp hU'] at heq
            exact heq
        · rw [mem_singleton.mp hU] at heq hne
          rcases mem_insert.mp hU' with rfl | hU'
          · exact fun i => (heq i).symm
          · exact absurd (mem_singleton.mp hU').symm hne
    _ = S.card.choose 2 * ((d + E) * Fintype.card K) ^ s := by
        rw [sum_const, card_powersetCard, smul_eq_mul]

/-- Lemma 4.11 of the paper: for a set `S` of at most `L` tuples of degree at most `d`, `s`
independent uniform points fail to separate `S` with probability at most `C(L, 2) ε^s`,
`ε = (d + E) / q`. -/
theorem dens_nonSep_le {S : Finset (ι → K[X])} {ex : ι → ℕ} (hex : Function.Injective ex)
    {E d : ℕ} (hE : ∀ u, ex u ≤ E) (hS : ∀ U ∈ S, ∀ u, (U u).natDegree ≤ d) {L : ℕ}
    (hL : S.card ≤ L) (s : ℕ) :
    dens (fun z : Fin s → K × K => z ∈ NonSep S ex s) ≤
      (L.choose 2 : ℚ) * (((d + E : ℕ) : ℚ) / Fintype.card K) ^ s := by
  have h1 : ((NonSep S ex s).card : ℚ) ≤
      (L.choose 2 : ℚ) * (((d + E : ℕ) : ℚ) * Fintype.card K) ^ s := by
    have h := (card_nonSep_le hex hE hS s).trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hL))
    exact_mod_cast h
  have hq : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (Fin s → K × K) : ℚ) = ((Fintype.card K : ℚ) ^ 2) ^ s := by
    simp [Fintype.card_prod, sq]
  rw [dens_mem, hcard, div_le_iff₀ (by positivity)]
  refine h1.trans_eq ?_
  rw [div_pow, mul_pow]
  field_simp
  ring

/-- The use of separating points: outside `NonSep`, for every answer vector `y` at most one
member of `S` is consistent with all `s` answers. The answers come after the points. -/
theorem pinned_unique {S : Finset (ι → K[X])} {ex : ι → ℕ} {s : ℕ} {z : Fin s → K × K}
    (hz : z ∉ NonSep S ex s) (y : Fin s → K) {U U' : ι → K[X]} (hU : U ∈ S) (hU' : U' ∈ S)
    (h : ∀ i, evL ex (z i) U = y i) (h' : ∀ i, evL ex (z i) U' = y i) : U = U' := by
  by_contra hne
  exact hz (mem_filter.mpr ⟨mem_univ _, U, hU, U', hU', hne, fun i => (h i).trans (h' i).symm⟩)

/-- The same as a count: at most one member of `S` matches the answers. -/
theorem card_pinned_le_one {S : Finset (ι → K[X])} {ex : ι → ℕ} {s : ℕ} {z : Fin s → K × K}
    (hz : z ∉ NonSep S ex s) (y : Fin s → K) :
    (S.filter (fun U => ∀ i, evL ex (z i) U = y i)).card ≤ 1 :=
  card_le_one.mpr (fun _ hU _ hU' =>
    pinned_unique hz y (mem_filter.mp hU).1 (mem_filter.mp hU').1 (mem_filter.mp hU).2
      (mem_filter.mp hU').2)

/-- Lemma 4.11 for the list of an interleaved word, as the paper states it: if
`|List(O; A, d)| ≤ L`, the points fail to separate the list with probability at most
`C(L, 2) ε^s`. -/
theorem lemmaP (D : Finset K) (O : K → ι → K) (d A : ℕ) {ex : ι → ℕ}
    (hex : Function.Injective ex) {E : ℕ} (hE : ∀ u, ex u ≤ E) {L : ℕ}
    (hL : (listW D O d A).card ≤ L) (s : ℕ) :
    dens (fun z : Fin s → K × K => z ∈ NonSep (listW D O d A) ex s) ≤
      (L.choose 2 : ℚ) * (((d + E : ℕ) : ℚ) / Fintype.card K) ^ s :=
  dens_nonSep_le hex hE (listW_natDegree_le D O d A) hL s

end Protocol
