module

public import Quantum.Xmss.Assembly.MassSources
public import Quantum.Xmss.Assembly.PathBad

@[expose] public section

/-!
# The source-goodness bad fraction of leanXMSS's reparametrization

`Quantum.Xmss.Assembly.MassSources` leaves open the fraction of public data and hidden values that
are not source-good (`SrcGood`): a cell of an in-table slot is never the cell of another in-table
slot, or of the same slot with its designated source changed. Here it is bounded by the sequential
count of `Quantum.Xmss.Assembly.PathBad`, charging the first stage where an injectivity fails.

**Over abstract types.** Real paths `I` and virtual paths `V` (a real path with its designated
source changed), all with distinct first blocks. `SColl`: the cells of the real rounds collide
(`InjAll` fails), or for some virtual path `w` the cells of the real rounds and `w`'s collide. A
collision gives an event (`exists_ev_of_not_injAll`); with the real rounds injective, the event
pair contains a round of `w` (`sColl_ind_le`), so only `|R|² + |V| · 2m (N + m)` pairs are charged,
each at `1 / |X| + (G + 1) / |Z|` (`card_mul_sum_evCount_le`, `card_mul_sum_sColl_le`,
`frac_srcColl_le`).

**leanXMSS.** Paths are indexed by (in-table output position, designated-source value)
(`sBlk`, `sLen`, `sReal`, `sVirt`); their first blocks name the slot and carry the source value
(`sBlk_injOn`); the template's cells are the paths' (`srcCellK_eq_rnK`, `srcCellK'_eq_rnR`,
`roundH_fst_eq_rnZ`), so `¬SrcGood` gives `SColl` (`sColl_of_not_srcGood`). With `N = 8 |xI|`,
`m = 8`, `|V| ≤ |xI| · 2^128`:

* `srcBad_good_frac_le`: `PermGood π G ∧ ¬SrcGood` for at most `K / |X| + K (G + 1) / |Z|`,
  `K = N² + |xI| |Digest| · 2 · 8 (N + 8)`;
* `srcBad_frac_le`: `¬SrcGood` for at most the bad permutations plus that bound;
* `srcBad_frac_le_keccak`: at most `2^-290` (`K ≤ 2^217`, `G = 18`).
-/

open scoped ENNReal

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Over abstract types -/

section helpers

/-- A positive term bounds a double sum over two sets from below. -/
theorem one_le_sum_sum_of₂ {α β : Type*} {A : Finset α} {B : Finset β} (F : α → β → ℕ) {a : α}
    {b : β} (ha : a ∈ A) (hb : b ∈ B) (h : 1 ≤ F a b) : 1 ≤ ∑ a ∈ A, ∑ b ∈ B, F a b :=
  h.trans ((Finset.single_le_sum (f := fun b ↦ F a b) (fun _ _ ↦ Nat.zero_le _) hb).trans
    (Finset.single_le_sum (f := fun a ↦ ∑ b ∈ B, F a b) (fun _ _ ↦ Nat.zero_le _) ha))

/-- A constant factor through an exchange of two sums. -/
theorem mul_sum_sum_comm {T α : Type*} [Fintype T] (s : Finset α) (B : ℕ) (f : T → α → ℕ) :
    B * ∑ t, ∑ a ∈ s, f t a = ∑ a ∈ s, B * ∑ t, f t a := by
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The rounds of a path added to `I` are its own or `I`'s. -/
theorem mem_rnds_insert {S : Type} [DecidableEq S] {I : Finset S} {len : S → ℕ} {w : S}
    {a : S × ℕ} (ha : a ∈ rnds (insert w I) len) : a ∈ rnds {w} len ∨ a ∈ rnds I len := by
  obtain ⟨h1, h2⟩ := mem_rnds.mp ha
  rcases Finset.mem_insert.mp h1 with h | h
  · exact Or.inl (mem_rnds.mpr ⟨Finset.mem_singleton.mpr h, h2⟩)
  · exact Or.inr (mem_rnds.mpr ⟨h, h2⟩)

theorem mem_rnds_insert_of_single {S : Type} [DecidableEq S] {I : Finset S} {len : S → ℕ} {w : S}
    {a : S × ℕ} (ha : a ∈ rnds {w} len) : a ∈ rnds (insert w I) len := by
  obtain ⟨h1, h2⟩ := mem_rnds.mp ha
  exact mem_rnds.mpr ⟨Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h1)), h2⟩

theorem card_rnds_insert_le {S : Type} [DecidableEq S] (w : S) (I : Finset S) (len : S → ℕ) :
    (rnds (insert w I) len).card ≤ (rnds {w} len).card + (rnds I len).card :=
  (Finset.card_le_card fun _ ha ↦ Finset.mem_union.mpr (mem_rnds_insert ha)).trans
    (Finset.card_union_le _ _)

/-- Distinct first blocks on `I ∪ V` give distinct first blocks on the rounds of a subset. -/
theorem firstOn_rnds {S X : Type} [DecidableEq S] {blk : S → ℕ → X} {len : S → ℕ}
    {I V T : Finset S} (hT : T ⊆ I ∪ V) (hfirst : Set.InjOn (fun p ↦ blk p 0) ↑(I ∪ V)) :
    ∀ a ∈ rnds T len, ∀ b ∈ rnds T len, a.2 = 0 → b.2 = 0 → blk a.1 0 = blk b.1 0 → a.1 = b.1 :=
  fun _ ha _ hb _ _ e ↦ hfirst (Finset.mem_coe.mpr (hT (mem_rnds.mp ha).1))
    (Finset.mem_coe.mpr (hT (mem_rnds.mp hb).1)) e

/-- **From a count per fixed coordinate `q` to the fraction**: if for every `q` the event holds
for at most `K (|Z| + D |X|) / (|X| |Z|)` of `T`, it holds for at most `K / |X| + K D / |Z|` of
`Y ≃ Q × T`. -/
theorem frac_le_of_card_mul_sum_le {A B Q T Y : Type} [Fintype A] [Nonempty A] [Fintype B]
    [Nonempty B] [Fintype Q] [Nonempty Q] [Fintype T] [Nonempty T] [Fintype Y] (e : Q × T ≃ Y)
    (Bd : Y → Prop) [DecidablePred Bd] (K D : ℕ)
    (hq : ∀ q, Fintype.card A * Fintype.card B * ∑ t, (if Bd (e (q, t)) then 1 else 0) ≤
      Fintype.card T * (K * (Fintype.card B + D * Fintype.card A))) :
    (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card ≤
      (K : ℝ≥0∞) / Fintype.card A + ((K * D : ℕ) : ℝ≥0∞) / Fintype.card B := by
  have hcount : (Finset.univ.filter Bd).card = ∑ q, ∑ t, (if Bd (e (q, t)) then 1 else 0) := by
    rw [Finset.card_filter, ← Fintype.sum_equiv e (fun x ↦ if Bd (e x) then 1 else 0) _
      (fun _ ↦ rfl)]
    exact Fintype.sum_prod_type _
  have hY : Fintype.card Y = Fintype.card Q * Fintype.card T := by
    rw [← Fintype.card_congr e, Fintype.card_prod]
  have hnat : Fintype.card A * Fintype.card B * (Finset.univ.filter Bd).card ≤
      Fintype.card Y * (K * Fintype.card B + K * D * Fintype.card A) := by
    rw [hcount, Finset.mul_sum, hY]
    calc ∑ q, Fintype.card A * Fintype.card B * ∑ t, (if Bd (e (q, t)) then 1 else 0)
        ≤ ∑ _q : Q, Fintype.card T * (K * (Fintype.card B + D * Fintype.card A)) :=
          Finset.sum_le_sum fun q _ ↦ hq q
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have hA0 : (Fintype.card A : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB0 : (Fintype.card B : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hY0 : (Fintype.card Y : ℝ≥0∞) ≠ 0 := by
    rw [hY]
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero)
  have h1 := natCast_le_mul_div_of_mul_le
    (Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero) hnat
  calc (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card
      ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ * (Fintype.card Y *
          (((K * Fintype.card B + K * D * Fintype.card A : ℕ) : ℝ≥0∞) /
            ((Fintype.card A * Fintype.card B : ℕ) : ℝ≥0∞))) := by
        gcongr
    _ = ((K * Fintype.card B + K * D * Fintype.card A : ℕ) : ℝ≥0∞) /
          ((Fintype.card A * Fintype.card B : ℕ) : ℝ≥0∞) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hY0 (ENNReal.natCast_ne_top _), one_mul]
    _ = _ := by
        push_cast
        rw [ENNReal.add_div, ENNReal.mul_div_mul_right _ _ hB0 (ENNReal.natCast_ne_top _),
          mul_comm (Fintype.card A : ℝ≥0∞) (Fintype.card B : ℝ≥0∞),
          ENNReal.mul_div_mul_right _ _ hA0 (ENNReal.natCast_ne_top _)]

end helpers

section generic

variable {X Z S : Type} [AddCommGroup X] [AddCommGroup Z]
variable (π : Equiv.Perm (X × Z)) (blk : S → ℕ → X)

/-- **All cells of the rounds `R` are distinct**, per kind (`k`, `k'`, `h`). -/
def InjAll (R : Finset (S × ℕ)) (h : Z → X) (k k' : X → Z) : Prop :=
  Set.InjOn (famK π blk h k k') R ∧ Set.InjOn (famR π blk h k k') R ∧
    Set.InjOn (famZ π blk h k k') R

/-- **The source-collision event**: the cells of the real rounds collide, or for some virtual path
`w` the cells of the real rounds and `w`'s collide. -/
def SColl [DecidableEq S] (len : S → ℕ) (I V : Finset S) (h : Z → X) (k k' : X → Z) : Prop :=
  ¬InjAll π blk (rnds I len) h k k' ∨ ∃ w ∈ V, ¬InjAll π blk (rnds (insert w I) len) h k k'

open scoped Classical in
/-- The events of a pair of rounds, counted. -/
noncomputable def evCount (R : Finset (S × ℕ)) (a b : S × ℕ)
    (t : (Z → X) × (X → Z) × (X → Z)) : ℕ :=
  (if EvK π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
    (if EvR π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
    (if EvZ π blk R a b t.1 t.2.1 t.2.2 then 1 else 0)

variable {π blk}

/-- A collision of any cells comes with an event. -/
theorem exists_ev_of_not_injAll {R : Finset (S × ℕ)} {h : Z → X} {k k' : X → Z}
    (hfirst : ∀ a ∈ R, ∀ b ∈ R, a.2 = 0 → b.2 = 0 → blk a.1 0 = blk b.1 0 → a.1 = b.1)
    (hn : ¬InjAll π blk R h k k') :
    ∃ a ∈ R, ∃ b ∈ R, EvK π blk R a b h k k' ∨ EvR π blk R a b h k k' ∨
      EvZ π blk R a b h k k' := by
  by_contra hno
  push Not at hno
  have hall := preK_all hfirst hno
  exact hn ⟨fun a ha b hb e ↦ (hall (a.2 + b.2 + 1)).1 a (Finset.mem_coe.mp ha) b
      (Finset.mem_coe.mp hb) (by omega) (by omega) e,
    fun a ha b hb e ↦ (hall (a.2 + b.2 + 1)).2.1 a (Finset.mem_coe.mp ha) b
      (Finset.mem_coe.mp hb) (by omega) (by omega) e,
    fun a ha b hb e ↦ (hall (a.2 + b.2 + 1)).2.2 a (Finset.mem_coe.mp ha) b
      (Finset.mem_coe.mp hb) (by omega) (by omega) e⟩

/-- Rounds whose cells are injective carry no event, relative to any rounds `R'`. -/
theorem not_ev_of_injAll {R R' : Finset (S × ℕ)} {h : Z → X} {k k' : X → Z} {a b : S × ℕ}
    (hinj : InjAll π blk R h k k') (ha : a ∈ R) (hb : b ∈ R) :
    ¬(EvK π blk R' a b h k k' ∨ EvR π blk R' a b h k k' ∨ EvZ π blk R' a b h k k') := by
  obtain ⟨hK, hR, hZ⟩ := hinj
  rintro (hE | hE | hE)
  · exact hE.1.2.2.1 (hK (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hE.2)
  · exact hE.1.2.1 (hR (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hE.2)
  · exact hE.1.2.1 (hZ (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hE.2)

open scoped Classical in
theorem one_le_evCount {R : Finset (S × ℕ)} {a b : S × ℕ} {t : (Z → X) × (X → Z) × (X → Z)}
    (hev : EvK π blk R a b t.1 t.2.1 t.2.2 ∨ EvR π blk R a b t.1 t.2.1 t.2.2 ∨
      EvZ π blk R a b t.1 t.2.1 t.2.2) :
    1 ≤ evCount π blk R a b t := by
  unfold evCount
  rcases hev with h1 | h2 | h3
  · exact le_add_right (le_add_right (by rw [ite_eq_left h1]))
  · exact le_add_right (le_add_left (by rw [ite_eq_left h2]))
  · exact le_add_left (by rw [ite_eq_left h3])

open scoped Classical in
/-- **The events of one pair of rounds** hold for at most a fraction
`(|Z| + (G + 1) |X|) / (|X| |Z|)` of the keys. -/
theorem card_mul_sum_evCount_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {R : Finset (S × ℕ)} (hR : DownClosed R) {G : ℕ} (hG : ∀ x r, rateCount π x r ≤ G)
    {a b : S × ℕ} (ha : a ∈ R) (hb : b ∈ R) :
    Fintype.card X * Fintype.card Z * ∑ t, evCount π blk R a b t ≤
      Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
        (Fintype.card Z + (G + 1) * Fintype.card X) := by
  set M := Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z)
  have hK : Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
      (if EvK π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * 1 :=
    card_mul_sum_triple_le₁ (fun h k k' ↦ if EvK π blk R a b h k k' then 1 else 0) _ _
      fun k k' ↦ card_mul_sum_evK_le hR ha hb k k'
  have hRr : Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
      (if EvR π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * G :=
    card_mul_sum_triple_le₂ (fun h k k' ↦ if EvR π blk R a b h k k' then 1 else 0) _ _
      fun h k' ↦ card_mul_sum_evR_le hR hG ha hb h k'
  have hZz : Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
      (if EvZ π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * 1 :=
    card_mul_sum_triple_le₃ (fun h k k' ↦ if EvZ π blk R a b h k k' then 1 else 0) _ _
      fun h k ↦ card_mul_sum_evZ_le hR ha hb h k
  simp only [evCount, Finset.sum_add_distrib]
  calc Fintype.card X * Fintype.card Z * (∑ t : (Z → X) × (X → Z) × (X → Z),
        (if EvK π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
        ∑ t : (Z → X) × (X → Z) × (X → Z),
          (if EvR π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
        ∑ t : (Z → X) × (X → Z) × (X → Z),
          (if EvZ π blk R a b t.1 t.2.1 t.2.2 then 1 else 0))
      = Fintype.card Z * (Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
          (if EvK π blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) +
        Fintype.card X * (Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
          (if EvR π blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) +
        Fintype.card X * (Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
          (if EvZ π blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) := by ring
    _ ≤ Fintype.card Z * (M * 1) + Fintype.card X * (M * G) + Fintype.card X * (M * 1) :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hK)
          (Nat.mul_le_mul_left _ hRr)) (Nat.mul_le_mul_left _ hZz)
    _ = M * (Fintype.card Z + (G + 1) * Fintype.card X) := by ring

open scoped Classical in
/-- **The charged pairs**: the source-collision event is covered by the events of pairs of real
rounds, and of pairs of a virtual path's rounds with the rounds of it and the real paths. -/
theorem sColl_ind_le [DecidableEq S] {len : S → ℕ} {I V : Finset S}
    (hfirst : Set.InjOn (fun p ↦ blk p 0) ↑(I ∪ V)) (t : (Z → X) × (X → Z) × (X → Z)) :
    (if SColl π blk len I V t.1 t.2.1 t.2.2 then 1 else 0) ≤
      ∑ a ∈ rnds I len, ∑ b ∈ rnds I len, evCount π blk (rnds I len) a b t +
        ∑ w ∈ V, ∑ a ∈ rnds {w} len, ∑ b ∈ rnds (insert w I) len,
          (evCount π blk (rnds (insert w I) len) a b t +
            evCount π blk (rnds (insert w I) len) b a t) := by
  by_cases hs : SColl π blk len I V t.1 t.2.1 t.2.2
  · rw [ite_eq_left hs]
    by_cases hI : InjAll π blk (rnds I len) t.1 t.2.1 t.2.2
    · obtain ⟨w, hw, hn⟩ := Or.resolve_left hs (not_not.mpr hI)
      obtain ⟨a, ha, b, hb, hev⟩ := exists_ev_of_not_injAll
        (firstOn_rnds (Finset.insert_subset (Finset.mem_union_right _ hw)
          Finset.subset_union_left) hfirst) hn
      refine le_add_left (le_trans ?_ (Finset.single_le_sum (f := fun w ↦
        ∑ a ∈ rnds {w} len, ∑ b ∈ rnds (insert w I) len,
          (evCount π blk (rnds (insert w I) len) a b t +
            evCount π blk (rnds (insert w I) len) b a t)) (fun _ _ ↦ Nat.zero_le _) hw))
      rcases mem_rnds_insert ha with haw | haI
      · exact one_le_sum_sum_of₂ (fun a b ↦ evCount π blk (rnds (insert w I) len) a b t +
          evCount π blk (rnds (insert w I) len) b a t) haw hb
          (le_add_right (one_le_evCount hev))
      · rcases mem_rnds_insert hb with hbw | hbI
        · exact one_le_sum_sum_of₂ (fun a b ↦ evCount π blk (rnds (insert w I) len) a b t +
            evCount π blk (rnds (insert w I) len) b a t) hbw ha
            (le_add_left (one_le_evCount hev))
        · exact absurd hev (not_ev_of_injAll hI haI hbI)
    · obtain ⟨a, ha, b, hb, hev⟩ :=
        exists_ev_of_not_injAll (firstOn_rnds Finset.subset_union_left hfirst) hI
      exact le_add_right (one_le_sum_sum_of _ ha hb (one_le_evCount hev))
  · rw [ite_eq_right hs]
    exact Nat.zero_le _

open scoped Classical in
/-- **The source-collision count**: for at most a fraction
`(N² + |V| · 2m (N + m)) (|Z| + (G + 1) |X|) / (|X| |Z|)` of the keys, with at most `N` real rounds
and `m` rounds per virtual path, if `π`'s rate counts are at most `G` and the first blocks are
distinct. -/
theorem card_mul_sum_sColl_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [DecidableEq S] {len : S → ℕ} {I V : Finset S}
    (hfirst : Set.InjOn (fun p ↦ blk p 0) ↑(I ∪ V)) {G : ℕ} (hG : ∀ x r, rateCount π x r ≤ G)
    {N m nV : ℕ} (hN : (rnds I len).card ≤ N) (hm : ∀ w ∈ V, (rnds {w} len).card ≤ m)
    (hV : V.card ≤ nV) :
    Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if SColl π blk len I V t.1 t.2.1 t.2.2 then 1 else 0) ≤
      Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
        ((N * N + nV * (2 * (m * (N + m)))) * (Fintype.card Z + (G + 1) * Fintype.card X)) := by
  set B := Fintype.card X * Fintype.card Z
  set C := Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
    (Fintype.card Z + (G + 1) * Fintype.card X) with hC
  have hpair : ∀ R : Finset (S × ℕ), DownClosed R → ∀ a ∈ R, ∀ b ∈ R,
      B * ∑ t, evCount π blk R a b t ≤ C :=
    fun _ hR _ ha _ hb ↦ card_mul_sum_evCount_le hR hG ha hb
  have hRw : ∀ w ∈ V, (rnds (insert w I) len).card ≤ N + m := fun w hw ↦
    (card_rnds_insert_le w I len).trans (by have := hm w hw; omega)
  calc B * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if SColl π blk len I V t.1 t.2.1 t.2.2 then 1 else 0)
      ≤ B * ∑ t : (Z → X) × (X → Z) × (X → Z),
          (∑ a ∈ rnds I len, ∑ b ∈ rnds I len, evCount π blk (rnds I len) a b t +
            ∑ w ∈ V, ∑ a ∈ rnds {w} len, ∑ b ∈ rnds (insert w I) len,
              (evCount π blk (rnds (insert w I) len) a b t +
                evCount π blk (rnds (insert w I) len) b a t)) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun t _ ↦ sColl_ind_le hfirst t)
    _ = ∑ a ∈ rnds I len, ∑ b ∈ rnds I len, B * ∑ t, evCount π blk (rnds I len) a b t +
          ∑ w ∈ V, ∑ a ∈ rnds {w} len, ∑ b ∈ rnds (insert w I) len,
            (B * ∑ t, evCount π blk (rnds (insert w I) len) a b t +
              B * ∑ t, evCount π blk (rnds (insert w I) len) b a t) := by
        rw [Finset.sum_add_distrib, mul_add]
        congr 1
        · rw [mul_sum_sum_comm]
          exact Finset.sum_congr rfl fun a _ ↦ mul_sum_sum_comm _ _ _
        · rw [mul_sum_sum_comm]
          refine Finset.sum_congr rfl fun w _ ↦ ?_
          rw [mul_sum_sum_comm]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [mul_sum_sum_comm]
          refine Finset.sum_congr rfl fun b _ ↦ ?_
          rw [Finset.sum_add_distrib, mul_add]
    _ ≤ ∑ _a ∈ rnds I len, ∑ _b ∈ rnds I len, C +
          ∑ w ∈ V, ∑ _a ∈ rnds {w} len, ∑ _b ∈ rnds (insert w I) len, (C + C) :=
        add_le_add
          (Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum fun b hb ↦
            hpair _ (downClosed_rnds I len) a ha b hb)
          (Finset.sum_le_sum fun w _ ↦ Finset.sum_le_sum fun a ha ↦
            Finset.sum_le_sum fun b hb ↦ add_le_add
              (hpair _ (downClosed_rnds _ len) a (mem_rnds_insert_of_single ha) b hb)
              (hpair _ (downClosed_rnds _ len) b hb a (mem_rnds_insert_of_single ha)))
    _ = (rnds I len).card * ((rnds I len).card * C) +
          ∑ w ∈ V, (rnds {w} len).card * ((rnds (insert w I) len).card * (C + C)) := by
        simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ N * (N * C) + ∑ _w ∈ V, m * ((N + m) * (C + C)) :=
        add_le_add (Nat.mul_le_mul hN (Nat.mul_le_mul_right _ hN))
          (Finset.sum_le_sum fun w hw ↦
            Nat.mul_le_mul (hm w hw) (Nat.mul_le_mul_right _ (hRw w hw)))
    _ ≤ N * (N * C) + nV * (m * ((N + m) * (C + C))) := by
        refine add_le_add le_rfl ?_
        rw [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ hV
    _ = _ := by
        rw [hC]
        ring

open scoped Classical in
/-- **The source-collision fraction.** If the coordinates `Y` are `(q, (h, k, k'))`, each `q`
fixing a permutation `π q`, real paths `I q` and virtual paths `V q` with distinct first blocks,
at most `N` real rounds, `m` rounds per virtual path and `nV` virtual paths, and the event `Bd`
gives a `PermGood (π q) G` permutation and the source-collision event, then `Bd` holds for at most
a fraction `K / |X| + K (G + 1) / |Z|` of `Y`, `K = N² + nV · 2m (N + m)`. -/
theorem frac_srcColl_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq S]
    {Q Y : Type} [Fintype Q] [Nonempty Q] [Fintype Y]
    (e : Q × ((Z → X) × (X → Z) × (X → Z)) ≃ Y) (πf : Q → Equiv.Perm (X × Z))
    (blk : Q → S → ℕ → X) (len : Q → S → ℕ) (I V : Q → Finset S)
    (hfirst : ∀ q, Set.InjOn (fun p ↦ blk q p 0) ↑(I q ∪ V q)) (G N m nV : ℕ)
    (hN : ∀ q, (rnds (I q) (len q)).card ≤ N) (hm : ∀ q, ∀ w ∈ V q, (rnds {w} (len q)).card ≤ m)
    (hV : ∀ q, (V q).card ≤ nV) (Bd : Y → Prop) [DecidablePred Bd]
    (hBd : ∀ q t, Bd (e (q, t)) → PermGood (πf q) G ∧
      SColl (πf q) (blk q) (len q) (I q) (V q) t.1 t.2.1 t.2.2) :
    (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card ≤
      ((N * N + nV * (2 * (m * (N + m))) : ℕ) : ℝ≥0∞) / Fintype.card X +
        (((N * N + nV * (2 * (m * (N + m)))) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z := by
  refine frac_le_of_card_mul_sum_le e Bd _ (G + 1) fun q ↦ ?_
  have hT : Fintype.card ((Z → X) × (X → Z) × (X → Z)) =
      Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) := by
    simp only [Fintype.card_prod]
    ring
  by_cases hG : PermGood (πf q) G
  · rw [hT]
    calc Fintype.card X * Fintype.card Z * ∑ t, (if Bd (e (q, t)) then 1 else 0)
        ≤ Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
            (if SColl (πf q) (blk q) (len q) (I q) (V q) t.1 t.2.1 t.2.2 then 1 else 0) :=
          Nat.mul_le_mul_left _ (sum_ite_le_of_imp _ _ fun t ht ↦ (hBd q t ht).2)
      _ ≤ _ := card_mul_sum_sColl_le (hfirst q) hG.rate (hN q) (hm q) (hV q)
  · have h0 : ∀ t, ¬Bd (e (q, t)) := fun t ht ↦ hG (hBd q t ht).1
    simp [h0]

end generic

/-! ## leanXMSS -/

section xmss

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-! ### Paths indexed by (output position, designated-source value) -/

/-- The blocks of the in-table output `a.1`'s slot input, with its designated source set to
`a.2`. -/
def sBlk (P : PublicParameter) (v : ValPos → Digest) (a : ValPos × Digest) : ℕ → X :=
  xBlk P (Function.update v (dsrc (outSlot a.1)) a.2) a.1

/-- The number of blocks of such a path. -/
def sLen (P : PublicParameter) (a : ValPos × Digest) : ℕ :=
  xLen P a.1

/-- **The real paths**: every in-table output with its designated source's value. -/
def sReal (v : ValPos → Digest) : Finset (ValPos × Digest) :=
  xI.image fun p ↦ (p, v (dsrc (outSlot p)))

theorem mem_sReal {v : ValPos → Digest} {a : ValPos × Digest} :
    a ∈ sReal v ↔ a.1 ∈ xI ∧ a.2 = v (dsrc (outSlot a.1)) := by
  unfold sReal
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨a.1, h1, Prod.ext rfl h2.symm⟩

theorem card_sReal_le (v : ValPos → Digest) : (sReal v).card ≤ xI.card := by
  unfold sReal
  exact Finset.card_image_le

/-- **The virtual paths**: every in-table output with its designated source changed. -/
def sVirt (v : ValPos → Digest) : Finset (ValPos × Digest) :=
  (xI ×ˢ Finset.univ).filter fun a ↦ a.2 ≠ v (dsrc (outSlot a.1))

theorem mem_sVirt {v : ValPos → Digest} {a : ValPos × Digest} :
    a ∈ sVirt v ↔ a.1 ∈ xI ∧ a.2 ≠ v (dsrc (outSlot a.1)) := by
  unfold sVirt
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨fun hh ↦ ⟨hh.1.1, hh.2⟩, fun hh ↦ ⟨⟨hh.1, Finset.mem_univ _⟩, hh.2⟩⟩

theorem card_sVirt_le (v : ValPos → Digest) :
    (sVirt v).card ≤ xI.card * Fintype.card Digest := by
  unfold sVirt
  exact (Finset.card_filter_le _ _).trans
    (le_of_eq (by rw [Finset.card_product, Finset.card_univ]))

attribute [irreducible] sReal sVirt

theorem sLen_le (P : PublicParameter) (a : ValPos × Digest) : sLen P a ≤ 8 := by
  unfold sLen
  exact xLen_le P a.1

theorem card_rnds_sReal_le (P : PublicParameter) (v : ValPos → Digest) :
    (rnds (sReal v) (sLen P)).card ≤ 8 * xI.card := by
  have h1 : (rnds (sReal v) (sLen P)).card ≤ 8 * (sReal v).card :=
    card_rnds_le (sReal v) (sLen P) (m := 8) (sLen_le P)
  have h2 := card_sReal_le v
  omega

theorem card_rnds_single_le (P : PublicParameter) (w : ValPos × Digest) :
    (rnds {w} (sLen P)).card ≤ 8 := by
  have h1 : (rnds {w} (sLen P)).card ≤ 8 * ({w} : Finset (ValPos × Digest)).card :=
    card_rnds_le {w} (sLen P) (m := 8) (sLen_le P)
  rw [Finset.card_singleton, mul_one] at h1
  exact h1

/-! ### First blocks -/

theorem xBlk_zero (P : PublicParameter) (v : ValPos → Digest) (p : ValPos) :
    xBlk P v p 0 =
      blockOf (firstBlock (thInput P (slotFields (outSlot p)) (slotPayload v (outSlot p)))) := by
  unfold xBlk
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, head?_blocks, Option.getD_some]

/-- An in-table output's first block carries its designated source's value. -/
theorem payloadLo_xBlk {P : PublicParameter} {v : ValPos → Digest} {p : ValPos} (hp : InPos p) :
    payloadLo (xBlk P v p 0) = v (dsrc (outSlot p)) := by
  have h := payloadLo_cellK_zero (xPub (P, 1, 0, 0) 0) (inTable_outSlot hp) v
  rw [cellK_zero] at h
  rw [xBlk_zero]
  exact h

/-- **The paths' first blocks are distinct**: they name the slot and carry the source value. -/
theorem sBlk_injOn (P : PublicParameter) (v : ValPos → Digest) :
    Set.InjOn (fun a ↦ sBlk P v a 0) ↑(sReal v ∪ sVirt v) := by
  have hx : ∀ a ∈ (↑(sReal v ∪ sVirt v) : Set (ValPos × Digest)), InPos a.1 := fun a ha ↦ by
    rcases Finset.mem_union.mp (Finset.mem_coe.mp ha) with h | h
    · exact mem_xI.mp (mem_sReal.mp h).1
    · exact mem_xI.mp (mem_sVirt.mp h).1
  intro a ha b hb e
  have hpa := hx a ha
  have hpb := hx b hb
  have e' : xBlk P (Function.update v (dsrc (outSlot a.1)) a.2) a.1 0 =
      xBlk P (Function.update v (dsrc (outSlot b.1)) b.2) b.1 0 := e
  have h1 := slotOfBlock_xBlk P (Function.update v (dsrc (outSlot a.1)) a.2) hpa
  rw [e', slotOfBlock_xBlk P _ hpb] at h1
  have hab : outSlot a.1 = outSlot b.1 := (Option.some.inj h1).symm
  have h11 : a.1 = b.1 := by
    rw [← slotOutPos_outSlot hpa, hab, slotOutPos_outSlot hpb]
  have h2 := payloadLo_xBlk (P := P) (v := Function.update v (dsrc (outSlot a.1)) a.2) hpa
  rw [Function.update_self, e', payloadLo_xBlk hpb, Function.update_self] at h2
  exact Prod.ext h11 h2.symm

/-! ### The template's cells are the paths' -/

/-- **The template's `k`-cells are the path's.** -/
theorem srcCellK_eq_rnK (w : XW) (h : Z → X) (s : Slot) (f : ValPos → Digest) {j : ℕ}
    (hj : j < nBlocks (xPub w h) s) :
    srcCellK (xPub w h) s f j = rnK w.2.1 h w.2.2.1 w.2.2.2
      (fun i ↦ (blocks (slotInput (xPub w h) s f)).getD i 0) j := by
  show (stateAt (xPub w h) (blocks (slotInput (xPub w h) s f)) j).1 +
    (blocks (slotInput (xPub w h) s f)).getD j 0 = _
  rw [stateAt_eq_rnSt w h _ j (by rw [length_blocks_slotInput]; omega)]
  rfl

/-- **The template's `k'`-cells are the path's.** -/
theorem srcCellK'_eq_rnR (w : XW) (h : Z → X) (s : Slot) (f : ValPos → Digest) {j : ℕ}
    (hj : j < nBlocks (xPub w h) s) :
    srcCellK' (xPub w h) s f j = rnR w.2.1 h w.2.2.1 w.2.2.2
      (fun i ↦ (blocks (slotInput (xPub w h) s f)).getD i 0) j := by
  show (midAt (xPub w h) (stateAt (xPub w h) (blocks (slotInput (xPub w h) s f)) j)
    ((blocks (slotInput (xPub w h) s f)).getD j 0)).1 = _
  rw [stateAt_eq_rnSt w h _ j (by rw [length_blocks_slotInput]; omega)]
  rfl

/-- **A failure of pair goodness is a collision** of the real rounds, or of the real rounds and a
virtual path's. -/
theorem not_pairGood_cases {C : Type} {w : XW} {h : Z → X} {v : ValPos → Digest}
    {c : Slot → (ValPos → Digest) → ℕ → C} {ex : ℕ → ℕ → Prop}
    {F : (ValPos × Digest) × ℕ → C}
    (hc : ∀ p ∈ xI, ∀ d j, j < xLen w.1 p →
      c (outSlot p) (Function.update v (dsrc (outSlot p)) d) j = F ((p, d), j))
    (hn : ¬PairGood (nBlocks (xPub w h)) c ex v) :
    ¬Set.InjOn F ↑(rnds (sReal v) (sLen w.1)) ∨
      ∃ a ∈ sVirt v, ¬Set.InjOn F ↑(rnds (insert a (sReal v)) (sLen w.1)) := by
  by_contra hcon
  have hI : Set.InjOn F ↑(rnds (sReal v) (sLen w.1)) := by
    by_contra h1
    exact hcon (Or.inl h1)
  have hV : ∀ a ∈ sVirt v, Set.InjOn F ↑(rnds (insert a (sReal v)) (sLen w.1)) :=
    fun a ha ↦ by
      by_contra h1
      exact hcon (Or.inr ⟨a, ha, h1⟩)
  apply hn
  intro s s' hs hs' j hj j' hj' _ d hd he
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ xI, outSlot p = s :=
    ⟨slotOutPos s, mem_xI.mpr (inPos_slotOutPos hs), outSlot_slotOutPos hs⟩
  obtain ⟨p', hp', rfl⟩ : ∃ p ∈ xI, outSlot p = s' :=
    ⟨slotOutPos s', mem_xI.mpr (inPos_slotOutPos hs'), outSlot_slotOutPos hs'⟩
  have hb := hc p' hp' (v (dsrc (outSlot p'))) j' hj'
  rw [Function.update_eq_self] at hb
  have heq : F ((p, d), j) = F ((p', v (dsrc (outSlot p'))), j') := by
    rw [← hc p hp d j hj, ← hb]
    exact he.symm
  have hne : ((p, d), j) ≠ ((p', v (dsrc (outSlot p'))), j') := by
    intro e
    have e1 : p = p' := congrArg (fun x ↦ x.1.1) e
    have e2 : d = v (dsrc (outSlot p')) := congrArg (fun x ↦ x.1.2) e
    subst e1
    rcases hd with h1 | h1
    · exact h1 rfl
    · exact h1 e2
  have hbI : (p', v (dsrc (outSlot p'))) ∈ sReal v := mem_sReal.mpr ⟨hp', rfl⟩
  have hbR : ∀ T : Finset (ValPos × Digest), (p', v (dsrc (outSlot p'))) ∈ T →
      (((p', v (dsrc (outSlot p'))), j') : (ValPos × Digest) × ℕ) ∈
        (↑(rnds T (sLen w.1)) : Set ((ValPos × Digest) × ℕ)) :=
    fun T hT ↦ Finset.mem_coe.mpr (mem_rnds.mpr ⟨hT, hj'⟩)
  by_cases hdv : d = v (dsrc (outSlot p))
  · exact hne (hI (Finset.mem_coe.mpr (mem_rnds.mpr ⟨mem_sReal.mpr ⟨hp, hdv⟩, hj⟩))
      (hbR _ hbI) heq)
  · exact hne (hV (p, d) (mem_sVirt.mpr ⟨hp, hdv⟩)
      (Finset.mem_coe.mpr (mem_rnds.mpr ⟨Finset.mem_insert_self _ _, hj⟩))
      (hbR _ (Finset.mem_insert_of_mem hbI)) heq)

/-- **A source-bad table is a source collision.** -/
theorem sColl_of_not_srcGood {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hn : ¬SrcGood (xPub w h) v) :
    SColl w.2.1 (sBlk w.1 v) (sLen w.1) (sReal v) (sVirt v) h w.2.2.1 w.2.2.2 := by
  by_contra hcon
  have hI : InjAll w.2.1 (sBlk w.1 v) (rnds (sReal v) (sLen w.1)) h w.2.2.1 w.2.2.2 := by
    by_contra h1
    exact hcon (Or.inl h1)
  have hV : ∀ a ∈ sVirt v,
      InjAll w.2.1 (sBlk w.1 v) (rnds (insert a (sReal v)) (sLen w.1)) h w.2.2.1 w.2.2.2 :=
    fun a ha ↦ by
      by_contra h1
      exact hcon (Or.inr ⟨a, ha, h1⟩)
  obtain ⟨hIK, hIR, hIZ⟩ := hI
  apply hn
  refine ⟨?_, ?_, ?_⟩
  · by_contra hK
    rcases not_pairGood_cases (F := famK w.2.1 (sBlk w.1 v) h w.2.2.1 w.2.2.2)
      (fun p _ d j hj ↦ srcCellK_eq_rnK w h (outSlot p) _ hj) hK with h1 | ⟨a, ha, h1⟩
    · exact h1 hIK
    · exact h1 (hV a ha).1
  · by_contra hR
    rcases not_pairGood_cases (F := famR w.2.1 (sBlk w.1 v) h w.2.2.1 w.2.2.2)
      (fun p _ d j hj ↦ srcCellK'_eq_rnR w h (outSlot p) _ hj) hR with
      h1 | ⟨a, ha, h1⟩
    · exact h1 hIR
    · exact h1 (hV a ha).2.1
  · by_contra hZ
    rcases not_pairGood_cases (F := famZ w.2.1 (sBlk w.1 v) h w.2.2.1 w.2.2.2)
      (fun p _ d j hj ↦ roundH_fst_eq_rnZ w h (outSlot p) _ hj) hZ with
      h1 | ⟨a, ha, h1⟩
    · exact h1 hIZ
    · exact h1 (hV a ha).2.2

/-! ### The fraction -/

/-- The public data and hidden values other than the keys. -/
abbrev SQ : Type :=
  PublicParameter × Equiv.Perm (X × Z) × Rest × (ValPos → Digest)

/-- The public data and hidden values as `(q, (h, k, k'))`. -/
def sEquiv : SQ × ((Z → X) × (X → Z) × (X → Z)) ≃ PX × (ValPos → Digest) where
  toFun x := (((x.2.1, (x.1.1, x.1.2.1, x.2.2.1, x.2.2.2)), x.1.2.2.1), x.1.2.2.2)
  invFun y := ((y.1.1.2.1, y.1.1.2.2.1, y.1.2, y.2), (y.1.1.1, y.1.1.2.2.2.1, y.1.1.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The public data and hidden values as `(π, rest)`. -/
def pxPermEquiv : PX × (ValPos → Digest) ≃
    Equiv.Perm (X × Z) × ((Z → X) × PublicParameter × (X → Z) × (X → Z) × Rest ×
      (ValPos → Digest)) where
  toFun y := (y.1.1.2.2.1, (y.1.1.1, y.1.1.2.1, y.1.1.2.2.2.1, y.1.1.2.2.2.2, y.1.2, y.2))
  invFun x := (((x.2.1, (x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1)), x.2.2.2.2.2.1), x.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- **The source-bad event on good permutations**: `PermGood π G ∧ ¬SrcGood` for at most a
fraction `K / |X| + K (G + 1) / |Z|` of the public data and hidden values,
`K = (8 |xI|)² + |xI| |Digest| · 2 · 8 (8 |xI| + 8)`. -/
theorem srcBad_good_frac_le (G : ℕ) :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ ¬SrcGood (pubX y.1) y.2).card ≤
      ((8 * xI.card * (8 * xI.card) +
          xI.card * Fintype.card Digest * (2 * (8 * (8 * xI.card + 8))) : ℕ) : ℝ≥0∞) /
          Fintype.card X +
        (((8 * xI.card * (8 * xI.card) +
          xI.card * Fintype.card Digest * (2 * (8 * (8 * xI.card + 8)))) * (G + 1) : ℕ) :
            ℝ≥0∞) / Fintype.card Z :=
  frac_srcColl_le sEquiv (fun q ↦ q.2.1) (fun q ↦ sBlk q.1 q.2.2.2) (fun q ↦ sLen q.1)
    (fun q ↦ sReal q.2.2.2) (fun q ↦ sVirt q.2.2.2) (fun q ↦ sBlk_injOn q.1 q.2.2.2) G _ 8 _
    (fun q ↦ card_rnds_sReal_le q.1 q.2.2.2) (fun q w _ ↦ card_rnds_single_le q.1 w)
    (fun q ↦ card_sVirt_le q.2.2.2) _ fun q t hb ↦
      ⟨hb.1, sColl_of_not_srcGood (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1) (v := q.2.2.2)
        hb.2⟩

open scoped Classical in
/-- **The source-bad fraction of leanXMSS** (MassSources' last term of `goodT_bad_frac_le`):
`¬SrcGood` for at most the bad permutations plus `K / |X| + K (G + 1) / |Z|`. -/
theorem srcBad_frac_le (G : ℕ) :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) +
            xI.card * Fintype.card Digest * (2 * (8 * (8 * xI.card + 8))) : ℕ) : ℝ≥0∞) /
            Fintype.card X +
          (((8 * xI.card * (8 * xI.card) +
            xI.card * Fintype.card Digest * (2 * (8 * (8 * xI.card + 8)))) * (G + 1) : ℕ) :
              ℝ≥0∞) / Fintype.card Z) := by
  set N := Fintype.card (PX × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp
    (fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2)
    (fun y : PX × (ValPos → Digest) ↦ ¬PermGood (pxPermEquiv y).1 G)
    (fun y : PX × (ValPos → Digest) ↦ PermGood y.1.1.2.2.1 G ∧ ¬SrcGood (pubX y.1) y.2)
    fun y hy ↦ by
      by_cases hG : PermGood y.1.1.2.2.1 G
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv y).1 G).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ ¬SrcGood (pubX y.1) y.2).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv y).1 G).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ ¬SrcGood (pubX y.1) y.2).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst pxPermEquiv fun π ↦ ¬PermGood π G]
        exact add_le_add le_rfl (srcBad_good_frac_le G)

/-! ### At Keccak's sizes -/

theorem card_digest : Fintype.card Digest = 2 ^ 128 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  norm_num [digestBits]

set_option exponentiation.threshold 4096 in
/-- The source-collision terms at Keccak's sizes, for `n ≤ 498 · 2^32` outputs and `G = 18`:
`K ≤ 2^217`. -/
theorem srcCollTerms_le {n cD cX cZ : ℕ} (hn : n ≤ 498 * 2 ^ 32) (hD : cD = 2 ^ 128)
    (hX : cX = 2 ^ 1088) (hZ : cZ = 2 ^ 512) :
    ((8 * n * (8 * n) + n * cD * (2 * (8 * (8 * n + 8))) : ℕ) : ℝ≥0∞) / cX +
        (((8 * n * (8 * n) + n * cD * (2 * (8 * (8 * n + 8)))) * (18 + 1) : ℕ) : ℝ≥0∞) / cZ ≤
      ENNReal.ofReal (2 ^ 217 / 2 ^ 1088 + 2 ^ 217 * 19 / 2 ^ 512) := by
  subst hD hX hZ
  have hK : 8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8))) ≤ 2 ^ 217 :=
    calc 8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8)))
        ≤ 8 * (498 * 2 ^ 32) * (8 * (498 * 2 ^ 32)) +
          498 * 2 ^ 32 * 2 ^ 128 * (2 * (8 * (8 * (498 * 2 ^ 32) + 8))) := by gcongr
      _ ≤ 2 ^ 217 := by norm_num
  have hK' : (8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8)))) * (18 + 1) ≤
      2 ^ 217 * 19 :=
    (Nat.mul_le_mul_right _ hK).trans_eq (by norm_num)
  rw [natCast_div_eq_ofReal _ (2 ^ 1088) (by positivity),
    natCast_div_eq_ofReal _ (2 ^ 512) (by positivity),
    ← ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have hb : ((8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8))) : ℕ) : ℝ) /
      ((2 ^ 1088 : ℕ) : ℝ) ≤ 2 ^ 217 / 2 ^ 1088 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
  have hc : (((8 * n * (8 * n) + n * 2 ^ 128 * (2 * (8 * (8 * n + 8)))) * (18 + 1) : ℕ) : ℝ) /
      ((2 ^ 512 : ℕ) : ℝ) ≤ 2 ^ 217 * 19 / 2 ^ 512 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hK') (by positivity)
  exact add_le_add hb hc

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The source-bad fraction at Keccak's sizes**: at most `2^-290` (with `G = 18`: the bad
permutations `2^-777`, the source collisions `19 · 2^217 / 2^512 + 2^217 / 2^1088`, from
`|xI| ≤ 498 · 2^32` and `2^128` source values). -/
theorem srcBad_frac_le_keccak :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2).card ≤
      ENNReal.ofReal (1 / 2 ^ 290) := by
  refine ((srcBad_frac_le 18).trans (add_le_add permTerm_le_keccak
    (srcCollTerms_le card_xI_le card_digest rnCard_X rnCard_Z))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end xmss

end Quantum.Xmss.Assembly

end
