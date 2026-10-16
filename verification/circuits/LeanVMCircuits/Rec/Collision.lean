module

public import LeanVMCircuits.Rec.RecParts
public import LeanVMCircuits.Rec.RoundSound

@[expose] public section

/-!
Collision resistance as a bounded event of the ideal compression model.

`Bind.PairCR` asks two answers' compressions (`HashCRP`) and output windows (`WindowCRP`) not to collide on the rows a transcript binds from given seeds, and `Edges.RecParts` names the event `crBad` off which they do not. Here the compression is a uniformly drawn function `h : X → Y` and the prover an adaptive strategy `σ : List Y → X`: its query `i` is `σ` at the answers to its queries before `i` (`query`).

- `Collision.event_card`: for a symmetric relation `R` on answers, the oracles at which two distinct queries among the first `Q` have related answers are at most `e · Q · (Q - 1) / (2 d)` of all, where every answer is related to at most `e / d` of `Y`. The proof charges the event to the first query whose answer is related to an earlier one (`Collision.fresh_card`, by resampling that answer).
- `Collision.birthday_frac`: the adaptive birthday bound, two distinct queries with equal answers on at most `Q · (Q - 1) / (2 |Y|)` of the oracles.
- `Collision.win_frac`: for answers of four words in `V`, a window hit (`Collision.WinOn`: inputs `a`, `b` of one chaining value and `a'`, `b'` of another, alike off it pairwise, whose answers agree on four words straddling `a`'s and `b`'s) on at most `2 · Q · (Q - 1) · (Q - 2) / |V|^4` of the oracles. The proof charges it to the last first query of the four (`Collision.winHit_charged`): its fresh answer must agree on the window's words in its block with one answer per earlier pair of first queries agreeing on the other block's words (`Collision.winTargets_card`), and those pairs are at most `t · (t - 1) / |V|^(4 - |W|)` in expectation (`Collision.freshPairs_sum`), so the hit is a full four-word event (`Collision.charged_card`). An output block's other inputs (counter, finalization, message) are constants, which the window rule takes as premises, so the two blocks' inputs are determined by their chaining values.

`Bind.hashCRP_of_oracle` and `Bind.windowCRP_of_oracle` give `HashCRP` and `WindowCRP` from the ideal model's consistency on the live rows (`Bind.OracleRows`: every hash row not dropped that a rule firing on the live nodes reads has its outputs the oracle at its inputs, and its inputs among the queries) and the oracle off those events on the queries; `Bind.pairCR_of_oracle` bundles them.

`Edges.crEvent` is the event over outcomes that pair other coins with the oracle, bounded by `Edges.epsCR` of the number of compression queries (`Edges.crEvent_frac`). `Edges.PcsBound` is the PCS interface (#551), and `Edges.tree_sound_eps` is `tree_sound_parts` with the `pcsBad` and `crBad` fractions replaced by their bounds.
-/

namespace LeanVMCircuits.Rec.Collision

open Finset

variable {X Y : Type}

/-! An adaptive prover against an oracle. -/

/-- The oracle's answers to the prover's first `n` queries: query `i` is the strategy at the answers before it. -/
def answers (σ : List Y → X) (h : X → Y) : ℕ → List Y
  | 0 => []
  | n + 1 => answers σ h n ++ [h (σ (answers σ h n))]

/-- The prover's query `n`. -/
def query (σ : List Y → X) (h : X → Y) (n : ℕ) : X := σ (answers σ h n)

/-- Query `m` is new: no earlier query is it. -/
def Fresh (σ : List Y → X) (h : X → Y) (m : ℕ) : Prop := ∀ i < m, query σ h i ≠ query σ h m

/-- The event of relation `R`: two distinct queries among the first `Q` have related answers. -/
def Event (R : Y → Y → Prop) (σ : List Y → X) (h : X → Y) (Q : ℕ) : Prop :=
  ∃ i < Q, ∃ i' < Q, query σ h i ≠ query σ h i' ∧ R (h (query σ h i)) (h (query σ h i'))

theorem answers_length (σ : List Y → X) (h : X → Y) (n : ℕ) : (answers σ h n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [answers, ih]

theorem mem_answers {σ : List Y → X} {h : X → Y} {i n : ℕ} (hi : i < n) : h (query σ h i) ∈ answers σ h n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [answers, List.mem_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inl (ih hi)
    · exact Or.inr (by simp [query])

/-- Two oracles agreeing on the prover's first `n` queries give it the same answers. -/
theorem answers_congr {σ : List Y → X} {h g : X → Y} {n : ℕ} (hg : ∀ i < n, g (query σ h i) = h (query σ h i)) :
    answers σ g n = answers σ h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e := ih fun i hi => hg i (by omega)
    change answers σ g n ++ [g (σ (answers σ g n))] = answers σ h n ++ [h (σ (answers σ h n))]
    rw [e]
    exact congrArg (fun y => answers σ h n ++ [y]) (hg n (Nat.lt_succ_self n))

theorem query_congr {σ : List Y → X} {h g : X → Y} {n : ℕ} (hg : ∀ i < n, g (query σ h i) = h (query σ h i)) :
    query σ g n = query σ h n := by
  simp only [query, answers_congr hg]

/-- Every query's first occurrence is fresh. -/
theorem first_fresh (σ : List Y → X) (h : X → Y) (i : ℕ) : ∃ a ≤ i, query σ h a = query σ h i ∧ Fresh σ h a := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hf : Fresh σ h i
    · exact ⟨i, le_rfl, rfl, hf⟩
    · simp only [Fresh, not_forall, not_not] at hf
      obtain ⟨i', hi', he⟩ := hf
      obtain ⟨a, ha, hq, hfa⟩ := ih i' hi'
      exact ⟨a, by omega, hq.trans he, hfa⟩

/-- The event lands on a fresh query whose answer is related to an earlier answer. -/
theorem event_fresh {R : Y → Y → Prop} (hR : ∀ y z, R y z → R z y) {σ : List Y → X} {h : X → Y} {Q : ℕ}
    (he : Event R σ h Q) : ∃ m < Q, Fresh σ h m ∧ ∃ z ∈ answers σ h m, R (h (query σ h m)) z := by
  obtain ⟨i, hi, i', hi', hne, hr⟩ := he
  obtain ⟨a, ha, hqa, hfa⟩ := first_fresh σ h i
  obtain ⟨b, hb, hqb, hfb⟩ := first_fresh σ h i'
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact ⟨b, by omega, hfb, _, mem_answers hab, by rw [hqa, hqb]; exact hR _ _ hr⟩
  · exact absurd (hqa.symm.trans hqb) hne
  · exact ⟨a, by omega, hfa, _, mem_answers hab, by rw [hqa, hqb]; exact hr⟩

open Classical in
/-- Resampling a fresh query's answer: the oracles at which fresh query `m`'s answer is in a set `S` of the answers before it, times `|Y|`, are at most the sum over all oracles of `|S|`. -/
theorem fresh_card [Fintype X] [Fintype Y] (σ : List Y → X) (m : ℕ) (S : List Y → Finset Y) :
    (univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ S (answers σ h m)).card * Fintype.card Y ≤
      ∑ g : X → Y, (S (answers σ g m)).card := by
  set A := univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ S (answers σ h m)
  have hl : A.card * Fintype.card Y = (A ×ˢ (univ : Finset Y)).card := by rw [card_product, card_univ]
  rw [hl, ← card_sigma]
  -- the updated oracle agrees with `h` on the queries before `m`
  have hagree : ∀ h : X → Y, Fresh σ h m → ∀ y, ∀ i < m,
      Function.update h (query σ h m) y (query σ h i) = h (query σ h i) :=
    fun h hf y i hi => Function.update_of_ne (hf i hi) _ _
  refine card_le_card_of_injOn (fun p => (⟨Function.update p.1 (query σ p.1 m) p.2, p.1 (query σ p.1 m)⟩ :
    Σ _ : X → Y, Y)) ?_ ?_
  · intro p hp
    simp only [coe_product, Set.mem_prod, mem_coe, A, mem_filter, mem_univ, true_and] at hp
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_univ, true_and]
    rw [answers_congr (hagree p.1 hp.1.1 p.2)]
    exact hp.1.2
  · rintro ⟨h1, y1⟩ hp1 ⟨h2, y2⟩ hp2 he
    simp only [coe_product, Set.mem_prod, mem_coe, A, mem_filter, mem_univ, true_and] at hp1 hp2
    simp only [Sigma.mk.injEq] at he
    obtain ⟨hg, hz⟩ := he
    have hz := eq_of_heq hz
    have q1 := query_congr (hagree h1 hp1.1.1 y1)
    have q2 := query_congr (hagree h2 hp2.1.1 y2)
    rw [hg] at q1
    have hx : query σ h1 m = query σ h2 m := q1.symm.trans q2
    have hy : y1 = y2 := by
      have := congrFun hg (query σ h1 m)
      rwa [Function.update_self, hx, Function.update_self] at this
    refine Prod.ext ?_ hy
    funext a
    by_cases ha : a = query σ h1 m
    · subst ha
      show h1 (query σ h1 m) = h2 (query σ h1 m)
      rw [hz, hx]
    · have := congrFun hg a
      rw [Function.update_of_ne ha, Function.update_of_ne (by rwa [← hx])] at this
      exact this

open Classical in
/-- The generic adaptive bound: if every answer is related by `R` to at most `e / d` of `Y`, the oracles at which two distinct queries among the first `Q` have related answers are, times `2 d`, at most `e · Q · (Q - 1)` times all. -/
theorem event_card [Fintype X] [Fintype Y] [Nonempty Y] (R : Y → Y → Prop) (hR : ∀ y z, R y z → R z y) {d e : ℕ}
    (hde : ∀ z, (univ.filter fun y => R y z).card * d ≤ e * Fintype.card Y) (σ : List Y → X) (Q : ℕ) :
    (univ.filter fun h : X → Y => Event R σ h Q).card * d * 2 ≤ e * (Q * (Q - 1)) * Fintype.card (X → Y) := by
  set N := Fintype.card (X → Y)
  set S : List Y → Finset Y := fun as => as.toFinset.biUnion fun z => univ.filter fun y => R y z
  set G : ℕ → Finset (X → Y) := fun m =>
    univ.filter fun h : X → Y => Fresh σ h m ∧ h (query σ h m) ∈ S (answers σ h m)
  have hS : ∀ as : List Y, (S as).card * d ≤ as.length * e * Fintype.card Y := by
    intro as
    calc (S as).card * d ≤ (∑ z ∈ as.toFinset, (univ.filter fun y => R y z).card) * d :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ z ∈ as.toFinset, (univ.filter fun y => R y z).card * d := sum_mul _ _ _
      _ ≤ ∑ z ∈ as.toFinset, e * Fintype.card Y := sum_le_sum fun z _ => hde z
      _ = as.toFinset.card * (e * Fintype.card Y) := by rw [sum_const, smul_eq_mul]
      _ ≤ as.length * (e * Fintype.card Y) := Nat.mul_le_mul_right _ (List.toFinset_card_le as)
      _ = _ := by ring
  have hG : ∀ m, (G m).card * d ≤ m * e * N := by
    intro m
    have hY : 0 < Fintype.card Y := Fintype.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hY
    calc (G m).card * d * Fintype.card Y = (G m).card * Fintype.card Y * d := by ring
      _ ≤ (∑ g : X → Y, (S (answers σ g m)).card) * d := Nat.mul_le_mul_right _ (fresh_card σ m S)
      _ = ∑ g : X → Y, (S (answers σ g m)).card * d := sum_mul _ _ _
      _ ≤ ∑ _g : X → Y, m * e * Fintype.card Y := sum_le_sum fun g _ => by
          simpa [answers_length] using hS (answers σ g m)
      _ = m * e * N * Fintype.card Y := by rw [sum_const, card_univ, smul_eq_mul]; ring
  have hcov : (univ.filter fun h : X → Y => Event R σ h Q) ⊆ (range Q).biUnion G := by
    intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh
    obtain ⟨m, hm, hf, z, hz, hr⟩ := event_fresh hR hh
    simp only [mem_biUnion, mem_range, G, S, mem_filter, mem_univ, true_and, List.mem_toFinset]
    exact ⟨m, hm, hf, z, hz, hr⟩
  calc (univ.filter fun h : X → Y => Event R σ h Q).card * d * 2
      ≤ (∑ m ∈ range Q, (G m).card) * d * 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ((card_le_card hcov).trans card_biUnion_le))
    _ = (∑ m ∈ range Q, (G m).card * d) * 2 := by rw [sum_mul]
    _ ≤ (∑ m ∈ range Q, m * e * N) * 2 := Nat.mul_le_mul_right _ (sum_le_sum fun m _ => hG m)
    _ = (∑ m ∈ range Q, m) * 2 * (e * N) := by rw [← sum_mul, ← sum_mul]; ring
    _ = e * (Q * (Q - 1)) * N := by rw [sum_range_id_mul_two]; ring

/-- A fraction bound from a count bound. -/
theorem frac_le {a b d M : ℕ} (hd : 0 < d) (h : a * d ≤ b * M) : (a : ℚ≥0) / M ≤ (b : ℚ≥0) / d := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · simp [hM]
  · rw [div_le_div_iff₀ (by exact_mod_cast hM) (by exact_mod_cast hd)]
    exact_mod_cast h

/-! The adaptive birthday bound. -/

/-- A collision: two distinct queries among the first `Q` with equal answers. -/
def Coll (σ : List Y → X) (h : X → Y) (Q : ℕ) : Prop := Event (· = ·) σ h Q

open Classical in
theorem birthday_card [Fintype X] [Fintype Y] [Nonempty Y] (σ : List Y → X) (Q : ℕ) :
    (univ.filter fun h : X → Y => Coll σ h Q).card * Fintype.card Y * 2 ≤
      Q * (Q - 1) * Fintype.card (X → Y) := by
  have := event_card (· = ·) (fun _ _ h => h.symm) (d := Fintype.card Y) (e := 1) (fun z => by
    rw [filter_eq' univ z]; simp) σ Q
  rw [one_mul] at this
  exact this

open Classical in
/-- The adaptive birthday bound: a uniform oracle `h : X → Y` gives a prover of `Q` adaptive queries two distinct queries with equal answers with probability at most `Q · (Q - 1) / (2 |Y|)`. -/
theorem birthday_frac [Fintype X] [Fintype Y] [Nonempty Y] (σ : List Y → X) (Q : ℕ) :
    ((univ.filter fun h : X → Y => Coll σ h Q).card : ℚ≥0) / Fintype.card (X → Y) ≤
      ((Q * (Q - 1) : ℕ) : ℚ≥0) / ((2 * Fintype.card Y : ℕ) : ℚ≥0) :=
  frac_le (by have := Fintype.card_pos (α := Y); omega) (by
    have := birthday_card σ Q; rw [mul_comm 2]; linarith)

/-- Non-vacuity: two queries to an oracle from `Bool` to `Unit` always collide, and the bound is `2 · 1 / 2 = 1`. -/
example : ∀ h : Bool → Unit, Coll (fun as : List Unit => decide (as.length = 1)) h 2 :=
  fun h => ⟨0, by omega, 1, by omega, by simp [query, answers], rfl⟩

/-- Mutation test: the identity oracle on `Bool` gives the two distinct queries distinct answers, so no collision. -/
example : ¬ Coll (fun as : List Bool => decide (as.length = 1)) id 2 := by
  rintro ⟨i, hi, i', hi', hne, he⟩
  exact hne he

/-- Non-vacuity of the bound: one query never collides. -/
example (σ : List Bool → Bool) (h : Bool → Bool) : ¬ Coll σ h 1 := by
  rintro ⟨i, hi, i', hi', hne, _⟩
  exact hne (by rw [show i = 0 by omega, show i' = 0 by omega])

/-! Off the events, on the queries. -/

/-- The prover's first `Q` queries. -/
def queries (σ : List Y → X) (h : X → Y) (Q : ℕ) : Set X := {x | ∃ i < Q, query σ h i = x}

theorem injOn_of_not_coll {σ : List Y → X} {h : X → Y} {Q : ℕ} (hc : ¬ Coll σ h Q) :
    Set.InjOn h (queries σ h Q) := by
  rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩ he
  by_contra hne
  exact hc ⟨i, hi, i', hi', hne, he⟩

/-! A window straddling two answers of one chaining value. -/

variable {V C R : Type}

/-- Answers `y`, `y'` agree on the words of `W`. -/
def AgreeOn (W : Finset (Fin 4)) (y y' : Fin 4 → V) : Prop := ∀ k ∈ W, y k = y' k

theorem AgreeOn.symm {W : Finset (Fin 4)} {y y' : Fin 4 → V} (h : AgreeOn W y y') : AgreeOn W y' y :=
  fun k hk => (h k hk).symm

/-- The words from word `j` on. -/
def hiW (j : ℕ) : Finset (Fin 4) := univ.filter fun k => j ≤ k.val

/-- A window over inputs `Qs`: inputs `a`, `b` of one chaining value (`ch`) and `a'`, `b'` of another, `a'` alike
with `a` and `b'` with `b` off the chaining value (`re`), `a` and `b` not alike, whose answers agree on a window of
four words from word `j` of `a`'s on into `b`'s, `1 ≤ j < 4`. Two output blocks of distinct chaining values agreeing
on a window straddling them are such four inputs, the blocks' other inputs being constants. -/
def WinOn (ch : X → C) (re : X → R) (H : X → Fin 4 → V) (Qs : Set X) : Prop :=
  ∃ a ∈ Qs, ∃ b ∈ Qs, ∃ a' ∈ Qs, ∃ b' ∈ Qs, re a = re a' ∧ re b = re b' ∧ ch a = ch b ∧ ch a' = ch b' ∧
    ch a ≠ ch a' ∧ re a ≠ re b ∧ ∃ j, 1 ≤ j ∧ j < 4 ∧ AgreeOn (hiW j) (H a) (H a') ∧ AgreeOn (hiW j)ᶜ (H b) (H b')

/-- A window hit among the prover's first `Q` queries. -/
def WinHit (ch : X → C) (re : X → R) (σ : List (Fin 4 → V) → X) (h : X → Fin 4 → V) (Q : ℕ) : Prop :=
  WinOn ch re h (queries σ h Q)

open Classical in
/-- Answers agreeing with `z` on `W` and answers agreeing with `z'` off `W` are at most all answers together: an answer
is its words on `W` and off them. -/
theorem agree_mul_le [Fintype V] (W : Finset (Fin 4)) (z z' : Fin 4 → V) :
    #{y | AgreeOn W y z} * #{y | AgreeOn Wᶜ y z'} ≤ Fintype.card (Fin 4 → V) := by
  rw [← card_product, ← card_univ]
  refine card_le_card_of_injOn (fun p => fun k => if k ∈ W then p.2 k else p.1 k)
    (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
  rintro ⟨y1, y1'⟩ h1 ⟨y2, y2'⟩ h2 he
  simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and] at h1 h2
  have hk := fun k => congrFun he k
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · by_cases hkW : k ∈ W
    · exact (h1.1 k hkW).trans (h2.1 k hkW).symm
    · simpa [hkW] using hk k
  · by_cases hkW : k ∈ W
    · simpa [hkW] using hk k
    · exact (h1.2 k (mem_compl.mpr hkW)).trans (h2.2 k (mem_compl.mpr hkW)).symm

/-- Query `i` read off a list of answers: the strategy at its first `i`. -/
def qAt (σ : List Y → X) (as : List Y) (i : ℕ) : X := σ (as.take i)

theorem answers_take (σ : List Y → X) (h : X → Y) {m n : ℕ} (hmn : m ≤ n) :
    (answers σ h n).take m = answers σ h m := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    rfl
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · rw [answers, List.take_append_of_le_length (by rw [answers_length]; omega), ih (by omega)]
    · obtain rfl : m = n + 1 := by omega
      exact List.take_of_length_le (by rw [answers_length])

theorem qAt_answers (σ : List Y → X) (h : X → Y) {m n : ℕ} (hmn : m ≤ n) :
    qAt σ (answers σ h n) m = query σ h m := by
  simp only [qAt, query, answers_take σ h hmn]

theorem answers_getElem (σ : List Y → X) (h : X → Y) {i n : ℕ} (hi : i < (answers σ h n).length) :
    (answers σ h n)[i] = h (query σ h i) := by
  induction n with
  | zero => simp [answers] at hi
  | succ n ih =>
    have hl := answers_length σ h n
    simp only [answers]
    rcases Nat.lt_or_ge i n with hin | hin
    · rw [List.getElem_append_left (by omega)]
      exact ih (by omega)
    · have hi' : i < n + 1 := by rw [answers_length] at hi; exact hi
      obtain rfl : i = n := by omega
      rw [List.getElem_append_right (by omega)]
      simp [hl, query]

open Classical in
/-- The answers a fresh query after answers `as` must give to end a window hit there, its word set `W`: agreeing on
`W` with the answer to an earlier query `a` alike with it off the chaining value and of the chaining value of a first
query `b`, where a first query `b'` of its own chaining value, alike with `b`, answers as `b` does off `W`. -/
noncomputable def winTargets [Fintype V] (ch : X → C) (re : X → R) (W : Finset (Fin 4)) (σ : List (Fin 4 → V) → X)
    (as : List (Fin 4 → V)) : Finset (Fin 4 → V) :=
  univ.filter fun y => ∃ i i' l : Fin as.length, i ≠ i' ∧ (∀ m < i.val, qAt σ as m ≠ qAt σ as i) ∧
    (∀ m < i'.val, qAt σ as m ≠ qAt σ as i') ∧ AgreeOn Wᶜ as[i] as[i'] ∧ re (qAt σ as l) = re (σ as) ∧
    ch (qAt σ as l) = ch (qAt σ as i) ∧ re (qAt σ as i) = re (qAt σ as i') ∧ ch (qAt σ as i') = ch (σ as) ∧
    AgreeOn W y as[l]

open Classical in
/-- The ordered pairs of distinct first queries before `t` whose answers agree off `W`. -/
noncomputable def freshPairs (W : Finset (Fin 4)) (σ : List (Fin 4 → V) → X) (h : X → Fin 4 → V) (t : ℕ) :
    Finset (ℕ × ℕ) :=
  (range t).offDiag.filter fun p => Fresh σ h p.1 ∧ Fresh σ h p.2 ∧
    AgreeOn Wᶜ (h (query σ h p.1)) (h (query σ h p.2))

section Count

variable [Fintype X] [Fintype V]

open Classical in
/-- At most `A` answers per pair of first queries agreeing off `W`: the earlier query `a` a fresh one ends a window
hit with is one input, alike with it off the chaining value and of the pair's first chaining value. -/
theorem winTargets_card (ch : X → C) (re : X → R) (hinj : ∀ x y, re x = re y → ch x = ch y → x = y)
    (W : Finset (Fin 4)) {A : ℕ} (hA : ∀ z : Fin 4 → V, #{y | AgreeOn W y z} ≤ A) (σ : List (Fin 4 → V) → X)
    (g : X → Fin 4 → V) (t : ℕ) : #(winTargets ch re W σ (answers σ g t)) ≤ #(freshPairs W σ g t) * A := by
  set as := answers σ g t
  have hlen : as.length = t := answers_length σ g t
  have hq : ∀ m, m ≤ t → qAt σ as m = query σ g m := fun m hm => qAt_answers σ g hm
  have hget : ∀ (i : ℕ) (hi : i < as.length), as[i] = g (query σ g i) := fun i hi => answers_getElem σ g hi
  -- each target is in the set of some fresh pair
  let T : ℕ × ℕ → Finset (Fin 4 → V) := fun p => univ.filter fun y => ∃ l < t,
    re (query σ g l) = re (query σ g t) ∧ ch (query σ g l) = ch (query σ g p.1) ∧ AgreeOn W y (g (query σ g l))
  have hsub : winTargets ch re W σ as ⊆ (freshPairs W σ g t).biUnion T := by
    intro y hy
    simp only [winTargets, mem_filter, mem_univ, true_and] at hy
    obtain ⟨i, i', l, hii, fi, fi', hag, h1, h2, h3, h4, h5⟩ := hy
    have hit : i.val < t := hlen ▸ i.isLt
    have hit' : i'.val < t := hlen ▸ i'.isLt
    have hlt : l.val < t := hlen ▸ l.isLt
    rw [hq _ hit.le] at fi h2 h3
    rw [hq _ hit'.le] at fi' h3 h4
    rw [hq _ hlt.le] at h1 h2
    simp only [Fin.getElem_fin] at hag h5
    rw [hget _ i.isLt, hget _ i'.isLt] at hag
    rw [hget _ l.isLt] at h5
    have hσ : σ as = query σ g t := rfl
    rw [hσ] at h1 h4
    refine mem_biUnion.mpr ⟨(i.val, i'.val), ?_, ?_⟩
    · simp only [freshPairs, mem_filter, mem_offDiag, mem_range]
      refine ⟨⟨hit, hit', fun he => hii (Fin.ext he)⟩, fun m hm => ?_, fun m hm => ?_, hag⟩
      · rw [← hq _ (by omega)]
        exact fi m hm
      · rw [← hq _ (by omega)]
        exact fi' m hm
    · simp only [T, mem_filter, mem_univ, true_and]
      exact ⟨l.val, hlt, h1, h2, h5⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [card_eq_sum_ones, sum_mul]
  refine sum_le_sum fun p _ => ?_
  rw [one_mul]
  rcases (T p).eq_empty_or_nonempty with he | ⟨y₀, hy₀⟩
  · rw [he, card_empty]
    exact Nat.zero_le _
  · simp only [T, mem_filter, mem_univ, true_and] at hy₀
    obtain ⟨l₀, -, hr₀, hc₀, -⟩ := hy₀
    refine (card_le_card fun y hy => ?_).trans (hA (g (query σ g l₀)))
    simp only [T, mem_filter, mem_univ, true_and] at hy ⊢
    obtain ⟨l, -, hr, hc, hag⟩ := hy
    rwa [← hinj _ _ (hr.trans hr₀.symm) (hc.trans hc₀.symm)]

open Classical in
/-- Pairs of first queries agreeing off `W`, summed over the oracles: per ordered pair, resampling the later one's
answer, at most `B / |Y|` of the oracles, `B` the answers agreeing with one off `W`. -/
theorem freshPairs_sum (W : Finset (Fin 4)) {B : ℕ} (hB : ∀ z : Fin 4 → V, #{y | AgreeOn Wᶜ y z} ≤ B)
    (σ : List (Fin 4 → V) → X) (t : ℕ) :
    (∑ g : X → Fin 4 → V, #(freshPairs W σ g t)) * Fintype.card (Fin 4 → V) ≤
      t * (t - 1) * (Fintype.card (X → Fin 4 → V) * B) := by
  have hswap : ∑ g : X → Fin 4 → V, #(freshPairs W σ g t) =
      ∑ p ∈ (range t).offDiag, #{g : X → Fin 4 → V | Fresh σ g p.1 ∧ Fresh σ g p.2 ∧
        AgreeOn Wᶜ (g (query σ g p.1)) (g (query σ g p.2))} := by
    simp only [freshPairs, card_filter]
    exact sum_comm
  -- one ordered pair: the later query's answer is fresh and agrees off `W` with the earlier's
  have hpair : ∀ p ∈ (range t).offDiag, #{g : X → Fin 4 → V | Fresh σ g p.1 ∧ Fresh σ g p.2 ∧
      AgreeOn Wᶜ (g (query σ g p.1)) (g (query σ g p.2))} * Fintype.card (Fin 4 → V) ≤
      Fintype.card (X → Fin 4 → V) * B := by
    intro p hp
    simp only [mem_offDiag, mem_range] at hp
    obtain ⟨-, -, hne⟩ := hp
    -- `e` the earlier of the two, `m` the later
    have key : ∀ e m : ℕ, #{g : X → Fin 4 → V | Fresh σ g m ∧ ∃ z ∈ (answers σ g m)[e]?,
        AgreeOn Wᶜ (g (query σ g m)) z} * Fintype.card (Fin 4 → V) ≤ Fintype.card (X → Fin 4 → V) * B := by
      intro e m
      let S : List (Fin 4 → V) → Finset (Fin 4 → V) := fun as => univ.filter fun y => ∃ z ∈ as[e]?, AgreeOn Wᶜ y z
      have hS : ∀ as, #(S as) ≤ B := by
        intro as
        cases hz : as[e]? with
        | none =>
          rw [show S as = ∅ from filter_eq_empty_iff.mpr fun y _ ⟨z, hzm, _⟩ => by rw [hz] at hzm; simp at hzm]
          exact Nat.zero_le _
        | some z =>
          refine (card_le_card fun y hy => ?_).trans (hB z)
          simp only [S, mem_filter, mem_univ, true_and, hz, Option.mem_def, Option.some.injEq] at hy ⊢
          obtain ⟨z', rfl, hy⟩ := hy
          exact hy
      calc _ ≤ ∑ g : X → Fin 4 → V, #(S (answers σ g m)) := by
            refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun g hg => ?_)) (fresh_card σ m S)
            simp only [S, mem_filter, mem_univ, true_and] at hg ⊢
            exact hg
        _ ≤ ∑ _g : X → Fin 4 → V, B := sum_le_sum fun g _ => hS _
        _ = _ := by rw [sum_const, card_univ, smul_eq_mul]
    have hget : ∀ (g : X → Fin 4 → V) e m, e < m → g (query σ g e) ∈ (answers σ g m)[e]? := by
      intro g e m hem
      have hl : e < (answers σ g m).length := by rw [answers_length]; exact hem
      rw [List.getElem?_eq_getElem hl, answers_getElem]
      rfl
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun g hg => ?_)) (key p.1 p.2)
      simp only [mem_filter, mem_univ, true_and] at hg ⊢
      exact ⟨hg.2.1, _, hget g _ _ hlt, hg.2.2.symm⟩
    · refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun g hg => ?_)) (key p.2 p.1)
      simp only [mem_filter, mem_univ, true_and] at hg ⊢
      exact ⟨hg.1, _, hget g _ _ hlt, hg.2.2⟩
  rw [hswap, sum_mul]
  calc _ ≤ ∑ _p ∈ (range t).offDiag, Fintype.card (X → Fin 4 → V) * B := sum_le_sum hpair
    _ = t * (t - 1) * (Fintype.card (X → Fin 4 → V) * B) := by
        rw [sum_const, offDiag_card, card_range, smul_eq_mul, Nat.mul_sub_one]

open Classical in
/-- The answers agreeing with `z` on `U` are as many as those agreeing with `z'` on `U`. -/
theorem agree_card_eq (U : Finset (Fin 4)) (z z' : Fin 4 → V) : #{y | AgreeOn U y z} = #{y | AgreeOn U y z'} := by
  refine card_nbij' (fun y k => if k ∈ U then z' k else y k) (fun y k => if k ∈ U then z k else y k) ?_ ?_ ?_ ?_
  · intro y _
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    intro k hk
    simp [hk]
  · intro y _
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    intro k hk
    simp [hk]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
    funext k
    by_cases hk : k ∈ U
    · simp [hk, hy k hk]
    · simp [hk]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
    funext k
    by_cases hk : k ∈ U
    · simp [hk, hy k hk]
    · simp [hk]

open Classical in
/-- The oracles at which fresh query `t` ends a window hit with word set `W`, times `|Y|`, are at most
`t · (t - 1)` times all: per pair of first queries agreeing off `W` (`freshPairs_sum`), the fresh answer agrees on `W`
with one answer (`winTargets_card`), and agreeing on `W` and off it is one answer (`agree_mul_le`). -/
theorem charged_card [Nonempty V] (ch : X → C) (re : X → R) (hinj : ∀ x y, re x = re y → ch x = ch y → x = y)
    (W : Finset (Fin 4)) (σ : List (Fin 4 → V) → X) (t : ℕ) :
    #{g : X → Fin 4 → V | Fresh σ g t ∧ g (query σ g t) ∈ winTargets ch re W σ (answers σ g t)} *
      Fintype.card (Fin 4 → V) ≤ t * (t - 1) * Fintype.card (X → Fin 4 → V) := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  let z₀ : Fin 4 → V := fun _ => v₀
  have hA : ∀ z : Fin 4 → V, #{y | AgreeOn W y z} ≤ #{y | AgreeOn W y z₀} := fun z => (agree_card_eq W z z₀).le
  have hB : ∀ z : Fin 4 → V, #{y | AgreeOn Wᶜ y z} ≤ #{y | AgreeOn Wᶜ y z₀} := fun z => (agree_card_eq Wᶜ z z₀).le
  have hAB := agree_mul_le W z₀ z₀
  have hY : 0 < Fintype.card (Fin 4 → V) := Fintype.card_pos
  have h1 := fresh_card σ t (winTargets ch re W σ)
  have h2 : ∑ g : X → Fin 4 → V, #(winTargets ch re W σ (answers σ g t)) ≤
      (∑ g : X → Fin 4 → V, #(freshPairs W σ g t)) * #{y | AgreeOn W y z₀} := by
    rw [sum_mul]
    exact sum_le_sum fun g _ => winTargets_card ch re hinj W hA σ g t
  have h3 := freshPairs_sum W hB σ t
  set S := ∑ g : X → Fin 4 → V, #(winTargets ch re W σ (answers σ g t))
  set P := ∑ g : X → Fin 4 → V, #(freshPairs W σ g t)
  set A := #{y | AgreeOn W y z₀}
  set B := #{y | AgreeOn Wᶜ y z₀}
  set Y := Fintype.card (Fin 4 → V)
  set N := Fintype.card (X → Fin 4 → V)
  have h4 : S * Y ≤ t * (t - 1) * N * Y := by
    calc S * Y ≤ P * A * Y := Nat.mul_le_mul_right _ h2
      _ = A * (P * Y) := by ring
      _ ≤ A * (t * (t - 1) * (N * B)) := Nat.mul_le_mul_left _ h3
      _ = t * (t - 1) * N * (A * B) := by ring
      _ ≤ t * (t - 1) * N * Y := Nat.mul_le_mul_left _ hAB
  have h6 := Nat.le_of_mul_le_mul_right ((Nat.mul_le_mul_right Y h1).trans h4) hY
  convert h6 using 3
  ext g
  simp only [Finset.mem_filter]

end Count

/-- The window's word sets: from word `j` on, or before it. -/
def winW (p : ℕ × Bool) : Finset (Fin 4) := if p.2 then hiW p.1 else (hiW p.1)ᶜ

open Classical in
/-- A window hit ends at the last first query of its four inputs, with one of six word sets. -/
theorem winHit_charged [Fintype V] (ch : X → C) (re : X → R) {σ : List (Fin 4 → V) → X} {g : X → Fin 4 → V}
    {Q : ℕ} (hw : WinHit ch re σ g Q) : ∃ t < Q, ∃ p ∈ Ico 1 4 ×ˢ (univ : Finset Bool),
      Fresh σ g t ∧ g (query σ g t) ∈ winTargets ch re (winW p) σ (answers σ g t) := by
  obtain ⟨a, ⟨ia, hia, ea⟩, b, ⟨ib, hib, eb⟩, a', ⟨ia', hia', ea'⟩, b', ⟨ib', hib', eb'⟩, ra, rb, cab, cab',
    cne, rne, j, hj1, hj4, wa, wb⟩ := hw
  obtain ⟨fa, hfa, qa, Fa⟩ := first_fresh σ g ia
  obtain ⟨fb, hfb, qb, Fb⟩ := first_fresh σ g ib
  obtain ⟨fa', hfa', qa', Fa'⟩ := first_fresh σ g ia'
  obtain ⟨fb', hfb', qb', Fb'⟩ := first_fresh σ g ib'
  obtain rfl := qa.trans ea
  obtain rfl := qb.trans eb
  obtain rfl := qa'.trans ea'
  obtain rfl := qb'.trans eb'
  -- the four first queries are distinct
  have d1 : fa ≠ fa' := fun e => cne (by rw [e])
  have d2 : fb ≠ fb' := fun e => cne (by rw [cab, cab', e])
  have d3 : fa ≠ fb := fun e => rne (by rw [e])
  have d4 : fa' ≠ fb' := fun e => rne (by rw [ra, rb, e])
  have d5 : fa ≠ fb' := fun e => cne (by rw [cab', e])
  have d6 : fb ≠ fa' := fun e => cne (by rw [cab, e])
  -- a target from a fresh `t` and the three earlier queries
  have mk : ∀ (W : Finset (Fin 4)) (t i i' l : ℕ), Fresh σ g t → i < t → i' < t → l < t → i ≠ i' →
      Fresh σ g i → Fresh σ g i' → AgreeOn Wᶜ (g (query σ g i)) (g (query σ g i')) →
      re (query σ g l) = re (query σ g t) → ch (query σ g l) = ch (query σ g i) →
      re (query σ g i) = re (query σ g i') → ch (query σ g i') = ch (query σ g t) →
      AgreeOn W (g (query σ g t)) (g (query σ g l)) → g (query σ g t) ∈ winTargets ch re W σ (answers σ g t) := by
    intro W t i i' l _ hi hi' hl hii fi fi' hag h1 h2 h3 h4 h5
    have hlen : (answers σ g t).length = t := answers_length σ g t
    simp only [winTargets, mem_filter, mem_univ, true_and]
    refine ⟨⟨i, by rw [hlen]; exact hi⟩, ⟨i', by rw [hlen]; exact hi'⟩, ⟨l, by rw [hlen]; exact hl⟩,
      fun e => hii (congrArg Fin.val e), ?_, ?_, ?_, ?_⟩
    · intro m hm
      rw [qAt_answers σ g (by simp only at hm; omega), qAt_answers σ g hi.le]
      exact fi m hm
    · intro m hm
      rw [qAt_answers σ g (by simp only at hm; omega), qAt_answers σ g hi'.le]
      exact fi' m hm
    · simp only [Fin.getElem_fin, answers_getElem]
      exact hag
    · have hσ : σ (answers σ g t) = query σ g t := rfl
      simp only [qAt_answers σ g hi.le, qAt_answers σ g hi'.le, qAt_answers σ g hl.le, Fin.getElem_fin,
        answers_getElem, hσ]
      exact ⟨h1, h2, h3, h4, h5⟩
  have hp : ∀ s : Bool, (j, s) ∈ Ico 1 4 ×ˢ (univ : Finset Bool) := fun s =>
    mem_product.mpr ⟨mem_Ico.mpr ⟨hj1, hj4⟩, mem_univ _⟩
  have hT : winW (j, true) = hiW j := rfl
  have hF : winW (j, false) = (hiW j)ᶜ := rfl
  rcases (by omega : (fb < fa ∧ fa' < fa ∧ fb' < fa) ∨ (fa < fa' ∧ fb < fa' ∧ fb' < fa') ∨
      (fa < fb ∧ fa' < fb ∧ fb' < fb) ∨ (fa < fb' ∧ fa' < fb' ∧ fb < fb')) with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨fa, by omega, (j, true), hp true, Fa, ?_⟩
    rw [hT]
    exact mk _ fa fb' fb fa' Fa h3 h1 h2 (Ne.symm d2) Fb' Fb wb.symm ra.symm cab' rb.symm cab.symm wa
  · refine ⟨fa', by omega, (j, true), hp true, Fa', ?_⟩
    rw [hT]
    exact mk _ fa' fb fb' fa Fa' h2 h3 h1 d2 Fb Fb' wb ra cab rb cab'.symm wa.symm
  · refine ⟨fb, by omega, (j, false), hp false, Fb, ?_⟩
    rw [hF]
    exact mk _ fb fa' fa fb' Fb h2 h1 h3 (Ne.symm d1) Fa' Fa (by rw [compl_compl]; exact wa.symm) rb.symm
      cab'.symm ra.symm cab wb
  · refine ⟨fb', by omega, (j, false), hp false, Fb', ?_⟩
    rw [hF]
    exact mk _ fb' fa fa' fb Fb' h1 h2 h3 d1 Fa Fa' (by rw [compl_compl]; exact wa) rb cab.symm ra cab' wb.symm

theorem sum_range_mul_pred (Q : ℕ) : (∑ t ∈ range Q, t * (t - 1)) * 3 = Q * (Q - 1) * (Q - 2) := by
  induction Q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    rcases n with _ | _ | n
    · rfl
    · rfl
    · rw [show n + 1 + 1 + 1 - 1 = n + 2 by omega, show n + 1 + 1 + 1 - 2 = n + 1 by omega,
        show n + 1 + 1 - 1 = n + 1 by omega, show n + 1 + 1 - 2 = n by omega]
      ring

open Classical in
/-- The window bound: a uniform oracle `h : X → (Fin 4 → V)` gives a prover of `Q` adaptive queries a window hit, two
output blocks of distinct chaining values agreeing on a window straddling them, at most at a
`2 · Q · (Q - 1) · (Q - 2) / |V|^4` fraction of the oracles, inputs being their chaining value and their other words
(`hinj`). -/
theorem win_card [Fintype X] [Fintype V] [Nonempty V] (ch : X → C) (re : X → R)
    (hinj : ∀ x y, re x = re y → ch x = ch y → x = y) (σ : List (Fin 4 → V) → X) (Q : ℕ) :
    #{g : X → Fin 4 → V | WinHit ch re σ g Q} * Fintype.card (Fin 4 → V) ≤
      2 * (Q * (Q - 1) * (Q - 2)) * Fintype.card (X → Fin 4 → V) := by
  set N := Fintype.card (X → Fin 4 → V)
  set G : ℕ → ℕ × Bool → Finset (X → Fin 4 → V) := fun t p =>
    univ.filter fun g => Fresh σ g t ∧ g (query σ g t) ∈ winTargets ch re (winW p) σ (answers σ g t)
  have hcov : (univ.filter fun g : X → Fin 4 → V => WinHit ch re σ g Q) ⊆
      (range Q).biUnion fun t => (Ico 1 4 ×ˢ (univ : Finset Bool)).biUnion (G t) := by
    intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg
    obtain ⟨t, ht, p, hp, hf, hm⟩ := winHit_charged ch re hg
    exact mem_biUnion.mpr ⟨t, mem_range.mpr ht, mem_biUnion.mpr ⟨p, hp, by simp [G, hf, hm]⟩⟩
  have hsix : #(Ico 1 4 ×ˢ (univ : Finset Bool)) = 6 := by simp
  calc _ ≤ (∑ t ∈ range Q, ∑ p ∈ Ico 1 4 ×ˢ (univ : Finset Bool), #(G t p)) * Fintype.card (Fin 4 → V) :=
        Nat.mul_le_mul_right _ ((card_le_card hcov).trans (card_biUnion_le.trans (sum_le_sum fun t _ =>
          card_biUnion_le)))
    _ = ∑ t ∈ range Q, ∑ p ∈ Ico 1 4 ×ˢ (univ : Finset Bool), #(G t p) * Fintype.card (Fin 4 → V) := by
        rw [sum_mul]; exact sum_congr rfl fun t _ => sum_mul _ _ _
    _ ≤ ∑ t ∈ range Q, ∑ _p ∈ Ico 1 4 ×ˢ (univ : Finset Bool), t * (t - 1) * N :=
        sum_le_sum fun t _ => sum_le_sum fun p _ => charged_card ch re hinj (winW p) σ t
    _ = (∑ t ∈ range Q, t * (t - 1)) * 3 * 2 * N := by
        rw [sum_mul, sum_mul, sum_mul]
        exact sum_congr rfl fun t _ => by rw [sum_const, hsix, smul_eq_mul]; ring
    _ = 2 * (Q * (Q - 1) * (Q - 2)) * N := by rw [sum_range_mul_pred]; ring

open Classical in
/-- The window bound as a fraction: at most `2 · Q · (Q - 1) · (Q - 2) / |V|^4` of the oracles. -/
theorem win_frac [Fintype X] [Fintype V] [Nonempty V] (ch : X → C) (re : X → R)
    (hinj : ∀ x y, re x = re y → ch x = ch y → x = y) (σ : List (Fin 4 → V) → X) (Q : ℕ) :
    ((univ.filter fun h : X → Fin 4 → V => WinHit ch re σ h Q).card : ℚ≥0) / Fintype.card (X → Fin 4 → V) ≤
      ((2 * (Q * (Q - 1) * (Q - 2)) : ℕ) : ℚ≥0) / ((Fintype.card V ^ 4 : ℕ) : ℚ≥0) :=
  frac_le (by have := Fintype.card_pos (α := V); positivity) (by
    have := win_card ch re hinj σ Q
    simpa [Fintype.card_fun, Fintype.card_fin] using this)

/-- Non-vacuity: a prover of one query never collides nor hits a window. -/
example (ch : X → C) (re : X → R) (σ : List (Fin 4 → V) → X) (h : X → Fin 4 → V) :
    Set.InjOn h (queries σ h 1) ∧ ¬ WinHit ch re σ h 1 := by
  refine ⟨injOn_of_not_coll ?_, ?_⟩
  · rintro ⟨i, hi, i', hi', hne, _⟩
    exact hne (by rw [show i = 0 by omega, show i' = 0 by omega])
  · rintro ⟨_, ⟨i, hi, rfl⟩, _, ⟨i', hi', rfl⟩, -, -, -, -, -, -, -, -, -, hre, -⟩
    exact hre (by rw [show i = 0 by omega, show i' = 0 by omega])

/-- Mutation test: four answers on `Fin 2` words of two chaining values agreeing on a window from word 2 are a window
hit; changing one window word of `b'` is not. -/
example : AgreeOn (hiW 2) (![0, 0, 1, 1] : Fin 4 → Fin 2) ![1, 1, 1, 1] ∧
    AgreeOn (hiW 2)ᶜ (![0, 1, 0, 0] : Fin 4 → Fin 2) ![0, 1, 1, 1] ∧
    ¬ AgreeOn (hiW 2)ᶜ (![0, 1, 0, 0] : Fin 4 → Fin 2) ![1, 1, 1, 1] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [AgreeOn, hiW] <;> decide

end LeanVMCircuits.Rec.Collision

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Collision

/-- A hash row's input words at an assignment: counter, finalization, chaining value, message (`hashIn`'s nodes). -/
def rowIn (val : Val) (row : List ℕ) : Fin 14 → K := fun c => nu val (colNode row (hashSrc c))

/-- A hash row's output words at an assignment (`hashOut`'s nodes). -/
def rowOut (val : Val) (row : List ℕ) : Fin 4 → K := fun k => nu val (colNode row (hashSrc (14 + k)))

/-- An input's chaining value words. -/
def chainOf (x : Fin 14 → K) : Fin 4 → K := fun k => x ⟨2 + k, by omega⟩

theorem hashIn_map (val : Val) (row : List ℕ) : (hashIn row).map (nu val) = List.ofFn (rowIn val row) := by
  apply List.ext_getElem (by simp [hashIn])
  intro n h1 h2
  simp only [hashIn, rowIn, List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem hashOut_map (val : Val) (row : List ℕ) : (hashOut row).map (nu val) = List.ofFn (rowOut val row) := by
  apply List.ext_getElem (by simp [hashOut])
  intro n h1 h2
  simp only [hashOut, rowOut, List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem hashSrc_chain {k : ℕ} (hk : k < 4) : hashSrc (2 + k) = (0, k) := by
  simp only [hashSrc, if_neg (show ¬ 2 + k < 2 by omega), if_pos (show 2 + k < 6 by omega), Nat.add_sub_cancel_left]

/-- Two hash rows of one chaining value wire have the same chaining value words. -/
theorem chainOf_rowIn {val : Val} {ra rb : List ℕ} (h0 : ra.getD 0 0 = rb.getD 0 0) :
    chainOf (rowIn val ra) = chainOf (rowIn val rb) := by
  funext k
  show nu val (colNode ra (hashSrc (2 + k.val))) = nu val (colNode rb (hashSrc (2 + k.val)))
  rw [hashSrc_chain k.isLt]
  simp only [colNode, h0]

/-- An input's words other than its chaining value (`restIdx`'s): counter, finalization and message. -/
def restFin : Fin 10 → Fin 14 := ![0, 1, 6, 7, 8, 9, 10, 11, 12, 13]

/-- An input's words other than its chaining value. -/
def restOf (x : Fin 14 → K) : Fin 10 → K := fun i => x (restFin i)

theorem restFin_val (i : Fin 10) : (restFin i).val = restIdx i := by fin_cases i <;> rfl

/-- An input is its chaining value and its other words. -/
theorem input_ext {x y : Fin 14 → K} (hc : chainOf x = chainOf y) (hr : restOf x = restOf y) : x = y := by
  have hc' := fun i => congrFun hc i
  have hr' := fun i => congrFun hr i
  funext k
  fin_cases k
  exacts [hr' 0, hr' 1, hc' 0, hc' 1, hc' 2, hc' 3, hr' 2, hr' 3, hr' 4, hr' 5, hr' 6, hr' 7, hr' 8, hr' 9]

theorem hashRest_map (val : Val) (row : List ℕ) : (hashRest row).map (nu val) = List.ofFn (restOf (rowIn val row)) := by
  simp only [hashRest, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp, restOf, rowIn, restFin_val]

/-- The ideal compression model's consistency at an assignment on the rows live on `L`: every hash row `drop` does
not name and a rule firing on `L` reads has its inputs among the queries `Qs` and its outputs the oracle `H` at its
inputs. -/
def OracleRows (H : (Fin 14 → K) → Fin 4 → K) (Qs : Set (Fin 14 → K)) (s : State) (drop : List ℕ → Bool)
    (L : ℕ → Prop) (val : Val) : Prop :=
  ∀ row ∈ s.hash, drop row = false → RowLive L row → rowIn val row ∈ Qs ∧ rowOut val row = H (rowIn val row)

/-- `HashCRP` from the ideal model: two assignments consistent with an oracle injective on the queries. -/
theorem hashCRP_of_oracle {H : (Fin 14 → K) → Fin 4 → K} {Qs : Set (Fin 14 → K)} {s : State} {drop : List ℕ → Bool}
    {L : ℕ → Prop} {val val' : Val} (hinj : Set.InjOn H Qs) (hv : OracleRows H Qs s drop L val)
    (hv' : OracleRows H Qs s drop L val') : HashCRP s drop L val val' := by
  intro row hr row' hr' hd hd' hl hl' ho
  rw [hashOut_map, hashOut_map, List.ofFn_inj] at ho
  obtain ⟨q, e⟩ := hv row hr hd hl
  obtain ⟨q', e'⟩ := hv' row' hr' hd' hl'
  rw [hashIn_map, hashIn_map, List.ofFn_inj]
  exact hinj q q' (e.symm.trans (ho.trans e'))

/-- `WindowCRP` from the ideal model: two assignments consistent with an oracle injective and window-free on the
queries. The two rows' other words agreeing, distinct chaining values make the four inputs a window hit
(`Collision.WinOn`), or, the rows' other words being alike, one input whose two answers agree on all four words. -/
theorem windowCRP_of_oracle {H : (Fin 14 → K) → Fin 4 → K} {Qs : Set (Fin 14 → K)} {s : State}
    {drop : List ℕ → Bool} {L : ℕ → Prop} {val val' : Val} (hinj : Set.InjOn H Qs)
    (hwin : ¬ WinOn chainOf restOf H Qs) (hv : OracleRows H Qs s drop L val) (hv' : OracleRows H Qs s drop L val') :
    WindowCRP s drop L val val' := by
  intro ra ha rb hb hda hdb hla hlb h0 j hj1 hj4 hw
  obtain ⟨qa, ea⟩ := hv ra ha hda hla
  obtain ⟨qa', ea'⟩ := hv' ra ha hda hla
  obtain ⟨qb, eb⟩ := hv rb hb hdb hlb
  obtain ⟨qb', eb'⟩ := hv' rb hb hdb hlb
  -- the window's words: `ra`'s from word `j` on, `rb`'s before it
  have wa : ∀ k : Fin 4, j ≤ k.val → H (rowIn val ra) k = H (rowIn val' ra) k := by
    intro k hk
    rw [← ea, ← ea']
    refine hw _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨k.val - j, List.mem_range.mpr (by omega), ?_⟩))))
    show colNode ra (hashSrc (14 + j + (k.val - j))) = colNode ra (hashSrc (14 + k.val))
    rw [show 14 + j + (k.val - j) = 14 + k.val by omega]
  have wb : ∀ k : Fin 4, k.val < j → H (rowIn val rb) k = H (rowIn val' rb) k := by
    intro k hk
    rw [← eb, ← eb']
    exact hw _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨k.val, List.mem_range.mpr hk, rfl⟩))))
  -- the rows' other words
  have hra : restOf (rowIn val ra) = restOf (rowIn val' ra) := by
    funext i
    have := hw _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    simpa only [restOf, rowIn, restFin_val] using this
  have hrb : restOf (rowIn val rb) = restOf (rowIn val' rb) := by
    funext i
    have := hw _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    simpa only [restOf, rowIn, restFin_val] using this
  have hc : chainOf (rowIn val ra) = chainOf (rowIn val' ra) := by
    by_contra hc
    by_cases hre : restOf (rowIn val ra) = restOf (rowIn val rb)
    · -- one input per assignment: its two answers agree on every word
      have e1 : rowIn val ra = rowIn val rb := input_ext (chainOf_rowIn h0) hre
      have e2 : rowIn val' ra = rowIn val' rb := input_ext (chainOf_rowIn h0) (by rw [← hra, hre, hrb])
      have hfull : H (rowIn val ra) = H (rowIn val' ra) := by
        funext k
        by_cases hk : j ≤ k.val
        · exact wa k hk
        · rw [e1, e2]
          exact wb k (by omega)
      exact hc (by rw [hinj qa qa' hfull])
    · refine hwin ⟨_, qa, _, qb, _, qa', _, qb', hra, hrb, chainOf_rowIn h0, chainOf_rowIn h0, hc, hre, j, hj1, hj4,
        fun k hk => wa k ?_, fun k hk => wb k ?_⟩
      · simpa [hiW] using hk
      · simp only [hiW, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
        exact hk
  intro n hn
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
  exact congrFun hc ⟨k, List.mem_range.mp hk⟩

/-- Non-vacuity of `OracleRows`: an assignment whose hash rows not dropped give equal inputs equal outputs (as the compression's rows do) is consistent with some oracle, all inputs being queries. -/
theorem oracleRows_exists (s : State) (drop : List ℕ → Bool) (L : ℕ → Prop) (val : Val)
    (hf : ∀ row ∈ s.hash, ∀ row' ∈ s.hash, drop row = false → drop row' = false → rowIn val row = rowIn val row' →
      rowOut val row = rowOut val row') :
    ∃ H, OracleRows H Set.univ s drop L val := by
  classical
  refine ⟨fun x => if h : ∃ row ∈ s.hash, drop row = false ∧ rowIn val row = x then rowOut val h.choose else 0, ?_⟩
  intro row hr hd _
  have hx : ∃ row' ∈ s.hash, drop row' = false ∧ rowIn val row' = rowIn val row := ⟨row, hr, hd, rfl⟩
  refine ⟨Set.mem_univ _, ?_⟩
  simp only [dif_pos hx]
  obtain ⟨hm, hdm, he⟩ := hx.choose_spec
  exact (hf _ hm _ hr hdm hd he).symm

/-- `PairCR` from the ideal compression model: two assignments consistent, on the rows the seeds `X` bind, with one
oracle `H` on queries `Qs`, at which `H` is injective and window-free. -/
theorem pairCR_of_oracle {c : Cert} {s : State} {T : ℕ} {X : List ℕ} {val val' : Val}
    (H : (Fin 14 → K) → Fin 4 → K) (Qs : Set (Fin 14 → K)) (hinj : Set.InjOn H Qs)
    (hwin : ¬ WinOn chainOf restOf H Qs)
    (hv : OracleRows H Qs s (dropOf s (c.transcripts.getD T default)) (c.liveOn T X) val)
    (hv' : OracleRows H Qs s (dropOf s (c.transcripts.getD T default)) (c.liveOn T X) val') :
    PairCR c s T X val val' :=
  ⟨hashCRP_of_oracle hinj hv hv', windowCRP_of_oracle hinj hwin hv hv'⟩

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model Finset Collision

section Oracle

variable {ι Ω₀ X V C R : Type}

open Classical in
/-- The collision event over outcomes pairing other coins `ω.1` with the compression oracle `ω.2`: among the first `Q` compression queries of the prover `σ ω.1`, a collision or a window hit (inputs being their chaining value `ch` and their other words `re`). -/
noncomputable def crEvent [Fintype Ω₀] [Fintype X] [Fintype V] (ch : X → C) (re : X → R)
    (σ : Ω₀ → List (Fin 4 → V) → X) (Q : ℕ) : Finset (Ω₀ × (X → Fin 4 → V)) :=
  univ.filter fun ω => Coll (σ ω.1) ω.2 Q ∨ WinHit ch re (σ ω.1) ω.2 Q

/-- The ideal compression model's `ε_CR` for `Q` compression queries with words in `V`: the birthday bound `Q · (Q - 1) / (2 |V|^4)` and the window bound `2 · Q · (Q - 1) · (Q - 2) / |V|^4`. -/
noncomputable def epsCR (V : Type) [Fintype V] (Q : ℕ) : ℚ≥0 :=
  ((Q * (Q - 1) : ℕ) : ℚ≥0) / ((2 * Fintype.card V ^ 4 : ℕ) : ℚ≥0) +
    ((2 * (Q * (Q - 1) * (Q - 2)) : ℕ) : ℚ≥0) / ((Fintype.card V ^ 4 : ℕ) : ℚ≥0)

open Classical in
theorem card_filter_prod {A B : Type} [Fintype A] [Fintype B] (P : A → B → Prop) :
    (univ.filter fun ω : A × B => P ω.1 ω.2).card = ∑ a, (univ.filter (P a)).card := by
  rw [card_filter, ← univ_product_univ, sum_product]
  simp only [card_filter]

open Classical in
/-- `crEvent`'s fraction of the outcomes is at most `epsCR`. -/
theorem crEvent_frac [Fintype Ω₀] [Fintype X] [Fintype V] [Nonempty V] (ch : X → C) (re : X → R)
    (hinj : ∀ x y, re x = re y → ch x = ch y → x = y) (σ : Ω₀ → List (Fin 4 → V) → X) (Q : ℕ) :
    ((crEvent ch re σ Q).card : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤ epsCR V Q := by
  set M := Fintype.card (Ω₀ × (X → Fin 4 → V))
  have hM : M = Fintype.card Ω₀ * Fintype.card (X → Fin 4 → V) := Fintype.card_prod _ _
  have hY : Fintype.card (Fin 4 → V) = Fintype.card V ^ 4 := by simp
  have hV := Fintype.card_pos (α := V)
  set cA := (univ.filter fun ω : Ω₀ × (X → Fin 4 → V) => Coll (σ ω.1) ω.2 Q).card
  set cB := (univ.filter fun ω : Ω₀ × (X → Fin 4 → V) => WinHit ch re (σ ω.1) ω.2 Q).card
  have hA : (cA : ℚ≥0) / M ≤ ((Q * (Q - 1) : ℕ) : ℚ≥0) / ((2 * Fintype.card V ^ 4 : ℕ) : ℚ≥0) := by
    refine frac_le (by positivity) ?_
    have hcA : cA = ∑ a, (univ.filter fun h => Coll (σ a) h Q).card := card_filter_prod fun a h => Coll (σ a) h Q
    calc cA * (2 * Fintype.card V ^ 4) = ∑ a, (univ.filter fun h => Coll (σ a) h Q).card *
          Fintype.card (Fin 4 → V) * 2 := by rw [hcA, sum_mul, hY]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ _a : Ω₀, Q * (Q - 1) * Fintype.card (X → Fin 4 → V) := sum_le_sum fun a _ => birthday_card (σ a) Q
      _ = Q * (Q - 1) * M := by rw [sum_const, card_univ, smul_eq_mul, hM]; ring
  have hB : (cB : ℚ≥0) / M ≤ ((2 * (Q * (Q - 1) * (Q - 2)) : ℕ) : ℚ≥0) / ((Fintype.card V ^ 4 : ℕ) : ℚ≥0) := by
    refine frac_le (by positivity) ?_
    have hcB : cB = ∑ a, (univ.filter fun h => WinHit ch re (σ a) h Q).card :=
      card_filter_prod fun a h => WinHit ch re (σ a) h Q
    calc cB * Fintype.card V ^ 4 = ∑ a, (univ.filter fun h => WinHit ch re (σ a) h Q).card *
          Fintype.card (Fin 4 → V) := by rw [hcB, sum_mul, hY]
      _ ≤ ∑ _a : Ω₀, 2 * (Q * (Q - 1) * (Q - 2)) * Fintype.card (X → Fin 4 → V) :=
          sum_le_sum fun a _ => win_card ch re hinj (σ a) Q
      _ = 2 * (Q * (Q - 1) * (Q - 2)) * M := by rw [sum_const, card_univ, smul_eq_mul, hM]; ring
  have hcard : ((crEvent ch re σ Q).card : ℚ≥0) ≤ cA + cB := by
    have : crEvent ch re σ Q = (univ.filter fun ω : Ω₀ × (X → Fin 4 → V) => Coll (σ ω.1) ω.2 Q) ∪
        (univ.filter fun ω : Ω₀ × (X → Fin 4 → V) => WinHit ch re (σ ω.1) ω.2 Q) := by
      rw [crEvent, filter_or]
    rw [this]
    exact_mod_cast card_union_le _ _
  calc ((crEvent ch re σ Q).card : ℚ≥0) / M ≤ ((cA : ℚ≥0) + cB) / M := by gcongr
    _ = (cA : ℚ≥0) / M + (cB : ℚ≥0) / M := add_div _ _ _
    _ ≤ epsCR V Q := add_le_add hA hB

/-- Off `crEvent`, the oracle is injective and window-free on the prover's queries: what `Bind.pairCR_of_oracle` asks. -/
theorem not_mem_crEvent [Fintype Ω₀] [Fintype X] [Fintype V] {ch : X → C} {re : X → R}
    {σ : Ω₀ → List (Fin 4 → V) → X} {Q : ℕ} {ω : Ω₀ × (X → Fin 4 → V)} (h : ω ∉ crEvent ch re σ Q) :
    Set.InjOn ω.2 (queries (σ ω.1) ω.2 Q) ∧ ¬ WinOn ch re ω.2 (queries (σ ω.1) ω.2 Q) := by
  classical
  simp only [crEvent, mem_filter, mem_univ, true_and, not_or] at h
  exact ⟨injOn_of_not_coll h.1, h.2⟩

open Classical in
/-- `crBad` as the collision event of each child's compression queries: its fraction in `tree_sound_parts`' sum is at most `epsCR` of the child's number of compression queries. -/
theorem crBad_frac [Fintype Ω₀] [Fintype X] [Fintype V] [Nonempty V] (ch : X → C) (re : X → R)
    (hinj : ∀ x y, re x = re y → ch x = ch y → x = y) (P : RecParts ι (Ω₀ × (X → Fin 4 → V)))
    (σ : ι → Ω₀ → List (Fin 4 → V) → X) (Q : ι → ℕ) (hcr : ∀ v, P.crBad v = crEvent ch re (σ v) (Q v)) (v : ι) :
    ((P.crBad v).card : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤ epsCR V (Q v) := by
  rw [hcr v]
  exact crEvent_frac ch re hinj (σ v) (Q v)

open Classical in
/-- Non-vacuity: the least parts with the collision events as `crBad` satisfy `RecParts.Ok` and `crBad_frac`'s premise. -/
example [Fintype Ω₀] [Fintype X] [Fintype V] (ch : X → C) (re : X → R) (J : ι → ℕ)
    (inOk outOk : ι → ℕ → Ω₀ × (X → Fin 4 → V) → Prop)
    (held : ι → Ω₀ × (X → Fin 4 → V) → Prop) (σ : ι → Ω₀ → List (Fin 4 → V) → X) (Q : ι → ℕ) :
    (RecParts.least J inOk outOk held fun v => crEvent ch re (σ v) (Q v)).Ok held ∧
      ∀ v, (RecParts.least J inOk outOk held fun v => crEvent ch re (σ v) (Q v)).crBad v =
        crEvent ch re (σ v) (Q v) :=
  ⟨RecParts.least_ok _ _ _ _ _, fun _ => rfl⟩

end Oracle

section Pcs

variable {ι Ω : Type}

/-- The PCS interface: child `v`'s `pcsBad` is at most `epsPCS v` of the outcomes. #551 proves such a bound for WHIR in its separate Lean project (`verification/whir`, commit `8198d0b2`): theorem `Whir.SpongefishCurrentKnowledgeFinal.current_knowledge` in `verification/whir/Whir/SpongefishCurrentKnowledgeFinal.lean` bounds, in the ideal compression model, the probability that some received record is natively accepted while the public straight-line extractor fails by `∑ k : Fin 4, finalBound Q_k`, with `finalBound Q = Q · ((17/32)^56 + 2^-78) + min(1, (2 Q^2 - Q) / 2^256) + (Q^3 + 3 Q^2 - 2 Q) / 2^256` and `Q_k` the aggregate budget of binding message shape `k`; `current_knowledge_level` gives `B / 2^49` for budgets at most `B ≤ 2^64`. Its event and outcome space are its own; matching them to `pcsBad` is this interface's premise. -/
structure PcsBound [Fintype Ω] (P : RecParts ι Ω) (epsPCS : ι → ℚ≥0) : Prop where
  le : ∀ v, ((P.pcsBad v).card : ℚ≥0) / Fintype.card Ω ≤ epsPCS v

/-- Non-vacuity: every part's PCS events are at most all the outcomes. -/
theorem PcsBound.one [Fintype Ω] (P : RecParts ι Ω) : PcsBound P fun _ => 1 :=
  ⟨fun v => div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (by positivity)⟩

/-- Non-vacuity at the least parts. -/
example [Fintype Ω] (J : ι → ℕ) (inOk outOk : ι → ℕ → Ω → Prop) (held : ι → Ω → Prop) (crBad : ι → Finset Ω) :
    PcsBound (RecParts.least J inOk outOk held crBad) fun _ => 1 :=
  PcsBound.one _

open Classical in
/-- `tree_sound_parts` with each child's `pcsBad` fraction replaced by its PCS bound `epsPCS v` (`PcsBound`, #551) and its `crBad` fraction by a bound `epsCR v` (for the collision events, `crBad_frac`). -/
theorem tree_sound_eps [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι Ω)
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (hair : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      (∀ j < P.J v, P.inOk v j ω) → ω ∉ P.crBad v →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω))
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (epsPCS epsCR : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hcr : ∀ v ∈ T.nodes, ((P.crBad v).card : ℚ≥0) / Fintype.card Ω ≤ epsCR v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card Ω ≤
      ∑ v ∈ T.nodes, (((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card : ℚ≥0) / Fintype.card Ω +
        epsPCS v + epsCR v) := by
  refine (tree_sound_parts T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP hair tD tM bad hstep
    hroot).trans (sum_le_sum fun v hv => ?_)
  rw [add_div, add_div]
  exact add_le_add (add_le_add le_rfl (hpcs.le v)) (hcr v hv)

end Pcs

end LeanVMCircuits.Rec.Edges
