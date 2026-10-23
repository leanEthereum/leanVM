/-
  LeanVM.Protocol.Whir.Sound.Group

  The move-free fragments of a WHIR level as joint groups of challenges: the out-of-domain point
  and the query group (positions, `λ`, openings), with their escape expectations.
-/

module

public import LeanVM.Protocol.Whir.Sound.Queries

/-!
# Groups of challenges

The calculus bounds a move-free fragment jointly (`Spec.ofNoMove`). This module provides:

* `NoMoves`: a program whose every node is a sample, an opening, a return or a rejection, closed
  under `bind`; `NoMoves.not_isMove` discharges the hypothesis of `Spec.ofNoMove`.
* `retExp_sampleQueriesAux_restrict`: the positions `sample_queries` returns are below
  `2^depth` (chunks are reduced modulo `2^depth`), so an expectation over them only sees such
  position lists.
* `queryFrag depth t i`: the query group `sample_queries`, `λ`, opening of commitment `i`, as one
  fragment returning `(positions, λ, rows)`; `retExp_queryFrag_le`: if, for every in-range
  position list, the average over `λ` of a function of the opened rows is at most
  `allIn S qs + ε`, the expectation over the group is at most `(|S| / 2^depth)^t + ε`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Prog Finset

@[expose] public section

variable {α β : Type}

/-! ## Move-free programs -/

/-- Every node of the program is a sample, an opening, a return or a rejection. -/
inductive NoMoves : Prog α → Prop where
  | ret (a : α) : NoMoves (Prog.ret a)
  | fail : NoMoves Prog.fail
  | sample {k : E → Prog α} : (∀ c, NoMoves (k c)) → NoMoves (Prog.sample k)
  | query {i : ℕ} {ps : List ℕ} {k : List (List K) → Prog α} :
      (∀ rows, NoMoves (k rows)) → NoMoves (Prog.query i ps k)

theorem NoMoves.after {p q : Prog α} (hp : NoMoves p) :
    ∀ {l : List Ev}, p.after l = some q → NoMoves q := by
  intro l
  induction l generalizing p with
  | nil => intro h; simp [Prog.after] at h; exact h ▸ hp
  | cons e l ih =>
    intro h
    cases hp with
    | ret a => cases e <;> simp [Prog.after] at h
    | fail => cases e <;> simp [Prog.after] at h
    | sample hk =>
      cases e <;> simp [Prog.after] at h
      exact ih (hk _) h
    | query hk =>
      cases e <;> simp [Prog.after] at h
      exact ih (hk _) h

theorem NoMoves.not_isMove {q : Prog α} (hq : NoMoves q) : ¬ q.IsMove := by
  cases hq <;> simp [Prog.IsMove]

/-- The hypothesis of `Spec.ofNoMove`. -/
theorem NoMoves.noMove {p : Prog α} (hp : NoMoves p) :
    ∀ {h₀ l : List Ev} {q : Prog α}, p.Reach h₀ l → p.after l = some q → ¬ q.IsMove :=
  fun _ ha ↦ (hp.after ha).not_isMove

theorem NoMoves.bind {p : Prog α} {f : α → Prog β} (hp : NoMoves p) (hf : ∀ a, NoMoves (f a)) :
    NoMoves (p.bind f) := by
  induction hp with
  | ret a => exact hf a
  | fail => exact NoMoves.fail
  | sample _ ih => exact NoMoves.sample ih
  | query _ ih => exact NoMoves.query ih

theorem noMoves_sampleE : NoMoves sampleE := NoMoves.sample fun c ↦ NoMoves.ret c

theorem noMoves_queryP (i : ℕ) (ps : List ℕ) : NoMoves (queryP i ps) :=
  NoMoves.query fun rows ↦ NoMoves.ret rows

theorem noMoves_sampleN : ∀ n, NoMoves (sampleN n)
  | 0 => NoMoves.ret []
  | n + 1 => noMoves_sampleE.bind fun _ ↦ (noMoves_sampleN n).bind fun _ ↦ NoMoves.ret _

theorem noMoves_sampleQueriesAux (depth : ℕ) : ∀ fuel rem, NoMoves (sampleQueriesAux depth fuel rem)
  | 0, rem => NoMoves.ret []
  | fuel + 1, rem => by
    unfold sampleQueriesAux
    split
    · exact NoMoves.ret []
    · exact noMoves_sampleE.bind fun _ ↦
        (noMoves_sampleQueriesAux depth fuel _).bind fun _ ↦ NoMoves.ret _

/-! ## The positions are in range -/

/-- An expectation over `sample_queries` only sees position lists below `2^depth`. -/
theorem retExp_sampleQueriesAux_restrict (depth : ℕ) (g : List ℕ → List Ev → ENNReal) :
    ∀ fuel rem h₀ l, retExp g h₀ l (sampleQueriesAux depth fuel rem) =
      retExp (fun qs h ↦ if ∀ q ∈ qs, q < 2 ^ depth then g qs h else 0) h₀ l
        (sampleQueriesAux depth fuel rem)
  | 0, rem, h₀, l => by simp [sampleQueriesAux, retExp]
  | fuel + 1, rem, h₀, l => by
    unfold sampleQueriesAux
    split
    · simp [retExp]
    · simp only [bind_eq, pure_eq]
      rw [show sampleE = (sample ret : Prog E) from rfl, Prog.bind]
      simp only [retExp, ret_bind]
      congr 1
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [retExp_bind, retExp_bind]
      rw [retExp_sampleQueriesAux_restrict depth _ fuel _ h₀ _]
      conv_rhs => rw [retExp_sampleQueriesAux_restrict depth _ fuel _ h₀ _]
      congr 1
      funext rest h
      simp only [retExp]
      by_cases hr : ∀ q ∈ rest, q < 2 ^ depth
      · have hall : ∀ q ∈ (List.range (min (192 / depth) rem)).map
            (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ rest, q < 2 ^ depth := by
          intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          · exact hr q hq
        split_ifs
        simp_all
      · simp [hr]

/-- An expectation over `sample_queries` only sees position lists of the requested length below
`2^depth`. -/
theorem retExp_sampleQueriesAux_restrict_len (depth : ℕ) (h1 : 1 ≤ depth) (h192 : depth ≤ 192)
    (g : List ℕ → List Ev → ENNReal) :
    ∀ fuel rem, rem ≤ fuel → ∀ h₀ l, retExp g h₀ l (sampleQueriesAux depth fuel rem) =
      retExp (fun qs h ↦ if (∀ q ∈ qs, q < 2 ^ depth) ∧ qs.length = rem then g qs h else 0) h₀ l
        (sampleQueriesAux depth fuel rem)
  | 0, rem, hrem, h₀, l => by
    obtain rfl : rem = 0 := by omega
    simp [sampleQueriesAux, retExp]
  | fuel + 1, rem, hrem, h₀, l => by
    unfold sampleQueriesAux
    split
    · rename_i h0
      subst h0
      simp [retExp]
    · rename_i h0
      have hn1 : 1 ≤ min (192 / depth) rem :=
        le_min ((Nat.one_le_div_iff (by omega)).mpr h192) (by omega)
      have hnr : min (192 / depth) rem ≤ rem := min_le_right _ _
      simp only [bind_eq, pure_eq]
      rw [show sampleE = (sample ret : Prog E) from rfl, Prog.bind]
      simp only [retExp, ret_bind]
      congr 1
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [retExp_bind, retExp_bind]
      rw [retExp_sampleQueriesAux_restrict_len depth h1 h192 _ fuel _ (by omega) h₀ _]
      conv_rhs => rw [retExp_sampleQueriesAux_restrict_len depth h1 h192 _ fuel _ (by omega) h₀ _]
      congr 1
      funext rest h
      simp only [retExp]
      by_cases hr : (∀ q ∈ rest, q < 2 ^ depth) ∧ rest.length = rem - min (192 / depth) rem
      · have hall : (∀ q ∈ (List.range (min (192 / depth) rem)).map
            (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ rest, q < 2 ^ depth) ∧
            ((List.range (min (192 / depth) rem)).map
            (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ rest).length = rem := by
          refine ⟨fun q hq ↦ ?_, by
            simp only [List.length_append, List.length_map, List.length_range, hr.2]; omega⟩
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          · exact hr.1 q hq
        split_ifs
        simp_all
      · simp [hr]

/-! ## The query group -/

/-- The query group: positions, `λ`, the opening of commitment `i`. -/
def queryFrag (depth t i : ℕ) : Prog (List ℕ × E × List (List K)) :=
  sampleQueries depth t >>= fun qs ↦ sampleE >>= fun lam ↦ queryP i qs >>= fun words ↦
    Prog.ret (qs, lam, words)

theorem noMoves_queryFrag (depth t i : ℕ) : NoMoves (queryFrag depth t i) :=
  (noMoves_sampleQueriesAux depth t t).bind fun _ ↦ noMoves_sampleE.bind fun _ ↦
    (noMoves_queryP i _).bind fun _ ↦ NoMoves.ret _

/-- **The query group's expectation.** For a function `F` of the group's values, if every
in-range position list has `avg_λ F(qs, λ, W(qs)) ≤ allIn S qs + ε` (the rows read from the
word `W` of commitment `i`), the expectation over the group is at most
`(|S ∩ [0, 2^depth)| / 2^depth)^t + ε`. -/
theorem retExp_queryFrag_le (depth t i : ℕ) (h1 : 1 ≤ depth) (h192 : depth ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hc : (commits h₀)[i]? = some (depth, wd, W))
    (F : List ℕ × E × List (List K) → ENNReal) (S : ℕ → Prop) [DecidablePred S] (ε : ENNReal)
    (hF : ∀ qs : List ℕ, (∀ q ∈ qs, q < 2 ^ depth) → qs.length = t →
      (Fintype.card E : ENNReal)⁻¹ * ∑ lam : E, F (qs, lam, qs.map W) ≤ allIn S qs + ε) :
    retExp (fun a _ ↦ F a) h₀ [] (queryFrag depth t i) ≤
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ t + ε := by
  unfold queryFrag
  simp only [bind_eq]
  rw [retExp_bind]
  -- The inner expectation depends on the history only through its commitments.
  have hin : ∀ qs h, retExp (fun a _ ↦ F a) h []
      ((sampleE.bind fun lam ↦ (queryP i qs).bind fun words ↦ Prog.ret (qs, lam, words))) =
      (Fintype.card E : ENNReal)⁻¹ * ∑ lam : E,
        (match answer h i qs with
          | some rows => F (qs, lam, rows)
          | none => 0) := by
    intro qs h
    rw [retExp_bind, retExp_sampleE]
    congr 1
    refine Finset.sum_congr rfl fun lam _ ↦ ?_
    rw [retExp_bind, retExp_queryP, List.append_nil, List.append_nil, answer_append_sample]
    cases answer h i qs <;> simp [retExp]
  simp only [hin]
  -- Its value along the run is that at `h₀`.
  have hcom := retExp_commits (fun qs cs ↦ (Fintype.card E : ENNReal)⁻¹ * ∑ lam : E,
      (match (cs[i]?.map fun c ↦ qs.map fun p ↦ c.2.2 (p % 2 ^ c.1)) with
        | some rows => F (qs, lam, rows)
        | none => 0)) (sampleQueries depth t) h₀ []
  simp only [answer] at hcom ⊢
  rw [hcom, List.append_nil, sampleQueries,
    retExp_sampleQueriesAux_restrict_len depth h1 h192 _ t t le_rfl]
  calc _ ≤ retExp (fun qs _ ↦ allIn S qs + ε) h₀ [] (sampleQueriesAux depth t t) := by
        refine retExp_mono (fun qs _ ↦ ?_) _ _ _
        split_ifs with hr
        · simp only [hc, Option.map_some]
          have hmap : (qs.map fun p ↦ W (p % 2 ^ depth)) = qs.map W :=
            List.map_congr_left fun q hq ↦ by rw [Nat.mod_eq_of_lt (hr.1 q hq)]
          rw [hmap]
          exact hF qs hr.1 hr.2
        · exact zero_le
    _ ≤ retExp (fun qs _ ↦ allIn S qs) h₀ [] (sampleQueriesAux depth t t) + ε :=
        retExp_le_add (fun _ _ ↦ le_rfl) _ _ _
    _ ≤ _ := by
        gcongr
        exact retExp_sampleQueries_le depth t h1 h192 S h₀ []

end
end LeanVM.Protocol.Whir.Sound
