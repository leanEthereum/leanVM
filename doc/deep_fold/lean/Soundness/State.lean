/-
The full round-by-round state of Section 5.3 of the paper and the transition of every verifier
message for it (Section 5.4), each as a probability over the verifier's message with the error of
Theorem 5.2.

The state after `k` fold rounds of a level is `FullState`: the invariant `(I_{i,k})` (`Rounds.Doomed`:
no list member with the predicate satisfies the running claim and all carried point claims)
TOGETHER with `(G_{i,k})`: the potential of the level's points is below one (`Protocol.levelPot`).
The library `Rounds` proves the transitions of the first part taking "the points are not
exceptional" and "the points separate the list" as hypotheses; the library `Protocol` proves
that the potential gives the first and goodness the second. Here they are joined.

- `points_full` (M0): the point message after a commitment.
- `batch_full` (M1): the batching challenge at level 0.
- `fold_full` (M2): a fold challenge, `(K₀ - 1)/q^2 + τ`, and `(K₀ - 1)/q^2` in the last round.
- `query_full` (M3): the query message of a level that is not the last. This is where the state
  is re-initialized: the potential of the new level is the goodness of its points.
- `final_full` (M4): the query message of the last level.

A probability is `Protocol.dens`: the number of messages with the property over the number of
messages. The query positions are the vectors `Fin t → D`, the domain `D` seen as a type.
-/
import Rounds.Fold
import Rounds.Final
import Rounds.Pinned
import Protocol.Level

open Polynomial
open Finset hiding dens
open scoped Classical

namespace Soundness

open DeepFold
open Protocol (Lane Word exL levelPot Good NonSep listW foldW dens)
open Rounds (Doomed Doomed₁ InList foldVal foldWeight foldClaim pull batchW batchC nextW nextC
  constL)

/-- A word with no lane variable left has one lane. -/
instance : Unique (Lane 0) := inferInstanceAs (Unique Unit)

section Counting

variable {α : Type*} [Fintype α]

/-- `dens` as a quotient of cardinalities, for any decidability of the predicate. -/
theorem dens_eq_card_div (p : α → Prop) [DecidablePred p] :
    dens p = ((univ.filter p).card : ℚ) / Fintype.card α := by
  unfold Protocol.dens
  congr

/-- The probability of an impossible event. -/
theorem dens_of_forall_not {p : α → Prop} (h : ∀ a, ¬ p a) : dens p = 0 := by
  rw [dens_eq_card_div, filter_eq_empty_iff.mpr fun a _ => h a]
  simp

variable {K : Type*}

/-- Vectors of `t` positions of `D`, as vectors of elements of the type `D`, are the vectors of
`Fintype.piFinset`: a count over the first is at most the count over the second. -/
theorem card_queries_le (D : Finset K) (t : ℕ) (Q : (Fin t → K) → Prop) [DecidablePred Q]
    [DecidablePred fun x : Fin t → D => Q fun q => (x q : K)] :
    (univ.filter (fun x : Fin t → D => Q (fun q => (x q : K)))).card ≤
      ((Fintype.piFinset (fun _ : Fin t => D)).filter Q).card := by
  refine card_le_card_of_injOn (fun x q => (x q : K)) ?_ ?_
  · intro x hx
    exact mem_coe.mpr (mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun q => (x q).2,
      (mem_filter.mp (mem_coe.mp hx)).2⟩)
  · intro x _ x' _ h
    funext q
    exact Subtype.ext (congrFun h q)

/-- The same with a second component. -/
theorem card_queries_prod_le (D : Finset K) (t : ℕ) (Q : (Fin t → K) × α → Prop)
    [DecidablePred Q] [DecidablePred fun xl : (Fin t → D) × α => Q (fun q => (xl.1 q : K), xl.2)] :
    (univ.filter (fun xl : (Fin t → D) × α => Q (fun q => (xl.1 q : K), xl.2))).card ≤
      (((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset α)).filter Q).card := by
  refine card_le_card_of_injOn (fun xl => (fun q => (xl.1 q : K), xl.2)) ?_ ?_
  · intro xl hxl
    exact mem_coe.mpr (mem_filter.mpr ⟨mem_product.mpr
      ⟨Fintype.mem_piFinset.mpr fun q => (xl.1 q).2, mem_univ _⟩,
      (mem_filter.mp (mem_coe.mp hxl)).2⟩)
  · intro xl _ xl' _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine Prod.ext ?_ h2
    funext q
    exact Subtype.ext (congrFun h1 q)

end Counting

variable {K : Type*} [Field K] [Fintype K]

/-- **The full state** of Section 5.3 of the paper, after `k` fold rounds of a level, with `r`
rounds to come. The level has domain `D`, degree bound `d`, thresholds `thr` (`thr k = A^{(i,k)}`),
`s` points `z`, and the analysis constants `τ` and `Θ` (the threshold `K₀ (K₀ - 1) (K₀ - M)` of
the triple count). `O` is the committed word folded by the `k` challenges so far, `(W, σ)` the
running claim, `v` the carried point values and `B` the predicate of the relativised invariant
(`fun _ => True` for plain soundness).

- `(I_{i,k})`: no `U ∈ List(O; thr k, d)` with `B(U)` satisfies `(W, σ)` and all point claims;
- `(G_{i,k})`: the potential `Ψ_k` of the points is below one. -/
def FullState (τ : ℚ) (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (s Θ : ℕ) (k r : ℕ) (O : Word K r)
    (z : Fin s → K × K) (v : Fin s → K) (W : (Lane r → K[X]) →ₗ[K] K) (σ : K)
    (B : (Lane r → K[X]) → Prop) : Prop :=
  Doomed D O d (thr k) (exL k r) z v W σ B ∧ levelPot τ D d thr s Θ z k r O < 1

/-- **M0, the point message, for the full state** (Section 5.4 of the paper). `O` is the word
committed before the points, with `ℓ ≥ 1` lane variables, and every word of the level folded `k`
times has at most `L` list members at the agreement `thr k` (`ListBound`). The points `z` are
*bad* if for some answer vector `y`, sent by the prover after the points, two distinct members of
`List(O; thr 0, d)` match all answers, or if the potential `Ψ_0` is at least one. The probability
of bad points is at most `[C(L, 2) + L^3 q^6 / Θ · ∑_{j < ℓ} τ^(-j)] ε^s`, `ε = (d + 2^ℓ - 1)/q`. -/
theorem points_full {τ : ℚ} {D : Finset K} {d : ℕ} {thr : ℕ → ℕ} {s Θ : ℕ} (hτ : 0 ≤ τ)
    (hΘ : 0 < Θ) {L ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hL : ∀ k r, k + r = ℓ → ∀ O' : Word K r, (listW D O' d (thr k)).card ≤ L) (O : Word K ℓ) :
    dens (fun z : Fin s → K × K =>
        (∃ (y : Fin s → K) (U U' : Lane ℓ → K[X]), InList D O d (thr 0) U ∧
          InList D O d (thr 0) U' ∧ U ≠ U' ∧ (∀ m, evL (exL 0 ℓ) (z m) U = y m) ∧
          ∀ m, evL (exL 0 ℓ) (z m) U' = y m) ∨
        1 ≤ levelPot τ D d thr s Θ z 0 ℓ O) ≤
      ((L.choose 2 : ℚ) + (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 / Θ *
          ∑ j ∈ range ℓ, τ⁻¹ ^ j) * (((d + 2 ^ ℓ - 1 : ℕ) : ℚ) / Fintype.card K) ^ s := by
  refine (Protocol.dens_mono ?_).trans (Protocol.dens_not_good_le hτ hΘ hℓ hL O)
  rintro z hz ⟨hsep, hpot⟩
  rcases hz with ⟨y, U, U', hU, hU', hne, hy, hy'⟩ | hz
  · exact hne (Rounds.sep_of_not_mem_nonSep hsep y U U' hU hU' hy hy')
  · exact absurd hpot (not_lt.mpr hz)

/-- Good points are not bad: for every answer vector at most one list member matches (Lemma 4.11 of
the paper),
and the potential is below one. -/
theorem Good.not_bad {τ : ℚ} {D : Finset K} {d : ℕ} {thr : ℕ → ℕ} {s Θ ℓ : ℕ} {O : Word K ℓ}
    {z : Fin s → K × K} (hz : Good τ D d thr s Θ ℓ O z) :
    (∀ (y : Fin s → K) (U U' : Lane ℓ → K[X]), InList D O d (thr 0) U → InList D O d (thr 0) U' →
      (∀ m, evL (exL 0 ℓ) (z m) U = y m) → (∀ m, evL (exL 0 ℓ) (z m) U' = y m) → U = U') ∧
      levelPot τ D d thr s Θ z 0 ℓ O < 1 :=
  ⟨fun y => Rounds.sep_of_not_mem_nonSep hz.1 y, hz.2⟩

/-- **M1, the batching challenge, for the full state** (Section 5.4 of the paper). The points `z`
are good for the committed word `O`, the prover has answered `y` and the `J` input claims
`(W_k, c_k)` are false relative to `B` (`hfalse`; with `B` true, the definition of false input
claims of Section 5.2). Then the state after `λ` is the full state of round `0` except with
probability `(J - 1)/q`. The potential part is the goodness of the points, which `λ` does not
touch. -/
theorem batch_full {τ : ℚ} {D : Finset K} {d : ℕ} {thr : ℕ → ℕ} {s Θ ℓ : ℕ} (O : Word K ℓ)
    {z : Fin s → K × K} (hz : Good τ D d thr s Θ ℓ O z) (y : Fin s → K) {J : ℕ}
    (Wk : Fin J → (Lane ℓ → K[X]) →ₗ[K] K) (ck : Fin J → K) (B : (Lane ℓ → K[X]) → Prop)
    (hfalse : ∀ U : Lane ℓ → K[X], InList D O d (thr 0) U → B U →
      (∀ m, evL (exL 0 ℓ) (z m) U = y m) → ∃ k, Wk k U ≠ ck k) :
    dens (fun l : K => ¬ FullState τ D d thr s Θ 0 ℓ O z y (batchW Wk l) (batchC ck l) B) ≤
      ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have h := Rounds.batch_transition_density D O d (thr 0) (exL 0 ℓ) z y Wk ck B
    (Rounds.sep_of_not_mem_nonSep hz.1 y) hfalse
  refine (Protocol.dens_mono (p' := fun l : K =>
    ¬ Doomed D O d (thr 0) (exL 0 ℓ) z y (batchW Wk l) (batchC ck l) B) ?_).trans ?_
  · intro l hl hd
    exact hl ⟨hd, hz.2⟩
  · rw [dens_eq_card_div]
    exact h

/-- **M2, the fold challenge, for the full state** (Section 5.4 of the paper): Lemma 4.12(b)
(`Protocol.levelPot_step`) joined with Lemma 4.10(2) (`Rounds.fold_transition`).

Before the challenge of round `k + 1` the full state holds for the word `O` (folded `k` times,
`r + 1` rounds to come): `(I_{i,k})` and `Ψ_k < 1`. The thresholds grow by at least one a round
(`hthr`; in the paper, exactly one), and `M ≥ max(2 q, C(n, 2))`. Then for every prover message
`(v_G, v_F, σ₀, σ₁, φ)` the challenge `c` leads to a state that is not the full state of round
`k + 1` (for the fold `O_c`, the updated claim and values, and the pull-back of `B`) with
probability at most `(K₀ - 1)/q^2 + τ`, and at most `(K₀ - 1)/q^2` in the last round of the level
(`r = 0`), where the potential that follows is zero. -/
theorem fold_full [CharP K 2] {τ : ℚ} (hτ : 0 < τ) {D : Finset K} {d : ℕ} {thr : ℕ → ℕ}
    {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M) {k r : ℕ}
    (hthr : thr k + 1 ≤ thr (k + 1)) (O : Word K (r + 1)) (z : Fin s → K × K) (v : Fin s → K)
    (W : (Lane (r + 1) → K[X]) →ₗ[K] K) (σ : K) (B : (Lane (r + 1) → K[X]) → Prop)
    (h : FullState τ D d thr s (K₀ * (K₀ - 1) * (K₀ - M)) k (r + 1) O z v W σ B)
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    dens (fun c : K × K => ¬ FullState τ D d thr s (K₀ * (K₀ - 1) * (K₀ - M)) (k + 1) r
        (foldW O c) z (foldVal (2 ^ k) z v φm c) (foldWeight W c) (foldClaim σ vG vF σ₀ σ₁ c)
        (pull D O d (thr (k + 1)) c B)) ≤
      ((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2 + if r = 0 then 0 else τ := by
  obtain ⟨hI, hT⟩ := h
  obtain ⟨hz, hstep⟩ := Protocol.levelPot_step hτ hT
  have hI' : Doomed D O d (thr (k + 1) - 1) (Rounds.exHalves (2 ^ k) (exL (k + 1) r)) z v W σ
      B := by
    intro U hU hB hpt
    exact hI U ⟨hU.1, by have := hU.2; omega⟩ hB hpt
  have hfold : dens (fun c : K × K => ¬ Doomed D (foldW O c) d (thr (k + 1)) (exL (k + 1) r) z
      (foldVal (2 ^ k) z v φm c) (foldWeight W c) (foldClaim σ vG vF σ₀ σ₁ c)
      (pull D O d (thr (k + 1)) c B)) ≤ ((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2 := by
    rw [dens_eq_card_div]
    exact Rounds.fold_transition_density D O d (thr (k + 1)) (exL (k + 1) r) (2 ^ k) hMq hMn hz
      W σ v B hI' vG vF σ₀ σ₁ φm
  have hsplit : dens (fun c : K × K => ¬ FullState τ D d thr s (K₀ * (K₀ - 1) * (K₀ - M))
        (k + 1) r (foldW O c) z (foldVal (2 ^ k) z v φm c) (foldWeight W c)
        (foldClaim σ vG vF σ₀ σ₁ c) (pull D O d (thr (k + 1)) c B)) ≤
      dens (fun c : K × K => ¬ Doomed D (foldW O c) d (thr (k + 1)) (exL (k + 1) r) z
        (foldVal (2 ^ k) z v φm c) (foldWeight W c) (foldClaim σ vG vF σ₀ σ₁ c)
        (pull D O d (thr (k + 1)) c B)) +
      dens (fun c : K × K =>
        1 ≤ levelPot τ D d thr s (K₀ * (K₀ - 1) * (K₀ - M)) z (k + 1) r (foldW O c)) := by
    refine (Protocol.dens_mono ?_).trans (Protocol.dens_or_le _ _)
    intro c hc
    by_contra hcon
    rcases not_or.mp hcon with ⟨h1, h2⟩
    exact hc ⟨not_not.mp h1, not_le.mp h2⟩
  refine hsplit.trans (add_le_add hfold ?_)
  split_ifs with hr
  · subst hr
    rw [dens_of_forall_not]
    intro c
    rw [Protocol.levelPot_zero]
    norm_num
  · exact hstep.le

/-- **M3, the query message of a level that is not the last, for the full state** (Section 5.4 of
the paper), and the re-initialization of the state at a level boundary.

The level that ends: domain `D` (nonempty), degree bound `d`, agreement `A = A_i`, its word `O`
folded to one lane, its points `z` with carried values `v`, the running claim `(W, σ)`, and
`(I_{i,ℓ_i})` (`hI`). Its potential plays no role any more. The new level: committed word `O'`,
points `z'` that are good for it (`hz'`: the state after the new point message, whose failure is
charged to `points_full`), answers `y'`. The link: `low U = 𝒫_{g_U}` (any linear map), the high
part `C` with `deg(low U + C) ≤ d` for list members (`hdeg`) and `⟨W, C⟩ = 0` (`hWC`).

Then the message (`t` positions of `D` and `λ`) leads to a state that is not the full state of
round `0` of the new level (the batched claim of step 2, the carried values `y'`, the
predicate `U ↦ B(low U + C)`, and the potential of the new points) with probability at most
`((A - 1)/n)^t + (s + t)/q`. -/
theorem query_full [CharP K 2] (D : Finset K) (hD : D.Nonempty) (d A : ℕ) {s : ℕ}
    (O : Word K 0) (z : Fin s → K × K) (v : Fin s → K) (W : (Lane 0 → K[X]) →ₗ[K] K) (σ : K)
    (B : (Lane 0 → K[X]) → Prop) (hI : Doomed D O d A (fun _ => 0) z v W σ B)
    {τ' : ℚ} {D' : Finset K} {d' : ℕ} {thr' : ℕ → ℕ} {s' Θ' ℓ' : ℕ} (O' : Word K ℓ')
    {z' : Fin s' → K × K} (hz' : Good τ' D' d' thr' s' Θ' ℓ' O' z') (y' : Fin s' → K)
    (low : (Lane ℓ' → K[X]) →ₗ[K] K[X]) (C : K[X])
    (hdeg : ∀ U : Lane ℓ' → K[X], InList D' O' d' (thr' 0) U → (low U + C).natDegree ≤ d)
    (hWC : W (fun _ => C) = 0) (t : ℕ) :
    dens (fun xl : (Fin t → D) × K => ¬ FullState τ' D' d' thr' s' Θ' 0 ℓ' O' z' y'
        (nextW (W ∘ₗ constL (Lane 0)) low (fun m => (z m).2) (fun q => (xl.1 q : K)) xl.2)
        (nextC σ C (fun x => O x default) (fun m => (z m).2) v (fun q => (xl.1 q : K)) xl.2)
        (fun U => B (fun _ => low U + C))) ≤
      (((A - 1 : ℕ) : ℚ) / (D.card : ℚ)) ^ t + ((s + t : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have hcount := Rounds.query_transition_pinned D (fun x => O x default) d A (fun m => (z m).2) v
    (W ∘ₗ constL (Lane 0)) σ (fun P => B (fun _ => P)) hI.one_lane D' O' d' (thr' 0) (exL 0 ℓ')
    hz'.1 y' low C hdeg hWC t
  have hle : (univ.filter (fun xl : (Fin t → D) × K => ¬ FullState τ' D' d' thr' s' Θ' 0 ℓ' O'
        z' y'
        (nextW (W ∘ₗ constL (Lane 0)) low (fun m => (z m).2) (fun q => (xl.1 q : K)) xl.2)
        (nextC σ C (fun x => O x default) (fun m => (z m).2) v (fun q => (xl.1 q : K)) xl.2)
        (fun U => B (fun _ => low U + C)))).card ≤
      (A - 1) ^ t * Fintype.card K + D.card ^ t * (s + t) := by
    refine (card_le_card ?_).trans ((card_queries_prod_le D t (fun xl : (Fin t → K) × K =>
      ¬ Doomed D' O' d' (thr' 0) (exL 0 ℓ') z' y'
        (nextW (W ∘ₗ constL (Lane 0)) low (fun m => (z m).2) xl.1 xl.2)
        (nextC σ C (fun x => O x default) (fun m => (z m).2) v xl.1 xl.2)
        (fun U => B (fun _ => low U + C)))).trans hcount)
    intro xl hxl
    refine mem_filter.mpr ⟨mem_univ _, fun hd => (mem_filter.mp hxl).2 ⟨hd, hz'.2⟩⟩
  have hq : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℚ) < (D.card : ℚ) := by exact_mod_cast hD.card_pos
  have hcard : (Fintype.card ((Fin t → D) × K) : ℚ) = (D.card : ℚ) ^ t * (Fintype.card K : ℚ) := by
    simp [Fintype.card_prod]
  have hle' : ((univ.filter (fun xl : (Fin t → D) × K => ¬ FullState τ' D' d' thr' s' Θ' 0 ℓ' O'
        z' y'
        (nextW (W ∘ₗ constL (Lane 0)) low (fun m => (z m).2) (fun q => (xl.1 q : K)) xl.2)
        (nextC σ C (fun x => O x default) (fun m => (z m).2) v (fun q => (xl.1 q : K)) xl.2)
        (fun U => B (fun _ => low U + C)))).card : ℚ) ≤
      ((A - 1 : ℕ) : ℚ) ^ t * (Fintype.card K : ℚ) + (D.card : ℚ) ^ t * ((s + t : ℕ) : ℚ) := by
    exact_mod_cast hle
  rw [dens_eq_card_div, hcard, div_le_iff₀ (by positivity), div_pow]
  refine hle'.trans (le_of_eq ?_)
  field_simp

/-- A full state for a predicate is a full state for every stronger predicate. -/
theorem FullState.mono {τ : ℚ} {D : Finset K} {d : ℕ} {thr : ℕ → ℕ} {s Θ k r : ℕ} {O : Word K r}
    {z : Fin s → K × K} {v : Fin s → K} {W : (Lane r → K[X]) →ₗ[K] K} {σ : K}
    {B B' : (Lane r → K[X]) → Prop} (h : FullState τ D d thr s Θ k r O z v W σ B)
    (hB : ∀ U, B' U → B U) : FullState τ D d thr s Θ k r O z v W σ B' :=
  ⟨h.1.mono hB, h.2⟩

omit [Fintype K] in
/-- **M4, the query message of the last level, for the full state** (Section 5.4 of the paper),
in the relativised form of Theorem 5.6. At the end of the last level the word `O` is one lane and
`(I_{Λ-1,ℓ})` holds (`hI`). The prover has sent a polynomial `P` of degree at most `d`. Then with
probability at most `((A - 1)/n)^t` over `t` positions of `D`: the point check and the query
check pass, `P` satisfies the running claim, and `B(P)` (for plain soundness `B` is true and the
event is "the verifier accepts"). -/
theorem final_full (D : Finset K) (d A : ℕ) {s : ℕ} (O : Word K 0) (z : Fin s → K × K)
    (v : Fin s → K) (W : (Lane 0 → K[X]) →ₗ[K] K) (σ : K) (B : (Lane 0 → K[X]) → Prop)
    (hI : Doomed D O d A (fun _ => 0) z v W σ B) (P : K[X]) (hP : P.natDegree ≤ d) (t : ℕ) :
    dens (fun x : Fin t → D => (∀ m, P.eval (z m).2 = v m) ∧
        (∀ q, P.eval (x q : K) = O (x q) default) ∧ W (fun _ => P) = σ ∧ B (fun _ => P)) ≤
      (((A - 1 : ℕ) : ℚ) / (D.card : ℚ)) ^ t := by
  have hcount := Rounds.final_transition D (fun x => O x default) d A (fun m => (z m).2) v
    (W ∘ₗ constL (Lane 0)) σ (fun P => B (fun _ => P)) hI.one_lane P hP t
  have hle : (univ.filter (fun x : Fin t → D => (∀ m, P.eval (z m).2 = v m) ∧
      (∀ q, P.eval (x q : K) = O (x q) default) ∧ W (fun _ => P) = σ ∧ B (fun _ => P))).card ≤
      (A - 1) ^ t := by
    refine (card_le_card ?_).trans ((card_queries_le D t (fun x : Fin t → K =>
      (∀ m, P.eval (z m).2 = v m) ∧ (∀ q, P.eval (x q) = O (x q) default) ∧
        (W ∘ₗ constL (Lane 0)) P = σ ∧
        ¬ (A ≤ (D.filter (fun x => P.eval x = O x default)).card ∧ ¬ B (fun _ => P)))).trans
      hcount)
    intro x hx
    obtain ⟨_, h1, h2, h3, h4⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_univ _, h1, h2, h3, fun hc => hc.2 h4⟩
  have hcard : (Fintype.card (Fin t → D) : ℚ) = (D.card : ℚ) ^ t := by simp
  rw [dens_eq_card_div, hcard, div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast hle

end Soundness
