/-
  LeanVM.Protocol.ToArkLib.Whir.Fold

  Folding interleaved words: one coordinate at a time and by eq-weights over a cube, the fold of
  the list of close interleaved codewords, and the count of challenges at which folding creates
  new close codewords. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.Interleaved
public import LeanVM.Protocol.ToCompPoly.Multilinear
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine

/-!
# Folding interleaved words

Annex B of the leanVM specification (leanVM `127510d1`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`): the fold of `def:interleaved`, the fact
`fact:fold-decode` that folding commutes with decoding, and the lemma `lem:fold-list` that
folding preserves lists outside few challenges, in count form.

The count bounds here are the row-by-row union bound of the Annex at `a386121f` (`|ρ|` times the
pair bound, the `2^{ℓ-1} ε` of that revision). At `127510d1` `lem:fold-list` states the bound `ε`
without the row-union factor, from Jo's interleaving stability theorem (`Jo26`, Thm. 4.4,
`b-polynomial-commitment-scheme.tex:189-205`); that sharper statement is not formalized here.

## One coordinate

An interleaved word with rows `Bool × ρ` folds at `s : F` to the word with rows `ρ`,
`fold s O u = (1 - s) O (false, u) + s O (true, u)`.

* `isInterleavedCodeword_fold`, `fold_mem_iList`, `image_fold_iList_subset`: folding keeps
  codewords and closeness, so the fold of the list is always contained in the list of the fold.
* `fold_encoder`: folding commutes with any linear encoder applied row by row;
  `eq_fold_of_encoder`: for an injective encoder, a folded row decodes to the folded messages.
* `card_foldBad_le_of_lineExact`: **the fold-list lemma.** If the Reed-Solomon code admits
  ArkLib's uniform exact line agreement `ReedSolomon.LineExactAgreementBound domain k A B`, then
  at most `|ρ| ⌊B⌋₊` challenges `s` have `Λ(fold s O) ≠ fold s '' Λ(O)` at threshold `A`.
* `card_foldBad_le_johnson`: the Johnson instance, from
  `ReedSolomon.exists_johnson_line_exactCorrelatedPair_ceil` (the count behind
  `ReedSolomon.mcaError_affineLine_johnson_le`): at the threshold
  `⌈johnsonAgreement n D η * n⌉₊`, at most `|ρ| ⌊johnsonExceptionCount n D ⌈…⌉₊ η⌋₊` challenges are
  bad, in any characteristic.
* `card_foldBad_le_of_mca`: the Annex's own argument for an arbitrary linear code, from a count
  bound on the mutual correlated agreement event `McaBad` of every pair of rows and the
  uniqueness of codewords on `A` coordinates.

The Annex's footnote rewrites `(1 - s) u₀ + s u₁` as `u₀ + s (u₁ - u₀)`; the pair `(u₀, u₁)`
agrees with the interleaved code on a set exactly when `(u₀, u₁ - u₀)` does, so the affine-line
statements apply after this change of pair, which is valid in every characteristic (the
footnote's `u₀ + u₁` is the characteristic-two case). ArkLib's exact line agreement gives a
decomposition `P = P₀ + s P₁` of the decoded polynomial itself, so the route through it needs no
uniqueness hypothesis; the route through the bare MCA event (`card_foldBad_le_of_mca`) needs it,
as in the Annex.

## Many coordinates

For a word with rows `Fin (2 ^ j) × ρ` (the cube in CompPoly's little-endian table indexing),
`foldMany s O u x` is the multilinear extension of the column `i ↦ O (i, u) x` at
`s : Vector F j`.

* `foldMany_eq_sum`: it is the eq-weighted sum `Σ_i eq(s, i) O[(i, u), x]` of the Annex, the weight
  being CompPoly's `lagrangeBasis s`.
* `foldMany_succ`: it is the one-coordinate fold at `s.head` (coordinate `0`, the low index bit)
  followed by the fold at `s.tail`, with rows paired by `pairUp`; `foldMany_zero` is the base.
* `isInterleavedCodeword_foldMany`, `foldMany_mem_iList`, `foldMany_encoder`: the same closure
  properties as one fold.
-/

namespace LeanVM.Protocol.Whir

open Finset Polynomial CompPoly CMlPolynomialEval ReedSolomon.HiddenDerivative

@[expose] public section

variable {F : Type*} [Field F] {ι ρ σ : Type*}

/-- A union of per-row exceptional sets of at most `B` challenges each has at most `|R| ⌊B⌋₊`
elements. -/
private theorem card_biUnion_le_floor {G R : Type*} [DecidableEq G] [Fintype R]
    (ex : R → Finset G) {B : ℝ}
    (hex : ∀ u, ((ex u).card : ℝ) ≤ B) :
    (univ.biUnion ex).card ≤ Fintype.card R * ⌊B⌋₊ :=
  (Finset.card_biUnion_le).trans <| by
    simpa using Finset.sum_le_card_nsmul univ (fun u ↦ (ex u).card) ⌊B⌋₊
      fun u _ ↦ Nat.le_floor (hex u)

/-! ## One coordinate -/

/-- **The fold at `s`** of an interleaved word with rows `Bool × ρ`:
`fold s O u = (1 - s) O (false, u) + s O (true, u)`. -/
def fold (s : F) (O : Bool × ρ → ι → F) : ρ → ι → F :=
  fun u x ↦ (1 - s) * O (false, u) x + s * O (true, u) x

/-- The fold on the affine line through `O (false, u)` in direction `O (true, u) - O (false, u)`. -/
theorem fold_apply_eq_line (s : F) (O : Bool × ρ → ι → F) (u : ρ) (x : ι) :
    fold s O u x = O (false, u) x + s * (O (true, u) x - O (false, u) x) := by
  simp only [fold]; ring

/-- A folded row is a linear combination of the two rows. -/
theorem fold_apply_eq_smul (s : F) (O : Bool × ρ → ι → F) (u : ρ) :
    fold s O u = (1 - s) • O (false, u) + s • O (true, u) := by
  funext x; simp [fold]

/-- Folding keeps interleaved codewords of a linear code. -/
theorem isInterleavedCodeword_fold (C : Submodule F (ι → F)) {U : Bool × ρ → ι → F}
    (hU : IsInterleavedCodeword C U) (s : F) : IsInterleavedCodeword C (fold s U) := fun u ↦ by
  rw [fold_apply_eq_smul]
  exact C.add_mem (C.smul_mem _ (hU _)) (C.smul_mem _ (hU _))

/-- Folding keeps agreement on a set. -/
theorem AgreeOn.fold {O U : Bool × ρ → ι → F} {S : Finset ι} (h : AgreeOn O U S) (s : F) :
    AgreeOn (Whir.fold s O) (Whir.fold s U) S := fun u x hx ↦ by
  simp only [Whir.fold, h (false, u) x hx, h (true, u) x hx]

/-- **Folding commutes with decoding** (Annex B, `fact:fold-decode`): for a linear encoder
applied row by row, the fold of the encoded word is the encoding of the folded messages. -/
theorem fold_encoder (enc : (σ → F) →ₗ[F] (ι → F)) (s : F) (g : Bool × ρ → σ → F) :
    fold s (fun r ↦ enc (g r)) = fun u ↦ enc (fold s g u) := by
  funext u
  rw [fold_apply_eq_smul, fold_apply_eq_smul, map_add, map_smul, map_smul]

/-- **The decoded message of a fold.** For an injective linear encoder, a row of the fold of an
encoded word decodes to the fold of the messages. -/
theorem eq_fold_of_encoder (enc : (σ → F) →ₗ[F] (ι → F)) (henc : Function.Injective enc)
    (s : F) (g : Bool × ρ → σ → F) (u : ρ) {m : σ → F}
    (hm : fold s (fun r ↦ enc (g r)) u = enc m) : m = fold s g u :=
  henc (hm.symm.trans (congrFun (fold_encoder enc s g) u))

section List

variable [Fintype F] [Fintype ι] [Fintype ρ]

/-- **The fold of a list member is in the list of the fold.** -/
theorem fold_mem_iList (C : Submodule F (ι → F)) {A : ℕ} {O U : Bool × ρ → ι → F}
    (hU : U ∈ iList C A O) (s : F) : fold s U ∈ iList C A (fold s O) := by
  rw [mem_iList] at hU ⊢
  obtain ⟨hcw, S, hS, hagree⟩ := hU
  exact ⟨isInterleavedCodeword_fold C hcw s, S, hS, hagree.fold s⟩

/-- **The inclusion that always holds** (Annex B, `lem:fold-list`, `⊇`): the fold of the list is
contained in the list of the fold. -/
theorem image_fold_iList_subset [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F))
    (A : ℕ) (O : Bool × ρ → ι → F) (s : F) :
    (iList C A O).image (fold s) ⊆ iList C A (fold s O) := by
  intro V hV
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hV
  exact fold_mem_iList C hU s

/-- The challenges at which folding the list differs from the list of the fold: the bad event of
Annex B, `lem:fold-list`. -/
noncomputable def foldBad [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F)) (A : ℕ)
    (O : Bool × ρ → ι → F) : Finset F :=
  univ.filter fun s ↦ iList C A (fold s O) ≠ (iList C A O).image (fold s)

theorem mem_foldBad [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F)) (A : ℕ)
    (O : Bool × ρ → ι → F) (s : F) :
    s ∈ foldBad C A O ↔ iList C A (fold s O) ≠ (iList C A O).image (fold s) := by
  simp [foldBad]

/-- A challenge is good as soon as every member of the list of the fold is a fold of a member of
the list. -/
theorem not_mem_foldBad_of_subset [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F))
    (A : ℕ) (O : Bool × ρ → ι → F) (s : F)
    (h : ∀ V ∈ iList C A (fold s O), ∃ W ∈ iList C A O, fold s W = V) :
    s ∉ foldBad C A O := by
  rw [mem_foldBad, not_not]
  refine Finset.Subset.antisymm (fun V hV ↦ ?_) (image_fold_iList_subset C A O s)
  obtain ⟨W, hW, rfl⟩ := h V hV
  exact Finset.mem_image_of_mem _ hW

/-! ### Through exact line agreement -/

omit [Fintype F] in
/-- A larger threshold keeps a uniform exact line agreement bound. -/
theorem lineExactAgreementBound_mono_threshold [DecidableEq F] {domain : ι ↪ F} {k A A' : ℕ}
    {B : ℝ} (h : ReedSolomon.LineExactAgreementBound domain k A B) (hA : A ≤ A') :
    ReedSolomon.LineExactAgreementBound domain k A' B := fun f g ↦
  (h f g).imp fun _ hex ↦ ⟨hex.1, fun z hz P hP hagree ↦ hex.2 z hz P hP (hA.trans hagree)⟩

/-- **The fold-list lemma, by exact line agreement** (Annex B, `lem:fold-list`, count form).
If the Reed-Solomon code of degree below `k` has uniform exact line agreement at threshold `A`
with at most `B` exceptional challenges per pair of words, then for every interleaved word with
rows `Bool × ρ`, at most `|ρ| ⌊B⌋₊` challenges `s` have `Λ(fold s O) ≠ fold s '' Λ(O)`. -/
theorem card_foldBad_le_of_lineExact [DecidableEq F] [DecidableEq ι] (domain : ι ↪ F)
    {k A : ℕ} {B : ℝ} (hline : ReedSolomon.LineExactAgreementBound domain k A B)
    (O : Bool × ρ → ι → F) :
    (foldBad (ReedSolomon.code domain k) A O).card ≤ Fintype.card ρ * ⌊B⌋₊ := by
  choose ex hexcard hex using fun u : ρ ↦
    hline (O (false, u)) (fun x ↦ O (true, u) x - O (false, u) x)
  refine (Finset.card_le_card fun s hs ↦ ?_).trans (card_biUnion_le_floor ex hexcard)
  by_contra hsex
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hsex
  refine not_mem_foldBad_of_subset _ A O s (fun V hV ↦ ?_) hs
  obtain ⟨hVcw, S, hS, hagree⟩ := (mem_iList _ A _ V).mp hV
  -- Decompose every row of `V` along the line of the matching pair of rows of `O`.
  have hdec : ∀ u, ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ x, V u x = P₀.eval (domain x) + s * P₁.eval (domain x)) ∧
      ∀ x ∈ S, P₀.eval (domain x) = O (false, u) x ∧
        P₁.eval (domain x) = O (true, u) x - O (false, u) x := by
    intro u
    obtain ⟨P, hP, hPV⟩ := ReedSolomon.mem_code_iff_eval.mp (hVcw u)
    have hA : A ≤ (ReedSolomon.polynomialAgreementSet domain
        (fun x ↦ O (false, u) x + s * (O (true, u) x - O (false, u) x)) P).card :=
      hS.trans (Finset.card_le_card fun x hx ↦ by
        rw [ReedSolomon.mem_polynomialAgreementSet, hPV, ← hagree u x hx, fold_apply_eq_line])
    obtain ⟨P₀, P₁, hP₀, hP₁, hPeq, hset⟩ := hex u s (hsex u) P hP hA
    refine ⟨P₀, P₁, hP₀, hP₁, fun x ↦ ?_, fun x hx ↦ ?_⟩
    · rw [← hPV, hPeq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    · have hmem : x ∈ ReedSolomon.polynomialAgreementSet domain
          (fun x ↦ O (false, u) x + s * (O (true, u) x - O (false, u) x)) P := by
        rw [ReedSolomon.mem_polynomialAgreementSet, hPV, ← hagree u x hx, fold_apply_eq_line]
      rw [hset, ReedSolomon.mem_commonPolynomialAgreementSet] at hmem
      exact hmem
  choose P₀ P₁ hP₀ hP₁ hVeq hP using hdec
  -- The rows `P₀` and `P₀ + P₁` form a list member of `O` folding to `V`.
  let W : Bool × ρ → ι → F := fun r x ↦
    (P₀ r.2).eval (domain x) + if r.1 then (P₁ r.2).eval (domain x) else 0
  have hcode (P : F[X]) (hP : P.degree < k) :
      (fun x ↦ P.eval (domain x)) ∈ ReedSolomon.code domain k :=
    ReedSolomon.mem_code_iff_eval.mpr ⟨P, hP, fun _ ↦ rfl⟩
  have hWcw : IsInterleavedCodeword (ReedSolomon.code domain k) W := by
    rintro ⟨b, u⟩
    cases b
    · simpa [W] using hcode _ (hP₀ u)
    · convert (ReedSolomon.code domain k).add_mem (hcode _ (hP₀ u)) (hcode _ (hP₁ u)) using 1
      funext x
      simp [W]
  have hWagree : AgreeOn O W S := by
    rintro ⟨b, u⟩ x hx
    cases b
    · simp [W, (hP u x hx).1]
    · simp [W, (hP u x hx).1, (hP u x hx).2]
  refine ⟨W, (mem_iList _ A O W).mpr ⟨hWcw, S, hS, hWagree⟩, ?_⟩
  funext u x
  simp only [fold, W, hVeq u x, ite_false, ite_true, Bool.false_eq_true]
  ring

omit [Fintype F] in
/-- **ArkLib's Johnson line count as uniform exact line agreement.** For the Reed-Solomon code of
dimension `D + 1` on `n` points with `1 ≤ D ≤ n - 2`, `0 < η` and `a = √(D / n) + η ≤ 1`, every
pair of words has at most `johnsonExceptionCount n D ⌈a n⌉₊ η` exceptional challenges at the
threshold `⌈a n⌉₊`. The counting core of `ReedSolomon.mcaError_affineLine_johnson_le`. -/
theorem lineExactAgreementBound_johnson [DecidableEq F] {n D : ℕ} {η : ℝ}
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (hη : 0 < η)
    (ha : johnsonAgreement n D η ≤ 1) :
    ReedSolomon.LineExactAgreementBound domain (D + 1) ⌈johnsonAgreement n D η * n⌉₊
      (johnsonExceptionCount n D ⌈johnsonAgreement n D η * n⌉₊ η) := by
  classical
  intro f g
  obtain ⟨ex, hcard, hgood⟩ :=
    ReedSolomon.exists_johnson_line_exactCorrelatedPair_ceil domain f g hD hDn hη ha
  refine ⟨ex, hcard, fun z hz P hP hagree ↦ ?_⟩
  obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP (by convert hagree)
  refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
  · simpa [ReedSolomon.correlatedPairSpecialization] using heq
  · ext i
    have hi := congrArg (i ∈ ·) hset
    simp only [ReedSolomon.mem_polynomialAgreementSet, ReedSolomon.mem_commonPolynomialAgreementSet,
      eq_iff_iff] at hi ⊢
    simpa using hi

/-- **The fold-list lemma up to the Johnson bound** (Annex B, `lem:fold-list` with
`thm:mca-johnson`, count form). For the Reed-Solomon code of dimension `D + 1` on `n` points with
`1 ≤ D ≤ n - 2`, `0 < η` and `a = √(D / n) + η ≤ 1`, i.e. at radius `γ = 1 - √ρ₋ - η` with
`ρ₋ = D / n`, every interleaved word with rows `Bool × ρ` has at most
`|ρ| ⌊johnsonExceptionCount n D ⌈a n⌉₊ η⌋₊` challenges `s` with
`Λ(fold s O) ≠ fold s '' Λ(O)` at the threshold `⌈a n⌉₊`. Any characteristic. -/
theorem card_foldBad_le_johnson [DecidableEq F] {n D : ℕ} {η : ℝ} (domain : Fin n ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (hη : 0 < η) (ha : johnsonAgreement n D η ≤ 1)
    (O : Bool × ρ → Fin n → F) :
    (foldBad (ReedSolomon.code domain (D + 1)) ⌈johnsonAgreement n D η * n⌉₊ O).card ≤
      Fintype.card ρ * ⌊johnsonExceptionCount n D ⌈johnsonAgreement n D η * n⌉₊ η⌋₊ :=
  card_foldBad_le_of_lineExact domain (lineExactAgreementBound_johnson domain hD hDn hη ha) O

/-! ### Through the mutual correlated agreement event -/

/-- **The MCA event** for the affine line `u₀ + s u₁` at threshold `A` (Annex B, `thm:mca-johnson`):
on some set of at least `A` coordinates the combination agrees with a codeword while the pair
does not agree with the interleaved code. -/
def McaBad (C : Submodule F (ι → F)) (A : ℕ) (u₀ u₁ : ι → F) (s : F) : Prop :=
  ∃ S : Finset ι, A ≤ S.card ∧ (∃ c ∈ C, ∀ x ∈ S, u₀ x + s * u₁ x = c x) ∧
    ¬ ∃ c₀ ∈ C, ∃ c₁ ∈ C, ∀ x ∈ S, u₀ x = c₀ x ∧ u₁ x = c₁ x

open Classical in
/-- **The fold-list lemma, the Annex's argument** (Annex B, `lem:fold-list`, count form). For a
linear code in which codewords agreeing on `A` coordinates are equal, if every pair of words has
at most `E` challenges with the MCA event at threshold `A`, then every interleaved word with
rows `Bool × ρ` has at most `|ρ| E` challenges with `Λ(fold s O) ≠ fold s '' Λ(O)`. -/
theorem card_foldBad_le_of_mca [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F))
    {A E : ℕ}
    (huniq : ∀ c ∈ C, ∀ c' ∈ C, ∀ S : Finset ι, A ≤ S.card → (∀ x ∈ S, c x = c' x) → c = c')
    (hmca : ∀ u₀ u₁ : ι → F, (univ.filter fun s ↦ McaBad C A u₀ u₁ s).card ≤ E)
    (O : Bool × ρ → ι → F) :
    (foldBad C A O).card ≤ Fintype.card ρ * E := by
  classical
  let ex : ρ → Finset F := fun u ↦
    univ.filter fun s ↦ McaBad C A (O (false, u)) (fun x ↦ O (true, u) x - O (false, u) x) s
  refine (Finset.card_le_card fun s hs ↦ ?_).trans
    ((card_biUnion_le_floor ex (B := E) fun u ↦ by exact_mod_cast hmca _ _).trans (by simp))
  by_contra hsex
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists, ex,
    Finset.mem_filter] at hsex
  refine not_mem_foldBad_of_subset _ A O s (fun V hV ↦ ?_) hs
  obtain ⟨hVcw, S, hS, hagree⟩ := (mem_iList _ A _ V).mp hV
  have hpair : ∀ u, ∃ c₀ ∈ C, ∃ c₁ ∈ C, ∀ x ∈ S,
      O (false, u) x = c₀ x ∧ O (true, u) x - O (false, u) x = c₁ x := by
    intro u
    by_contra hno
    exact hsex u ⟨S, hS, ⟨V u, hVcw u, fun x hx ↦ by
      rw [← fold_apply_eq_line]; exact hagree u x hx⟩, hno⟩
  choose c₀ hc₀ c₁ hc₁ hc using hpair
  let W : Bool × ρ → ι → F := fun r ↦ if r.1 then c₀ r.2 + c₁ r.2 else c₀ r.2
  have hWcw : IsInterleavedCodeword C W := by
    rintro ⟨b, u⟩
    cases b
    · simpa [W] using hc₀ u
    · simpa [W] using C.add_mem (hc₀ u) (hc₁ u)
  have hWagree : AgreeOn O W S := by
    rintro ⟨b, u⟩ x hx
    cases b
    · simp [W, (hc u x hx).1]
    · simp only [W, ite_true, Pi.add_apply, ← (hc u x hx).1, ← (hc u x hx).2]
      ring
  refine ⟨W, (mem_iList _ A O W).mpr ⟨hWcw, S, hS, hWagree⟩, funext fun u ↦ ?_⟩
  refine huniq _ (isInterleavedCodeword_fold C hWcw s u) _ (hVcw u) S hS fun x hx ↦ ?_
  rw [← hagree u x hx]
  exact ((hWagree.fold s) u x hx).symm

end List

/-! ## Many coordinates -/

/-- Pair the rows of a word on the cube `Fin (2 ^ (j + 1))` by their low index bit: row
`(b, i, u)` is row `(2 i + b, u)`, so that folding coordinate `0` is the one-coordinate fold. -/
def pairUp {j : ℕ} {M : Type*} (O : Fin (2 ^ (j + 1)) × ρ → M) : Bool × (Fin (2 ^ j) × ρ) → M :=
  fun r ↦ O (⟨2 * r.2.1.val + (if r.1 then 1 else 0), by
    have := r.2.1.isLt; rw [pow_succ]; split <;> omega⟩, r.2.2)

/-- **The fold by `s : Vector F j`** of an interleaved word whose rows are the cube
`Fin (2 ^ j)` (CompPoly's little-endian table indexing) times `ρ`: entry `(u, x)` is the
multilinear extension at `s` of the column `i ↦ O (i, u) x` (Annex B, `def:interleaved`). -/
def foldMany {j : ℕ} (s : Vector F j) (O : Fin (2 ^ j) × ρ → ι → F) : ρ → ι → F :=
  fun u x ↦ evalMle (Vector.ofFn fun i ↦ O (i, u) x) s

/-- **The eq-weighted sum.** The fold is `Σ_i eq(s, i) O[(i, u), x]`, the weight `eq(s, ·)` being
CompPoly's Lagrange basis `lagrangeBasis s`. -/
theorem foldMany_eq_sum {j : ℕ} (s : Vector F j) (O : Fin (2 ^ j) × ρ → ι → F) (u : ρ) (x : ι) :
    foldMany s O u x = ∑ i : Fin (2 ^ j), (lagrangeBasis s)[i] * O (i, u) x := by
  rw [foldMany, evalMle_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_comm]

/-- Folding no coordinate reads the single row of the cube. -/
theorem foldMany_zero (s : Vector F 0) (O : Fin (2 ^ 0) × ρ → ι → F) (u : ρ) :
    foldMany s O u = O (0, u) := by
  funext x
  simp [foldMany, evalMle_zero]

/-- **Folding one coordinate at a time.** The fold by `s` is the one-coordinate fold at `s.head`
on coordinate `0` (rows paired by `pairUp`), followed by the fold by `s.tail`. -/
theorem foldMany_succ {j : ℕ} (s : Vector F (j + 1)) (O : Fin (2 ^ (j + 1)) × ρ → ι → F) :
    foldMany s O = foldMany s.tail (fold s.head (pairUp O)) := by
  funext u x
  simp only [foldMany, evalMle]
  rw [evalMleValues]
  congr 1
  ext i hi
  simp [evalMleStep, fold, pairUp]

/-- A folded row is a linear combination of the rows. -/
theorem foldMany_apply_eq_sum_smul {j : ℕ} (s : Vector F j) (O : Fin (2 ^ j) × ρ → ι → F)
    (u : ρ) : foldMany s O u = ∑ i : Fin (2 ^ j), (lagrangeBasis s)[i] • O (i, u) := by
  funext x
  rw [foldMany_eq_sum, Finset.sum_apply]
  rfl

/-- Folding by many coordinates keeps interleaved codewords of a linear code. -/
theorem isInterleavedCodeword_foldMany (C : Submodule F (ι → F)) {j : ℕ}
    {U : Fin (2 ^ j) × ρ → ι → F} (hU : IsInterleavedCodeword C U) (s : Vector F j) :
    IsInterleavedCodeword C (foldMany s U) := fun u ↦ by
  rw [foldMany_apply_eq_sum_smul]
  exact C.sum_mem fun i _ ↦ C.smul_mem _ (hU _)

/-- Folding by many coordinates keeps agreement on a set. -/
theorem AgreeOn.foldMany {j : ℕ} {O U : Fin (2 ^ j) × ρ → ι → F} {S : Finset ι}
    (h : AgreeOn O U S) (s : Vector F j) :
    AgreeOn (Whir.foldMany s O) (Whir.foldMany s U) S := fun u x hx ↦ by
  rw [foldMany_eq_sum, foldMany_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h (i, u) x hx]

/-- **Folding commutes with decoding, many coordinates** (Annex B, `fact:fold-decode`). -/
theorem foldMany_encoder (enc : (σ → F) →ₗ[F] (ι → F)) {j : ℕ} (s : Vector F j)
    (g : Fin (2 ^ j) × ρ → σ → F) :
    foldMany s (fun r ↦ enc (g r)) = fun u ↦ enc (foldMany s g u) := by
  funext u
  rw [foldMany_apply_eq_sum_smul, foldMany_apply_eq_sum_smul, map_sum]
  simp_rw [map_smul]

/-- The fold by many coordinates of a list member is in the list of the fold. -/
theorem foldMany_mem_iList [Fintype F] [Fintype ι] [Fintype ρ] (C : Submodule F (ι → F))
    {A j : ℕ} {O U : Fin (2 ^ j) × ρ → ι → F} (hU : U ∈ iList C A O) (s : Vector F j) :
    foldMany s U ∈ iList C A (foldMany s O) := by
  rw [mem_iList] at hU ⊢
  obtain ⟨hcw, S, hS, hagree⟩ := hU
  exact ⟨isInterleavedCodeword_foldMany C hcw s, S, hS, hagree.foldMany s⟩

end
end LeanVM.Protocol.Whir
