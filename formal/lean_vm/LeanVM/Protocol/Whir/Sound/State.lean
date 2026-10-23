/-
  LeanVM.Protocol.Whir.Sound.State

  The meaning of the WHIR verifier's running state: the running weight it owes at the terminal
  point (`runW`), the shape of its round polynomial, the effect of a fold and of gluing a level's
  claims, and the lane oracles the committed words define.
-/

module

public import LeanVM.Protocol.Whir.Sound.Escape
public import LeanVM.Protocol.Whir.Sound.Prob

/-!
# The running state of `verify_whir`

`LeanVM.Protocol.Verifier.WhirState` (`verify_whir`'s locals `running_target`, `running_quad`,
`folds`, `glued`, leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`python-verifier/verifier.py:1008-1086`) holds the running claim as a target value and a list of
glued claims whose weights are only evaluated at the terminal point. This module reads it as a
weighted claim:

* `runW w ℓ₀ s x`: the running weight at the point `x` of the remaining variables. It is literally
  the terminal check's `weight` at `x = tail_folds`: the opening weight `w` at the rotated point
  `(folds ++ x)[ℓ₀:] ++ (folds ++ x)[:ℓ₀]`, plus each glued claim's scalar times its weight at
  `folds[fold_start:] ++ x`.
* `runW_fold`: a fold challenge `c` binds the first remaining variable,
  `runW (s with folds ++ [c]) x = runW s (c :: x)`; `isMultiaffine_runW`: the running weight is
  multiaffine in the remaining variables.
* `QuadOK quad σ`: the round polynomial has three coefficients and `q(0) + q(1) = σ`, which
  `sumcheckRoundPoly 3 σ none` guarantees by construction (`quadOK_roundPoly`).
* `glue`: gluing claims adds their weights with the powers of `λ` to the running weight and their
  values to the target, and keeps `QuadOK` (`glue_two`, `glue_one`).
* `laneO i cs`: the lane oracle of commitment `i` of the commitments `cs`: lane `j` of column `v`
  is entry `j` of the reversed leaf (level `0`, `row.reverse.map ofK`) or of the leaf regrouped
  into `E` (deeper levels, `_ext_row`). `enforcedSum_eq`: the verifier's `_enforced_sum` of the
  opened rows is `Σ_q λ^q c[x_q]` with `c` the oracle folded by the level's challenges.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## The running weight -/

/-- The running weight of the state `s` at the point `x` of the remaining variables. -/
def runW (w : List E → E) (ℓ₀ : ℕ) (s : WhirState) (x : List E) : E :=
  s.glued.foldl (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ x))
    (w (rotL ℓ₀ (s.folds ++ x)))

/-- `foldl` of a sum is the initial value plus the sum. -/
theorem foldl_add_map {γ : Type*} (f : γ → E) (a : E) (l : List γ) :
    l.foldl (fun acc c ↦ acc + f c) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem runW_eq (w : List E → E) (ℓ₀ : ℕ) (s : WhirState) (x : List E) :
    runW w ℓ₀ s x = w (rotL ℓ₀ (s.folds ++ x)) +
      (s.glued.map fun c ↦ c.scalar * c.weightAt (s.folds.drop c.foldStart ++ x)).sum :=
  foldl_add_map _ _ _

/-- Every glued claim started at or before the current fold and owes a multiaffine weight on the
variables left when it was glued. -/
def GluedOK (μ : ℕ) (s : WhirState) : Prop :=
  ∀ c ∈ s.glued, c.foldStart ≤ s.folds.length ∧ IsMultiaffine (μ - c.foldStart) c.weightAt

/-- **A fold binds the first remaining variable.** -/
theorem runW_fold (w : List E → E) (ℓ₀ : ℕ) (s : WhirState) (c t : E) (q : List E)
    (hg : ∀ g ∈ s.glued, g.foldStart ≤ s.folds.length) (x : List E) :
    runW w ℓ₀ { s with target := t, quad := q, folds := s.folds ++ [c] } x =
      runW w ℓ₀ s (c :: x) := by
  rw [runW_eq, runW_eq]
  dsimp only
  rw [List.append_assoc, List.singleton_append]
  refine congrArg (_ + ·) (congrArg List.sum (List.map_congr_left fun g hgm ↦ ?_))
  rw [List.drop_append_of_le_length (hg g hgm), List.append_assoc, List.singleton_append]

/-- A list sum of multiaffine weights is multiaffine. -/
theorem isMultiaffine_listSum_mem {n : ℕ} {γ : Type*} (xs : List γ) (F : γ → List E → E)
    (hF : ∀ a ∈ xs, IsMultiaffine n (F a)) :
    IsMultiaffine n fun l ↦ (xs.map fun a ↦ F a l).sum := by
  induction xs with
  | nil => simpa using (IsMultiaffine.zero (n := n))
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF a (List.mem_cons_self ..)).add (ih fun b hb ↦ hF b (List.mem_cons_of_mem _ hb))

/-- **The running weight is multiaffine** in the remaining variables. -/
theorem isMultiaffine_runW {μ : ℕ} {w : List E → E} (hw : IsMultiaffine μ w) {ℓ₀ : ℕ}
    (hℓ₀ : ℓ₀ ≤ μ) (s : WhirState) (hs : s.folds.length ≤ μ) (hg : GluedOK μ s) :
    IsMultiaffine (μ - s.folds.length) (runW w ℓ₀ s) := by
  have hrot : IsMultiaffine (s.folds.length + (μ - s.folds.length))
      fun l ↦ w (rotL ℓ₀ l) := by
    rw [Nat.add_sub_cancel' hs]; exact isMultiaffine_rotL hw hℓ₀
  have h1 := hrot.append s.folds rfl
  have key : ∀ c ∈ s.glued, IsMultiaffine (μ - s.folds.length)
      (fun x ↦ c.scalar * c.weightAt (s.folds.drop c.foldStart ++ x)) := by
    intro c hc
    obtain ⟨hfs, hma⟩ := hg c hc
    have heq : (s.folds.drop c.foldStart).length + (μ - s.folds.length) = μ - c.foldStart := by
      rw [List.length_drop]; omega
    have h' : IsMultiaffine ((s.folds.drop c.foldStart).length + (μ - s.folds.length))
        c.weightAt := by
      rw [heq]; exact hma
    exact (h'.append _ rfl).const_mul c.scalar
  have h2 : IsMultiaffine (μ - s.folds.length) fun x ↦
      (s.glued.map fun c ↦ c.scalar * c.weightAt (s.folds.drop c.foldStart ++ x)).sum :=
    isMultiaffine_listSum_mem s.glued
      (fun c x ↦ c.scalar * c.weightAt (s.folds.drop c.foldStart ++ x)) key
  have := h1.add h2
  intro l hl k hk X
  simp only [runW_eq]
  exact this l hl k hk X

/-! ## Round polynomials -/

/-- The round polynomial has three coefficients and `q(0) + q(1) = σ`. -/
def QuadOK (quad : List E) (σ : E) : Prop :=
  ∃ c₀ c₁ c₂, quad = [c₀, c₁, c₂] ∧ polyEval quad 0 + polyEval quad 1 = σ

/-- The quadratic `sumcheckRoundPoly 3 σ none` builds from `c₀` and `[c₂]` has `q(0)+q(1) = σ`. -/
theorem quadOK_roundPoly (σ c₀ c₂ : E) :
    QuadOK (c₀ :: (σ + sumE [c₂]) :: [c₂]) σ := by
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [polyEval_three, sumE, List.foldl_cons, List.foldl_nil, zero_add]
  ring_nf
  rw [show (2 : E) = 0 from CharTwo.two_eq_zero]
  ring

/-- The sum of two quadratics with a scalar keeps the coefficient form. -/
theorem quadOK_zipWith {q i : List E} {σ v : E} (hq : QuadOK q σ) (hi : QuadOK i v) (c : E) :
    QuadOK (List.zipWith (fun a b ↦ a + c * b) q i) (σ + c * v) := by
  obtain ⟨a₀, a₁, a₂, rfl, ha⟩ := hq
  obtain ⟨b₀, b₁, b₂, rfl, hb⟩ := hi
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, polyEval_three] at ha hb ⊢
  rw [← ha, ← hb]
  ring

/-! ## Gluing -/

/-- Gluing two claims (a level with a next commitment): the out-of-domain claim with `λ`, the
consistency claims with `λ²`. -/
theorem glue_two (lam : E) (s : WhirState) (y e : E) (hy he : List E) (wy we : List E → E) :
    glue lam s [(y, hy, wy), (e, he, we)] =
      { target := s.target + 1 * lam * y + 1 * lam * lam * e
        quad := List.zipWith (fun q i ↦ q + 1 * lam * lam * i)
          (List.zipWith (fun q i ↦ q + 1 * lam * i) s.quad hy) he
        folds := s.folds
        glued := s.glued ++
          [⟨1 * lam, s.folds.length, wy⟩, ⟨1 * lam * lam, s.folds.length, we⟩] } := by
  simp [glue]

/-- Gluing one claim (the final level): the consistency claims with `λ`. -/
theorem glue_one (lam : E) (s : WhirState) (e : E) (he : List E) (we : List E → E) :
    glue lam s [(e, he, we)] =
      { target := s.target + 1 * lam * e
        quad := List.zipWith (fun q i ↦ q + 1 * lam * i) s.quad he
        folds := s.folds
        glued := s.glued ++ [⟨1 * lam, s.folds.length, we⟩] } := by
  simp [glue]

/-- Glued claims at the current fold add their weights. -/
theorem runW_glue (w : List E → E) (ℓ₀ : ℕ) (s : WhirState) (new : List GluedClaim)
    (hnew : ∀ c ∈ new, c.foldStart = s.folds.length) (x : List E) :
    runW w ℓ₀ { s with glued := s.glued ++ new } x =
      runW w ℓ₀ s x + (new.map fun c ↦ c.scalar * c.weightAt x).sum := by
  rw [runW_eq, runW_eq]
  dsimp only
  rw [List.map_append, List.sum_append, add_assoc]
  refine congrArg (_ + ·) (congrArg (_ + ·) (congrArg List.sum (List.map_congr_left fun c hc ↦ ?_)))
  rw [hnew c hc, List.drop_length, List.nil_append]

/-! ## Lane oracles of committed words -/

/-- The word of commitment `i` (the empty word if there is none). -/
def wordOf (cs : List (ℕ × ℕ × Word)) (i : ℕ) : Word :=
  (cs[i]?.map fun c ↦ c.2.2).getD fun _ ↦ []

/-- The lanes of a leaf: reversed at level `0`, regrouped into `E` deeper. -/
def lanesOf (i : ℕ) (row : List K) : List E :=
  if i = 0 then row.reverse.map ofK else extRow row

/-- **The lane oracle of commitment `i`**: lane `j` of column `v`. -/
def laneO (i : ℕ) (cs : List (ℕ × ℕ × Word)) (n : ℕ) : ℕ → Fin n → E :=
  fun j v ↦ (lanesOf i (wordOf cs i v)).getD j 0

theorem length_extRow (m : ℕ) : ∀ (l : List K), l.length = 3 * m → (extRow l).length = m
  | c0 :: c1 :: c2 :: rest, h => by
    rw [extRow, List.length_cons]
    cases m with
    | zero => simp at h
    | succ m => rw [length_extRow m rest (by simp at h; omega)]
  | [c0, c1], h => by simp at h; omega
  | [c0], h => by simp at h; omega
  | [], h => by simp at h; subst h; rfl

/-- The lanes of a well-shaped leaf: `2^ℓ` of them. -/
theorem length_lanesOf {i ℓ : ℕ} (row : List K)
    (h : row.length = if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ) : (lanesOf i row).length = 2 ^ ℓ := by
  unfold lanesOf
  split_ifs at h ⊢ with hi
  · simp [h]
  · exact length_extRow _ row h

/-- The rows the history's `i`-th commitment holds at in-range positions. -/
theorem answer_eq {h : List Ev} {i ht wd : ℕ} {W : Word}
    (hc : (commits h)[i]? = some (ht, wd, W)) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < 2 ^ ht) :
    answer h i qs = some (qs.map W) := by
  simp only [answer, hc, Option.map_some, Option.some.injEq]
  exact List.map_congr_left fun q hq ↦ by rw [Nat.mod_eq_of_lt (hqs q hq)]

/-- The word of a commitment that is present. -/
theorem wordOf_eq {cs : List (ℕ × ℕ × Word)} {i ht wd : ℕ} {W : Word}
    (hc : cs[i]? = some (ht, wd, W)) : wordOf cs i = W := by
  simp [wordOf, hc]

/-- **The enforced sum** of the opened rows is `Σ_q λ^q c[x_q]`, `c` the lane oracle folded by
the level's challenges. -/
theorem enforcedSum_eq (i : ℕ) (cs : List (ℕ × ℕ × Word)) {n ℓ : ℕ} (lf : List E)
    (hlf : lf.length = ℓ) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < n) (lam : E)
    (hshape : ∀ q ∈ qs, (wordOf cs i q).length = if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ) :
    enforcedSum ((qs.map (wordOf cs i)).map (lanesOf i)) lf (powers lam qs.length) =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) *
        wordAt (fun v : Fin n ↦ foldsN lf (laneO i cs n) 0 v) qs[k] := by
  rw [← sum_zip_powers]
  unfold enforcedSum
  rw [List.map_map]
  simp only
  have hzip : ∀ (ws : List E), ws.length = qs.length →
      (List.zip ws (qs.map (lanesOf i ∘ wordOf cs i))).foldl
          (fun total (wr : E × List E) ↦ total + wr.1 * dot wr.2 (eqKernel lf)) 0 =
        ((ws.zip qs).map fun wq ↦ wq.1 *
          wordAt (fun v : Fin n ↦ foldsN lf (laneO i cs n) 0 v) wq.2).sum := by
    intro ws hws
    rw [foldl_add_map (fun wr : E × List E ↦ wr.1 * dot wr.2 (eqKernel lf))]
    rw [zero_add, List.zip_map_right, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun wq hwq ↦ ?_)
    have hq := (List.of_mem_zip hwq).2
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    congr 1
    rw [dot_eqKernel _ _ (by rw [hlf]; exact length_lanesOf _ (hshape _ hq))]
    simp only [wordAt, hqs _ hq, ↓reduceDIte]
    rw [foldsN_apply lf (laneO i cs n)]
    rfl
  exact hzip _ (length_powers lam qs.length)

end
end LeanVM.Protocol.Whir.Sound
