/-
  LeanVM.Protocol.Whir.Sound.State

  The meaning of the WHIR verifier's running state: the running weight it owes at the terminal
  point, the effect of a fold round and of gluing a level's claims, the lane oracles the
  committed words define, and the verifier's fold of an opened row as the affine fold of the
  oracle.
-/

module

public import LeanVM.Protocol.Whir.Sound.FoldRound
public import LeanVM.Protocol.Whir.Sound.Weights

/-!
# The running state of `verify_whir`

`LeanVM.Protocol.Verifier.WhirState` (`verify_whir`'s locals, `crates/verifier/src/whir.rs:223-343`)
holds the running claim, every fold round's `α`, and the glued claims, whose weights are only
evaluated at the terminal point. This module reads it as a weighted claim:

* `runW w ℓ₀ s x`: the running weight at the point `x` of the remaining variables, the terminal
  check's `weight` at `x = tail`: the opening weight `w` at the rotated point
  `(αs ++ x)[ℓ₀:] ++ (αs ++ x)[:ℓ₀]`, plus each glued claim's scalar times its weight at
  `αs[fold_start:] ++ x`. `runW_fold`: a round's `α` binds the first remaining variable;
  `isMultiaffine_runW`: the running weight is multiaffine in the remaining variables.
* `glueLevel_eq`: gluing a level's claims adds `λ` times the out-of-domain value and `λ²` times
  the query batch to the claim, and the matching weights to the glued claims
  (`runW_glue`).
* `laneO i cs`: the lane oracle of commitment `i`: lane `j` of column `v` is entry `j` of the
  reversed leaf (level `0`, `row.reverse.map ofK`) or of the leaf regrouped into `E`, two limbs
  per lane (deeper levels, `ext_row`).
* `foldsA dom rounds O`: the oracle folded by the level's rounds with the affine combiner, the
  rounds' lanes `(2m, 2m + 1)`; `rowsOf_foldsA_concat`: on lanes split at the first variable it is
  `foldQ`, and `foldRow_eq`: the verifier's `foldRow` of an opened row is the folded oracle at the
  row's column.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## The running weight -/

/-- The running weight of the state `s` at the point `x` of the remaining variables. -/
def runW (w : List E → E) (ℓ₀ : ℕ) (s : WhirState) (x : List E) : E :=
  s.glued.foldl (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (s.alphas.drop claim.foldStart ++ x))
    (w (rotL ℓ₀ (s.alphas ++ x)))

/-- `foldl` of a sum is the initial value plus the sum. -/
theorem foldl_add_map {γ : Type*} (f : γ → E) (a : E) (l : List γ) :
    l.foldl (fun acc c ↦ acc + f c) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem runW_eq (w : List E → E) (ℓ₀ : ℕ) (s : WhirState) (x : List E) :
    runW w ℓ₀ s x = w (rotL ℓ₀ (s.alphas ++ x)) +
      (s.glued.map fun c ↦ c.scalar * c.weightAt (s.alphas.drop c.foldStart ++ x)).sum :=
  foldl_add_map _ _ _

/-- Every glued claim started at or before the current fold and owes a multiaffine weight on the
variables left when it was glued. -/
def GluedOK (μ : ℕ) (s : WhirState) : Prop :=
  ∀ c ∈ s.glued, c.foldStart ≤ s.alphas.length ∧ IsMultiaffine (μ - c.foldStart) c.weightAt

/-- **A fold round's `α` binds the first remaining variable.** -/
theorem runW_fold (w : List E → E) (ℓ₀ : ℕ) (s : WhirState) (c γ : E)
    (hg : ∀ g ∈ s.glued, g.foldStart ≤ s.alphas.length) (x : List E) :
    runW w ℓ₀ { s with claim := c, alphas := s.alphas ++ [γ] } x = runW w ℓ₀ s (γ :: x) := by
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
    (hℓ₀ : ℓ₀ ≤ μ) (s : WhirState) (hs : s.alphas.length ≤ μ) (hg : GluedOK μ s) :
    IsMultiaffine (μ - s.alphas.length) (runW w ℓ₀ s) := by
  have hrot : IsMultiaffine (s.alphas.length + (μ - s.alphas.length))
      fun l ↦ w (rotL ℓ₀ l) := by
    rw [Nat.add_sub_cancel' hs]; exact isMultiaffine_rotL hw hℓ₀
  have h1 := hrot.append s.alphas rfl
  have key : ∀ c ∈ s.glued, IsMultiaffine (μ - s.alphas.length)
      (fun x ↦ c.scalar * c.weightAt (s.alphas.drop c.foldStart ++ x)) := by
    intro c hc
    obtain ⟨hfs, hma⟩ := hg c hc
    have heq : (s.alphas.drop c.foldStart).length + (μ - s.alphas.length) = μ - c.foldStart := by
      rw [List.length_drop]; omega
    have h' : IsMultiaffine ((s.alphas.drop c.foldStart).length + (μ - s.alphas.length))
        c.weightAt := by
      rw [heq]; exact hma
    exact (h'.append _ rfl).const_mul c.scalar
  have h2 : IsMultiaffine (μ - s.alphas.length) fun x ↦
      (s.glued.map fun c ↦ c.scalar * c.weightAt (s.alphas.drop c.foldStart ++ x)).sum :=
    isMultiaffine_listSum_mem s.glued
      (fun c x ↦ c.scalar * c.weightAt (s.alphas.drop c.foldStart ++ x)) key
  have := h1.add h2
  intro l hl k hk X
  simp only [runW_eq]
  exact this l hl k hk X

/-! ## Gluing -/

/-- **Gluing a level's claims** (`glueLevel`): the out-of-domain claim with `λ`, the query
batch with `λ²`, both at the current fold. -/
theorem glueLevel_eq (s : WhirState) (lam : E) (mu : ℕ) (z : List E) (y : E)
    (queries : List ℕ) (queryWeights : List E) (batched : E) :
    glueLevel s lam mu z y queries queryWeights batched =
      { claim := s.claim + lam * y + lam * lam * batched
        alphas := s.alphas
        glued := s.glued ++ [⟨lam, s.alphas.length, fun x ↦ eqEval z x⟩,
          ⟨lam * lam, s.alphas.length, Verifier.inducedWeight mu queries queryWeights⟩] } :=
  rfl

/-- Glued claims at the current fold add their weights. -/
theorem runW_glue (w : List E → E) (ℓ₀ : ℕ) (s : WhirState) (new : List GluedClaim) (c : E)
    (hnew : ∀ g ∈ new, g.foldStart = s.alphas.length) (x : List E) :
    runW w ℓ₀ { s with claim := c, glued := s.glued ++ new } x =
      runW w ℓ₀ s x + (new.map fun g ↦ g.scalar * g.weightAt x).sum := by
  rw [runW_eq, runW_eq]
  dsimp only
  rw [List.map_append, List.sum_append, add_assoc]
  refine congrArg (_ + ·) (congrArg (_ + ·) (congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)))
  rw [hnew g hg, List.drop_length, List.nil_append]

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

/-- The width of commitment `i`'s leaves for `2^ℓ` lanes: one word per lane at level `0`, two
deeper. -/
def wdOf (i ℓ : ℕ) : ℕ := if i = 0 then 2 ^ ℓ else 2 * 2 ^ ℓ

theorem length_extRow (m : ℕ) : ∀ (l : List K), l.length = 2 * m → (extRow l).length = m
  | c0 :: c1 :: rest, h => by
    rw [extRow, List.length_cons]
    cases m with
    | zero => simp at h
    | succ m => rw [length_extRow m rest (by simp at h; omega)]
  | [c0], h => by simp at h; omega
  | [], h => by simp at h; subst h; rfl

/-- The lanes of a well-shaped leaf: `2^ℓ` of them. -/
theorem length_lanesOf {i ℓ : ℕ} (row : List K) (h : row.length = wdOf i ℓ) :
    (lanesOf i row).length = 2 ^ ℓ := by
  unfold lanesOf
  unfold wdOf at h
  split_ifs at h ⊢ with hi
  · simp [h]
  · exact length_extRow _ row h

/-- The word of a commitment that is present. -/
theorem wordOf_eq {cs : List (ℕ × ℕ × Word)} {i ht wd : ℕ} {W : Word}
    (hc : cs[i]? = some (ht, wd, W)) : wordOf cs i = W := by
  simp [wordOf, hc]

/-- Appending a commitment keeps the earlier ones' words. -/
theorem wordOf_append (cs : List (ℕ × ℕ × Word)) (x : ℕ × ℕ × Word) {i : ℕ} (h : i < cs.length) :
    wordOf (cs ++ [x]) i = wordOf cs i := by
  simp [wordOf, List.getElem?_append_left h]

theorem laneO_append (cs : List (ℕ × ℕ × Word)) (x : ℕ × ℕ × Word) {i : ℕ} (h : i < cs.length)
    (n : ℕ) : laneO i (cs ++ [x]) n = laneO i cs n := by
  funext j v
  simp [laneO, wordOf_append cs x h]

/-! ## The affine fold of an oracle -/

/-- One affine fold of lanes at a column whose domain point is `y`: lane `k` of the fold is
`G + (α + β y) F`, `F` and `G` the lanes `2k` and `2k + 1`. -/
def foldC (y : E) (r : FoldRound) (o : ℕ → E) : ℕ → E :=
  fun k ↦ o (2 * k + 1) + (r.alpha + r.beta * y) * o (2 * k)

/-- The folds of a level at one column, first round first. -/
def foldsC (y : E) (rounds : List FoldRound) (o : ℕ → E) : ℕ → E :=
  rounds.foldl (fun o r ↦ foldC y r o) o

/-- **The oracle folded by the level's rounds.** -/
def foldsA {n : ℕ} (dom : Fin n ↪ E) (rounds : List FoldRound) (O : ℕ → Fin n → E) :
    ℕ → Fin n → E :=
  fun k v ↦ foldsC (dom v) rounds (fun j ↦ O j v) k

/-- The last round of the folds is `foldQ` on the lanes split at their first variable. -/
theorem rowsOf_foldsA_concat {n m : ℕ} (dom : Fin n ↪ E) (rounds : List FoldRound) (r : FoldRound)
    (O : ℕ → Fin n → E) :
    rowsOf m (foldsA dom (rounds ++ [r]) O) =
      foldQ dom r.alpha r.beta (rowsOf (m + 1) (foldsA dom rounds O)) := by
  funext u x
  simp only [rowsOf, foldsA, foldsC, List.foldl_append, List.foldl_cons, List.foldl_nil, foldC,
    foldQ, bitsToNat_cons, Bool.toNat_false, Bool.toNat_true]
  ring_nf

/-- With no round, the oracle itself. -/
theorem foldsA_nil {n : ℕ} (dom : Fin n ↪ E) (O : ℕ → Fin n → E) : foldsA dom [] O = O := rfl

/-- The lanes of a list, zero past its end. -/
def laneFn (vals : List E) : ℕ → E := fun j ↦ vals.getD j 0

theorem length_foldLanes (x : K) (r : FoldRound) :
    ∀ vals : List E, (foldLanes x r vals).length = vals.length / 2
  | [] => rfl
  | [_] => by simp [foldLanes]
  | f :: g :: rest => by
    rw [foldLanes, List.length_cons, length_foldLanes x r rest]
    simp only [List.length_cons]
    omega

/-- One `foldLanes` is `foldC` on an even list. -/
theorem laneFn_foldLanes (x : K) (r : FoldRound) :
    ∀ vals : List E, Even vals.length →
      laneFn (foldLanes x r vals) = foldC (ofK x) r (laneFn vals)
  | [], _ => by funext k; simp [laneFn, foldLanes, foldC]
  | [_], h => by simp at h
  | f :: g :: rest, h => by
    have hr : Even rest.length := by
      simpa [Nat.even_add_one, parity_simps] using h
    have ih := laneFn_foldLanes x r rest hr
    funext k
    cases k with
    | zero => simp [laneFn, foldLanes, foldC]
    | succ k =>
      have := congrFun ih k
      simp only [laneFn, foldLanes, List.getD_cons_succ] at this ⊢
      rw [this]
      simp only [foldC, laneFn, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.getD_cons_succ]

/-- **The verifier's fold of an opened row**: on `2^|rounds|` lanes, `foldRow` is the folds at
the row's point, read at lane `0`. -/
theorem foldRow_eq (x : K) : ∀ (rounds : List FoldRound) (vals : List E),
    vals.length = 2 ^ rounds.length →
      foldRow vals x rounds = foldsC (ofK x) rounds (laneFn vals) 0
  | [], vals, _ => by
    simp only [foldRow, List.foldl_nil, foldsC, laneFn]
    cases vals <;> rfl
  | r :: rounds, vals, h => by
    have hev : Even vals.length := ⟨2 ^ rounds.length, by rw [h, List.length_cons, pow_succ]; ring⟩
    have hlen : (foldLanes x r vals).length = 2 ^ rounds.length := by
      rw [length_foldLanes, h, List.length_cons, pow_succ, Nat.mul_div_cancel _ two_pos]
    have := foldRow_eq x rounds (foldLanes x r vals) hlen
    simp only [foldRow, List.foldl_cons] at this ⊢
    rw [this, laneFn_foldLanes x r vals hev]
    rfl

end
end LeanVM.Protocol.Whir.Sound
