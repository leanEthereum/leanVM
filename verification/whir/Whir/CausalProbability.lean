import Whir.CausalRefinement
import Mathlib.Data.Fintype.BigOperators

/-! Exact finite-coordinate disintegration of the production tape. OOD points and
query squeezes together with lambda are indivisible samples. No validity test or
prover-dependent rejection occurs in this factorization. -/
namespace Whir.CausalProbability
open Concrete Protocol CausalGame

noncomputable local instance {c : Config} : DecidableEq (Tape c) := Classical.decEq _

inductive Coordinate (c : Config) where
  | initial
  | fold (i : Fin c.folds.size) (j : Fin c.folds[i.val]!)
  | ood (i : Fin c.folds.size) (j : Fin (oodCount c i.val))
  | query (i : Fin c.folds.size)
  | tail (j : Fin (c.logN - c.folds.toList.sum))
  deriving DecidableEq, Fintype

abbrev Sample {c : Config} : Coordinate c → Type
  | .initial => E
  | .fold _ _ => E
  | .ood i _ => Fin (remaining c i.val) → E
  | .query i => (Fin (queryChunks c i.val) → E) × E
  | .tail _ => E

noncomputable instance {c : Config} (q : Coordinate c) : Fintype (Sample q) := by
  cases q <;> unfold Sample <;> infer_instance

instance {c : Config} (q : Coordinate c) : Zero (Sample q) := by
  cases q <;> unfold Sample <;> infer_instance

instance {c : Config} (q : Coordinate c) : Nonempty (Sample q) := ⟨0⟩

def get {c : Config} (q : Coordinate c) (t : Tape c) : Sample q :=
  match q with
  | .initial => t.1
  | .fold i j => (t.2.1 i).1 j
  | .ood i j => (t.2.1 i).2.1 j
  | .query i => (t.2.1 i).2.2
  | .tail j => t.2.2 j

/-- Regrouping only: the underlying tape values are not transformed. -/
def coordinates (c : Config) : Tape c ≃ (∀ q : Coordinate c, Sample q) where
  toFun t q := get q t
  invFun f := ⟨f .initial, (fun i => ⟨(fun j => f (.fold i j)),
    (fun j => f (.ood i j)), f (.query i)⟩), (fun j => f (.tail j))⟩
  left_inv t := rfl
  right_inv f := by funext q; cases q <;> rfl

def set {c : Config} (q : Coordinate c) (t : Tape c) (x : Sample q) : Tape c :=
  (coordinates c).symm (Function.update (coordinates c t) q x)

@[simp] theorem get_set {c : Config} (q : Coordinate c) (t : Tape c) (x : Sample q) :
    get q (set q t x) = x := by
  classical
  change (coordinates c (set q t x)) q = x
  simp [set]

@[simp] theorem get_set_ne {c : Config} (q r : Coordinate c) (t : Tape c)
    (x : Sample q) (h : r ≠ q) : get r (set q t x) = get r t := by
  classical
  change (coordinates c (set q t x)) r = (coordinates c t) r
  simp [set, h]

@[simp] theorem set_get {c : Config} (q : Coordinate c) (t : Tape c) :
    set q t (get q t) = t := by
  classical
  simp [set, get, coordinates, Function.update_eq_self]

@[simp] theorem set_set {c : Config} (q : Coordinate c) (t : Tape c)
    (x y : Sample q) : set q (set q t x) y = set q t y := by
  classical
  simp [set, Function.update_idem]

abbrev Rest {c : Config} (q : Coordinate c) := {t : Tape c // get q t = 0}

noncomputable instance {c : Config} (q : Coordinate c) : Fintype (Rest q) := by
  classical
  unfold Rest
  infer_instance

instance {c : Config} (q : Coordinate c) : Nonempty (Rest q) :=
  ⟨⟨set q (0, (fun _ => (0, 0, 0, 0)), 0) 0, get_set _ _ _⟩⟩

/-- Exact product decomposition, with inverse given by coordinate replacement. -/
noncomputable def split {c : Config} (q : Coordinate c) : Tape c ≃ Rest q × Sample q where
  toFun t := (⟨set q t 0, get_set _ _ _⟩, get q t)
  invFun p := set q p.1.val p.2
  left_inv t := by simp
  right_inv p := by
    rcases p with ⟨⟨t, ht⟩, x⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [← ht]
    · simp

private theorem card_equiv_fibers {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B × C) (p : A → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      ∑ b : B, (Finset.univ.filter fun x : C => p (e.symm (b, x))).card := by
  classical
  have h := Fintype.sum_equiv e
    (fun a => if p a then (1 : ℕ) else 0)
    (fun bc => if p (e.symm bc) then (1 : ℕ) else 0)
    (by intro a; simp)
  rw [Fintype.sum_prod_type] at h
  simpa only [Finset.sum_boole, Nat.cast_id] using h

/-- Counting all fibers is an identity, including for history-dependent events. -/
theorem card_event {c : Config} (q : Coordinate c) (event : Tape c → Prop)
    [DecidablePred event] :
    (Finset.univ.filter event).card =
      ∑ rest : Rest q, (Finset.univ.filter fun x : Sample q =>
        event (set q rest.val x)).card := by
  exact card_equiv_fibers (split q) event

/-- Exact averaging of conditional uniform probabilities, with no independence
hypothesis on the events themselves. -/
theorem uniformProb_event {c : Config} (q : Coordinate c) (event : Tape c → Prop)
    [DecidablePred event] :
    Soundness.uniformProb (Finset.univ.filter event) =
      (∑ rest : Rest q, Soundness.uniformProb
        (Finset.univ.filter fun x : Sample q => event (set q rest.val x))) /
      Fintype.card (Rest q) := by
  classical
  have hc : Fintype.card (Tape c) =
      Fintype.card (Rest q) * Fintype.card (Sample q) :=
    (Fintype.card_congr (split q)).trans (Fintype.card_prod _ _)
  simp only [Soundness.uniformProb, card_event q event, Nat.cast_sum, hc,
    Nat.cast_mul, ← Finset.sum_div]
  rw [div_div, mul_comm]

theorem fiber_event_bound {c : Config} (q : Coordinate c) (event : Tape c → Prop)
    [DecidablePred event] (bound : ℚ)
    (h : ∀ rest : Rest q, Soundness.uniformProb
      (Finset.univ.filter fun x : Sample q => event (set q rest.val x)) ≤ bound) :
    Soundness.uniformProb (Finset.univ.filter event) ≤ bound := by
  classical
  rw [uniformProb_event q event]
  have hp : (0 : ℚ) < Fintype.card (Rest q) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ ∑ _rest : Rest q, bound := Finset.sum_le_sum (fun rest _ => h rest)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- Fixed coordinate families compose by the union bound, not event independence. -/
theorem coordinate_union_bound {c : Config} {I : Type*} [Fintype I]
    (q : I → Coordinate c) (event : I → Tape c → Prop)
    [∀ i, DecidablePred (event i)] (bound : I → ℚ)
    (h : ∀ i (rest : Rest (q i)), Soundness.uniformProb
      (Finset.univ.filter fun x : Sample (q i) => event i (set (q i) rest.val x)) ≤ bound i) :
    Soundness.uniformProb (Finset.univ.biUnion fun i =>
      Finset.univ.filter (event i)) ≤ ∑ i, bound i := by
  classical
  exact (Soundness.union_bound _).trans
    (Finset.sum_le_sum fun i _ => fiber_event_bound (q i) (event i) (bound i) (h i))

@[simp] theorem set_tail {c : Config} (j : Fin (c.logN - c.folds.toList.sum))
    (t : Tape c) (x : E) :
    set (.tail j) t x = (t.1, t.2.1, Function.update t.2.2 j x) := by
  classical
  apply (coordinates c).injective
  funext q
  change get q (set (.tail j) t x) =
    get q (t.1, t.2.1, Function.update t.2.2 j x)
  cases q with
  | initial => rw [get_set_ne _ _ _ _ (by intro h; cases h)]; rfl
  | fold i k => rw [get_set_ne _ _ _ _ (by intro h; cases h)]; rfl
  | ood i k => rw [get_set_ne _ _ _ _ (by intro h; cases h)]; rfl
  | query i => rw [get_set_ne _ _ _ _ (by intro h; cases h)]; rfl
  | tail k =>
    by_cases h : k = j
    · subst k; rw [get_set]; simp [get]
    · rw [get_set_ne _ _ _ _ (by simpa using h)]
      simp [get, h]

/-- Replacing a tail scalar leaves all levels and earlier tail entries unchanged. -/
theorem tail_challenges_prefix {c : Config} (j : Fin (c.logN - c.folds.toList.sum))
    (t : Tape c) (x : E) :
    (challenges c (set (.tail j) t x)).levels = (challenges c t).levels ∧
    (challenges c (set (.tail j) t x)).tail.toList.take j.val =
      (challenges c t).tail.toList.take j.val := by
  classical
  constructor
  · simp [challenges]
  · simp only [set_tail, challenges, Array.toList_ofFn]
    apply List.ext_getElem
    · simp
    · intro k hk hk'
      simp only [List.getElem_take, List.getElem_ofFn]
      apply Function.update_of_ne
      have : k < j.val := lt_of_lt_of_le hk (List.length_take_le _ _)
      exact Fin.ne_of_val_ne (by simpa only [Fin.val_mk] using Nat.ne_of_lt this)

/-- Actual strategy input before a tail draw is invariant under replacing it. -/
theorem tail_visible_prefix {c : Config} (j : Fin (c.logN - c.folds.toList.sum))
    (t : Tape c) (x : E) :
    (visibleBatches c (set (.tail j) t x).1 (challenges c (set (.tail j) t x))).take
        (tailStart c (challenges c t) + j.val) =
      (visibleBatches c t.1 (challenges c t)).take
        (tailStart c (challenges c t) + j.val) := by
  classical
  rw [set_tail]
  let pre := [Batch.initial t.1] ++
    (List.range c.folds.size).flatMap (levelBatches (challenges c t))
  have hl : pre.length = tailStart c (challenges c t) := by
    simp only [pre, List.length_append, List.length_singleton, tailStart, levelStart]
  unfold visibleBatches
  simp only [challenges, Array.size_ofFn]
  change (pre ++ (List.ofFn fun k : Fin (c.logN - c.folds.toList.sum - 1) =>
      Batch.tail k (Array.ofFn (Function.update t.2.2 j x))[k.val]!)).take _ =
    (pre ++ (List.ofFn fun k : Fin (c.logN - c.folds.toList.sum - 1) =>
      Batch.tail k (Array.ofFn t.2.2)[k.val]!)).take _
  simp only [challenges] at hl
  rw [← hl]
  simp only [List.take_append, Nat.add_sub_cancel_left]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
  · intro k hk hk'
    simp only [List.getElem_take, List.getElem_ofFn]
    congr 1
    have hkj : k < j.val := lt_of_lt_of_le hk (List.length_take_le _ _)
    have hkn : k < c.logN - c.folds.toList.sum := lt_trans hkj j.isLt
    have hne : (⟨k, hkn⟩ : Fin (c.logN - c.folds.toList.sum)) ≠ j :=
      Fin.ne_of_val_ne (by simpa using Nat.ne_of_lt hkj)
    rw [_root_.getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hkn),
      _root_.getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hkn)]
    simp only [Array.getElem_ofFn, Function.update_of_ne hne]

theorem final_tail_visible {c : Config} (j : Fin (c.logN - c.folds.toList.sum))
    (last : j.val + 1 = c.logN - c.folds.toList.sum) (t : Tape c) (x : E) :
    visibleBatches c (set (.tail j) t x).1 (challenges c (set (.tail j) t x)) =
      visibleBatches c t.1 (challenges c t) := by
  classical
  rw [set_tail]
  apply CausalRefinement.visible_tail_congr
  · rfl
  · simp [challenges]
  · intro k hk
    simp only [challenges, Array.size_ofFn] at hk
    have hkn : k < c.logN - c.folds.toList.sum := by omega
    have hne : (⟨k, hkn⟩ : Fin (c.logN - c.folds.toList.sum)) ≠ j :=
      Fin.ne_of_val_ne (by change k ≠ j.val; omega)
    simp only [challenges]
    rw [_root_.getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hkn),
      _root_.getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hkn)]
    simp only [Array.getElem_ofFn, Function.update_of_ne hne]

/-- Coordinate order is fixed by the configuration, never by prover messages. -/
def levelCoordinates (c : Config) (i : Nat) : List (Coordinate c) :=
  if hi : i < c.folds.size then
    (List.ofFn fun j => Coordinate.fold ⟨i, hi⟩ j) ++
    (List.ofFn fun j => Coordinate.ood ⟨i, hi⟩ j) ++ [.query ⟨i, hi⟩]
  else []

def visibleCoordinates (c : Config) : List (Coordinate c) :=
  [.initial] ++ (List.range c.folds.size).flatMap (levelCoordinates c) ++
    (List.ofFn fun j : Fin (c.logN - c.folds.toList.sum - 1) =>
      Coordinate.tail ⟨j.val, by omega⟩)

def batch {c : Config} (q : Coordinate c) (x : Sample q) : Batch :=
  match q with
  | .initial => .initial x
  | .fold i j => .fold i.val j.val x
  | .ood i j => .ood i.val j.val (Array.ofFn x)
  | .query i => .query i.val (Array.ofFn x.1) x.2
  | .tail j => .tail j.val x

theorem levelCoordinates_map (c : Config) (t : Tape c) (i : Nat)
    (hi : i < c.folds.size) :
    (levelCoordinates c i).map (fun q => batch q (get q t)) =
      levelBatches (challenges c t) i := by
  simp [levelCoordinates, hi, List.map_ofFn, levelBatches, challenges,
    _root_.getElem!_pos, batch, get, Function.comp_def]
  congr 1

/-- This is the actual Array.ofFn challenge conversion and actual wire stream. -/
theorem visibleCoordinates_map (c : Config) (t : Tape c) :
    (visibleCoordinates c).map (fun q => batch q (get q t)) =
      visibleBatches c t.1 (challenges c t) := by
  simp only [visibleCoordinates, visibleBatches, List.map_append, List.map_cons,
    List.map_nil, batch, get, List.map_flatMap]
  congr 1
  · congr 1
    apply List.flatMap_congr
    intro i hi
    exact levelCoordinates_map c t i (List.mem_range.mp hi)
  · simp only [challenges, Array.size_ofFn, List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext j
    dsimp
    congr 1
    rw [_root_.getElem!_pos _ _ (by
      simp only [Array.size_ofFn]
      exact Nat.lt_of_lt_of_le j.isLt (Nat.sub_le _ _))]
    simp only [Array.getElem_ofFn]
    rfl

/-- Zero-based position of the indivisible batch; the invisible final tail has
position equal to the length of the entire visible stream. -/
def position {c : Config} (q : Coordinate c) : Nat := (visibleCoordinates c).idxOf q

private theorem not_mem_take_idxOf {A : Type*} [DecidableEq A] (q : A) (xs : List A) :
    q ∉ xs.take (xs.idxOf q) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases h : a = q
    · subst a; simp
    · simp [h, Ne.symm h, ih]

/-- Replacing one real tape coordinate cannot alter the actual challenge prefix
before its batch, including arbitrary malformed strategy executions. -/
theorem visible_prefix {c : Config} (q : Coordinate c) (t : Tape c) (x : Sample q) :
    (visibleBatches c (set q t x).1 (challenges c (set q t x))).take (position q) =
      (visibleBatches c t.1 (challenges c t)).take (position q) := by
  rw [← visibleCoordinates_map, ← visibleCoordinates_map]
  simp only [← List.map_take]
  apply List.map_congr_left
  intro r hr
  rw [get_set_ne q r t x]
  intro h
  subst r
  exact not_mem_take_idxOf q (visibleCoordinates c) hr

/-- The causal strategy itself, not an assumed adaptedness predicate, supplies
identical earlier responses. No parser success or proof validity is required. -/
theorem response_prefix {c : Config} (q : Coordinate c) (t : Tape c) (x : Sample q)
    (strategy : Strategy) (input : Public) :
    (run strategy input []
      (visibleBatches c (set q t x).1 (challenges c (set q t x)))).take (position q) =
    (run strategy input [] (visibleBatches c t.1 (challenges c t))).take (position q) :=
  prefix_independent strategy input (position q) [] _ _ (visible_prefix q t x)

/-- Read one indivisible coordinate through the verifier's actual arrays. -/
def challengeBatch {c : Config} (q : Coordinate c) (t : Tape c) : Batch :=
  let ch := challenges c t
  match q with
  | .initial => .initial t.1
  | .fold i j => .fold i.val j.val ch.levels[i.val]!.folds[j.val]!
  | .ood i j => .ood i.val j.val ch.levels[i.val]!.oodPoints[j.val]!
  | .query i => .query i.val ch.levels[i.val]!.querySqueezes ch.levels[i.val]!.lambda
  | .tail j => .tail j.val ch.tail[j.val]!

theorem challengeBatch_eq {c : Config} (q : Coordinate c) (t : Tape c) :
    challengeBatch q t = batch q (get q t) := by
  cases q with
  | initial => rfl
  | fold i j =>
    simp [challengeBatch, challenges, _root_.getElem!_pos, i.isLt, batch, get]
    rw [_root_.getElem!_pos _ _ (by simpa only [Array.size_ofFn] using j.isLt)]
    exact Array.getElem_ofFn _
  | ood i j =>
    simp [challengeBatch, challenges, _root_.getElem!_pos, i.isLt, j.isLt, batch, get]
  | query i =>
    simp [challengeBatch, challenges, _root_.getElem!_pos, i.isLt, batch, get]
  | tail j =>
    simp only [challengeBatch, challenges, batch, get]
    congr 1
    rw [_root_.getElem!_pos _ _ (by simpa only [Array.size_ofFn] using j.isLt)]
    exact Array.getElem_ofFn _

theorem challengeBatch_set_ne {c : Config} (q r : Coordinate c) (t : Tape c)
    (x : Sample q) (h : r ≠ q) :
    challengeBatch r (set q t x) = challengeBatch r t := by
  rw [challengeBatch_eq, challengeBatch_eq, get_set_ne q r t x h]

theorem challenges_prefix {c : Config} (q : Coordinate c) (t : Tape c) (x : Sample q) :
    ((visibleCoordinates c).take (position q)).map (fun r => challengeBatch r (set q t x)) =
      ((visibleCoordinates c).take (position q)).map (fun r => challengeBatch r t) := by
  apply List.map_congr_left
  intro r hr
  apply challengeBatch_set_ne
  intro h
  subst r
  exact not_mem_take_idxOf q (visibleCoordinates c) hr

theorem field_before {c : Config} {R : Type*} (q : Coordinate c)
    (t : Tape c) (x : Sample q) (strategy : Strategy) (input : Public)
    (field : Reply → R) (n : Nat) (hn : n < position q) :
    field (run strategy input []
      (visibleBatches c (set q t x).1 (challenges c (set q t x))))[n]! =
      field (run strategy input [] (visibleBatches c t.1 (challenges c t)))[n]! := by
  apply CausalRefinement.field_prefix
  have h := congrArg (List.take (n+1)) (visible_prefix q t x)
  simpa only [List.take_take, Nat.min_eq_left (by omega : n+1 ≤ position q)] using h

theorem final_tail_response {c : Config} (j : Fin (c.logN - c.folds.toList.sum))
    (last : j.val + 1 = c.logN - c.folds.toList.sum) (t : Tape c) (x : E)
    (strategy : Strategy) (input : Public) :
    run strategy input []
      (visibleBatches c (set (.tail j) t x).1 (challenges c (set (.tail j) t x))) =
      run strategy input [] (visibleBatches c t.1 (challenges c t)) := by
  rw [final_tail_visible j last t x]

end Whir.CausalProbability
