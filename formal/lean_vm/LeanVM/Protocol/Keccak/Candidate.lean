/-
  LeanVM.Protocol.Keccak.Candidate

  A candidate `q_keccak` column and what the reduction says of it: its states per segment and
  step, the claims the reduction starts from and ends with, `RegionValid`, and a generic
  multilinear zero test for the phase that draws the table point.
-/

module

public import LeanVM.Protocol.Keccak.Words
public import LeanVM.Protocol.Keccak.Layer

/-!
# Candidates

A candidate's `q_keccak` column is read as `col : ℕ → K` (word `n`, `0` past the end): word
`x + 2^h·slot` is lane `slot` of step `x`'s input state (slots `0..24`), or for slot `25 + ℓ`
lane `ℓ` of the committed state after twelve rounds (`doc/leanvm` §`keccak:segments`).

* `inState col m x`: segment `m`'s committed input at step `x` (slots `25m .. 25m + 24`);
  `statesAt col d`: the states `12 - d` rounds into each segment, as bits (depth `d`);
  `statesAt_round`: depth `d` is the round `12(m + 1) - d - 1` of depth `d + 1`
  (`afterRound`), so a layer's specification applies (`claimTrue_round`).
* The statements: `outClaimsTrue` (the table's `25` output-lane claims at `inst`, against
  `keccakF` of the inputs), `outClaimsTrueMid` (against the second segment from the committed
  middle state), `midAgree` (the first segment's output and the committed middle state agree at
  `inst`, lane by lane), `RegionValid` (they agree at every step); `colTrue`, `slicesTrue`: the
  claims the reduction leaves on `q_keccak`. `outClaims_of_regionValid`: a valid region with
  true output claims has true middle-state claims.
* `ZeroOn δ acc n`: the multilinear extension of the table `δ` on `n` bits, with its first
  `|acc|` coordinates bound to `acc`, is identically zero; `zeroOn_escape`: a coordinate drawn
  uniformly makes a nonzero partial extension zero with probability at most `1/|E|`.
  `midAgree_iff`, `regionValid_iff`: `midAgree` at `inst` and `RegionValid` are `ZeroOn` of the
  `25` tables `midDelta` at `inst` and at `[]`. This is the escape the phase drawing `inst`
  (the table sumcheck) charges, `h/|E|` per candidate, to turn `RegionValid` into `midAgree`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open Finset
open scoped ENNReal

@[expose] public section

variable (h : ℕ)

/-! ## States -/

/-- Segment `m`'s committed input at step `x`: slots `25m .. 25m + 24`. -/
def inState (col : ℕ → K) (m x : ℕ) : KeccakState :=
  Vector.ofFn fun l : Fin 25 ↦ K.lane (col (x + 2 ^ h * (25 * m + l)))

/-- The state `e` rounds into segment `m` at step `x`. -/
def segState (col : ℕ → K) (m e x : ℕ) : KeccakState := roundsFrom (12 * m) e (inState h col m x)

/-- The states at depth `d` (`12 - d` rounds into each segment), as bits. -/
def statesAt (col : ℕ → K) (d : ℕ) : States := fun m x j ↦ sbit (segState h col m (12 - d) x) j

theorem statesAt_round (col : ℕ → K) {d : ℕ} (hd : d < 12) (m x j : ℕ) (hm : m < 2)
    (hj : j < 1600) : statesAt h col d m x j = afterRound (statesAt h col (d + 1)) d m x j := by
  have e : 12 - d = (12 - (d + 1)) + 1 := by omega
  rw [statesAt, segState, e, roundsFrom_succ (by omega), sbit_round _ _ hj, afterRound, layerRC]
  have e2 : keccakDepth * (m + 1) - d - 1 = 12 * m + (12 - (d + 1)) := by
    rw [show keccakDepth = 12 from rfl]; omega
  rw [e2]
  rfl

theorem claimTrue_round (col : ℕ → K) {d : ℕ} (hd : d < 12) (P : ℕ) (c : KeccakClaim) :
    ClaimTrue (statesAt h col d) P c ↔ ClaimTrue (afterRound (statesAt h col (d + 1)) d) P c := by
  unfold ClaimTrue
  rw [claimSum_congr P (fun m x j hm hj ↦ statesAt_round h col hd m x j hm hj)]

/-! ## The statements -/

/-- The multilinear extension over the steps of a `K`-valued function, at `pt`. -/
def stepMle (pt : List E) (f : ℕ → K) : E := ∑ x ∈ range (2 ^ h), eqAt pt x * ofK (f x)

/-- Lane `l` of a state as a word. -/
def laneWord (a : KeccakState) (l : ℕ) : K := K.ofLane (Keccak.lane a l)

/-- **The table's output-lane claims** at `inst`: lane `l` of `keccakF` of each step's input. -/
def outClaimsTrue (col : ℕ → K) (inst output : List E) : Prop :=
  ∀ l < 25, stepMle h inst (fun x ↦ laneWord (keccakF1600 (inState h col 0 x)) l) = output.getD l 0

/-- The output-lane claims against the second segment, from the committed middle state. -/
def outClaimsTrueMid (col : ℕ → K) (inst output : List E) : Prop :=
  ∀ l < 25, stepMle h inst (fun x ↦ laneWord (roundsFrom 12 12 (inState h col 1 x)) l) =
    output.getD l 0

/-- The first segment's output and the committed middle state agree at `inst`, lane by lane. -/
def midAgree (col : ℕ → K) (inst : List E) : Prop :=
  ∀ l < 25, stepMle h inst (fun x ↦ laneWord (roundsFrom 0 12 (inState h col 0 x)) l) =
    stepMle h inst (fun x ↦ col (x + 2 ^ h * (25 + l)))

/-- **The committed middle state is twelve rounds of the input**, at every step. -/
def RegionValid (col : ℕ → K) : Prop :=
  ∀ x < 2 ^ h, inState h col 1 x = roundsFrom 0 12 (inState h col 0 x)

/-- A column claim on `q_keccak` holds: the column's multilinear extension (step bits low, the
six slot bits high) at the claim's point. -/
def colTrue (col : ℕ → K) (c : ColumnClaim) : Prop :=
  c.column = qkeccak ∧ c.point.length = h + 6 ∧
    c.value = ∑ n ∈ range (2 ^ (h + 6)), eqAt c.point n * ofK (col n)

/-- The `64` bit-slice claims hold: slice `i`'s multilinear extension at `point` is
`slices[i]`. -/
def slicesTrue (col : ℕ → K) (point slices : List E) : Prop :=
  point.length = h + 6 ∧ slices.length = 64 ∧ ∀ i < 64,
    slices.getD i 0 = ∑ n ∈ range (2 ^ (h + 6)), eqAt point n * bitE ((col n).toBitVec.getLsbD i)

theorem lane_inState (col : ℕ → K) (m x : ℕ) {l : ℕ} (hl : l < 25) :
    Keccak.lane (inState h col m x) l = K.lane (col (x + 2 ^ h * (25 * m + l))) := by
  rw [lane_eq _ hl, inState, Vector.getElem_ofFn]

/-! ## A multilinear zero test -/

/-- The table `δ` with its first `|acc|` coordinates bound to `acc`, at the remaining index `v`. -/
def foldT (δ : ℕ → E) (acc : List E) (v : ℕ) : E :=
  ∑ w ∈ range (2 ^ acc.length), eqAt acc w * δ (w + 2 ^ acc.length * v)

/-- The multilinear extension of `δ` on `n` bits, its first coordinates bound to `acc`, is
identically zero. -/
def ZeroOn (δ : ℕ → E) (acc : List E) (n : ℕ) : Prop :=
  ∀ v < 2 ^ (n - acc.length), foldT δ acc v = 0

theorem foldT_nil (δ : ℕ → E) (v : ℕ) : foldT δ [] v = δ v := by simp [foldT]

theorem foldT_snoc (δ : ℕ → E) (acc : List E) (c : E) (v : ℕ) :
    foldT δ (acc ++ [c]) v = (1 + c) * foldT δ acc (2 * v) + c * foldT δ acc (2 * v + 1) := by
  unfold foldT
  rw [List.length_append, List.length_singleton, pow_succ, mul_comm (2 ^ acc.length) 2,
    sum_range_mul 2 (2 ^ acc.length), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.1 hw
    rw [eqAt_append, Nat.mul_zero, Nat.zero_add, Nat.div_eq_of_lt hw']
    simp only [eqAt_cons, eqAt_nil, Nat.zero_mod, zero_ne_one, ite_false, mul_one]
    rw [show w + 2 * 2 ^ acc.length * v = w + 2 ^ acc.length * (2 * v) by ring]
    ring
  · refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.1 hw
    have hd : (2 ^ acc.length * 1 + w) / 2 ^ acc.length = 1 := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hw']
    rw [eqAt_append, hd, eqAt_mod acc (2 ^ acc.length * 1 + w), Nat.add_comm,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw']
    simp only [eqAt_cons, eqAt_nil, Nat.one_mod, ite_true, mul_one]
    rw [show w + 2 ^ acc.length + 2 * 2 ^ acc.length * v =
      w + 2 ^ acc.length * (2 * v + 1) by ring]
    ring

theorem zeroOn_nil (δ : ℕ → E) (n : ℕ) : ZeroOn δ [] n ↔ ∀ v < 2 ^ n, δ v = 0 := by
  simp [ZeroOn, foldT_nil]

theorem zeroOn_full (δ : ℕ → E) {acc : List E} {n : ℕ} (h : acc.length = n) :
    ZeroOn δ acc n ↔ ∑ w ∈ range (2 ^ n), eqAt acc w * δ w = 0 := by
  rw [ZeroOn, h, Nat.sub_self]
  simp [foldT, h]

/-- **The zero test's escape**: a coordinate drawn uniformly makes a nonzero partial extension
zero at one value at most. -/
theorem zeroOn_escape (δ : ℕ → E) {n : ℕ} {acc : List E} (hacc : acc.length < n)
    (hne : ¬ ZeroOn δ acc n) :
    avgE (fun c ↦ indE (ZeroOn δ (acc ++ [c]) n)) ≤ errE 1 := by
  obtain ⟨v, hv, hfv⟩ : ∃ v < 2 ^ (n - acc.length), foldT δ acc v ≠ 0 := by
    by_contra hall
    exact hne fun v hv ↦ by_contra fun h0 ↦ hall ⟨v, hv, h0⟩
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by omega
  have hv2 : v / 2 < 2 ^ (n - (acc.length + 1)) := by
    rw [hm, pow_succ] at hv; omega
  -- the pair at `v / 2` is not zero, so its fold is a nonzero affine function of `c`
  let a0 := foldT δ acc (2 * (v / 2))
  let a1 := foldT δ acc (2 * (v / 2) + 1)
  have hpair : ¬ (a0 = 0 ∧ a1 = 0) := by
    rintro ⟨h0, h1⟩
    rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv0
    · exact hfv (by rw [show v = 2 * (v / 2) by omega]; exact h0)
    · exact hfv (by rw [show v = 2 * (v / 2) + 1 by omega]; exact h1)
  open Polynomial in
  have hne' : (C a0 + C (a0 + a1) * X : E[X]) ≠ 0 := by
    intro he
    refine hpair ⟨?_, ?_⟩
    · have := congrArg (coeff · 0) he; simpa using this
    · have h0 : a0 = 0 := by have := congrArg (coeff · 0) he; simpa using this
      have := congrArg (coeff · 1) he
      simp at this
      rw [h0, zero_add] at this; exact this
  open Polynomial in
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
    (sz_escape hne' (q := 0) (d := 1) (natDegree_add_le_of_degree_le
      ((natDegree_C _).trans_le (by norm_num)) ((natDegree_C_mul_le _ _).trans (by simp)))
      (by simp))
  have := hc (v / 2) (by rw [List.length_append, List.length_singleton]; exact hv2)
  rw [foldT_snoc] at this
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_zero]
  rw [← this]
  ring

/-- The `25` tables of the middle state's mismatch: lane `l` of the first segment's output
minus (plus, in characteristic two) the committed middle state's, at each step. -/
def midDelta (col : ℕ → K) (l x : ℕ) : E :=
  ofK (laneWord (roundsFrom 0 12 (inState h col 0 x)) l) + ofK (col (x + 2 ^ h * (25 + l)))

end
end LeanVM.Protocol.KeccakGkr
