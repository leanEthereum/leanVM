/-
  LeanVM.Protocol.Spine.KeccakZero

  The Keccak predicate along the table sumcheck's point: the multilinear zero test of the
  difference between the region's committed states after twelve rounds and the first twelve rounds
  of its input states, with the high coordinates bound first.
-/

module

public import LeanVM.Protocol.Spine.Instance

/-!
# The Keccak predicate along a point

`M3Holds` asks of the Keccak region (`KeccakRegion.Holds`) that at every step `x` the state in
slots `25 … 49` is the first twelve rounds of the state in slots `0 … 24`. The protocol does not
check this with challenges of its own: the Keccak reduction's first claim compares the two at the
point `inst` of the `KECCAK` table's claims, which the table sumcheck draws. So the predicate is
carried through the table sumcheck as a zero test that the sumcheck's challenges evaluate one
coordinate at a time, and after the table sumcheck it is the predicate at `inst`
(`KeccakRegion.HoldsOn`): for every lane, the multilinear extension of the difference
(`KeccakRegion.delta`) over the steps vanishes at `inst`.

The table sumcheck binds the variables highest first (its point is its challenges reversed), so
the zero test binds the *high* coordinates first: `ZeroOnHi δ acc n` says the extension of `δ` on
`n` bits, its last `|acc|` coordinates bound to `acc`, vanishes on the whole remaining cube
(`foldHi`). With nothing bound it is `δ = 0` on the cube (`zeroOnHi_nil`), so `HoldsOn [] ↔ Holds`
(`holdsOn_nil`); with everything bound it is the extension at the point (`zeroOnHi_full`); and a
fresh coordinate keeps a failing test failing except at one value at most
(`card_zeroOnHi_cons_le`), the escape the table sumcheck's rounds absorb within their own
`3/|E|`.

Written from the specification (the Keccak reduction's first claim, `verify_keccak` in
`crates/verifier/src/keccak.rs` at leanVM `40f877dc`); nothing here transcribes Rust.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

namespace KeccakZero

/-- The equality weight of the bits of `w` against the point `acc`: bit `i` of `w` weighs
`acc[i]` when set and `1 - acc[i]` when not. -/
def eqAt : List E → ℕ → E
  | [], _ => 1
  | a :: acc, w => (if w % 2 = 1 then a else 1 - a) * eqAt acc (w / 2)

/-- The table `δ` on `n` bits with its high `|acc|` coordinates bound to `acc`, at the index `v`
of the low coordinates. -/
def foldHi (δ : ℕ → E) (n : ℕ) (acc : List E) (v : ℕ) : E :=
  ∑ w ∈ Finset.range (2 ^ acc.length), eqAt acc w * δ (v + 2 ^ (n - acc.length) * w)

/-- The multilinear extension of `δ` on `n` bits, its high coordinates bound to `acc`, vanishes on
the remaining cube. -/
def ZeroOnHi (δ : ℕ → E) (acc : List E) (n : ℕ) : Prop :=
  ∀ v < 2 ^ (n - acc.length), foldHi δ n acc v = 0

/-- A sum over `2 N` indices, by pairs. -/
theorem sum_range_two_mul (f : ℕ → E) (N : ℕ) :
    ∑ w ∈ Finset.range (2 * N), f w = ∑ w ∈ Finset.range N, (f (2 * w) + f (2 * w + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

/-- Nothing bound: the table itself. -/
theorem foldHi_nil (δ : ℕ → E) (n v : ℕ) : foldHi δ n [] v = δ v := by
  simp [foldHi, eqAt]

/-- Binding one more coordinate, the next lower one. -/
theorem foldHi_cons (δ : ℕ → E) {n : ℕ} (c : E) {acc : List E} (h : acc.length < n) (v : ℕ) :
    foldHi δ n (c :: acc) v =
      (1 - c) * foldHi δ n acc v + c * foldHi δ n acc (v + 2 ^ (n - acc.length - 1)) := by
  obtain ⟨m, h1, h2, h3⟩ : ∃ m, n - (acc.length + 1) = m ∧ n - acc.length = m + 1 ∧
      n - acc.length - 1 = m := ⟨n - (acc.length + 1), rfl, by omega, by omega⟩
  unfold foldHi
  rw [List.length_cons, h1, h2, Nat.add_sub_cancel, pow_succ, mul_comm _ 2, sum_range_two_mul,
    Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have e0 : eqAt (c :: acc) (2 * w) = (1 - c) * eqAt acc w := by
    simp [eqAt, Nat.mul_mod_right, Nat.mul_div_cancel_left w (by norm_num : 0 < 2)]
  have e1 : eqAt (c :: acc) (2 * w + 1) = c * eqAt acc w := by
    simp only [eqAt]
    rw [ite_eq_left (by omega), show (2 * w + 1) / 2 = w by omega]
  have i0 : v + 2 ^ m * (2 * w) = v + 2 ^ (m + 1) * w := by
    rw [pow_succ]; ring
  have i1 : v + 2 ^ m * (2 * w + 1) = v + 2 ^ m + 2 ^ (m + 1) * w := by
    rw [pow_succ]; ring
  rw [e0, e1, i0, i1]
  ring

/-- Nothing bound: the table vanishes on the cube. -/
theorem zeroOnHi_nil (δ : ℕ → E) (n : ℕ) : ZeroOnHi δ [] n ↔ ∀ v < 2 ^ n, δ v = 0 := by
  simp [ZeroOnHi, foldHi_nil]

/-- Everything bound: the extension vanishes at the point. -/
theorem zeroOnHi_full (δ : ℕ → E) {acc : List E} {n : ℕ} (h : acc.length = n) :
    ZeroOnHi δ acc n ↔ ∑ w ∈ Finset.range (2 ^ n), eqAt acc w * δ w = 0 := by
  unfold ZeroOnHi foldHi
  rw [h, Nat.sub_self, pow_zero]
  constructor
  · intro hz
    simpa using hz 0 Nat.one_pos
  · intro hz v hv
    obtain rfl : v = 0 := by omega
    simpa using hz

/-- A table that vanishes on the cube passes the test at every point. -/
theorem zeroOnHi_of_zero (δ : ℕ → E) {n : ℕ} (hδ : ∀ v < 2 ^ n, δ v = 0) (acc : List E)
    (hacc : acc.length ≤ n) : ZeroOnHi δ acc n := by
  intro v hv
  refine Finset.sum_eq_zero fun w hw ↦ ?_
  have hw' := Finset.mem_range.1 hw
  have hlt : v + 2 ^ (n - acc.length) * w < 2 ^ n := by
    calc v + 2 ^ (n - acc.length) * w < 2 ^ (n - acc.length) + 2 ^ (n - acc.length) * w := by
          omega
      _ = 2 ^ (n - acc.length) * (w + 1) := by ring
      _ ≤ 2 ^ (n - acc.length) * 2 ^ acc.length := Nat.mul_le_mul_left _ hw'
      _ = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hacc]
  rw [hδ _ hlt, mul_zero]

/-- **The escape**: a failing test passes after a fresh coordinate at one value at most. -/
theorem card_zeroOnHi_cons_le (δ : ℕ → E) {n : ℕ} {acc : List E} (hacc : acc.length < n)
    (hne : ¬ ZeroOnHi δ acc n) : Nat.card {c : E // ZeroOnHi δ (c :: acc) n} ≤ 1 := by
  obtain ⟨u, hu, hfu⟩ : ∃ u < 2 ^ (n - acc.length), foldHi δ n acc u ≠ 0 := by
    by_contra hall
    exact hne fun v hv ↦ by_contra fun h0 ↦ hall ⟨v, hv, h0⟩
  set m := n - acc.length - 1 with hm
  have hpow : 2 ^ (n - acc.length) = 2 * 2 ^ m := by
    rw [show n - acc.length = m + 1 by omega, pow_succ, mul_comm]
  obtain ⟨v, hv, hAB⟩ : ∃ v < 2 ^ m,
      foldHi δ n acc v ≠ 0 ∨ foldHi δ n acc (v + 2 ^ m) ≠ 0 := by
    by_cases hum : u < 2 ^ m
    · exact ⟨u, hum, Or.inl hfu⟩
    · refine ⟨u - 2 ^ m, by omega, Or.inr ?_⟩
      rwa [Nat.sub_add_cancel (by omega)]
  rw [Finite.card_le_one_iff_subsingleton]
  refine ⟨fun ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ ↦ Subtype.ext ?_⟩
  have hv' : v < 2 ^ (n - (c₁ :: acc).length) := by
    simp only [List.length_cons]; rw [show n - (acc.length + 1) = m by omega]; exact hv
  have z₁ := h₁ v hv'
  have z₂ := h₂ v hv'
  rw [foldHi_cons δ c₁ hacc] at z₁
  rw [foldHi_cons δ c₂ hacc] at z₂
  set A := foldHi δ n acc v
  set B := foldHi δ n acc (v + 2 ^ m)
  have hdiff : (c₁ - c₂) * (B - A) = 0 := by linear_combination z₁ - z₂
  rcases mul_eq_zero.1 hdiff with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have hBA : B = A := sub_eq_zero.1 h
    rw [hBA] at z₁
    have hA : A = 0 := by linear_combination z₁
    rcases hAB with h' | h'
    · exact h' hA
    · exact h' (hBA.trans hA)

/-- The escape for a family of tests: if one fails, all pass after a fresh coordinate at one
value at most. -/
theorem card_forall_zeroOnHi_cons_le {ι : Type} (δ : ι → ℕ → E) {n : ℕ} {acc : List E}
    (hacc : acc.length < n) (hne : ¬ ∀ i, ZeroOnHi (δ i) acc n) :
    Nat.card {c : E // ∀ i, ZeroOnHi (δ i) (c :: acc) n} ≤ 1 := by
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  refine le_trans ?_ (card_zeroOnHi_cons_le (δ i) hacc hi)
  have := Fintype.ofFinite E
  exact Nat.card_mono (Set.toFinite _) fun c hc ↦ hc i

end KeccakZero

open KeccakZero

/-! ## The Keccak region along a point -/

namespace KeccakRegion

variable {S : Shape} (r : KeccakRegion S)

/-- Lane `l` of the difference at step `x`: lane `l` of the first twelve rounds of the input
state, minus the committed word in slot `25 + l`; zero past the steps. -/
def delta (c : Column (r.logSteps + 6)) (l : Fin 25) (x : ℕ) : E :=
  if hx : x < 2 ^ r.logSteps then
    ofK (stateLanes (keccakSegment 0 (r.state c 0 ⟨x, hx⟩)) l) - ofK (r.word c (25 + l) ⟨x, hx⟩)
  else 0

/-- The Keccak predicate along the bound coordinates `acc` (high first): every lane's difference
passes the zero test. -/
def HoldsOn (c : Column (r.logSteps + 6)) (acc : List E) : Prop :=
  ∀ l : Fin 25, ZeroOnHi (r.delta c l) acc r.logSteps

/-- With nothing bound, the Keccak predicate along a point is the Keccak predicate. -/
theorem holdsOn_nil (c : Column (r.logSteps + 6)) : r.HoldsOn c [] ↔ r.Holds c := by
  unfold HoldsOn Holds
  simp only [zeroOnHi_nil, delta]
  constructor
  · intro h x
    have hl : ∀ l : Fin 25, r.word c (25 + l) x = stateLanes (keccakSegment 0 (r.state c 0 x)) l :=
      fun l ↦ by
        have := h l x.val x.isLt
        rw [dite_eq_left x.isLt, sub_eq_zero] at this
        exact (ofK_injective this).symm
    rw [← laneState_stateLanes (keccakSegment 0 (r.state c 0 x))]
    unfold state
    refine congrArg laneState ?_
    funext l
    exact hl l
  · intro h l x hx
    rw [dite_eq_left hx, sub_eq_zero]
    refine congrArg ofK ?_
    rw [← h ⟨x, hx⟩]
    simp only [state, stateLanes_laneState]

/-- The Keccak predicate passes the test at every point. -/
theorem holdsOn_of_holds {c : Column (r.logSteps + 6)} (h : r.Holds c) (acc : List E)
    (hacc : acc.length ≤ r.logSteps) : r.HoldsOn c acc := fun l ↦
  zeroOnHi_of_zero _ (((r.holdsOn_nil c).mpr h) l |> (zeroOnHi_nil _ _).mp) acc hacc

end KeccakRegion

/-! ## The instance's Keccak predicate along the table sumcheck -/

namespace M3Instance

variable (I : M3Instance)

/-- The Keccak predicate at a point of the table sumcheck, in coordinate order: along the region's
low `logSteps` coordinates (all of them when the region fits in the sumcheck), the point of the
`KECCAK` table's claims. -/
def auxAt (point : List E) (q : Column I.μ) : Prop :=
  ∀ r ∈ I.keccak, r.HoldsOn (I.keccakColumn r q) (point.take (min r.logSteps I.τmax))

/-- The Keccak predicate during the table sumcheck, after the challenges `ch` (in the order
drawn): the challenges past the first `τmax − logSteps` bind the region's coordinates, highest
first. -/
def auxStage (ch : List E) (q : Column I.μ) : Prop :=
  ∀ r ∈ I.keccak, r.HoldsOn (I.keccakColumn r q) ((ch.drop (I.τmax - r.logSteps)).reverse)

/-- Before the first challenge, the Keccak predicate. -/
theorem auxStage_nil (q : Column I.μ) : I.auxStage [] q ↔ I.aux q := by
  simp only [auxStage, aux, List.drop_nil, List.reverse_nil, KeccakRegion.holdsOn_nil]

/-- After the last challenge, the Keccak predicate at the point, the challenges reversed. -/
theorem auxStage_full (q : Column I.μ) {ch : List E} (hch : ch.length = I.τmax) :
    I.auxStage ch q ↔ I.auxAt ch.reverse q := by
  unfold auxStage auxAt
  refine forall₂_congr fun r _ ↦ ?_
  rw [List.reverse_drop, hch, show I.τmax - (I.τmax - r.logSteps) = min r.logSteps I.τmax by
    omega]

/-- The Keccak predicate holds along every point. -/
theorem auxAt_of_aux {q : Column I.μ} (h : I.aux q) (point : List E) : I.auxAt point q :=
  fun r hr ↦ r.holdsOn_of_holds (h r hr) _ ((List.length_take_le _ _).trans (min_le_left _ _))

/-- **The escape at a round of the table sumcheck**: a failing Keccak predicate passes after a
fresh challenge at one value at most. -/
theorem card_auxStage_push_le (q : Column I.μ) {ch : List E} (hch : ch.length < I.τmax)
    (hne : ¬ I.auxStage ch q) : Nat.card {x : E // I.auxStage (ch ++ [x]) q} ≤ 1 := by
  unfold auxStage at hne ⊢
  rcases hk : I.keccak with _ | r
  · exact absurd (fun r hr ↦ by simp [hk] at hr) hne
  · simp only [hk, Option.mem_def, Option.some.injEq, forall_eq'] at hne ⊢
    by_cases hlt : ch.length < I.τmax - r.logSteps
    · have hd : ∀ x : E, (ch ++ [x]).drop (I.τmax - r.logSteps) = [] := fun x ↦
        List.drop_eq_nil_of_le (by simp only [List.length_append, List.length_singleton]; omega)
      have hd' : ch.drop (I.τmax - r.logSteps) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hd'] at hne
      simp only [hd]
      have : IsEmpty {x : E // r.HoldsOn (I.keccakColumn r q) [].reverse} :=
        ⟨fun x ↦ hne x.2⟩
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
    · have hd : ∀ x : E, ((ch ++ [x]).drop (I.τmax - r.logSteps)).reverse =
          x :: (ch.drop (I.τmax - r.logSteps)).reverse := fun x ↦ by
        rw [List.drop_append_of_le_length (by omega), List.reverse_append]
        rfl
      simp only [hd]
      exact KeccakZero.card_forall_zeroOnHi_cons_le _
        (by simp only [List.length_reverse, List.length_drop]; omega) hne

end M3Instance

end
end LeanVM.Protocol
