/-
  LeanVM.Protocol.EndToEnd.Front.RingFidelity

  The program's ring-switching claim on `q_keccak` paired with a stack, given where the layout
  places `q_keccak`: it holds exactly at the target's honest value under the drawn map.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.KeccakLayout
public import LeanVM.Protocol.EndToEnd.Complete.Gkr
public import LeanVM.Protocol.Keccak.Candidate
public import LeanVM.Protocol.EndToEnd.Front.RingSwitch

/-!
# The ring claim on the stack

The program's claim on the stack (`ringSwitchClaim`, `crates/verifier/src/lib.rs:338-344` at
leanVM at `leanvm-rev`) with the weight `ring_weight` of the drawn map (`ring_switch.rs`); the map,
its coefficients and target are `RingMap`'s (`Ring.ringSwitch_eq`):

* `ringWeight_eq_sum`: the program's weight is `Σ_k c_k eq(r^(2^k), ·)`;
* `colExt_frob`: the extension of `q_keccak` at `point^(2^k)` is `Σ_i x^i ẑ_i(point)^(2^k)`,
  `ẑ_i` the extension of bit slice `i` (`sliceExt`): a word is its bits packed by the powers of
  `x` (`K.eq_sum_bits`), and the Frobenius fixes bits and raises the equality weights;
* `pair_ringClaim`: where the layout places `q_keccak` on an aligned block of `2^(h + 6)` cells
  (`RingLayoutHyp`), the program's ring claim paired with a stack is `Σ_i x^i Φ(ẑ_i(point))`
  (`frobPhi_eq_idxSum`: `Φ` is the Frobenius sum with the program's coefficients); so
  (`ringClaim_holds_iff`) the claim holds exactly when the target is that honest value, and
  (`ringClaimBad_stack`) only at a bad challenge list of ring switching's group;
* `ringLayoutHyp_verifierLayout`: the verifier's layout places `q_keccak` so.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Ring LeanVM.Protocol.KeccakGkr
open LeanVM.Semantics LeanVM.Protocol.LeanIsa

@[expose] public section

/-! ## The Frobenius of `E` -/

/-- The Frobenius `b ↦ b^(2^k)` is additive. -/
theorem ring_frob_add (a b : E) (k : ℕ) : (a + b) ^ 2 ^ k = a ^ 2 ^ k + b ^ 2 ^ k :=
  add_pow_char_pow a b 2 k

/-- The Frobenius commutes with finite sums. -/
theorem ring_frob_sum {ι : Type} (s : Finset ι) (f : ι → E) (k : ℕ) :
    (∑ i ∈ s, f i) ^ 2 ^ k = ∑ i ∈ s, f i ^ 2 ^ k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ring_frob_add, ih]

/-- The Frobenius fixes a bit. -/
theorem bitE_frob (b : Bool) (k : ℕ) : bitE b ^ 2 ^ k = bitE b := by
  cases b <;> simp [bitE]

/-- The Frobenius of an equality weight raises the point. -/
theorem eqAt_frob (k : ℕ) : ∀ (pt : List E) (w : ℕ),
    eqAt pt w ^ 2 ^ k = eqAt (pt.map (· ^ 2 ^ k)) w
  | [], _ => by simp
  | r :: rs, w => by
    rw [List.map_cons, eqAt_cons, eqAt_cons, mul_pow, eqAt_frob k rs]
    split_ifs
    · rfl
    · rw [ring_frob_add, one_pow]

/-! ## The weight -/

/-- **The program's weight is `Σ_k c_k eq(r^(2^k), ·)`** (`Ring.ringWeight_fold`). -/
theorem ringWeight_eq_sum (r y cs : List E) :
    ringWeight r y cs =
      ∑ k ∈ Finset.range cs.length, cs.getD k 0 * eqEval (r.map (· ^ 2 ^ k)) y := by
  rw [ringWeight, Ring.ringWeight_fold, zero_add, idxSum_eq_sum_range]

/-! ## Slices and the column -/

/-- Bit slice `i` of a word column, extended at `pt` over `2^(h + 6)` words. -/
def sliceExt (h : ℕ) (col : ℕ → K) (pt : List E) (i : ℕ) : E :=
  ∑ n ∈ Finset.range (2 ^ (h + 6)), eqAt pt n * bitE ((col n).toBitVec.getLsbD i)

/-- The word column, extended at `pt` over `2^(h + 6)` words. -/
def colExt (h : ℕ) (col : ℕ → K) (pt : List E) : E :=
  ∑ n ∈ Finset.range (2 ^ (h + 6)), eqAt pt n * ofK (col n)

/-- A word of `K` in `E` is its bits packed by the powers of `x`. -/
theorem ofK_eq_sum_bitE (a : K) : ofK a = ∑ i : Fin 64, ringW i * bitE (a.toBitVec.getLsbD i) := by
  conv_lhs => rw [K.eq_sum_bits a]
  change algebraMap K E _ = _
  rw [map_sum (algebraMap K E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold ringW
  split <;> simp_all [bitE]

/-- **The column at `pt^(2^k)` packs the slices' Frobenius**:
`q̂(pt^(2^k)) = Σ_i x^i ẑ_i(pt)^(2^k)`. -/
theorem colExt_frob (h : ℕ) (col : ℕ → K) (pt : List E) (k : ℕ) :
    colExt h col (pt.map (· ^ 2 ^ k)) = ∑ i : Fin 64, ringW i * sliceExt h col pt i ^ 2 ^ k := by
  simp only [colExt, sliceExt, ring_frob_sum, mul_pow, bitE_frob, eqAt_frob, ofK_eq_sum_bitE,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun n _ ↦ by ring

/-! ## The layout -/

/-- Word `n` of the block of a stack at `off`. -/
def qkAt {μ : ℕ} (off : ℕ) (q : Column μ) (n : ℕ) : K := q.values.toArray.getD (off + n) 0

/-- `q_keccak`'s words on a stack of the layout are the block's at its placement. -/
theorem qkOf_eq_qkAt (layout : Verifier.Layout) (q : Column layout.stackLog) :
    qkOf layout q = qkAt (layout.placement qkeccak).index q := rfl

/-- **What ring switching needs of the layout**: `q_keccak` is placed on `h + 6` variables, at an
offset aligned to its size, inside the stack. -/
structure RingLayoutHyp (layout : Verifier.Layout) (h off : ℕ) : Prop where
  /-- `q_keccak`'s placement: `h + 6` variables at `off`. -/
  placement : layout.placement qkeccak = { variableCount := h + 6, index := off }
  /-- The offset is aligned to the block's size. -/
  aligned : 2 ^ (h + 6) ∣ off
  /-- The block lies inside the stack. -/
  fits : off + 2 ^ (h + 6) ≤ 2 ^ layout.stackLog

/-- `eq_eval` against a cube point on as many coordinates is the equality weight `eqAt`. -/
theorem eqEval_boolPoint_eqAt : ∀ (p : List E) (y : ℕ), eqEval p (boolPoint p.length y) = eqAt p y
  | [], _ => by simp [eqEval, boolPoint]
  | r :: p, y => by
    rw [List.length_cons, Whir.Complete.boolPoint_succ, Whir.Complete.eqEval_cons,
      eqEval_boolPoint_eqAt p, eqAt_cons]
    congr 1
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy
    · simp [hy]
    · simp only [hy, decide_true, ↓reduceIte]
      linear_combination CharTwo.add_self_eq_zero (1 : E)

/-- **An aligned placement's weight at a cube point**: the indicator of the block times the
equality weight of the offset inside it. -/
theorem eqAbove_mul_eqEval_boolPoint {v off μ x : ℕ} (hfit : off + 2 ^ v ≤ 2 ^ μ) (hx : x < 2 ^ μ)
    (p : List E) (hp : p.length = v) :
    ({ variableCount := v, index := off } : Placement).eqAbove (boolPoint μ x) *
        eqEval p ((boolPoint μ x).take v) =
      if x / 2 ^ v = off / 2 ^ v then eqAt p (x % 2 ^ v) else 0 := by
  have hv : v ≤ μ := by
    have : 2 ^ v ≤ 2 ^ μ := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hpow : 2 ^ μ = 2 ^ v * 2 ^ (μ - v) := by rw [← pow_add, Nat.add_sub_cancel' hv]
  have hoff : off / 2 ^ v < 2 ^ (μ - v) :=
    Nat.div_lt_of_lt_mul (by rw [← hpow]; have := Nat.two_pow_pos v; omega)
  have hxv : x / 2 ^ v < 2 ^ (μ - v) := Nat.div_lt_of_lt_mul (by rw [← hpow]; exact hx)
  simp only [Placement.eqAbove, length_boolPoint, selectorPoint_eq_boolPoint,
    Nat.shiftRight_eq_div_pow, drop_boolPoint]
  rw [Complete.eqEval_boolPoint_boolPoint _ _ _ hoff hxv, take_boolPoint μ v x hv, ← hp,
    ← boolPoint_mod, eqEval_boolPoint_eqAt, hp]
  by_cases h : x / 2 ^ v = off / 2 ^ v
  · simp [h]
  · simp [h, Ne.symm h]

/-- **A sum over the stack weighted by an aligned placement** is the sum over the block. -/
theorem sum_placed {v off μ : ℕ} (hal : 2 ^ v ∣ off) (hfit : off + 2 ^ v ≤ 2 ^ μ) (p : List E)
    (hp : p.length = v) (q : Column μ) :
    ∑ x : Fin (2 ^ μ), ({ variableCount := v, index := off } : Placement).eqAbove (boolPoint μ x) *
        eqEval p ((boolPoint μ x).take v) * ofK (q.values.getD x 0) =
      ∑ n ∈ Finset.range (2 ^ v), eqAt p n * ofK (qkAt off q n) := by
  obtain ⟨t, rfl⟩ := hal
  have hpos := Nat.two_pow_pos v
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ ({ variableCount := v, index := 2 ^ v * t } :
      Placement).eqAbove
    (boolPoint μ x) * eqEval p ((boolPoint μ x).take v) * ofK (q.values.getD x 0))]
  have hsub : Finset.Ico (2 ^ v * t) (2 ^ v * t + 2 ^ v) ⊆ Finset.range (2 ^ μ) := fun x hx ↦ by
    simp only [Finset.mem_Ico] at hx
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub fun x hx hn ↦ ?_, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn' := Finset.mem_range.mp hn
    rw [eqAbove_mul_eqEval_boolPoint hfit (by omega) p hp,
      Nat.mul_add_div hpos, Nat.div_eq_of_lt hn', add_zero, Nat.mul_div_cancel_left _ hpos]
    simp only [↓reduceIte]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hn', qkAt]
    rfl
  · have hx := Finset.mem_range.mp hx
    rw [eqAbove_mul_eqEval_boolPoint hfit hx p hp, Nat.mul_div_cancel_left _ hpos]
    suffices hne : x / 2 ^ v ≠ t by simp [hne]
    intro he
    refine hn (Finset.mem_Ico.mpr ⟨?_, ?_⟩)
    · rw [← he]; exact Nat.mul_div_le x _
    · have := Nat.lt_mul_div_succ x hpos
      rw [he, mul_add, mul_one] at this
      exact this

/-! ## The ring claim on the stack -/

/-- **The ring claim paired with a stack** (any stack size `μ` the block fits in): with
`q_keccak` placed on `h + 6` variables at an aligned `off`, the pairing of the program's ring
claim at the drawn map `Φ = frobPhi 8 f g` is `Σ_i x^i Φ(ẑ_i(point))`. -/
theorem pair_ringClaim {layout : Verifier.Layout} {h off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h + 6, index := off })
    (hal : 2 ^ (h + 6) ∣ off) (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ) (q : Column μ) {pt : List E}
    (hpt : pt.length = h + 6) (f g : Fin 8 → E) (target : E) :
    ∑ x : Fin (2 ^ μ), (ringSwitchClaim layout target
        fun rPrime ↦ ringWeight pt rPrime (Ring.ringCoefficients (List.ofFn f) (List.ofFn g))).1
          (boolPoint μ x) * ofK (q.values.getD x 0) =
      ∑ i : Fin 64, ringW i * frobPhi 8 f g (sliceExt h (qkAt off q) pt i) := by
  simp only [ringSwitchClaim, hpl, ringWeight_eq_sum, Ring.length_ringCoefficients,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ k ∈ Finset.range 64,
      ∑ x : Fin (2 ^ μ), ({ variableCount := h + 6, index := off } : Placement).eqAbove
          (boolPoint μ x) *
          ((Ring.ringCoefficients (List.ofFn f) (List.ofFn g)).getD k 0 *
            eqEval (pt.map (· ^ 2 ^ k)) ((boolPoint μ x).take (h + 6))) *
          ofK (q.values.getD x 0) =
        (Ring.ringCoefficients (List.ofFn f) (List.ofFn g)).getD k 0 *
          ∑ i : Fin 64, ringW i * sliceExt h (qkAt off q) pt i ^ 2 ^ k := fun k _ ↦ by
    rw [← colExt_frob, colExt, ← sum_placed hal hfit _ (by rw [List.length_map, hpt]) q,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  rw [Finset.sum_congr rfl e]
  simp only [frobPhi_eq_idxSum, idxSum_eq_sum_range, Ring.length_ringCoefficients, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The ring claim holds exactly at the target's honest value**: the program's claim at the
drawn map holds of a stack iff the target is `Σ_i x^i Φ(ẑ_i(point))`. -/
theorem ringClaim_holds_iff {layout : Verifier.Layout} {h off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h + 6, index := off })
    (hal : 2 ^ (h + 6) ∣ off) (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ) (q : Column μ) {pt : List E}
    (hpt : pt.length = h + 6) (f g : Fin 8 → E) (target : E) :
    StackClaim.Holds μ (ringSwitchClaim layout target
        fun rPrime ↦ ringWeight pt rPrime (Ring.ringCoefficients (List.ofFn f) (List.ofFn g))) q ↔
      target = ∑ i : Fin 64, ringW i * frobPhi 8 f g (sliceExt h (qkAt off q) pt i) := by
  unfold StackClaim.Holds
  rw [pair_ringClaim hpl hal hfit q hpt f g, eq_comm]
  rfl

/-- **The stack's ring claim holds only at bad challenge lists** (`RingClaimBad`), against the
true slices `ẑ_i(point)` of the block. -/
theorem ringClaimBad_stack {layout : Verifier.Layout} {h off : ℕ}
    (hl : RingLayoutHyp layout h off) {pt : List E} (hpt : pt.length = h + 6) (sv : Fin 64 → E) :
    RingClaimBad (fun q : Column layout.stackLog ↦ fun i ↦ sliceExt h (qkAt off q) pt i) sv
      (fun r q ↦ StackClaim.Holds layout.stackLog (ringSwitchClaim layout r.1 r.2) q) pt := by
  intro q ch hch hq
  rw [ringBad_iff hch]
  have hq' := hq
  simp only [ringResult, take_eq_ofFn_fOf hch, drop_eq_ofFn_gOf hch] at hq'
  exact (ringClaim_holds_iff hl.placement hl.aligned hl.fits q hpt _ _ _).1 hq'

/-! ## The verifier's layout -/

/-- **The verifier's layout places `q_keccak` as ring switching needs**: on `τ_KECCAK + 6`
variables at its block's offset, aligned and inside the stack. -/
theorem ringLayoutHyp_verifierLayout (prog : LeanIsaProgram) (s : Sizes) :
    RingLayoutHyp (verifierLayout prog s) (s.τ 5) ((blocks prog s).offset (keccakBlock prog s)) where
  placement := placement_qkeccak prog s
  aligned := by
    have h := (blocks prog s).pow_size_dvd_offset (keccakBlock prog s)
    rwa [size_keccakBlock] at h
  fits := by
    have h1 := (blocks prog s).offset_add_pow_le_total (keccakBlock prog s)
    have h2 := blocks_fits prog s
    rw [size_keccakBlock] at h1
    rw [stackLog_verifierLayout]
    omega

end
end LeanVM.Protocol.EndToEnd.Front
