/-
  LeanVM.Protocol.Keccak.Start

  The start of `verifyKeccak`: the segment and lane challenges, the committed middle-state value,
  and the first claim, a random combination of the fifty lane claims of the two segments.
-/

module

public import LeanVM.Protocol.Keccak.SlotWeights

/-!
# The first claim

`verify_keccak` (`crates/verifier/src/keccak.rs`) draws the segment challenge `r_seg` and
five lane challenges, reads `committed` and forms the first claim at the point `(r_pack, r_seg)`
with instance weights `eq(r_low, ·)` and position weights `eq(r_lane, ℓ)·x^z` (`firstClaim`). On a
candidate (`firstClaim_true`), the claim's sum is

  `Σ_m eq(r_seg, m) Σ_ℓ eq(r_lane, ℓ) · stepMle inst (lane ℓ of segment m's output)`,

a random combination of the fifty lane claims of the two segments (`doc/leanvm`
§`keccak:segments`, "The first claim"). The candidate is alive after `committed` when that value
opens the committed middle state (`OpenTrue`) and the first claim holds; before, when the
mismatch table `startDelta` (the fifty differences between the lanes' claimed and true values)
has a zero extension at the challenges drawn (`ZeroOn`). `startSpec`: the six challenges escape
at `L₀/|E|` each.

`sum_split`: the claims' (pack, segment) and instance sums are a sum over the steps with the
equality weights of `(r_low, r_pack)`, the reading of every claim on the committed states.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal

@[expose] public section

/-! ## Splitting the point -/

/-- A sum over (pack, segment) and instance, at `(b, seg)` and `a`, is a sum over the steps at
`a ++ b`, segment by segment. -/
theorem sum_split {P : ℕ} {a b seg : List E} (ha : a.length = 4) (hb : b.length = P)
    (G : ℕ → ℕ → E) :
    ∑ z ∈ range (2 ^ (P + 1)), eqAt (b ++ seg) z *
        ∑ i ∈ range 16, eqAt a i * G (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) =
      ∑ m ∈ range 2, eqAt seg m * ∑ x ∈ range (2 ^ (P + 4)), eqAt (a ++ b) x * G m x := by
  rw [pow_succ, mul_comm (2 ^ P) 2, sum_range_mul 2 (2 ^ P)]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  rw [show 2 ^ (P + 4) = 2 ^ P * 16 by rw [pow_add]; rfl, sum_range_mul (2 ^ P) 16,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have hy' := Finset.mem_range.1 hy
  have hd : (2 ^ P * m + y) / 2 ^ P = m := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hy', zero_add]
  have hmod : (2 ^ P * m + y) % 2 ^ P = y := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
  rw [eqAt_append, hb, hd, eqAt_mod b, hb, hmod, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  have e1 : (16 * y + i) / 2 ^ 4 = y := by omega
  have e2 : (16 * y + i) % 2 ^ 4 = i := by omega
  rw [eqAt_append a b (16 * y + i), ha, e1, eqAt_mod a (16 * y + i), ha, e2,
    show i + 16 * y = 16 * y + i by ring]
  ring

/-! ## The first claim -/

/-- The first claim's position weights: `eq(r_lane, ℓ)·x^z` (`keccak.rs`). -/
def firstWeights (lanesPt : List E) : List E :=
  (List.range keccakBits).map fun j ↦ (eqKernel lanesPt).getD (j / 64) 0 * eOfNat (2 ^ (j % 64))

/-- The first claim (`keccak.rs`). -/
def firstClaim (inst segment lanesPt output : List E) (committed : E) : KeccakClaim :=
  ⟨committed + (eqKernel segment).getD (keccakSegments - 1) 0 *
      dot ((eqKernel lanesPt).take 25) output,
    eqKernel (inst.take 4), inst.drop 4 ++ segment, firstWeights lanesPt⟩

theorem firstClaim_mu (inst segment lanesPt output : List E) (committed : E) :
    (firstClaim inst segment lanesPt output committed).mu = eqKernel (inst.take 4) := by
  simp only [firstClaim]

theorem firstClaim_point (inst segment lanesPt output : List E) (committed : E) :
    (firstClaim inst segment lanesPt output committed).point = inst.drop 4 ++ segment := by
  simp only [firstClaim]

theorem firstClaim_weights (inst segment lanesPt output : List E) (committed : E) :
    (firstClaim inst segment lanesPt output committed).weights = firstWeights lanesPt := by
  simp only [firstClaim]

theorem firstWeights_length (lanesPt : List E) : (firstWeights lanesPt).length = 1600 := by
  rw [firstWeights, List.length_map, List.length_range]; rfl

theorem firstClaim_shape {P : ℕ} {inst segment lanesPt output : List E} (committed : E)
    (hi : inst.length = P + 4) (hs : segment.length = 1) :
    ClaimShape P (firstClaim inst segment lanesPt output committed) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [firstClaim_mu, eqKernel_length, List.length_take, hi, min_eq_left (by omega)]; rfl
  · rw [firstClaim_point, List.length_append, List.length_drop, hi, hs]; omega
  · rw [firstClaim_weights]; exact firstWeights_length lanesPt

/-- The first claim's weights read a state's lanes as words. -/
theorem sum_firstWeights {lanesPt : List E} (hl : lanesPt.length = 5) (a : KeccakState) :
    ∑ j ∈ range 1600, (firstWeights lanesPt).getD j 0 * bitE (sbit a j) =
      ∑ l ∈ range 25, eqAt lanesPt l * ofK (laneWord a l) := by
  rw [show 1600 = 25 * 64 from rfl, sum_range_mul]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [laneWord, ofK_ofLane, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have hj : 64 * l + z < 1600 := by omega
  rw [firstWeights, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa [keccakBits] using hj)]
  simp only [Option.map_some, Option.getD_some]
  have e1 : (64 * l + z) / 64 = l := by omega
  have e2 : (64 * l + z) % 64 = z := by omega
  rw [e1, e2, eqKernel_getD, hl, ite_eq_left (by omega), sbit_lane a l hz']
  ring

variable (h : ℕ)

/-- **The first claim on a candidate**: the lanes of the two segments' outputs, combined. -/
theorem firstClaim_sum (P : ℕ) (hP : h = P + 4) (col : ℕ → K) {inst segment lanesPt : List E}
    (hi : inst.length = h) (hl : lanesPt.length = 5) (output : List E) (committed : E) :
    claimSum (statesAt h col 0) P (firstClaim inst segment lanesPt output committed).point
        (firstClaim inst segment lanesPt output committed).mu
        (firstClaim inst segment lanesPt output committed).weights =
      ∑ m ∈ range 2, eqAt segment m * ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col m 12 x) l) := by
  subst hP
  have ha : (inst.take 4).length = 4 := by simp [hi]
  have hb : (inst.drop 4).length = P := by simp [hi]
  simp only [firstClaim, claimSum, stAt]
  have hmu : ∀ i ∈ range 16, (eqKernel (inst.take 4)).getD i 0 = eqAt (inst.take 4) i :=
    fun i hi' ↦ by
      rw [eqKernel_getD, ha, ite_eq_left (show i < 2 ^ 4 by
        have := Finset.mem_range.1 hi'; simpa using this)]
  have e : ∀ z, ∑ i ∈ range 16, (eqKernel (inst.take 4)).getD i 0 * ∑ j ∈ range 1600,
      (firstWeights lanesPt).getD j 0 * bitE (statesAt (P + 4) col 0 (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) j) =
      ∑ i ∈ range 16, eqAt (inst.take 4) i * (fun m x ↦ ∑ l ∈ range 25, eqAt lanesPt l *
        ofK (laneWord (segState (P + 4) col m 12 x) l)) (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) := by
    intro z
    refine Finset.sum_congr rfl fun i hi' ↦ ?_
    rw [hmu i hi']
    exact congrArg _ (sum_firstWeights hl _)
  simp only [e]
  rw [sum_split ha hb (fun m x ↦ ∑ l ∈ range 25, eqAt lanesPt l *
    ofK (laneWord (segState (P + 4) col m 12 x) l)), List.take_append_drop]
  refine Finset.sum_congr rfl fun m _ ↦ congrArg _ ?_
  simp only [stepMle, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

/-! ## The mismatch table -/

/-- The committed middle state's lane `l` at `inst`. -/
def midMle (col : ℕ → K) (inst : List E) (l : ℕ) : E := stepMle h inst (fun x ↦ col (x + 2 ^ h * (25 + l)))

/-- The fifty mismatches, index `m + 2ℓ`: segment `0`'s output against the committed middle
state, segment `1`'s output against the claimed `output`. -/
def startDelta (col : ℕ → K) (inst output : List E) (u : ℕ) : E :=
  if u / 2 < 25 then
    (if u % 2 = 0 then stepMle h inst (fun x ↦ laneWord (segState h col 0 12 x) (u / 2)) +
        midMle h col inst (u / 2)
      else stepMle h inst (fun x ↦ laneWord (segState h col 1 12 x) (u / 2)) +
        output.getD (u / 2) 0)
  else 0

theorem add_eq_zero_iff_E {a b : E} : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- A zero mismatch table: the middle-state and output claims hold. -/
theorem claims_of_zeroOn (col : ℕ → K) (inst output : List E)
    (hz : ZeroOn (startDelta h col inst output) [] 6) :
    outClaimsTrueMid h col inst output ∧ midAgree h col inst := by
  rw [zeroOn_nil] at hz
  refine ⟨fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · have := hz (1 + 2 * l) (by omega)
    have e1 : (1 + 2 * l) / 2 = l := by omega
    have e2 : (1 + 2 * l) % 2 = 1 := by omega
    rw [startDelta, e1, e2, ite_eq_left hl, ite_eq_right (by norm_num)] at this
    exact add_eq_zero_iff_E.1 this
  · have := hz (2 * l) (by omega)
    have e1 : 2 * l / 2 = l := by omega
    have e2 : 2 * l % 2 = 0 := by omega
    rw [startDelta, e1, e2, ite_eq_left hl, ite_eq_left rfl] at this
    exact add_eq_zero_iff_E.1 this

/-- The candidate's state after `committed`: the value opens the committed middle state. -/
def OpenTrue (col : ℕ → K) (inst segment lanesPt : List E) (committed : E) : Prop :=
  committed = eqAt segment 0 * ∑ l ∈ range 25, eqAt lanesPt l * midMle h col inst l

/-- **After `committed`**: an open value and a true first claim leave the mismatch table's
extension zero at the challenges. -/
theorem zeroOn_of_first (P : ℕ) (hP : h = P + 4) (col : ℕ → K) {inst segment lanesPt output : List E}
    (hi : inst.length = h) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (ho : output.length = 25) (committed : E)
    (hopen : OpenTrue h col inst segment lanesPt committed)
    (htrue : ClaimTrue (statesAt h col 0) P (firstClaim inst segment lanesPt output committed)) :
    ZeroOn (startDelta h col inst output) (segment ++ lanesPt) 6 := by
  rw [zeroOn_full _ (by simp [hs, hl])]
  rw [ClaimTrue, firstClaim_sum h P hP col hi hl] at htrue
  have hdot : dot ((eqKernel lanesPt).take 25) output =
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
    rw [dot_eq _ _ (by simp [eqKernel_length, hl, ho])]
    simp only [List.length_take, eqKernel_length, hl]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
      ← List.getD_eq_getElem?_getD, eqKernel_getD, hl, ite_eq_left (by omega)]
  have hseg : (eqKernel segment).getD (keccakSegments - 1) 0 = eqAt segment 1 := by
    rw [eqKernel_getD, hs]; rfl
  change committed + (eqKernel segment).getD (keccakSegments - 1) 0 *
    dot ((eqKernel lanesPt).take 25) output = _ at htrue
  rw [hseg, hdot] at htrue
  -- the sum over the 64 indices, split into segment and lane
  have hsplit : ∑ w ∈ range (2 ^ 6), eqAt (segment ++ lanesPt) w * startDelta h col inst output w =
      ∑ m ∈ range 2, eqAt segment m * ∑ l ∈ range 32, eqAt lanesPt l *
        startDelta h col inst output (2 * l + m) := by
    rw [show 2 ^ 6 = 32 * 2 from rfl, sum_range_mul 32 2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have hm' := Finset.mem_range.1 hm
    have e1 : (2 * l + m) / 2 = l := by omega
    rw [eqAt_append, hs, eqAt_mod segment, hs, pow_one, e1,
      show (2 * l + m) % 2 = m by omega]
    ring
  have hzero : ∀ m < 2, ∑ x ∈ range 7, eqAt lanesPt (25 + x) *
      startDelta h col inst output (2 * (25 + x) + m) = 0 := fun m hm ↦
    Finset.sum_eq_zero fun x _ ↦ by
      rw [startDelta, ite_eq_right (by omega), mul_zero]
  have hm0 : ∑ l ∈ range 32, eqAt lanesPt l * startDelta h col inst output (2 * l + 0) =
      ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col 0 12 x) l) +
      ∑ l ∈ range 25, eqAt lanesPt l * midMle h col inst l := by
    rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 0 (by norm_num), add_zero,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [startDelta, ite_eq_left (by omega), ite_eq_left (by omega),
      show (2 * l + 0) / 2 = l by omega, mul_add]
  have hm1 : ∑ l ∈ range 32, eqAt lanesPt l * startDelta h col inst output (2 * l + 1) =
      ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col 1 12 x) l) +
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
    rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 1 (by norm_num), add_zero,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [startDelta, ite_eq_left (by omega), ite_eq_right (by omega),
      show (2 * l + 1) / 2 = l by omega, mul_add]
  rw [hsplit, Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
    Finset.sum_range_zero, zero_add, hm0, hm1]
  rw [Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0), Finset.sum_range_zero,
    zero_add] at htrue
  rw [OpenTrue] at hopen
  linear_combination (-1 : E) * htrue + (-1 : E) * hopen +
    (CharTwo.two_eq_zero (R := E)) * (eqAt segment 1 *
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 + committed)

end
end LeanVM.Protocol.KeccakGkr
