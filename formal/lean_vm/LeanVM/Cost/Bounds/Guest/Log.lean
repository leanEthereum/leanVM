module

public import LeanVM.Cost.Bounds.Guest.Basic
public import LeanVM.Cost.Bounds.FieldLib
public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.Step
public import LeanVM.Cost.Bounds.Decoder.PreTest
public import LeanVM.Cost.Decoder.Readers

/-!
# Bounds on the guest decoder's prices: the exponent of a power of `g`

The decoder reads counts and positions as exponents (`B1.Main.gLog`), compiled as `gLogD D`
(`Cost/Decoder/Log.lean`): the discrete logarithm `discreteLogWith D` in baby-step tables `D` the
decoder's top level builds once, then `gLogAt` (below `2^34`, else `0`):

* `giantSteps_cost` (`(t + 1)·(FL + 52)`, `FL` the binary search's price),
  `phResidue_cost`, `crtCombine_cost`, `phCandidate_cost`, `logCheck_cost`,
  **`discreteLogWith_cost`**: at most `122420` in the tables `discreteLogTables`;
* **`GLogBound P D G`**: a logarithm (`gLogDC`) in the tables `D` costs at most `G`, the
  hypothesis every bound of the decoder takes; **`gLog_bound`**: `GLogBound P discreteLogTables
  gLogPrice`, `gLogPrice = 122435 ≈ 2^16.90` (the exponents' bits priced at `64`);
* `gLogD_lt`: every count the decoder reads is below `2^34`;
* `powSqE_cost_lt`: `a^n` in `E` by squaring (`powSqEC`, `Bounds/Decoder/PreTest.lean`'s
  `powSqE_cost`), `n < 2^k`: `11 + 606·k`; `powSqK_cost_lt`: `5 + 73·k`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-! ## `a^n` in `E` -/

/-- `a^n` in `E`, `n < 2^k`, `k ≤ 64`: at most `11 + 606·k`. -/
theorem powSqE_cost_lt (hP : Includes P Decoder.powSqEC.costDeps) (a : E)
    (n k : ℕ) (hk0 : 0 < k) (hk : k ≤ 64) (hn : n < 2 ^ k) :
    machineCost P Decoder.powSqEC.costIdx [encodeValue a, encodeValue n] ≤
      11 + 606 * k := by
  have h64 : n < 2 ^ 64 := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hk)
  refine (LeanVM.Cost.Bounds.powSqE_cost P hP a n h64).trans ?_
  have := log2_lt_of hk0 hn
  nlinarith

/-- `a^n` in `K`, `n < 2^k`, `k ≤ 64`: at most `5 + 73·k`. -/
theorem powSqK_cost_lt (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c101.costDeps) (a : K)
    (n k : ℕ) (hk0 : 0 < k) (hk : k ≤ 64) (hn : n < 2 ^ k) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c101.costIdx [encodeValue a, encodeValue n] ≤
      5 + 73 * k := by
  have h64 : n < 2 ^ 64 := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hk)
  refine (powSq_cost P hP a n h64).trans ?_
  have := log2_lt_of hk0 hn
  nlinarith

/-! ## The baby-step tables -/

theorem length_powPairsBy (b : K) : ∀ (n j : ℕ) (y : K), (powPairsBy b n j y).length = n
  | 0, _, _ => rfl
  | n + 1, j, y => by rw [powPairsBy, List.length_cons, length_powPairsBy b n]

theorem mem_powPairsBy_lt (b : K) : ∀ (n j : ℕ) (y : K) (e : ℕ × ℕ), e ∈ powPairsBy b n j y →
    e.1 < 2 ^ 64 ∧ e.2 < j + n
  | 0, _, _, e, h => by simp [powPairsBy] at h
  | n + 1, j, y, e, h => by
    rw [powPairsBy, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨UInt64.toNat_lt _, by dsimp only; omega⟩
    · have := mem_powPairsBy_lt b n (j + 1) (y * b) e h
      omega

theorem babyTable_size (b : K) (s : ℕ) : (babyTable b s).size = s := by
  rw [babyTable, List.size_toArray, List.length_mergeSort, length_powPairsBy]

theorem wordTable_babyTable (b : K) (s : ℕ) (hs : s < 2 ^ 63) : WordTable (babyTable b s) := by
  refine ⟨by rw [babyTable_size]; exact hs, ?_⟩
  rintro ⟨k, v⟩ he
  obtain ⟨hv, rfl⟩ := (mem_babyTable b s k v).1 he
  exact ⟨UInt64.toNat_lt _, by omega⟩

/-! ## The search -/

/-- The binary search's price over a table of `n` entries. -/
@[expose] def findLanePrice (n : ℕ) : ℕ := 28 + 36 * (Nat.log2 n + 1)

theorem findLane_some_lt (T : Array (ℕ × ℕ)) (hT : WordTable T) (key : ℕ) {v : ℕ}
    (h : findLane T key 0 T.size = some v) : v < 2 ^ 64 :=
  (hT.2 _ (findLane_sound T key _ 0 T.size rfl le_rfl h)).2

theorem giantSteps_some_lt (T : Array (ℕ × ℕ)) (hT : WordTable T) (c : K) (s : ℕ) :
    ∀ (t k : ℕ) (y : K) {v : ℕ}, giantSteps T c s t k y = some v → v < 2 ^ 64 + s * (k + t)
  | 0, k, y, v, h => by simp [giantSteps] at h
  | t + 1, k, y, v, h => by
    rw [giantSteps] at h
    generalize hb : babyLookup T y = o at h
    cases o with
    | some j =>
      simp only [Option.some.injEq] at h
      subst h
      have := findLane_some_lt T hT _ hb
      have : s * k ≤ s * (k + (t + 1)) := Nat.mul_le_mul_left s (by omega)
      omega
    | none =>
      have := giantSteps_some_lt T hT c s t (k + 1) (y * c) h
      have : s * (k + 1 + t) = s * (k + (t + 1)) := by ring_nf
      omega

open Auto.LeanVM.Extraction.Fast in
/-- **The giant steps** (`Decoder.giantStepsC`), `t` of them: at most `(t + 1)·(FL + 52)`, `FL`
the binary search's price. -/
theorem giantSteps_cost (hP : Includes P Decoder.giantStepsC.costDeps) (T : Array (ℕ × ℕ))
    (hT : WordTable T) (c : K) (s : ℕ) (hs : s < 2 ^ 32) :
    ∀ (t k : ℕ) (y : K), t + k < 2 ^ 32 →
      machineCost P Decoder.giantStepsC.costIdx [encodeValue T, encodeValue c, encodeValue s,
        encodeValue t, encodeValue k, encodeValue y] ≤ (t + 1) * (findLanePrice T.size + 52)
  | 0, k, y, _ => by rw [Decoder.giantStepsC.costEq_zero P hP]; omega
  | t + 1, k, y, h => by
    rw [Decoder.giantStepsC.costEq_succ P hP, limbs_of_lt (by omega : t + 1 < 2 ^ 64)]
    have hf := findLane_cost P (by includes) T hT y.lane.toNat (UInt64.toNat_lt _) 0 T.size
      (by omega) le_rfl
    simp only [Nat.sub_zero] at hf
    unfold findLanePrice
    generalize hb : babyLookup T y = o
    cases o with
    | none =>
      have := giantSteps_cost hP T hT c s hs t (k + 1) (y * c) (by omega)
      unfold findLanePrice at this
      simp only [limbs_of_lt (by omega : k < 2 ^ 64), limbs_of_lt (by omega : k + 1 < 2 ^ 64),
        max_self]
      nlinarith
    | some j =>
      have hj := findLane_some_lt T hT _ hb
      have hsk : s * k < 2 ^ 64 := by
        calc s * k < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_lt hs (by omega)
          _ = 2 ^ 64 := by norm_num
      simp only [limbs_of_lt (by omega : k < 2 ^ 64), limbs_of_lt (by omega : s < 2 ^ 64), limbs_of_lt hj,
        limbs_of_lt hsk, max_self]
      have := max_le (limbs_le_two (x := j + s * k) (by omega)) (by norm_num : 1 ≤ 2)
      nlinarith

open Auto.LeanVM.Extraction.Fast in
/-- **A residue** (`Decoder.phResidueC`): `x^q` and the giant steps. -/
theorem phResidue_cost (hP : Includes P Decoder.phResidueC.costDeps) (q p s t : ℕ)
    (T : Array (ℕ × ℕ)) (hT : WordTable T) (c x : K) (hq : q < 2 ^ 64) (hp : p < 2 ^ 64)
    (hs : s < 2 ^ 32) (ht : t < 2 ^ 31) :
    machineCost P Decoder.phResidueC.costIdx [encodeValue q, encodeValue p, encodeValue s,
      encodeValue t, encodeValue T, encodeValue c, encodeValue x] ≤
      4696 + (t + 1) * (findLanePrice T.size + 52) := by
  rw [Decoder.phResidueC.costEq P hP]
  split_ifs with hx
  · omega
  · have h1 := powSqK_cost_lt P (by includes) x q 64 (by norm_num) le_rfl hq
    have h2 := giantSteps_cost P (by includes) T hT c s hs t 0 (x ^ q) (by omega)
    have hv : ∀ v, bsgs T c s t (x ^ q) = some v → v < 2 ^ 128 := fun v hv ↦ by
      have := giantSteps_some_lt T hT c s t 0 (x ^ q) hv
      have : s * (0 + t) < 2 ^ 63 := by
        calc s * (0 + t) < 2 ^ 32 * 2 ^ 31 := Nat.mul_lt_mul_of_lt_of_lt hs (by omega)
          _ = 2 ^ 63 := by norm_num
      omega
    have hl : limbCount ((bsgs T c s t (x ^ q)).getD 0) ≤ 2 := by
      generalize hb : bsgs T c s t (x ^ q) = o at hv
      cases o with
      | none => simp
      | some v => exact limbs_le_two (hv v rfl)
    rw [limbs_of_lt hp]
    generalize bsgs T c s t (x ^ q) = o at hl
    cases o <;> dsimp only at hl ⊢ <;> omega

open Auto.LeanVM.Extraction.Fast in
/-- The Chinese remainder theorem (`Decoder.crtCombineC`), on residues below `2^32`: at most `43`. -/
theorem crtCombine_cost (hP : Includes P Decoder.crtCombineC.costDeps)
    (r3 r5 r17 r257 r641 r65537 r6700417 : ℕ) (h3 : r3 < 2 ^ 32) (h5 : r5 < 2 ^ 32)
    (h17 : r17 < 2 ^ 32) (h257 : r257 < 2 ^ 32) (h641 : r641 < 2 ^ 32) (h65537 : r65537 < 2 ^ 32)
    (h6700417 : r6700417 < 2 ^ 32) :
    machineCost P Decoder.crtCombineC.costIdx [encodeValue r3, encodeValue r5, encodeValue r17,
      encodeValue r257, encodeValue r641, encodeValue r65537, encodeValue r6700417] ≤ 43 := by
  rw [Decoder.crtCombineC.costEq P hP]
  simp only [limbs_of_lt (by omega : r3 < 2 ^ 64), limbs_of_lt (by omega : r5 < 2 ^ 64),
    limbs_of_lt (by omega : r17 < 2 ^ 64), limbs_of_lt (by omega : r257 < 2 ^ 64),
    limbs_of_lt (by omega : r641 < 2 ^ 64), limbs_of_lt (by omega : r65537 < 2 ^ 64),
    limbs_of_lt (by omega : r6700417 < 2 ^ 64)]
  -- every product and partial sum is below `2^128`: each `max` of two limbs at most (each
  -- generalized, so that `omega` splits no `max`)
  have m1 : max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5)) (max (limbCount (12297829382473034410 * r3)) (limbCount (7378697629483820646 * r5))) ≤ 2 :=
    max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5) (by omega)) (max_le (limbs_le_two (x := 12297829382473034410 * r3) (by omega))
      (limbs_le_two (x := 7378697629483820646 * r5) (by omega)))
  generalize max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5)) (max (limbCount (12297829382473034410 * r3)) (limbCount (7378697629483820646 * r5))) = b1 at *
  have m2 : max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5)) (limbCount (1085102592571150095 * r17))) ≤ 2 :=
    max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17) (by omega)) (max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5) (by omega))
      (limbs_le_two (x := 1085102592571150095 * r17) (by omega)))
  generalize max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5)) (limbCount (1085102592571150095 * r17))) = b2 at *
  have m3 : max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17)) (limbCount (2296870857426870240 * r257))) ≤ 2 :=
    max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257) (by omega)) (max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17) (by omega))
      (limbs_le_two (x := 2296870857426870240 * r257) (by omega)))
  generalize max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17)) (limbCount (2296870857426870240 * r257))) = b3 at *
  have m4 : max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257)) (limbCount (16979062407938588850 * r641))) ≤ 2 :=
    max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641) (by omega)) (max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257) (by omega))
      (limbs_le_two (x := 16979062407938588850 * r641) (by omega)))
  generalize max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257)) (limbCount (16979062407938588850 * r641))) = b4 at *
  have m5 : max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641)) (limbCount (4611615650756935680 * r65537))) ≤ 2 :=
    max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537) (by omega)) (max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641) (by omega))
      (limbs_le_two (x := 4611615650756935680 * r65537) (by omega)))
  generalize max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641)) (limbCount (4611615650756935680 * r65537))) = b5 at *
  have m6 : max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537 + 10691053700478254925 * r6700417)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537)) (limbCount (10691053700478254925 * r6700417))) ≤ 2 :=
    max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537 + 10691053700478254925 * r6700417) (by omega)) (max_le (limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537) (by omega))
      (limbs_le_two (x := 10691053700478254925 * r6700417) (by omega)))
  generalize max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537 + 10691053700478254925 * r6700417)) (max (limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537)) (limbCount (10691053700478254925 * r6700417))) = b6 at *
  have m7 : max (limbCount (12297829382473034410 * r3)) 1 ≤ 2 := max_le (limbs_le_two (x := 12297829382473034410 * r3) (by omega)) (by norm_num)
  generalize max (limbCount (12297829382473034410 * r3)) 1 = b7 at *
  have m8 : max (limbCount (7378697629483820646 * r5)) 1 ≤ 2 := max_le (limbs_le_two (x := 7378697629483820646 * r5) (by omega)) (by norm_num)
  generalize max (limbCount (7378697629483820646 * r5)) 1 = b8 at *
  have m9 : max (limbCount (1085102592571150095 * r17)) 1 ≤ 2 := max_le (limbs_le_two (x := 1085102592571150095 * r17) (by omega)) (by norm_num)
  generalize max (limbCount (1085102592571150095 * r17)) 1 = b9 at *
  have m10 : max (limbCount (2296870857426870240 * r257)) 1 ≤ 2 := max_le (limbs_le_two (x := 2296870857426870240 * r257) (by omega)) (by norm_num)
  generalize max (limbCount (2296870857426870240 * r257)) 1 = b10 at *
  have m11 : max (limbCount (16979062407938588850 * r641)) 1 ≤ 2 := max_le (limbs_le_two (x := 16979062407938588850 * r641) (by omega)) (by norm_num)
  generalize max (limbCount (16979062407938588850 * r641)) 1 = b11 at *
  have m12 : max (limbCount (4611615650756935680 * r65537)) 1 ≤ 2 := max_le (limbs_le_two (x := 4611615650756935680 * r65537) (by omega)) (by norm_num)
  generalize max (limbCount (4611615650756935680 * r65537)) 1 = b12 at *
  have m13 : max (limbCount (10691053700478254925 * r6700417)) 1 ≤ 2 := max_le (limbs_le_two (x := 10691053700478254925 * r6700417) (by omega)) (by norm_num)
  generalize max (limbCount (10691053700478254925 * r6700417)) 1 = b13 at *
  have m14 := limbs_le_two (x := 12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537 + 10691053700478254925 * r6700417) (by omega)
  generalize limbCount (12297829382473034410 * r3 + 7378697629483820646 * r5 + 1085102592571150095 * r17 + 2296870857426870240 * r257 + 16979062407938588850 * r641 + 4611615650756935680 * r65537 + 10691053700478254925 * r6700417) = b14 at *
  omega

theorem phResidue_lt (q p s t : ℕ) (T : Array (ℕ × ℕ)) (c x : K) (hp : 0 < p) :
    phResidue q p s t T c x < p := by
  unfold phResidue; split_ifs
  · exact hp
  · exact Nat.mod_lt _ hp

/-- The seven tables' sizes and their binary searches' prices. -/
theorem findLanePrice_le {n k : ℕ} (hk : 0 < k) (h : n < 2 ^ k) :
    findLanePrice n ≤ 28 + 36 * k := by
  unfold findLanePrice
  have := log2_lt_of hk h
  omega

open Auto.LeanVM.Extraction.Fast in
/-- **The candidate exponent** (`Decoder.phCandidateC`) in the tables `discreteLogTables`: at most
`117723`. -/
theorem phCandidate_cost (hP : Includes P Decoder.phCandidateC.costDeps) (x : K) :
    machineCost P Decoder.phCandidateC.costIdx [encodeValue discreteLogTables, encodeValue x] ≤
      117723 := by
  rw [Decoder.phCandidateC.costEq P hP]
  have hT : ∀ (b : K) (s : ℕ), s < 2 ^ 63 → WordTable (babyTable b s) :=
    fun b s hs ↦ wordTable_babyTable b s hs
  have e1 : (discreteLogTables).1 = babyTable phBase3 3 := rfl
  have e2 : (discreteLogTables).2.1 = babyTable phBase5 5 := rfl
  have e3 : (discreteLogTables).2.2.1 = babyTable phBase17 17 := rfl
  have e4 : (discreteLogTables).2.2.2.1 = babyTable phBase257 257 := rfl
  have e5 : (discreteLogTables).2.2.2.2.1 = babyTable phBase641 641 := rfl
  have e6 : (discreteLogTables).2.2.2.2.2.1 = babyTable phBase65537 4096 := rfl
  have e7 : (discreteLogTables).2.2.2.2.2.2 = babyTable phBase6700417 65536 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  have r1 := phResidue_cost P (by includes) 6148914691236517205 3 3 1 _
    (hT phBase3 3 (by norm_num)) 1 x (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r2 := phResidue_cost P (by includes) 3689348814741910323 5 5 1 _
    (hT phBase5 5 (by norm_num)) 1 x (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r3 := phResidue_cost P (by includes) 1085102592571150095 17 17 1 _
    (hT phBase17 17 (by norm_num)) 1 x (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r4 := phResidue_cost P (by includes) 71777214294589695 257 257 1 _
    (hT phBase257 257 (by norm_num)) 1 x (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r5 := phResidue_cost P (by includes) 28778071877862015 641 641 1 _
    (hT phBase641 641 (by norm_num)) 1 x (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r6 := phResidue_cost P (by includes) 281470681808895 65537 4096 17 _
    (hT phBase65537 4096 (by norm_num)) phStride65537 x (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have r7 := phResidue_cost P (by includes) 2753074036095 6700417 65536 103 _
    (hT phBase6700417 65536 (by norm_num)) phStride6700417 x (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [babyTable_size, Nat.reduceAdd] at r1 r2 r3 r4 r5 r6 r7
  have f1 := findLanePrice_le (n := 3) (k := 2) (by norm_num) (by norm_num)
  have f2 := findLanePrice_le (n := 5) (k := 3) (by norm_num) (by norm_num)
  have f3 := findLanePrice_le (n := 17) (k := 5) (by norm_num) (by norm_num)
  have f4 := findLanePrice_le (n := 257) (k := 9) (by norm_num) (by norm_num)
  have f5 := findLanePrice_le (n := 641) (k := 10) (by norm_num) (by norm_num)
  have f6 := findLanePrice_le (n := 4096) (k := 13) (by norm_num) (by norm_num)
  have f7 := findLanePrice_le (n := 65536) (k := 17) (by norm_num) (by norm_num)
  have hc := crtCombine_cost P (by includes)
    (phResidue 6148914691236517205 3 3 1 (babyTable phBase3 3) 1 x)
    (phResidue 3689348814741910323 5 5 1 (babyTable phBase5 5) 1 x)
    (phResidue 1085102592571150095 17 17 1 (babyTable phBase17 17) 1 x)
    (phResidue 71777214294589695 257 257 1 (babyTable phBase257 257) 1 x)
    (phResidue 28778071877862015 641 641 1 (babyTable phBase641 641) 1 x)
    (phResidue 281470681808895 65537 4096 17 (babyTable phBase65537 4096) phStride65537 x)
    (phResidue 2753074036095 6700417 65536 103 (babyTable phBase6700417 65536) phStride6700417 x)
    ((phResidue_lt _ _ _ _ _ _ _ (by norm_num)).trans (by norm_num))
    ((phResidue_lt _ _ _ _ _ _ _ (by norm_num)).trans (by norm_num))
    ((phResidue_lt _ _ _ _ _ _ _ (by norm_num)).trans (by norm_num))
    ((phResidue_lt _ _ _ _ _ _ _ (by norm_num)).trans (by norm_num))
    ((phResidue_lt _ _ _ _ _ _ _ (by norm_num)).trans (by norm_num))
    ((phResidue_lt _ _ _ _ _ _ _ (by norm_num)).trans (by norm_num))
    ((phResidue_lt _ _ _ _ _ _ _ (by norm_num)).trans (by norm_num))
  omega

open Auto.LeanVM.Extraction.Fast in
/-- The check `g^n = x` (`Decoder.logCheckC`), `n < 2^64`: at most `4688`. -/
theorem logCheck_cost (hP : Includes P Decoder.logCheckC.costDeps) (x : K) (n : ℕ) (hn : n < 2 ^ 64) :
    machineCost P Decoder.logCheckC.costIdx [encodeValue x, encodeValue n] ≤ 4688 := by
  rw [Decoder.logCheckC.costEq P hP]
  have := powSqK_cost_lt P (by includes) g n 64 (by norm_num) le_rfl hn
  split_ifs <;> omega

open Auto.LeanVM.Extraction.Fast in
/-- **The discrete logarithm** (`discreteLogWithC`) in the tables `discreteLogTables`: at most
`122420`. -/
theorem discreteLogWith_cost (hP : Includes P Decoder.discreteLogWithC.costDeps) (x : K) :
    machineCost P Decoder.discreteLogWithC.costIdx [encodeValue discreteLogTables, encodeValue x] ≤
      122420 := by
  rw [Decoder.discreteLogWithC.costEq P hP]
  split_ifs
  · omega
  · have h1 := phCandidate_cost P (by includes) x
    have h2 := logCheck_cost P (by includes) x (phCandidate discreteLogTables x)
      (by unfold phCandidate crtCombine; omega)
    omega

/-- `gLogAt` (`gLogAtC`): at most `10`. -/
theorem gLogAt_cost (hP : Includes P Decoder.gLogAtC.costDeps) (o : Option ℕ)
    (ho : ∀ v, o = some v → v < 2 ^ 64) :
    machineCost P Decoder.gLogAtC.costIdx [encodeValue o] ≤ 10 := by
  rw [Decoder.gLogAtC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some v =>
    dsimp only
    rw [limbs_shift (by norm_num), limbs_two_pow (by norm_num), limbs_of_lt (ho v rfl)]
    split_ifs <;> omega

theorem discreteLogWith_lt (x : K) (v : ℕ) (h : discreteLogWith discreteLogTables x = some v) :
    v < 2 ^ 64 := by
  unfold discreteLogWith logCheck at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  unfold phCandidate crtCombine
  omega

/-- **The price of a logarithm** in the tables built (`gLogDC`): the search and the check. -/
@[expose] def gLogPrice : ℕ := 122435

theorem gLogD_lt (D : DiscreteLogTables) (x : E) : Decoder.gLogD D x < 2 ^ 34 := by
  unfold Decoder.gLogD Decoder.gLogAt
  split
  · split_ifs <;> omega
  · norm_num

/-- **A logarithm's price is at most `G`** (`gLogDC` in the tables `D`): the hypothesis the
decoder's bounds take, so that they are parametric in it. -/
abbrev GLogBound (D : DiscreteLogTables) (G : ℕ) : Prop :=
  ∀ x : E, machineCost P Decoder.gLogDC.costIdx [encodeValue D, encodeValue x] ≤ G

/-- **A logarithm in the tables built** (`gLogDC` at `discreteLogTables`): at most
`gLogPrice = 122435 ≈ 2^16.90`. -/
theorem gLog_bound (hP : Includes P Decoder.gLogDC.costDeps) :
    GLogBound P discreteLogTables gLogPrice := by
  intro x
  rw [Decoder.gLogDC.costEq P hP]
  have h1 := discreteLogWith_cost P (by includes) (x.limb 0)
  have h2 := gLogAt_cost P (by includes) _ (discreteLogWith_lt (x.limb 0))
  unfold gLogPrice
  omega

end

end LeanVM.Cost.Bounds.Guest
