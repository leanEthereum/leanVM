import Whir.ArrayLayout

/-! Exact refinement of the mutable sampler, including zero counts and repeated cosets.
The representation map discards only the symbolic stratum's bound proofs. -/
namespace Whir.SamplingRefinement
open Concrete ArrayLayout

def stratumPair {depth : Nat} (s : Layout.Stratum depth) : Nat × Nat :=
  (s.bits, s.index)

private def bitStrata (width count depth : Nat) : List (Layout.Stratum depth) :=
  ((List.range width).reverse).flatMap fun g =>
    if count.testBit g then Layout.stratumGroup depth g else []

private theorem bitStrata_mod (width count depth : Nat) :
    bitStrata width (count % 2 ^ width) depth = bitStrata width count depth := by
  unfold bitStrata
  apply congrArg List.flatten
  apply List.map_congr_left
  intro g hg
  have hg' : g < width := List.mem_range.mp (List.mem_reverse.mp hg)
  simp [Nat.testBit_mod_two_pow, hg']

private theorem bitStrata_eq (width count depth : Nat) (hc : count < 2 ^ width) :
    bitStrata width count depth = Layout.strataBits width count depth := by
  induction width generalizing count with
  | zero => simp [bitStrata, Layout.strataBits]
  | succ width ih =>
    have hp : 0 < 2 ^ width := by positivity
    have hbound : count < 2 ^ width * 2 := by simpa [pow_succ] using hc
    have hbit : count.testBit width = decide (2 ^ width ≤ count) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      apply decide_eq_decide.mpr
      have hdiv : count / 2 ^ width < 2 :=
        (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
      rw [Nat.mod_eq_of_lt hdiv]
      constructor
      · intro h
        have hm := Nat.div_mul_le_self count (2 ^ width)
        simpa [h] using hm
      · intro h
        have := (Nat.le_div_iff_mul_le hp).mpr (show 1 * 2 ^ width ≤ count by simpa using h)
        omega
    simp only [bitStrata, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.flatMap_cons, hbit, decide_eq_true_eq, Layout.strataBits]
    change (if 2 ^ width ≤ count then Layout.stratumGroup depth width else []) ++
      bitStrata width count depth = _
    by_cases h : 2 ^ width ≤ count
    · have hm : count % 2 ^ width = count - 2 ^ width := by
        have hdiv : count / 2 ^ width = 1 := by
          apply Nat.le_antisymm
          · have := (Nat.div_lt_iff_lt_mul hp).mpr (show count < 2 * 2 ^ width by omega); omega
          · exact (Nat.le_div_iff_mul_le hp).mpr (by simpa using h)
        have := Nat.mod_add_div count (2 ^ width)
        rw [hdiv, Nat.mul_one] at this
        omega
      rw [ite_eq_left h, ite_eq_left h, ← bitStrata_mod width count depth, hm,
        ih _ (by omega)]
    · simp only [ite_eq_right h, List.nil_append]
      exact ih _ (by omega)

private theorem groups_fold (gs : List Nat) (count depth : Nat)
    (out : Array (Nat × Nat)) :
    (gs.foldl (fun out g => if count.testBit g then
      (List.range (2 ^ g)).foldl (fun out j => out.push (min g depth, j % 2 ^ min g depth)) out
      else out) out).toList = out.toList ++
        (gs.flatMap fun g => if count.testBit g then Layout.stratumGroup depth g else []).map
          stratumPair := by
  induction gs generalizing out with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.map_append]
    rw [ih]
    cases count.testBit g <;>
      simp [Layout.stratumGroup, Layout.stratumAt, stratumPair,
        List.map_map, List.append_assoc]

/-- The executable high-to-low bit loop is exactly the bound-carrying specification. -/
theorem strata_toList (count depth : Nat) :
    (Concrete.strata count depth).toList =
      (Layout.strataBits (count.log2 + 1) count depth).map stratumPair := by
  unfold Concrete.strata
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind]
  simp only [← apply_ite (fun a : Array (Nat × Nat) =>
    (pure (.yield a) : Id (ForInStep (Array (Nat × Nat)))))]
  simp only [List.forIn_pure_yield_eq_foldl]
  change (List.foldl _ #[] (List.range (count.log2 + 1)).reverse).toList = _
  rw [groups_fold]
  simp only [List.nil_append]
  rw [← bitStrata, bitStrata_eq _ _ _ Nat.lt_log2_self]

theorem strata_eq (count depth : Nat) :
    Concrete.strata count depth =
      ((Layout.strataBits (count.log2 + 1) count depth).map stratumPair).toArray := by
  apply Array.toList_inj.mp
  simpa using strata_toList count depth

@[simp] theorem strata_size (count depth : Nat) :
    (Concrete.strata count depth).size = count := by
  have h := congrArg List.length (strata_toList count depth)
  simpa [Layout.strataBits_length _ _ _ Nat.lt_log2_self] using h

/-- Default-valued machine indexing agrees with the bounded symbolic stratum. -/
theorem strata_getElem! (count depth i : Nat) (hi : i < count) :
    (Concrete.strata count depth)[i]! =
      stratumPair ((Layout.strataBits (count.log2 + 1) count depth)[i]'(by
        rw [Layout.strataBits_length _ _ _ Nat.lt_log2_self]; exact hi)) := by
  rw [strata_eq]
  simp [getElem!_pos, Layout.strataBits_length _ _ _ Nat.lt_log2_self, hi]

/-- The exact production squeeze count makes every raw-word lookup in bounds. -/
theorem squeeze_index_lt {depth count : Nat} (hpos : 1 ≤ depth) (hmax : depth ≤ 64)
    (squeezes : Array E)
    (hs : squeezes.size = (count + 192 / depth - 1) / (192 / depth))
    (i : Nat) (hi : i < count) :
    i / (192 / depth) < squeezes.size := by
  have hp : 0 < 192 / depth := Layout.query_chunks_positive hpos (by omega)
  rw [hs]
  have hle : i / (192 / depth) * (192 / depth) ≤ i := Nat.div_mul_le_self _ _
  apply (Nat.lt_div_iff_mul_lt hp).mpr
  omega

/-- Raw extraction is the symbolic chunk extractor applied to the supplied E words. -/
theorem rawQuery_eq (depth : Nat) (squeezes : Array E) (i : Nat) :
    (squeezes[i / (192 / depth)]!.toNat / 2 ^ ((i % (192 / depth)) * depth)) %
        2 ^ depth =
      Layout.rawQuery depth (fun j => squeezes[j]!.toNat) i := rfl

/-- Exact successful sampler identity, preserving order and all duplicate queries.
No condition limits `count` to the domain size. -/
theorem deriveQueries_eq (depth count : Nat) (squeezes : Array E)
    (hpos : 1 ≤ depth) (hmax : depth ≤ 64)
    (hs : squeezes.size = (count + 192 / depth - 1) / (192 / depth)) :
    Concrete.deriveQueries depth count squeezes =
      some ((Layout.sampleQueries (count.log2 + 1) count depth
        (fun i => squeezes[i]!.toNat)).toArray) := by
  have hz : depth ≠ 0 := by omega
  have hn : ¬64 < depth := by omega
  simp [Concrete.deriveQueries, hz, hn, hs]
  apply Array.toList_inj.mp
  apply List.ext_getElem
  · simp [Layout.sampleQueries_length _ _ _ _ Nat.lt_log2_self]
  · intro i hi hj
    have hic : i < count := by simpa using hi
    simp only [toList_tab, List.getElem_map, List.getElem_range]
    rw [strata_getElem! count depth i hic, Layout.sampleQueries_order]
    rfl

/-- List-facing endpoint for the probability model. -/
theorem deriveQueries_toList (depth count : Nat) (squeezes : Array E)
    (hpos : 1 ≤ depth) (hmax : depth ≤ 64)
    (hs : squeezes.size = (count + 192 / depth - 1) / (192 / depth)) :
    (Concrete.deriveQueries depth count squeezes).map Array.toList =
      some (Layout.sampleQueries (count.log2 + 1) count depth
        (fun i => squeezes[i]!.toNat)) := by
  rw [deriveQueries_eq depth count squeezes hpos hmax hs]
  simp

end Whir.SamplingRefinement
