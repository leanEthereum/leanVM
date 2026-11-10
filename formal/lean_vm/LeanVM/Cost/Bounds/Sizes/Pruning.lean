module

public import LeanVM.Cost.Bounds.Sizes.Lane
public import LeanVM.Protocol.Extraction.Sound
public import LeanVM.Protocol.Whir.Params.Iface
public import LeanVM.Protocol.ToArkLib.Whir.Johnson

/-!
# Sizes along the decoder: the pruning's survivors, by the Johnson bound

At every admissible shape (`Whir.Admissible μ R`), after any `U ≥ 1` lanes at most `2^12` prefixes
survive the pruning the extractor runs (`pruneUpToDistinct_length_le_johnson`), and the decoder
returns at most `2^12` stacks (`decodeStacksDistinct_length_le_johnson`). The survivors' encodings
are distinct interleaved Reed–Solomon codewords on `U` lanes, close to the word's first `U` lanes
at the extractor's threshold (`length_pruneUpTo_le`, `evalTuple_mem_code`), so the Johnson bound on
`U` lanes (`card_le_jl`) caps them by level 0's list bound `listMax₀ ≤ 166`, as the soundness
statement's `card_candidates_le` does for all `2^6` lanes (`pruneUpTo_length_le`); the stacks by
`decodeStacks_length_le` at the deployed opening (`Whir.Params.openingIface`). Both are transported
along `pruneUpToDistinct_eq`/`pruneUpToFast_eq` and `decodeStacksDistinct_eq`/`decodeStacksFast_eq`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Extraction.Fast LeanVM.Extraction LeanVM.Parameters

public section

/-- **The pruning keeps few prefixes**: at every admissible shape, after any `U ≥ 1` lanes at most
`listMax₀ ≤ 166` prefixes survive. -/
theorem pruneUpTo_length_le {μ R : ℕ} (h : Whir.Admissible μ R) (W : ℕ → List K) {U : ℕ}
    (hU : 0 < U) :
    (pruneUpTo (μ - Whir.initialFold) R (johnsonThreshold μ R) W U).length ≤ 2 ^ 12 := by
  classical
  obtain ⟨level, rest, F⟩ :=
    Protocol.Whir.Params.level0Facts (Protocol.Whir.Params.shapeOK_of_admissible h)
  have hthr := Protocol.Whir.Params.johnsonThreshold_eq_thr0Of h
  have hlb : Protocol.EndToEnd.laneBits = Whir.initialFold := rfl
  have hn64 : μ - Whir.initialFold + R ≤ 64 := hlb ▸ F.h64
  have hdim : 2 ^ (μ - Whir.initialFold) - 1 + 1 = 2 ^ (μ - Whir.initialFold) :=
    Nat.sub_add_cancel Nat.one_le_two_pow
  set κ := μ - Whir.initialFold with hκ
  let dom := LaneProofs.domainEmb (2 ^ (κ + R)) (Nat.pow_le_pow_right (by norm_num) hn64)
  let O : Fin U → Fin (2 ^ (κ + R)) → K := fun u v ↦ laneSymbol W u v
  let T := Protocol.Whir.iList (ReedSolomon.code dom (2 ^ κ - 1 + 1)) (johnsonThreshold μ R) O
  have hT : ∀ cs : List (Array K), cs.length = U → (∀ u < U, (cs.getD u #[]).size = 2 ^ κ) →
      johnsonThreshold μ R ≤ (PruneProofs.commonCols κ R W cs U).length →
        PruneProofs.evalTuple κ R U cs ∈ T := by
    intro cs _ _ hA'
    rw [Protocol.Whir.mem_iList]
    refine ⟨fun u ↦ ?_, ?_⟩
    · rw [hdim]
      exact PruneProofs.evalTuple_mem_code hn64 cs u
    · refine ⟨Finset.univ.filter fun v : Fin (2 ^ (κ + R)) ↦
          v.val ∈ PruneProofs.commonCols κ R W cs U, ?_, ?_⟩
      · refine hA'.trans (le_of_eq ?_)
        have hnd : (PruneProofs.commonCols κ R W cs U).Nodup := (List.nodup_range).filter _
        rw [← List.toFinset_card_of_nodup hnd]
        symm
        refine Finset.card_bij (fun v _ ↦ v.val) (fun v hv ↦ ?_)
          (fun a _ b _ h ↦ Fin.ext h) (fun b hb ↦ ?_)
        · simpa using (Finset.mem_filter.mp hv).2
        · have hb' := List.mem_toFinset.mp hb
          have hlt : b < 2 ^ (κ + R) := by
            simp only [PruneProofs.commonCols, List.mem_filter, List.mem_range] at hb'
            exact hb'.1
          exact ⟨⟨b, hlt⟩, by simpa using hb', rfl⟩
      · intro u v hv
        have hv' := (Finset.mem_filter.mp hv).2
        simp only [PruneProofs.commonCols, List.mem_filter, List.mem_range,
          decide_eq_true_eq] at hv'
        exact (hv'.2 u u.isLt).symm
  have hgap : Fintype.card (Fin (2 ^ (κ + R))) * (2 ^ κ - 1) <
      johnsonThreshold μ R * johnsonThreshold μ R := by
    rw [Fintype.card_fin, hthr]
    exact F.hgap
  have hJ : T.card ≤ Protocol.Whir.jl (Fintype.card (Fin (2 ^ (κ + R))))
      (johnsonThreshold μ R) (2 ^ κ - 1) :=
    Protocol.Whir.card_le_jl T (Protocol.Whir.agreeSet O) (johnsonThreshold μ R)
      (2 ^ κ - 1)
      (fun _ hV ↦ Protocol.Whir.le_card_agreeSet_of_mem_iList hV)
      (fun V hV V' hV' hne ↦ (Finset.card_le_card (Protocol.Whir.agreeSet_inter_subset O V V')).trans
        (Nat.lt_succ_iff.mp (Protocol.Whir.card_agreeSet_lt dom
          ((Protocol.Whir.mem_iList _ _ O V).mp hV).1 ((Protocol.Whir.mem_iList _ _ O V').mp hV').1
          hne)))
      hgap
  have hL : Protocol.Whir.jl (Fintype.card (Fin (2 ^ (κ + R))))
      (johnsonThreshold μ R) (2 ^ κ - 1) = Protocol.Whir.Params.listMax₀ μ R := by
    rw [Fintype.card_fin, hthr, F.hL]
    rfl
  calc _ ≤ T.card := PruneProofs.length_pruneUpTo_le (by omega) W hU T hT
    _ ≤ Protocol.Whir.Params.listMax₀ μ R := hL ▸ hJ
    _ ≤ 166 := Protocol.Whir.Params.listMax₀_le h
    _ ≤ 2 ^ 12 := by norm_num

/-- **At most `2^12` survivors after any `U ≥ 1` lanes**, at every admissible shape. -/
theorem pruneUpToDistinct_length_le_johnson {μ R : ℕ} (h : Whir.Admissible μ R) (W : ℕ → List K)
    {U : ℕ} (hU : 0 < U) :
    (pruneUpToDistinct (μ - Whir.initialFold) R (johnsonThreshold μ R) W U).length ≤ 2 ^ 12 := by
  rw [pruneUpToDistinct_eq (checkRedundant_johnson h), pruneUpToFast_eq]
  exact pruneUpTo_length_le h W hU

/-- **At most `2^12` decoded stacks**, at every admissible shape. -/
theorem decodeStacksDistinct_length_le_johnson {μ R : ℕ} (h : Whir.Admissible μ R)
    (W : ℕ → List K) : (decodeStacksDistinct μ R W).length ≤ 2 ^ 12 := by
  rw [decodeStacksDistinct_eq h, decodeStacksFast_eq]
  exact (LeanVM.Protocol.EndToEnd.Sound.decodeStacks_length_le
    Protocol.Whir.Params.openingIface h W).trans
    ((Protocol.Whir.Params.listMax₀_le h).trans (by norm_num))

end

end LeanVM.Cost.Bounds
