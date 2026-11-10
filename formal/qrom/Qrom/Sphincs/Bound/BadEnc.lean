module

public import Qrom.Sphincs.Bound.Split

@[expose] public section

/-!
# Encoding collisions in the data

A key's first valid encoding counter is found among the counters below any later counter, so the
event that a later counter repeats the key's word fixes that counter's low bits from the values
below it. Over uniform data it has probability at most `2^-128` for each layer, index and counter
(`Qrom.Sphincs.card_badEnc_le`).
-/

open FORS FORS.Security Concrete

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- Among the functions to `HashOutput`, those whose low bits at `c` are a function of the others are
a fraction `2^-128`. -/
theorem card_trunc_upd_le {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι)
    (V : (ι → HashOutput) → Digest) (hV : ∀ f y, V (Function.update f c y) = V f)
    (P : (ι → HashOutput) → Prop) [DecidablePred P] (hP : ∀ b, P b → truncateHash (b c) = V b) :
    ((Finset.univ.filter P).card : ℝ) ≤ (2 : ℝ)⁻¹ ^ 128 * Fintype.card (ι → HashOutput) := by
  let e := Equiv.piSplitAt c fun _ ↦ HashOutput
  let V' : ({j // j ≠ c} → HashOutput) → Digest := fun r ↦ V (e.symm (0, r))
  have hVe : ∀ b, V b = V' (e b).2 := by
    intro b
    have : e.symm (0, (e b).2) = Function.update b c 0 := by
      funext j
      by_cases hj : j = c
      · subst hj; simp [e, Equiv.piSplitAt]
      · simp [e, Equiv.piSplitAt, hj]
    simp only [V', this, hV]
  have hsub : (Finset.univ.filter P).card ≤
      (Finset.univ.filter fun b : ι → HashOutput ↦ truncateHash (b c) = V' (e b).2).card :=
    Finset.card_le_card fun b hb ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [← hVe]
      exact hP b hb
  have hcount : (Finset.univ.filter fun b : ι → HashOutput ↦ truncateHash (b c) = V' (e b).2).card =
      ∑ r : {j // j ≠ c} → HashOutput,
        (Finset.univ.filter fun z : HashOutput ↦ truncateHash z = V' r).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun b _ ↦ ⟨(e b).2, (e b).1⟩) ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
      exact hb
    · intro b₁ _ b₂ _ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      apply e.injective
      exact Prod.ext (eq_of_heq h2) h1
    · rintro ⟨r, y⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hy
      refine ⟨e.symm (y, r), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
        simpa [e, Equiv.piSplitAt] using hy
      · simp
  have htot : Fintype.card (ι → HashOutput) = 2 ^ 256 * Fintype.card ({j // j ≠ c} → HashOutput) := by
    rw [Fintype.card_congr e, Fintype.card_prod, card_hashOutput]
  have hle : ((Finset.univ.filter P).card : ℝ) ≤
      (2 : ℝ) ^ 128 * Fintype.card ({j // j ≠ c} → HashOutput) := by
    have : (Finset.univ.filter P).card ≤ 2 ^ 128 * Fintype.card ({j // j ≠ c} → HashOutput) := by
      refine hsub.trans (le_of_eq ?_)
      rw [hcount]
      simp only [card_trunc_fiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      ring
    exact_mod_cast this
  refine hle.trans (le_of_eq ?_)
  rw [htot]
  push_cast
  ring

/-- `encH` reads only the counters it tries. -/
theorem encH_congr_below {h h' : Key → HashOutput} (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    ∀ n c₀, (∀ j, c₀ ≤ j → j < c₀ + n → h (.enc lay tree leaf (BitVec.ofNat counterBits j)) =
      h' (.enc lay tree leaf (BitVec.ofNat counterBits j))) →
      encH h lay tree leaf n c₀ = encH h' lay tree leaf n c₀ := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro c₀ H
    simp only [encH]
    rw [H c₀ le_rfl (by omega), ih (c₀ + 1) fun j h1 h2 ↦ H j (by omega) (by omega)]

/-- What `encH` finds: the first counter whose value decodes, found by any search that reaches it. -/
theorem encH_spec (h : Key → HashOutput) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    ∀ n c₀ cw, encH h lay tree leaf n c₀ = some cw → ∃ j, c₀ ≤ j ∧ j < c₀ + n ∧
      cw.1 = BitVec.ofNat counterBits j ∧
      TargetSum.decodeDigest (truncateHash (h (.enc lay tree leaf (BitVec.ofNat counterBits j)))) =
        some cw.2 ∧
      (∀ j', c₀ ≤ j' → j' < j →
        TargetSum.decodeDigest (truncateHash (h (.enc lay tree leaf (BitVec.ofNat counterBits j')))) =
          none) ∧
      ∀ m, j < c₀ + m → encH h lay tree leaf m c₀ = some cw := by
  intro n
  induction n with
  | zero => intro _ _ h0; simp [encH] at h0
  | succ n ih =>
    intro c₀ cw hn
    simp only [encH] at hn
    split at hn
    · rename_i w hw
      cases hn
      refine ⟨c₀, le_rfl, by omega, rfl, hw, fun j' h1 h2 ↦ by omega, fun m hm ↦ ?_⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [encH, hw]
    · rename_i hw
      obtain ⟨j, h1, h2, h3, h4, h5, h6⟩ := ih (c₀ + 1) cw hn
      refine ⟨j, by omega, by omega, h3, h4, fun j' h1' h2' ↦ ?_, fun m hm ↦ ?_⟩
      · rcases Nat.eq_or_lt_of_le h1' with rfl | hlt
        · exact hw
        · exact h5 j' (by omega) h2'
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [encH, hw]
        exact h6 m' (by omega)

theorem decodeDigest_valid {x : Digest} {w : Encoding} (h : TargetSum.decodeDigest x = some w) :
    TargetSum.Valid w := by
  unfold TargetSum.decodeDigest at h
  split at h
  · cases h; assumption
  · cases h

/-- A counter that repeats a key's word. -/
def BadAt (d : Data) (i : Index) (lay : Layer) (c : Counter) : Prop :=
  ∃ cw : Counter × Encoding,
    encH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay) encodingAttemptLimit 0 = some cw ∧
    c ≠ cw.1 ∧ truncateHash (hOf d (.enc lay (treeIndexAt i lay) (leafIndexAt i lay) c)) =
      Completeness.pack cw.2

/-- The word found among the counters below `c`, packed. -/
def wordBelow (d : Data) (i : Index) (lay : Layer) (c : Counter) : Digest :=
  Completeness.pack (((encH (hOf d) lay (treeIndexAt i lay) (leafIndexAt i lay) c.toNat 0).map
    Prod.snd).getD ReferenceChoice.dummyWord)

theorem badAt_trunc {d : Data} {i : Index} {lay : Layer} {c : Counter} (hb : BadAt d i lay c) :
    truncateHash (d (some (.enc lay (treeIndexAt i lay) (leafIndexAt i lay) c))) = wordBelow d i lay c := by
  obtain ⟨cw, he, hne, ht⟩ := hb
  obtain ⟨j, -, hj, hcw, hdec, hbelow, hfind⟩ := encH_spec _ _ _ _ _ _ _ he
  have hlim : encodingAttemptLimit = 2 ^ counterBits := rfl
  have hc : c = BitVec.ofNat counterBits c.toNat := by simp
  have hdc : TargetSum.decodeDigest (truncateHash (hOf d (.enc lay (treeIndexAt i lay)
      (leafIndexAt i lay) c))) = some cw.2 := by
    rw [ht]
    exact Completeness.decodeDigest_pack _ (decodeDigest_valid hdec)
  have hlt : j < c.toNat := by
    rcases lt_trichotomy j c.toNat with h | h | h
    · exact h
    · exact absurd (hcw.trans (by rw [h, ← hc])) hne.symm
    · have := hbelow c.toNat (Nat.zero_le _) h
      rw [← hc, hdc] at this
      cases this
  have hfind' := hfind c.toNat (by omega)
  change truncateHash (hOf d _) = _
  rw [ht, wordBelow, hfind']
  rfl

theorem wordBelow_update (d : Data) (i : Index) (lay : Layer) (c : Counter) (y : HashOutput) :
    wordBelow (Function.update d (some (.enc lay (treeIndexAt i lay) (leafIndexAt i lay) c)) y) i lay c =
      wordBelow d i lay c := by
  unfold wordBelow
  congr 3
  refine encH_congr_below _ _ _ _ _ fun j _ hj ↦ ?_
  have hne : (some (Key.enc lay (treeIndexAt i lay) (leafIndexAt i lay) (BitVec.ofNat counterBits j)) :
      Option Key) ≠ some (.enc lay (treeIndexAt i lay) (leafIndexAt i lay) c) := by
    intro heq
    simp only [Option.some.injEq, Key.enc.injEq, true_and] at heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := c.isLt; omega)] at this
    omega
  simp only [hOf, Function.update_of_ne hne]

theorem badEnc_iff (d : Data) : BadEnc d ↔ ∃ i lay c, BadAt d i lay c := by
  unfold BadEnc BadAt
  constructor
  · rintro ⟨i, lay, cw, c, h1, h2, h3⟩; exact ⟨i, lay, c, cw, h1, h2, h3⟩
  · rintro ⟨i, lay, c, cw, h1, h2, h3⟩; exact ⟨i, lay, cw, c, h1, h2, h3⟩

open Classical in
/-- **Encoding collisions are rare**: the data has one with probability at most
`numLayers · 2^totalHeight · 2^32 · 2^-128`. -/
theorem card_badEnc_le :
    ((Finset.univ.filter BadEnc).card : ℝ) ≤
      (2 ^ totalHeight * numLayers * 2 ^ counterBits * (2 : ℝ)⁻¹ ^ 128) * Fintype.card Data := by
  have hsub : Finset.univ.filter BadEnc ⊆
      (Finset.univ : Finset (Index × Layer × Counter)).biUnion fun t ↦
        Finset.univ.filter fun d ↦ BadAt d t.1 t.2.1 t.2.2 := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, badEnc_iff] at hd
    obtain ⟨i, lay, c, h⟩ := hd
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨(i, lay, c), h⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hc' : ((Finset.univ.filter BadEnc).card : ℝ) ≤
      ∑ t : Index × Layer × Counter, ((Finset.univ.filter fun d ↦ BadAt d t.1 t.2.1 t.2.2).card : ℝ) := by
    exact_mod_cast hc
  have hb : ∀ t : Index × Layer × Counter,
      ((Finset.univ.filter fun d ↦ BadAt d t.1 t.2.1 t.2.2).card : ℝ) ≤
        (2 : ℝ)⁻¹ ^ 128 * Fintype.card Data := fun t ↦
    card_trunc_upd_le (ι := Option Key)
      (some (.enc t.2.1 (treeIndexAt t.1 t.2.1) (leafIndexAt t.1 t.2.1) t.2.2))
      (fun d ↦ wordBelow d t.1 t.2.1 t.2.2) (fun d y ↦ wordBelow_update d t.1 t.2.1 t.2.2 y)
      (fun d ↦ BadAt d t.1 t.2.1 t.2.2) fun d hd ↦ badAt_trunc hd
  refine hc'.trans ((Finset.sum_le_sum fun t _ ↦ hb t).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Index × Layer × Counter) : ℝ) = 2 ^ totalHeight * numLayers * 2 ^ counterBits := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_bitVec]
    push_cast
    ring
  rw [hcard]
  ring

end Qrom.Sphincs
