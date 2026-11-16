module

public import Quantum.Xmss.Assembly.ReparamR0
public import Quantum.Xmss.Classify

@[expose] public section

/-!
# No top-layer trial block is a programmed `k` cell

A top key's randomizer grind reads, at each trial, the `k` cell of the one-block message-digest
input (`TopTrialBlock`). `TrialsOff L`: none of these blocks is a `k` cell of `tableHw L` (GameT),
so no trial reads a cell the game programs. Here the tables violating it are bounded.

**Over abstract types** (with PathBad's rounds `rnK`, `rnZ`, `famK`, `famZ`). A fixed finite set
`T` of rates:

* `EvT`, `card_mul_sum_evT_le`: round `a` (not the first) has its `k`-cell in `T`, the `h`-cells
  of the earlier rounds injective; resampling `h` at the previous round's `h`-cell moves the
  `k`-cell uniformly, so at most `|T| / |X|` of `h`.
* `card_mul_sum_trialHit_le`, `frac_pathTrial_le`: with distinct first blocks and at most `N`
  rounds, `PermGood π G` and a later `k`-cell in `T` for at most
  `N² / |X| + N² (G + 1) / |Z| + N |T| / |X|` (PathBad's collision fraction for the injectivity).

**leanXMSS.** `trialSet`: the top trial blocks, at most `2^416` (`2^128` parameters, `2^32` keys,
`2^128` digests and randomizers). A first `k`-cell names an in-table slot (`slotOfBlock_cellK_zero`)
while a trial block's address is a message digest's (type `12`, `not_inTable_of_topTrialBlock`), so
`TrialBad` (a `k`-cell of an in-table slot is a trial block) gives a later `k`-cell in `trialSet`
(`exists_rnd_of_trialBad`).

* `trialBad_frac_le`, `trialBad_frac_le_keccak`: `TrialBad` of the public data and hidden values for
  at most the bad permutations plus the bound above; `2^-400` at Keccak's sizes (`G = 18`).
* `trialBad_of_r0G`: on ReparamR0's good set `r0G treeQ 18`, `¬TrialsOff L` gives `TrialBad` at the
  coordinates (`r0E_hpath`: the table's `k` cells are the template's hidden `k`-cells).
* `trialsOff_r0G_frac_le_keccak`: `r0G treeQ 18 ∧ ¬TrialsOff` for at most `2^-400` of the padded
  tables; `trialsOff_frac_le_keccak`: `¬TrialsOff` for at most `2^-173` of the honest tables
  (with `r0G_frac_le_keccak`'s `2^-174`).
-/

open scoped ENNReal

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Over abstract types -/

section generic

variable {X Z S : Type} [AddCommGroup X] [AddCommGroup Z]

omit [AddCommGroup Z] in
/-- A translate `r + β + b` lies in `T` for at most `|T|` values `β`. -/
theorem sum_ite_add_mem_le [Fintype X] [DecidableEq X] (r b : X) (T : Finset X) :
    ∑ β : X, (if r + β + b ∈ T then 1 else 0) ≤ T.card := by
  rw [← Finset.card_filter]
  exact Finset.card_le_card_of_injOn (fun β ↦ r + β + b)
    (fun β hβ ↦ Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hβ)).2)
    fun β₁ _ β₂ _ e ↦ add_left_cancel (add_right_cancel e)

/-- **A later `k`-cell lies in `T`**: round `a` is not the first, the `h`-cells of the rounds
before it are injective, and its `k`-cell is in `T`. -/
def EvT (π : Equiv.Perm (X × Z)) (blk : S → ℕ → X) (R : Finset (S × ℕ)) (T : Finset X)
    (a : S × ℕ) (h : Z → X) (k k' : X → Z) : Prop :=
  (1 ≤ a.2 ∧ InjBelow R (famZ π blk h k k') a.2) ∧ famK π blk h k k' a ∈ T

open scoped Classical in
/-- **A later `k`-cell lies in `T`** for at most `|T| / |X|` of `h`. -/
theorem card_mul_sum_evT_le [Fintype X] [Fintype Z] [DecidableEq Z] {π : Equiv.Perm (X × Z)}
    {blk : S → ℕ → X} {R : Finset (S × ℕ)} (hR : DownClosed R) {a : S × ℕ} (ha : a ∈ R)
    (T : Finset X) (k k' : X → Z) :
    Fintype.card X * ∑ h : Z → X, (if EvT π blk R T a h k k' then 1 else 0) ≤
      Fintype.card (Z → X) * T.card := by
  obtain ⟨p, j⟩ := a
  rcases j with _ | j₀
  · have h0 : ∀ h, ¬EvT π blk R T (p, 0) h k k' := fun _ hE ↦ Nat.not_succ_le_zero 0 hE.1.1
    simp only [h0, ite_false, Finset.sum_const_zero, mul_zero]
    exact Nat.zero_le _
  · have hp : (p, j₀) ∈ R := hR _ ha j₀ (Nat.le_succ j₀)
    refine card_mul_sum_le_of_moving _ (fun h ↦ InjBelow R (famZ π blk h k k') (j₀ + 1))
      (fun h ↦ famK π blk h k k' (p, j₀ + 1) ∈ T) (fun h ↦ rnZ π h k k' (blk p) j₀) T.card
      (fun h hE ↦ ⟨hE.1.2, hE.2⟩) (fun h hP β ↦ ?_) (fun h hP ↦ ?_)
    · exact ⟨injBelow_congr (fun x hx hxj ↦ (fam_eq_h hR hp hP β hx (by omega)).2.2) hP,
        (fam_eq_h hR hp hP β hp le_rfl).2.2⟩
    · refine (sum_ite_le_of_imp _ (fun β ↦ rnR π h k k' (blk p) j₀ + β + blk p (j₀ + 1) ∈ T)
        fun β hβ ↦ ?_).trans (sum_ite_add_mem_le _ _ T)
      have hAp := agree_h hR hp hP β hp (by omega) fun i' hi' e ↦
        (show i' ≠ j₀ by omega) (congrArg Prod.snd e)
      have hKa : famK π blk (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' (p, j₀ + 1) =
          rnR π h k k' (blk p) j₀ + β + blk p (j₀ + 1) := by
        show (rnSt π (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' (blk p) (j₀ + 1)).1 +
          blk p (j₀ + 1) = _
        rw [rnSt_succ, rnR_congr hAp rfl, rnZ_congr hAp rfl rfl, Function.update_self]
      show rnR π h k k' (blk p) j₀ + β + blk p (j₀ + 1) ∈ T
      rw [← hKa]
      exact hβ

open scoped Classical in
/-- **A later `k`-cell of paths with distinct `h`-cells lies in `T`** for at most `|R| |T| / |X|`
of the keys `h`, `k`, `k'`. -/
theorem card_mul_sum_trialHit_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {π : Equiv.Perm (X × Z)}
    {blk : S → ℕ → X} {R : Finset (S × ℕ)} (hR : DownClosed R) (T : Finset X) :
    Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if Set.InjOn (famZ π blk t.1 t.2.1 t.2.2) R ∧
          ∃ a ∈ R, 1 ≤ a.2 ∧ famK π blk t.1 t.2.1 t.2.2 a ∈ T then 1 else 0) ≤
      Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) * (R.card * T.card) := by
  set M := Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z)
  have hpt : ∀ t : (Z → X) × (X → Z) × (X → Z),
      (if Set.InjOn (famZ π blk t.1 t.2.1 t.2.2) R ∧
        ∃ a ∈ R, 1 ≤ a.2 ∧ famK π blk t.1 t.2.1 t.2.2 a ∈ T then 1 else 0) ≤
        ∑ a ∈ R, (if EvT π blk R T a t.1 t.2.1 t.2.2 then 1 else 0) := by
    intro t
    by_cases hb : Set.InjOn (famZ π blk t.1 t.2.1 t.2.2) R ∧
        ∃ a ∈ R, 1 ≤ a.2 ∧ famK π blk t.1 t.2.1 t.2.2 a ∈ T
    · rw [ite_eq_left hb]
      obtain ⟨hinj, a, ha, h1, hT⟩ := hb
      have hE : EvT π blk R T a t.1 t.2.1 t.2.2 := ⟨⟨h1, fun x hx y hy _ _ e ↦
        hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) e⟩, hT⟩
      calc 1 = (if EvT π blk R T a t.1 t.2.1 t.2.2 then 1 else 0) := (ite_eq_left hE).symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun a ↦ if EvT π blk R T a t.1 t.2.1 t.2.2 then 1 else 0)
            (fun _ _ ↦ Nat.zero_le _) ha
    · rw [ite_eq_right hb]
      exact Nat.zero_le _
  calc Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if Set.InjOn (famZ π blk t.1 t.2.1 t.2.2) R ∧
          ∃ a ∈ R, 1 ≤ a.2 ∧ famK π blk t.1 t.2.1 t.2.2 a ∈ T then 1 else 0)
      ≤ Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
          ∑ a ∈ R, (if EvT π blk R T a t.1 t.2.1 t.2.2 then 1 else 0) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun t _ ↦ hpt t)
    _ = ∑ a ∈ R, Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
          (if EvT π blk R T a t.1 t.2.1 t.2.2 then 1 else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _a ∈ R, M * T.card := Finset.sum_le_sum fun a ha ↦
        card_mul_sum_triple_le₁ (fun h k k' ↦ if EvT π blk R T a h k k' then 1 else 0) _ _
          fun k k' ↦ card_mul_sum_evT_le hR ha T k k'
    _ = M * (R.card * T.card) := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

open scoped Classical in
/-- **The trial-hit fraction.** If the coordinates `Y` are `(q, (h, k, k'))`, each `q` fixing a
permutation `π q` and paths over `I` with distinct first blocks and at most `N` rounds in all, and
the event `Bd` gives a `PermGood (π q) G` permutation and a later `k`-cell in `T`, then `Bd` holds
for at most a fraction `N² / |X| + N² (G + 1) / |Z| + N |T| / |X|` of `Y`. -/
theorem frac_pathTrial_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq S]
    {Q Y : Type} [Fintype Q] [Nonempty Q] [Fintype Y] (e : Q × ((Z → X) × (X → Z) × (X → Z)) ≃ Y)
    (πf : Q → Equiv.Perm (X × Z)) (blk : Q → S → ℕ → X) (len : Q → S → ℕ) (I : Finset S)
    (hfirst : ∀ q, Set.InjOn (fun p ↦ blk q p 0) I) (G N : ℕ)
    (hN : ∀ q, (rnds I (len q)).card ≤ N) (T : Finset X) (Bd : Y → Prop) [DecidablePred Bd]
    (hBd : ∀ q t, Bd (e (q, t)) → PermGood (πf q) G ∧
      ∃ a ∈ rnds I (len q), 1 ≤ a.2 ∧ famK (πf q) (blk q) t.1 t.2.1 t.2.2 a ∈ T) :
    (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card ≤
      ((N * N : ℕ) : ℝ≥0∞) / Fintype.card X + ((N * N * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ((N * T.card : ℕ) : ℝ≥0∞) / Fintype.card X := by
  have : Nonempty X := ⟨0⟩
  have : Nonempty Z := ⟨0⟩
  have hsub := card_filter_le_add_of_imp Bd
    (fun y ↦ PermGood (πf (e.symm y).1) G ∧ ¬Set.InjOn (famZ (πf (e.symm y).1) (blk (e.symm y).1)
      (e.symm y).2.1 (e.symm y).2.2.1 (e.symm y).2.2.2) (rnds I (len (e.symm y).1)))
    (fun y ↦ Set.InjOn (famZ (πf (e.symm y).1) (blk (e.symm y).1) (e.symm y).2.1
      (e.symm y).2.2.1 (e.symm y).2.2.2) (rnds I (len (e.symm y).1)) ∧
      ∃ a ∈ rnds I (len (e.symm y).1), 1 ≤ a.2 ∧
        famK (πf (e.symm y).1) (blk (e.symm y).1) (e.symm y).2.1 (e.symm y).2.2.1
          (e.symm y).2.2.2 a ∈ T)
    fun y hy ↦ by
      have hq := hBd (e.symm y).1 (e.symm y).2 (by rwa [Prod.mk.eta, Equiv.apply_symm_apply])
      by_cases hi : Set.InjOn (famZ (πf (e.symm y).1) (blk (e.symm y).1) (e.symm y).2.1
          (e.symm y).2.2.1 (e.symm y).2.2.2) (rnds I (len (e.symm y).1))
      · exact Or.inr ⟨hi, hq.2⟩
      · exact Or.inl ⟨hq.1, hi⟩
  have h1 := frac_pathColl_le e πf blk len I hfirst G N hN
    (fun y ↦ PermGood (πf (e.symm y).1) G ∧ ¬Set.InjOn (famZ (πf (e.symm y).1) (blk (e.symm y).1)
      (e.symm y).2.1 (e.symm y).2.2.1 (e.symm y).2.2.2) (rnds I (len (e.symm y).1)))
    fun q t hb ↦ by simpa only [Equiv.symm_apply_apply] using hb
  have hT : Fintype.card ((Z → X) × (X → Z) × (X → Z)) =
      Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) := by
    simp only [Fintype.card_prod]
    ring
  have h2 := frac_le_of_card_mul_sum_le (A := X) (B := Z) e
    (fun y ↦ Set.InjOn (famZ (πf (e.symm y).1) (blk (e.symm y).1) (e.symm y).2.1
      (e.symm y).2.2.1 (e.symm y).2.2.2) (rnds I (len (e.symm y).1)) ∧
      ∃ a ∈ rnds I (len (e.symm y).1), 1 ≤ a.2 ∧
        famK (πf (e.symm y).1) (blk (e.symm y).1) (e.symm y).2.1 (e.symm y).2.2.1
          (e.symm y).2.2.2 a ∈ T) (N * T.card) 0 fun q ↦ by
    have hc := card_mul_sum_trialHit_le (π := πf q) (blk := blk q) (downClosed_rnds I (len q)) T
    have hs := sum_ite_le_of_imp _ (fun t : (Z → X) × (X → Z) × (X → Z) ↦
      Set.InjOn (famZ (πf q) (blk q) t.1 t.2.1 t.2.2) (rnds I (len q)) ∧
        ∃ a ∈ rnds I (len q), 1 ≤ a.2 ∧ famK (πf q) (blk q) t.1 t.2.1 t.2.2 a ∈ T)
      fun t (ht : Set.InjOn (famZ (πf (e.symm (e (q, t))).1) (blk (e.symm (e (q, t))).1)
        (e.symm (e (q, t))).2.1 (e.symm (e (q, t))).2.2.1 (e.symm (e (q, t))).2.2.2)
          (rnds I (len (e.symm (e (q, t))).1)) ∧
        ∃ a ∈ rnds I (len (e.symm (e (q, t))).1), 1 ≤ a.2 ∧
          famK (πf (e.symm (e (q, t))).1) (blk (e.symm (e (q, t))).1) (e.symm (e (q, t))).2.1
            (e.symm (e (q, t))).2.2.1 (e.symm (e (q, t))).2.2.2 a ∈ T) ↦ by
        simpa only [Equiv.symm_apply_apply] using ht
    rw [mul_comm (Fintype.card X) (Fintype.card Z), mul_assoc]
    refine (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ hs).trans hc)).trans
      ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (hN q)))).trans
        (le_of_eq ?_))
    rw [hT]
    ring
  calc (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card
      ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y ↦
            PermGood (πf (e.symm y).1) G ∧ ¬Set.InjOn (famZ (πf (e.symm y).1) (blk (e.symm y).1)
              (e.symm y).2.1 (e.symm y).2.2.1 (e.symm y).2.2.2) (rnds I (len (e.symm y).1))).card :
              ℝ≥0∞) +
          (Finset.univ.filter fun y ↦ Set.InjOn (famZ (πf (e.symm y).1) (blk (e.symm y).1)
            (e.symm y).2.1 (e.symm y).2.2.1 (e.symm y).2.2.2) (rnds I (len (e.symm y).1)) ∧
            ∃ a ∈ rnds I (len (e.symm y).1), 1 ≤ a.2 ∧
              famK (πf (e.symm y).1) (blk (e.symm y).1) (e.symm y).2.1 (e.symm y).2.2.1
                (e.symm y).2.2.2 a ∈ T).card) := by
        gcongr
        exact_mod_cast hsub
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add h1 (h2.trans_eq (by rw [Nat.mul_zero, Nat.cast_zero, ENNReal.zero_div,
        add_zero]))

end generic

/-! ## leanXMSS -/

section xmss

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- A one-block top-layer message-digest input's block, at any parameter, key, signed digest and
randomizer. -/
def TopTrialBlock (x : X) : Prop :=
  ∃ (P : PublicParameter) (e : KeyIndex) (d ρ : Digest),
    blocks (msgInput P topLayer e (littleEndianBytes 16 d) ρ) = [x]

/-- **No top-layer trial block is a `k` cell the game may program.** -/
def TrialsOff (L : HonestTable) : Prop :=
  ∀ x, TopTrialBlock x → (tableHw L).2.1 x = none

/-! ### Trial blocks name no in-table slot -/

/-- A message digest's address names no in-table slot. -/
theorem not_inTable_of_slotOfAddress_message (P Q : PublicParameter) (l : Layer) (e : KeyIndex)
    (idx : BitVec 128) {s : Slot}
    (hs : slotOfAddress P Q (hashDomainFields (.message l e)) idx = some s) : ¬InTable s := by
  have htag : (hashDomainFields (.message l e)).tag = 12 := rfl
  have h12 : (hashDomainFields (.message l e)).tag.toNat = 12 := rfl
  unfold slotOfAddress at hs
  split_ifs at hs with h1 h2
  · exact absurd (htag.symm.trans h1.2) (by decide)
  · simp only [fieldsSlot, h12, Option.some.injEq] at hs
    subst hs
    exact id

/-- **A top trial block names no in-table slot**: its address is a message digest's. -/
theorem not_inTable_of_topTrialBlock {x : X} (hx : TopTrialBlock x) (P : PublicParameter)
    {s : Slot} (hs : slotOfBlock P x = some s) : ¬InTable s := by
  obtain ⟨P', e, d, ρ, hb⟩ := hx
  have hh := head?_blocks (msgInput P' topLayer e (littleEndianBytes 16 d) ρ)
  rw [hb, List.head?_cons] at hh
  rw [Option.some.inj hh] at hs
  unfold msgInput at hs
  rw [slotOfBlock_thInput P P' _ _ (by rw [List.length_append, length_le16, length_le16])] at hs
  exact not_inTable_of_slotOfAddress_message P P' topLayer e _ hs

/-! ### The trial blocks as a finite set -/

/-- The first block of the top-layer message-digest input at a parameter, key, digest and
randomizer. -/
def trialBlk (a : PublicParameter × KeyIndex × Digest × Digest) : X :=
  (blocks (msgInput a.1 topLayer a.2.1 (littleEndianBytes 16 a.2.2.1) a.2.2.2)).getD 0 0

/-- **The top trial blocks**: the first block of each top-layer message-digest input of a digest
(irreducible after `mem_trialSet_of`). -/
def trialSet : Finset X :=
  Finset.univ.image trialBlk

theorem mem_trialSet_of (a : PublicParameter × KeyIndex × Digest × Digest) :
    trialBlk a ∈ trialSet := by
  simp only [trialSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨a, rfl⟩

attribute [irreducible] trialSet

theorem mem_trialSet {x : X} (hx : TopTrialBlock x) : x ∈ trialSet := by
  obtain ⟨P, e, d, ρ, hb⟩ := hx
  have h := mem_trialSet_of (P, e, d, ρ)
  have hx : trialBlk (P, e, d, ρ) = x := by
    show (blocks (msgInput P topLayer e (littleEndianBytes 16 d) ρ)).getD 0 0 = x
    rw [hb]
    rfl
  rw [hx] at h
  exact h

/-- The cardinality of a product of four types. -/
theorem card_prod_four {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {a b c d : ℕ} (ha : Fintype.card A = a) (hb : Fintype.card B = b) (hc : Fintype.card C = c)
    (hd : Fintype.card D = d) : Fintype.card (A × B × C × D) = a * (b * (c * d)) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ha, hb, hc, hd]

theorem card_publicParameter : Fintype.card PublicParameter = 2 ^ 128 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem card_keyIndex : Fintype.card KeyIndex = 2 ^ 32 := by
  rw [Fintype.card_fin]
  norm_num [lifetime, layerCount, layerHeight]

set_option exponentiation.threshold 4096 in
/-- **At most `2^416` top trial blocks.** -/
theorem card_trialSet_le : trialSet.card ≤ 2 ^ 416 := by
  unfold trialSet
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, card_prod_four card_publicParameter card_keyIndex card_digest card_digest]
  norm_num

/-! ### Trial blocks among the in-table cells -/

/-- **A trial block among the in-table cells** at the public datum `pub` and the values `v`: a
`k`-cell of an in-table slot's honest path is a top trial block. -/
def TrialBad (pub : Pub) (v : ValPos → Digest) : Prop :=
  ∃ s, InTable s ∧ ∃ j < nBlocks pub s, TopTrialBlock (srcCellK pub s v j)

/-- **A trial block among the in-table cells is a later `k`-cell of an in-table path in
`trialSet`**: the first `k`-cells name in-table slots. -/
theorem exists_rnd_of_trialBad {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hb : TrialBad (xPub w h) v) :
    ∃ a ∈ rnds xI (xLen w.1), 1 ≤ a.2 ∧
      famK w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 a ∈ trialSet := by
  obtain ⟨s, hs, j, hj, hT⟩ := hb
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact not_inTable_of_topTrialBlock hT (xPub w h).param
      (slotOfBlock_cellK_zero (xPub w h) hs v) hs
  obtain ⟨p, hp, rfl⟩ : ∃ p, InPos p ∧ outSlot p = s :=
    ⟨slotOutPos s, inPos_slotOutPos hs, outSlot_slotOutPos hs⟩
  refine ⟨(p, j), mem_rnds.mpr ⟨mem_xI.mpr hp, ?_⟩, Nat.one_le_iff_ne_zero.mpr hj0, ?_⟩
  · show j < xLen w.1 p
    rw [← nBlocks_xPub_eq w h p]
    exact hj
  · have e : famK w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p, j) =
        srcCellK (xPub w h) (outSlot p) v j :=
      (srcCellK_eq_rnK w h (outSlot p) v hj).symm
    rw [e]
    exact mem_trialSet hT

/-! ### The fraction of public data and hidden values -/

open scoped Classical in
/-- **The trial-hit event on good permutations**: `PermGood π G ∧ TrialBad` for at most a fraction
`N² / |X| + N² (G + 1) / |Z| + N |trialSet| / |X|` of the public data and hidden values,
`N = 8 |xI|`. -/
theorem trialBad_good_frac_le (G : ℕ) :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ TrialBad (pubX y.1) y.2).card ≤
      ((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ((8 * xI.card * trialSet.card : ℕ) : ℝ≥0∞) / Fintype.card X :=
  frac_pathTrial_le sEquiv (fun q ↦ q.2.1) (fun q ↦ xBlk q.1 q.2.2.2) (fun q ↦ xLen q.1) xI
    (fun q ↦ xBlk_injOn q.1 q.2.2.2) G _ (fun q ↦ card_rnds_xI_le q.1) trialSet _ fun q t hb ↦
      ⟨hb.1, exists_rnd_of_trialBad (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1) (v := q.2.2.2)
        hb.2⟩

open scoped Classical in
/-- **The trial-hit fraction of leanXMSS**: `TrialBad` for at most the bad permutations plus
`N² / |X| + N² (G + 1) / |Z| + N |trialSet| / |X|`, `N = 8 |xI|`. -/
theorem trialBad_frac_le (G : ℕ) :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ TrialBad (pubX y.1) y.2).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ((8 * xI.card * trialSet.card : ℕ) : ℝ≥0∞) / Fintype.card X) := by
  set N := Fintype.card (PX × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp
    (fun y : PX × (ValPos → Digest) ↦ TrialBad (pubX y.1) y.2)
    (fun y : PX × (ValPos → Digest) ↦ ¬PermGood (pxPermEquiv y).1 G)
    (fun y : PX × (ValPos → Digest) ↦ PermGood y.1.1.2.2.1 G ∧ TrialBad (pubX y.1) y.2)
    fun y hy ↦ by
      by_cases hG : PermGood y.1.1.2.2.1 G
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ TrialBad (pubX y.1) y.2).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv y).1 G).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ TrialBad (pubX y.1) y.2).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv y).1 G).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ TrialBad (pubX y.1) y.2).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst pxPermEquiv fun π ↦ ¬PermGood π G]
        exact add_le_add le_rfl (trialBad_good_frac_le G)

set_option exponentiation.threshold 4096 in
/-- The trial term at Keccak's sizes, for `n ≤ 498 · 2^32` outputs and at most `2^416` trial
blocks: `2^460 / 2^1088`. -/
theorem trialTerm_le {n m cX : ℕ} (hn : n ≤ 498 * 2 ^ 32) (hm : m ≤ 2 ^ 416)
    (hX : cX = 2 ^ 1088) : ((8 * n * m : ℕ) : ℝ≥0∞) / cX ≤ ENNReal.ofReal (1 / 2 ^ 600) := by
  subst hX
  have hK : 8 * n * m ≤ 2 ^ 460 :=
    calc 8 * n * m ≤ 8 * (498 * 2 ^ 32) * 2 ^ 416 := by gcongr
      _ ≤ 2 ^ 460 := by norm_num
  rw [natCast_div_eq_ofReal _ (2 ^ 1088) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((8 * n * m : ℕ) : ℝ) / ((2 ^ 1088 : ℕ) : ℝ) ≤ 2 ^ 460 / 2 ^ 1088 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    _ ≤ 1 / 2 ^ 600 := by norm_num

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The trial-hit fraction at Keccak's sizes**: at most `2^-400` (with `G = 18`: the bad
permutations `2^-777`, the collisions `2^-401`, the trial blocks `2^-600`). -/
theorem trialBad_frac_le_keccak :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ TrialBad (pubX y.1) y.2).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) := by
  refine ((trialBad_frac_le 18).trans (add_le_add permTerm_le_keccak
    (add_le_add (collTerms_le card_xI_le rnCard_X rnCard_Z)
      (trialTerm_le card_xI_le card_trialSet_le rnCard_X)))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 401)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 600),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-! ### The honest tables -/

open scoped Classical in
/-- **On ReparamR0's good set, a violated `TrialsOff` is a trial block among the in-table cells**
of the coordinates: the table's `k` cells are the template's hidden `k`-cells (`r0E_hpath`). -/
theorem trialBad_of_r0G {t : HonestTable × RE} (ht : r0G treeQ 18 t) (hn : ¬TrialsOff t.1) :
    TrialBad (pubX ((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2))
      (fwd xmssFix xO (r0Phi t).1.1).2 := by
  simp only [TrialsOff, not_forall] at hn
  obtain ⟨x, hx, hne⟩ := hn
  have hk : x ∈ pathK t.1 := by
    by_contra hk
    apply hne
    unfold tableHw
    dsimp only
    exact ite_eq_right hk
  obtain ⟨-, s, hs, j, hj, rfl⟩ := (r0E_hpath hashesSlots_treeQ ht).2.1 hk
  exact ⟨s, hs, j, hj, hx⟩

open scoped Classical in
/-- **The good tables violating `TrialsOff`** are at most `TrialBad`'s fraction of the public data
and hidden values (the coordinates of Reparam-good tables are distinct). -/
theorem trialsOff_r0G_frac_le :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬TrialsOff t.1).card ≤
      (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ TrialBad (pubX y.1) y.2).card := by
  have hC := card_filter_le_of_injOn
    (fun t ↦ ((((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2), (fwd xmssFix xO (r0Phi t).1.1).2),
      (r0Phi t).2) :
        HonestTable × RE → (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS))
    (fun t ↦ r0G treeQ 18 t ∧ ¬TrialsOff t.1)
    (fun z : (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) ↦
      TrialBad (pubX z.1.1) z.1.2)
    (fun _ h ↦ trialBad_of_r0G h.1 h.2) fun t₁ t₂ h₁ h₂ e ↦ by
      have hf : fwd xmssFix xO (r0Phi t₁).1.1 = fwd xmssFix xO (r0Phi t₂).1.1 :=
        Prod.ext (congrArg (fun z ↦ z.1.1.1) e :) (congrArg (fun z ↦ z.1.2) e :)
      have hθ := injOn_fwd xO_consistent (good_of_xGood h₁.1.2.2.1) (good_of_xGood h₂.1.2.2.1) hf
      exact r0Phi.injective (Prod.ext (Prod.ext hθ (congrArg (fun z ↦ z.1.1.2) e :))
        (congrArg (fun z ↦ z.2) e :))
  have hP := card_filter_pad (W := CoinSlots R0.RLabel × SeedKS)
    (fun y : PX × (ValPos → Digest) ↦ TrialBad (pubX y.1) y.2)
  have hN : Fintype.card (HonestTable × RE) =
      Fintype.card (PX × (ValPos → Digest)) * Fintype.card (CoinSlots R0.RLabel × SeedKS) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (r0Phi.trans (pxEquiv.symm.prodCongr (Equiv.refl _)))
  calc (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬TrialsOff t.1).card
      ≤ (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun z : (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) ↦
            TrialBad (pubX z.1.1) z.1.2).card := by
        gcongr
    _ = (((Fintype.card (PX × (ValPos → Digest)) * Fintype.card (CoinSlots R0.RLabel × SeedKS) :
          ℕ) : ℝ≥0∞))⁻¹ * (((Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
            TrialBad (pubX y.1) y.2).card * Fintype.card (CoinSlots R0.RLabel × SeedKS) : ℕ) :
              ℝ≥0∞) := by
        rw [hP, hN, Nat.cast_mul, Nat.cast_mul]
    _ = _ := natCast_mul_inv_mul_cancel _ _ _ Fintype.card_ne_zero

open scoped Classical in
/-- **The good tables violating `TrialsOff` at Keccak's sizes**: at most `2^-400` of the padded
tables are in ReparamR0's good set `r0G treeQ 18` and violate `TrialsOff`. -/
theorem trialsOff_r0G_frac_le_keccak :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬TrialsOff t.1).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) :=
  trialsOff_r0G_frac_le.trans trialBad_frac_le_keccak

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The honest tables violating `TrialsOff`** at Keccak's sizes: at most `2^-173` (the tables
outside `r0G treeQ 18`, `2^-174`, and the good ones violating it, `2^-400`). -/
theorem trialsOff_frac_le_keccak :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun L : HonestTable ↦ ¬TrialsOff L).card ≤
      ENNReal.ofReal (1 / 2 ^ 173) := by
  have hE := inv_card_mul_card_filter_comp_fst (Equiv.refl (HonestTable × RE))
    fun L ↦ ¬TrialsOff L
  have hsub := card_filter_le_add_of_imp (fun t : HonestTable × RE ↦ ¬TrialsOff t.1)
    (fun t ↦ ¬r0G treeQ 18 t) (fun t ↦ r0G treeQ 18 t ∧ ¬TrialsOff t.1) fun t ht ↦ by
      by_cases hg : r0G treeQ 18 t
      · exact Or.inr ⟨hg, ht⟩
      · exact Or.inl hg
  rw [mul_comm, ← div_eq_mul_inv, ← hE]
  calc (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t : HonestTable × RE ↦ ¬TrialsOff t.1).card
      ≤ (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card : ℝ≥0∞) +
            (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬TrialsOff t.1).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card +
        (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬TrialsOff t.1).card := mul_add _ _ _
    _ ≤ ENNReal.ofReal (1 / 2 ^ 174) + ENNReal.ofReal (1 / 2 ^ 400) :=
        add_le_add r0G_frac_le_keccak trialsOff_r0G_frac_le_keccak
    _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)

end xmss

end Quantum.Xmss.Assembly

end
