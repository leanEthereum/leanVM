module

public import Quantum.Sphincs.Hybrid.SchemeSeed

@[expose] public section

/-!
# Hiding leanSPHINCS's secret key: the staged swap, its good set and its bad fraction

leanSPHINCS's table `L = (t, π, SK.seed)` draws `SK.seed` uniformly; `SK.prf`, `PK.seed` and the
secrets (chain starts and FORS secrets) are one-block hashes of `SK.seed`-keyed inputs (`skInput`).
As for leanXMSS (`Quantum.Xmss.Hybrid.SchemeSplit`), extra uniform slots take the `h`-values at
these inputs' capacities, so that the public part determines `PK.seed` and the secrets' hashes
while `SK.seed` and `SK.prf` stay hidden and uniform.

* `schemeSplit : Tab ≃ Pub × Secret`: the table with three extra uniform slots. Stage `R` moves
  the `SK.prf` derivation's output to slot `0`, stage `A` the `PK.seed` derivation's to slot `1`,
  stage `B` the secrets' to the slots `2` (when their capacities are distinct), and `splitSeed`
  splits `SK.seed` off the table and `SK.prf` off slot `0`. The hidden coordinate is
  `(SK.seed, SK.prf)` (`schemeSplit_snd`); when the hidden capacities `posOf` are distinct, the
  public part gives `PK.seed`, the secrets' hashes and `h` off those capacities
  (`schemeSplit_transfer`).
* `schemeGood Q`: the hidden capacities are distinct and no computation `Q i` of `PK.seed` and the
  secrets' hashes reads `h` at one. On it the challenger's data is a function of the public part
  (`schemeData_eq_of_mem`).
* `schemeGood_frac_le`: the fraction outside it is at most the bad permutations, the collisions
  `|A|² (G + 1) / |Z|`, and per computation `qsᵢ / 2^256 + |A| (G + 1) qᵢ / |Z|`
  (`A = SkIdx`).
* `avg_hiddenMass_secretSeed_le_of_schemeData`, `avg_hiddenMass_prfKey_le_of_schemeData`: the
  mass at cells keyed by `SK.seed`, or by `SK.prf`, averaged over the table.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w

open Quantum.SufCma

open Quantum Quantum.Sponge Sphincs
open HashSig (HashOutput PublicParameter MasterSeed truncateHash)
open Common.SufCma (SchemeHashSpec)
open Quantum.Xmss (X Z out256 trunc128)
open Quantum.Xmss.Hybrid (firstCell capOf rateOf stage1 stage1_apply stageN stageN_eq_mk
  stageN_apply_of_injective xch xch_snd_mk xch_fst_mk_of_notMem sum_eq_sum_coords card_eq_coords
  sum_comm_three inv_card_mul_sum_fst sum_sum_le_mul card_mul_sum_fst_eq
  card_mul_sum_not_injective_capOf_le sum_capOf_mem_le hCells kCells k'Cells mem_hCells
  card_hCells_le card_k'Cells_le honestEval_update_k_of_not_mem honestEval_update_k'_of_not_mem
  sum_ite_mem_le_card_filter card_sub_card_le_sum natCast_le_mul_div_of_mul_le card_masterSeed
  runtime2 hiddenMass avg_hiddenMass_seed_le)

namespace Quantum.Sphincs.Hybrid

/-! ## Assembling a bad fraction, over abstract types -/

/-- **Assembling a bad fraction**: a count `a` bounded by parts, each at most `N` times its
fraction, is at most `N` times the sum of the fractions. -/
theorem inv_mul_le_of_parts₁ {ι : Type*} [Fintype ι] {N a p c : ℕ} {d : ι → ℕ}
    {A B : ℝ≥0∞} {C : ι → ℝ≥0∞} (hN : N ≠ 0) (ha : a ≤ p + (c + ∑ i, d i))
    (hp : (p : ℝ≥0∞) ≤ N * A) (hc : (c : ℝ≥0∞) ≤ N * B) (hd : ∀ i, (d i : ℝ≥0∞) ≤ N * C i) :
    (N : ℝ≥0∞)⁻¹ * a ≤ A + B + ∑ i, C i := by
  have h1 : (a : ℝ≥0∞) ≤ N * (A + B + ∑ i, C i) := by
    calc (a : ℝ≥0∞) ≤ ((p + (c + ∑ i, d i) : ℕ) : ℝ≥0∞) := by exact_mod_cast ha
      _ = p + (c + ∑ i, (d i : ℝ≥0∞)) := by simp only [Nat.cast_add, Nat.cast_sum]
      _ ≤ N * A + (N * B + ∑ i, N * C i) :=
          add_le_add hp (add_le_add hc (Finset.sum_le_sum fun i _ ↦ hd i))
      _ = _ := by simp only [mul_add, Finset.mul_sum, add_assoc]
  calc (N : ℝ≥0∞)⁻¹ * a ≤ (N : ℝ≥0∞)⁻¹ * (N * (A + B + ∑ i, C i)) := by gcongr
    _ = _ := ENNReal.inv_mul_cancel_left (Nat.cast_ne_zero.mpr hN) (ENNReal.natCast_ne_top _)

/-! ## The staged swap on leanSPHINCS tables -/

section split

/-- The extra slots: `SK.prf`'s, `PK.seed`'s, and the secrets'. -/
abbrev SeedSlots : Type := X × X × (KeygenDomain → X)

/-- The tables with the extra slots. -/
abbrev Tab : Type := HonestTable × SeedSlots

/-- The hidden part: `SK.seed` and `SK.prf`. -/
abbrev Secret : Type := MasterSeed × HashOutput

/-- The public part: the keys and `π`, and the slots without `SK.prf` (the first `256` bits of
slot `0`). -/
abbrev Pub : Type :=
  (SpongeKeys X Z × Equiv.Perm (X × Z)) × ((Fin 832 → ZMod 2) × X × (KeygenDomain → X))

/-- The data a one-slot stage preserves: `k`, `k'`, `π`, `SK.seed` and the two other slots. -/
abbrev Rest₁ : Type := (X → Z) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed × X × (KeygenDomain → X)

/-- The data stage `B` preserves: `k`, `k'`, `π`, `SK.seed` and the slots `0` and `1`. -/
abbrev RestB : Type := (X → Z) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed × X × X

/-- The secrets' slots are finite (named: the products of these slots are not found otherwise). -/
noncomputable instance instFintypeSecSlots : Fintype (KeygenDomain → X) :=
  Pi.instFintype

noncomputable instance instFintypePub : Fintype Pub :=
  instFintypeProd _ _

noncomputable instance instFintypePubSecret : Fintype (Pub × Secret) :=
  instFintypeProd _ _

/-- Stage `R`'s view of a table: `h` with slot `0`, and the rest. -/
def shufR : Tab ≃ ((Z → X) × X) × Rest₁ where
  toFun t := ((t.1.keys.1, t.2.1),
    t.1.keys.2.1, t.1.keys.2.2, t.1.perm, t.1.secretSeed, t.2.2.1, t.2.2.2)
  invFun p := (⟨(p.1.1, p.2.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2.1⟩,
    p.1.2, p.2.2.2.2.2.1, p.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Stage `A`'s view of a table: `h` with slot `1`, and the rest. -/
def shufA : Tab ≃ ((Z → X) × X) × Rest₁ where
  toFun t := ((t.1.keys.1, t.2.2.1),
    t.1.keys.2.1, t.1.keys.2.2, t.1.perm, t.1.secretSeed, t.2.1, t.2.2.2)
  invFun p := (⟨(p.1.1, p.2.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2.1⟩,
    p.2.2.2.2.2.1, p.1.2, p.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Stage `B`'s view of a table: `h` with the slots `2`, and the rest. -/
def shufB : Tab ≃ ((Z → X) × (KeygenDomain → X)) × RestB where
  toFun t := ((t.1.keys.1, t.2.2.2),
    t.1.keys.2.1, t.1.keys.2.2, t.1.perm, t.1.secretSeed, t.2.1, t.2.2.1)
  invFun p := (⟨(p.1.1, p.2.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2.1⟩,
    p.2.2.2.2.2.1, p.2.2.2.2.2.2, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem shufR_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed)
    (u₀ u₁ : X) (u₂ : KeygenDomain → X) :
    shufR (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) = ((h, u₀), (k, k', π, S, u₁, u₂)) :=
  rfl

theorem shufR_symm_apply (h : Z → X) (u₀ : X) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (S : MasterSeed) (u₁ : X) (u₂ : KeygenDomain → X) :
    shufR.symm ((h, u₀), (k, k', π, S, u₁, u₂)) = (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) :=
  rfl

theorem shufA_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed)
    (u₀ u₁ : X) (u₂ : KeygenDomain → X) :
    shufA (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) = ((h, u₁), (k, k', π, S, u₀, u₂)) :=
  rfl

theorem shufA_symm_apply (h : Z → X) (u₁ : X) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (S : MasterSeed) (u₀ : X) (u₂ : KeygenDomain → X) :
    shufA.symm ((h, u₁), (k, k', π, S, u₀, u₂)) = (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) :=
  rfl

theorem shufB_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed)
    (u₀ u₁ : X) (u₂ : KeygenDomain → X) :
    shufB (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) = ((h, u₂), (k, k', π, S, u₀, u₁)) :=
  rfl

theorem shufB_symm_apply (p : (Z → X) × (KeygenDomain → X)) (k k' : X → Z)
    (π : Equiv.Perm (X × Z)) (S : MasterSeed) (u₀ u₁ : X) :
    shufB.symm (p, (k, k', π, S, u₀, u₁)) = (⟨(p.1, k, k'), π, S⟩, (u₀, u₁, p.2)) :=
  rfl

/-- The first block of the `SK.prf` derivation. -/
def prfKeyCell (S : MasterSeed) : X :=
  firstCell (Sphincs.KeyGenerationAndSigning.keyDerivationInput S 1)

/-- The first block of the `PK.seed` derivation. -/
def pubSeedCell (S : MasterSeed) : X :=
  firstCell (Sphincs.KeyGenerationAndSigning.keyDerivationInput S 0)

/-- The first block of a secret's `PRF` call. -/
def secretCell (P : PublicParameter) (S : MasterSeed) (d : KeygenDomain) : X :=
  firstCell (prfInput P S d)

theorem skCell_none (P : PublicParameter) (S : MasterSeed) : skCell P S none = prfKeyCell S :=
  rfl

theorem skCell_some_none (P : PublicParameter) (S : MasterSeed) :
    skCell P S (some none) = pubSeedCell S :=
  rfl

theorem skCell_some_some (P : PublicParameter) (S : MasterSeed) (d : KeygenDomain) :
    skCell P S (some (some d)) = secretCell P S d :=
  rfl

/-- Stage `R`'s cell: the `SK.prf` derivation's capacity. -/
def posR (w : Rest₁) : Z :=
  capOf w.1 w.2.1 w.2.2.1 (prfKeyCell w.2.2.2.1)

/-- Stage `R`'s shift: the `SK.prf` derivation's rate. -/
def shR (w : Rest₁) : X :=
  rateOf w.1 w.2.2.1 (prfKeyCell w.2.2.2.1)

/-- Stage `A`'s cell: the `PK.seed` derivation's capacity. -/
def posA (w : Rest₁) : Z :=
  capOf w.1 w.2.1 w.2.2.1 (pubSeedCell w.2.2.2.1)

/-- Stage `A`'s shift: the `PK.seed` derivation's rate. -/
def shA (w : Rest₁) : X :=
  rateOf w.1 w.2.2.1 (pubSeedCell w.2.2.2.1)

/-- Stage `B`'s cells: the secrets' capacities, for `PK.seed` from slot `1`. -/
def posB (w : RestB) (d : KeygenDomain) : Z :=
  capOf w.1 w.2.1 w.2.2.1 (secretCell (trunc128 w.2.2.2.2.2) w.2.2.2.1 d)

/-- Stage `B`'s shifts: the secrets' rates. -/
def shB (w : RestB) (d : KeygenDomain) : X :=
  rateOf w.1 w.2.2.1 (secretCell (trunc128 w.2.2.2.2.2) w.2.2.2.1 d)

theorem posR_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed) (u₁ : X)
    (u₂ : KeygenDomain → X) : posR (k, k', π, S, u₁, u₂) = capOf k k' π (prfKeyCell S) :=
  rfl

theorem shR_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed) (u₁ : X)
    (u₂ : KeygenDomain → X) : shR (k, k', π, S, u₁, u₂) = rateOf k π (prfKeyCell S) :=
  rfl

theorem posA_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed) (u₀ : X)
    (u₂ : KeygenDomain → X) : posA (k, k', π, S, u₀, u₂) = capOf k k' π (pubSeedCell S) :=
  rfl

theorem shA_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed) (u₀ : X)
    (u₂ : KeygenDomain → X) : shA (k, k', π, S, u₀, u₂) = rateOf k π (pubSeedCell S) :=
  rfl

theorem posB_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed) (u₀ u₁ : X)
    (d : KeygenDomain) :
    posB (k, k', π, S, u₀, u₁) d = capOf k k' π (secretCell (trunc128 u₁) S d) :=
  rfl

theorem shB_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed) (u₀ u₁ : X)
    (d : KeygenDomain) :
    shB (k, k', π, S, u₀, u₁) d = rateOf k π (secretCell (trunc128 u₁) S d) :=
  rfl

/-- **Stage `R`**: the `SK.prf` derivation's capacity takes slot `0`, which takes its output. -/
def stageR : Tab ≃ Tab :=
  (shufR.trans (stage1 posR shR)).trans shufR.symm

/-- **Stage `A`**: the `PK.seed` derivation's capacity takes slot `1`, which takes its output. -/
def stageA : Tab ≃ Tab :=
  (shufA.trans (stage1 posA shA)).trans shufA.symm

/-- **Stage `B`**: the secrets' capacities take the slots `2`, which take their outputs, when the
capacities are distinct. -/
noncomputable def stageB : Tab ≃ Tab :=
  (shufB.trans (stageN posB shB)).trans shufB.symm

theorem stageR_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed)
    (u₀ u₁ : X) (u₂ : KeygenDomain → X) :
    stageR (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) =
      (⟨(Function.update h (capOf k k' π (prfKeyCell S)) u₀, k, k'), π, S⟩,
        (rateOf k π (prfKeyCell S) + h (capOf k k' π (prfKeyCell S)), u₁, u₂)) := by
  rw [stageR, Equiv.trans_apply, Equiv.trans_apply, shufR_apply, stage1_apply, shufR_symm_apply,
    posR_apply, shR_apply]

theorem stageA_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed)
    (u₀ u₁ : X) (u₂ : KeygenDomain → X) :
    stageA (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) =
      (⟨(Function.update h (capOf k k' π (pubSeedCell S)) u₁, k, k'), π, S⟩,
        (u₀, rateOf k π (pubSeedCell S) + h (capOf k k' π (pubSeedCell S)), u₂)) := by
  rw [stageA, Equiv.trans_apply, Equiv.trans_apply, shufA_apply, stage1_apply, shufA_symm_apply,
    posA_apply, shA_apply]

/-- Stage `B` keeps `k`, `k'`, `π`, `SK.seed` and the slots `0` and `1`. -/
theorem stageB_exists (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed)
    (u₀ u₁ : X) (u₂ : KeygenDomain → X) : ∃ (h' : Z → X) (u₂' : KeygenDomain → X),
    stageB (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) = (⟨(h', k, k'), π, S⟩, (u₀, u₁, u₂')) := by
  rw [stageB, Equiv.trans_apply, Equiv.trans_apply, shufB_apply, stageN_eq_mk, shufB_symm_apply]
  exact ⟨_, _, rfl⟩

/-- Stage `B` when the secrets' capacities are distinct. -/
theorem stageB_apply_of_injective (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (S : MasterSeed) (u₀ u₁ : X) (u₂ : KeygenDomain → X)
    (hinj : Function.Injective (posB (k, k', π, S, u₀, u₁))) :
    stageB (⟨(h, k, k'), π, S⟩, (u₀, u₁, u₂)) =
      (⟨((xch (posB (k, k', π, S, u₀, u₁)) hinj (shB (k, k', π, S, u₀, u₁)) (h, u₂)).1, k, k'),
        π, S⟩,
        (u₀, u₁,
          (xch (posB (k, k', π, S, u₀, u₁)) hinj (shB (k, k', π, S, u₀, u₁)) (h, u₂)).2)) := by
  rw [stageB, Equiv.trans_apply, Equiv.trans_apply, shufB_apply,
    stageN_apply_of_injective _ _ _ _ hinj, shufB_symm_apply]

/-- `SK.seed` split off the table and `SK.prf` (the first `256` bits of slot `0`) off the slots. -/
def splitSeed : Tab ≃ Pub × Secret where
  toFun t := (((t.1.keys, t.1.perm), (outSplit t.2.1).2, t.2.2.1, t.2.2.2),
    (t.1.secretSeed, (outSplit t.2.1).1))
  invFun p := (⟨p.1.1.1, p.1.1.2, p.2.1⟩, outSplit.symm (p.2.2, p.1.2.1), p.1.2.2.1, p.1.2.2.2)
  left_inv t := by
    obtain ⟨⟨t₀, π, S⟩, u₀, u₁, u₂⟩ := t
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨⟨⟨t₀, π⟩, r, u₁, u₂⟩, S, y⟩ := p
    simp only [Equiv.apply_symm_apply]

theorem splitSeed_apply (t₀ : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed)
    (u₀ u₁ : X) (u₂ : KeygenDomain → X) :
    splitSeed (⟨t₀, π, S⟩, (u₀, u₁, u₂)) =
      (((t₀, π), (outSplit u₀).2, u₁, u₂), (S, out256 u₀)) :=
  rfl

/-- **The staged swap**: the table with its extra slots as the public part and the hidden
`(SK.seed, SK.prf)`. -/
noncomputable def schemeSplit : Tab ≃ Pub × Secret :=
  stageR.trans (stageA.trans (stageB.trans splitSeed))

theorem schemeSplit_apply (t : Tab) : schemeSplit t = splitSeed (stageB (stageA (stageR t))) :=
  rfl

/-! ### The transfer facts -/

/-- `PK.seed` read off the public part. -/
def pubParam (p : Pub) : PublicParameter :=
  trunc128 p.2.2.1

/-- The secrets' hashes read off the public part. -/
def pubSec (p : Pub) (d : KeygenDomain) : HashOutput :=
  out256 (p.2.2.2 d)

/-- The hidden capacities: the `SK.seed`-keyed cells' under the public keys and `π`. -/
def posOf (p : Pub) (s : Secret) (a : SkIdx) : Z :=
  capOf p.1.1.2.1 p.1.1.2.2 p.1.2 (skCell (pubParam p) s.1 a)

/-- The hash of a secret's `PRF` call. -/
def secHash (L : HonestTable) (d : KeygenDomain) : HashOutput :=
  L.hash (prfInput L.publicSeed L.secretSeed d)

theorem secret_eq_secHash (L : HonestTable) (d : KeygenDomain) :
    L.secret d = truncateHash (secHash L d) :=
  rfl

/-- The `SK.prf` derivation's capacity. -/
def capR (t : Tab) : Z :=
  capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (prfKeyCell t.1.secretSeed)

/-- Slot `0` after stage `R`: the `SK.prf` derivation's output. -/
def slot0 (t : Tab) : X :=
  rateOf t.1.keys.2.1 t.1.perm (prfKeyCell t.1.secretSeed) + t.1.keys.1 (capR t)

/-- The `PK.seed` derivation's capacity. -/
def capP (t : Tab) : Z :=
  capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (pubSeedCell t.1.secretSeed)

/-- Slot `1` after stage `A`: the `PK.seed` derivation's output. -/
def slot1 (t : Tab) : X :=
  rateOf t.1.keys.2.1 t.1.perm (pubSeedCell t.1.secretSeed) +
    Function.update t.1.keys.1 (capR t) t.2.1 (capP t)

/-- `h` after stage `A`. -/
def hA (t : Tab) : Z → X :=
  Function.update (Function.update t.1.keys.1 (capR t) t.2.1) (capP t) t.2.2.1

/-- The data stage `B` sees after stages `R` and `A`. -/
abbrev wB (t : Tab) : RestB :=
  (t.1.keys.2.1, t.1.keys.2.2, t.1.perm, t.1.secretSeed, slot0 t, slot1 t)

theorem stageA_stageR (t : Tab) : stageA (stageR t) =
    (⟨(hA t, t.1.keys.2.1, t.1.keys.2.2), t.1.perm, t.1.secretSeed⟩,
      (slot0 t, slot1 t, t.2.2.2)) := by
  obtain ⟨⟨⟨h, k, k'⟩, π, S⟩, u₀, u₁, u₂⟩ := t
  rw [stageR_apply, stageA_apply]
  rfl

/-- After stage `R`, slot `0` holds `SK.prf`. -/
theorem out256_slot0 (t : Tab) : out256 (slot0 t) = t.1.prfKey := by
  rw [prfKey_eq t.1 0, hash_skInput]
  rfl

theorem schemeSplit_exists (t : Tab) : ∃ (h' : Z → X) (u₂' : KeygenDomain → X),
    schemeSplit t = ((((h', t.1.keys.2.1, t.1.keys.2.2), t.1.perm),
      (outSplit (slot0 t)).2, slot1 t, u₂'), (t.1.secretSeed, t.1.prfKey)) := by
  obtain ⟨h', u₂', hB⟩ := stageB_exists (hA t) t.1.keys.2.1 t.1.keys.2.2 t.1.perm
    t.1.secretSeed (slot0 t) (slot1 t) t.2.2.2
  refine ⟨h', u₂', ?_⟩
  rw [schemeSplit_apply, stageA_stageR, hB, splitSeed_apply, out256_slot0]

/-- The staged swap when the secrets' capacities are distinct. -/
theorem schemeSplit_of_injective (t : Tab) (hinj : Function.Injective (posB (wB t))) :
    schemeSplit t = (((((xch (posB (wB t)) hinj (shB (wB t)) (hA t, t.2.2.2)).1, t.1.keys.2.1,
      t.1.keys.2.2), t.1.perm), (outSplit (slot0 t)).2, slot1 t,
      (xch (posB (wB t)) hinj (shB (wB t)) (hA t, t.2.2.2)).2), (t.1.secretSeed, t.1.prfKey)) := by
  rw [schemeSplit_apply, stageA_stageR, stageB_apply_of_injective _ _ _ _ _ _ _ _ hinj,
    splitSeed_apply, out256_slot0]

/-- **The hidden coordinate is `(SK.seed, SK.prf)`.** -/
theorem schemeSplit_snd (t : Tab) : (schemeSplit t).2 = (t.1.secretSeed, t.1.prfKey) := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]

theorem schemeSplit_keys_snd (t : Tab) : (schemeSplit t).1.1.1.2 = t.1.keys.2 := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]

theorem schemeSplit_perm (t : Tab) : (schemeSplit t).1.1.2 = t.1.perm := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]

theorem pubParam_schemeSplit (t : Tab) : pubParam (schemeSplit t).1 = trunc128 (slot1 t) := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]
  rfl

theorem posOf_schemeSplit (t : Tab) (a : SkIdx) :
    posOf (schemeSplit t).1 (schemeSplit t).2 a = capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.secretSeed a) := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]
  rfl

/-- **The transfer facts**: when the hidden capacities are distinct, the public part gives
`PK.seed`, the secrets' hashes, and `h` off the hidden capacities. -/
theorem schemeSplit_transfer (t : Tab)
    (hinj : Function.Injective (posOf (schemeSplit t).1 (schemeSplit t).2)) :
    pubParam (schemeSplit t).1 = t.1.publicSeed ∧ pubSec (schemeSplit t).1 = secHash t.1 ∧
      ∀ z, (∀ a, posOf (schemeSplit t).1 (schemeSplit t).2 a ≠ z) →
        (schemeSplit t).1.1.1.1 z = t.1.keys.1 z := by
  have hpos := posOf_schemeSplit t
  have hinj' : Function.Injective fun a ↦ capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.secretSeed a) :=
    fun a b hab ↦ hinj ((hpos a).trans (hab.trans (hpos b).symm))
  have hPR : capP t ≠ capR t := fun h ↦
    absurd (hinj' (a₁ := some none) (a₂ := none) h) (by simp)
  have hslot : slot1 t = rateOf t.1.keys.2.1 t.1.perm (pubSeedCell t.1.secretSeed) +
      t.1.keys.1 (capP t) := by
    rw [slot1, Function.update_of_ne hPR]
  have hP : trunc128 (slot1 t) = t.1.publicSeed := by
    rw [hslot, publicSeed_eq t.1 0, hash_skInput]
    rfl
  have hBpos : ∀ d, posB (wB t) d = capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.secretSeed (some (some d))) := fun _ ↦ rfl
  have hBsh : ∀ d, shB (wB t) d =
      rateOf t.1.keys.2.1 t.1.perm (skCell (trunc128 (slot1 t)) t.1.secretSeed (some (some d))) :=
    fun _ ↦ rfl
  have hBinj : Function.Injective (posB (wB t)) := fun d d' hd ↦ by
    rw [hBpos, hBpos] at hd
    exact Option.some_injective _ (Option.some_injective _
      (hinj' (a₁ := some (some d)) (a₂ := some (some d')) hd))
  have hsplit := schemeSplit_of_injective t hBinj
  have hneR : ∀ d, capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.secretSeed (some (some d))) ≠ capR t := fun d h ↦
    absurd (hinj' (a₁ := some (some d)) (a₂ := none) h) (by simp)
  have hneP : ∀ d, capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.secretSeed (some (some d))) ≠ capP t := fun d h ↦
    absurd (hinj' (a₁ := some (some d)) (a₂ := some none) h) (by simp)
  refine ⟨(pubParam_schemeSplit t).trans hP, funext fun d ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hsplit]
    show out256 ((xch (posB (wB t)) hBinj (shB (wB t)) (hA t, t.2.2.2)).2 d) = _
    rw [xch_snd_mk, hBpos, hBsh, hA, Function.update_of_ne (hneP d),
      Function.update_of_ne (hneR d), secHash, ← hP]
    exact (hash_skInput t.1 _ _ (some (some d))).symm
  · have hz' : ∀ a, capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
        (skCell (trunc128 (slot1 t)) t.1.secretSeed a) ≠ z :=
      fun a ↦ (hpos a).symm.trans_ne (hz a)
    have hzP : z ≠ capP t := (hz' (some none)).symm
    have hzR : z ≠ capR t := (hz' none).symm
    rw [hsplit]
    show (xch (posB (wB t)) hBinj (shB (wB t)) (hA t, t.2.2.2)).1 z = _
    rw [xch_fst_mk_of_notMem _ _ _ _ _ fun d ↦ (hBpos d).trans_ne (hz' (some (some d))), hA,
      Function.update_of_ne hzP, Function.update_of_ne hzR]

/-! ### The challenger's data and the good set -/

variable {ι : Type} {β : ι → Type}

/-- **The challenger's honest data**: the honest evaluations of hash computations `Q i` of
`PK.seed` and the secrets' hashes. -/
def schemeData
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (L : HonestTable) : ∀ i, β i × List (SpongeRead X Z) :=
  fun i ↦ honestEval L.keys L.perm (Q i L.publicSeed (secHash L))

/-- The same computations from the public part. -/
def pubData
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (p : Pub) : ∀ i, β i × List (SpongeRead X Z) :=
  fun i ↦ honestEval p.1.1 p.1.2 (Q i (pubParam p) (pubSec p))

/-- Good coordinates: distinct hidden capacities, none read by the computations from the public
part. -/
def GoodPS
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (x : Pub × Secret) : Prop :=
  Function.Injective (posOf x.1 x.2) ∧ ∀ i a, posOf x.1 x.2 a ∉ hCells (pubData Q x.1 i).2

open scoped Classical in
/-- **The good set** of the staged swap. Irreducible: its membership does not unfold to the
enumeration of all tables. -/
@[irreducible]
noncomputable def schemeGood
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Finset Tab :=
  Finset.univ.filter fun t ↦ GoodPS Q (schemeSplit t)

theorem mem_schemeGood
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    {t : Tab} : t ∈ schemeGood Q ↔ GoodPS Q (schemeSplit t) := by
  unfold schemeGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **On the good set, the challenger's data is a function of the public part.** -/
theorem schemeData_eq_of_mem
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    {t : Tab} (ht : t ∈ schemeGood Q) : schemeData Q t.1 = pubData Q (schemeSplit t).1 := by
  obtain ⟨hinj, hread⟩ := mem_schemeGood.mp ht
  obtain ⟨hP, hC, hh⟩ := schemeSplit_transfer t hinj
  funext i
  have hr := hread i
  change ∀ a, posOf _ _ a ∉ hCells (honestEval (schemeSplit t).1.1.1 (schemeSplit t).1.1.2
    (Q i (pubParam (schemeSplit t).1) (pubSec (schemeSplit t).1))).2 at hr
  change honestEval t.1.keys t.1.perm (Q i t.1.publicSeed (secHash t.1)) =
    honestEval (schemeSplit t).1.1.1 (schemeSplit t).1.1.2
      (Q i (pubParam (schemeSplit t).1) (pubSec (schemeSplit t).1))
  rw [hP, hC, schemeSplit_perm] at hr ⊢
  refine honestEval_congr (t := (schemeSplit t).1.1.1) (t' := t.1.keys) t.1.perm _
    fun e he ↦ ?_
  have ha := honestEval_answeredBy t.1.perm (schemeSplit t).1.1.1 _ e he
  cases e with
  | h z a =>
    have hz : ∀ b, posOf (schemeSplit t).1 (schemeSplit t).2 b ≠ z :=
      fun b hb ↦ hr b (mem_hCells.mpr ⟨a, hb ▸ he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← hh z hz]
    exact ha
  | k x a =>
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← schemeSplit_keys_snd t]
    exact ha
  | k' x a =>
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← schemeSplit_keys_snd t]
    exact ha

/-! ### The bad fraction -/

open scoped Classical

variable (G : ℕ)

/-- A good permutation and colliding hidden capacities. -/
noncomputable def collInd (x : Pub × Secret) : ℕ :=
  if PermGood x.1.1.2 G ∧ ¬Function.Injective (posOf x.1 x.2) then 1 else 0

/-- A good permutation and a computation reading `h` at the hidden capacity `a`. -/
noncomputable def hitInd
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (i : ι) (a : SkIdx) (x : Pub × Secret) : ℕ :=
  if PermGood x.1.1.2 G ∧ posOf x.1 x.2 a ∈ hCells (pubData Q x.1 i).2 then 1 else 0

/-- The coordinates other than `k`, `k'` and `SK.seed`: `π`, `h`, the public slots, and
`SK.prf`. -/
abbrev Coord : Type :=
  Equiv.Perm (X × Z) × (Z → X) × ((Fin 832 → ZMod 2) × X × (KeygenDomain → X)) × HashOutput

noncomputable instance instFintypeCoord : Fintype Coord :=
  instFintypeProd _ _

noncomputable instance instFintypeCoords : Fintype (((Coord × MasterSeed) × (X → Z)) × (X → Z)) :=
  instFintypeProd _ _

/-- Coordinates with `SK.seed` second. -/
def coordS : ((Coord × MasterSeed) × (X → Z)) × (X → Z) ≃ Pub × Secret where
  toFun c := ((((c.1.1.1.2.1, c.1.2, c.2), c.1.1.1.1), c.1.1.1.2.2.1), (c.1.1.2, c.1.1.1.2.2.2))
  invFun x := ((((x.1.1.2, x.1.1.1.1, x.1.2, x.2.2), x.2.1), x.1.1.1.2.1), x.1.1.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The table with `π` first. -/
def permSplit : Tab ≃ Equiv.Perm (X × Z) × ((SpongeKeys X Z × MasterSeed) × SeedSlots) where
  toFun t := (t.1.perm, (t.1.keys, t.1.secretSeed), t.2)
  invFun p := (⟨p.2.1.1, p.1, p.2.1.2⟩, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypePermRest :
    Fintype (Equiv.Perm (X × Z) × ((SpongeKeys X Z × MasterSeed) × SeedSlots)) :=
  instFintypeProd _ _

theorem card_tab_eq : Fintype.card Tab = Fintype.card Coord * Fintype.card MasterSeed *
    (Fintype.card (X → Z) * Fintype.card (X → Z)) := by
  rw [Fintype.card_congr schemeSplit, card_eq_coords coordS]

/-- The computation `Q i` of the public slots in coordinates. -/
def coordQ
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (i : ι) (ω : Coord) : OracleComp SchemeHashSpec (β i) :=
  Q i (trunc128 ω.2.2.1.2.1) fun d ↦ out256 (ω.2.2.1.2.2 d)

/-- Its reads with the keys `ω.2.1, k, k'`, with their bound. -/
def coordR
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (i : ι) (k k' : X → Z) (ω : Coord) : {r : List (SpongeRead X Z) // r.length ≤ q i} :=
  ⟨(honestEval (ω.2.1, k, k') ω.1 (coordQ Q i ω)).2, hq i _ _ _ _⟩

theorem coordR_update_k
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (i : ι) (k k' : X → Z) (ω : Coord) (x : X) (w : Z)
    (hx : x ∉ kCells (coordR Q q hq i (Function.update k x w) k' ω).1) :
    coordR Q q hq i (Function.update k x w) k' ω = coordR Q q hq i k k' ω :=
  Subtype.ext (congrArg Prod.snd
    (honestEval_update_k_of_not_mem (coordQ Q i ω) ω.1 ω.2.1 k k' hx))

theorem coordR_update_k'
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (i : ι) (k k' : X → Z) (ω : Coord) (x : X) (a : Z)
    (hx : x ∉ k'Cells (coordR Q q hq i k (Function.update k' x a) ω).1) :
    coordR Q q hq i k (Function.update k' x a) ω = coordR Q q hq i k k' ω :=
  Subtype.ext (congrArg Prod.snd
    (honestEval_update_k'_of_not_mem (coordQ Q i ω) ω.1 ω.2.1 k k' hx))

theorem collInd_coordS (ω : Coord) (S : MasterSeed) (k k' : X → Z) :
    collInd G (coordS (((ω, S), k), k')) =
      (if PermGood ω.1 G ∧ ¬Function.Injective (fun a ↦ capOf k k' ω.1
        (skCell (trunc128 ω.2.2.1.2.1) S a)) then 1 else 0) :=
  rfl

theorem card_mul_sum_coordS_collInd :
    Fintype.card Z * ∑ ω : Coord, ∑ S : MasterSeed, ∑ k : X → Z, ∑ k' : X → Z,
        collInd G (coordS (((ω, S), k), k')) =
      ∑ ω : Coord, ∑ S : MasterSeed, Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
        (if PermGood ω.1 G ∧ ¬Function.Injective (fun a ↦ capOf k k' ω.1
          (skCell (trunc128 ω.2.2.1.2.1) S a)) then 1 else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  simp only [collInd_coordS]

/-- **Collisions**: at most `|A|² (G + 1) / |Z|` of the coordinates have a good permutation and
colliding hidden capacities. -/
theorem card_mul_sum_collInd_le :
    Fintype.card Z * ∑ x, collInd G x ≤ Fintype.card Tab *
      (Fintype.card SkIdx * Fintype.card SkIdx * (G + 1)) := by
  rw [sum_eq_sum_coords coordS (collInd G), card_tab_eq, card_mul_sum_coordS_collInd]
  exact sum_sum_le_mul _ _ _ fun ω S ↦
    card_mul_sum_not_injective_capOf_le ω.1 G _ (skCell_injective_idx _ S)

/-- **The hidden capacities are rarely read**: at most `qs / 2^256 + |A| (G + 1) q / |Z|`. -/
theorem sum_hitInd_le
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i) (i : ι) :
    ((∑ a, ∑ x, hitInd G Q i a x : ℕ) : ℝ≥0∞) ≤
      Fintype.card Tab * ((qs i : ℝ≥0∞) / 2 ^ 256 +
        Fintype.card SkIdx * (G + 1) * q i / Fintype.card Z) := by
  have h := sum_capOf_mem_le (Ω := Coord) (Sd := MasterSeed) (A := SkIdx)
    (fun ω ↦ ω.1) (fun b ω S ↦ skCell (trunc128 ω.2.2.1.2.1) S b) (coordR Q q hq i)
    (fun r ↦ kCells r.1) (fun r ↦ k'Cells r.1) (fun r ↦ hCells r.1) (coordR_update_k Q q hq i)
    (coordR_update_k' Q q hq i) G (q i) (qs i)
    (fun r ↦ (card_k'Cells_le r.1).trans r.2) (fun r ↦ (card_hCells_le r.1).trans r.2)
    (fun k k' ω ↦ by
      rw [← Fintype.sum_prod_type']
      exact (sum_ite_mem_le_card_filter (fun p : MasterSeed × SkIdx ↦
        skCell (trunc128 ω.2.2.1.2.1) p.1 p.2) (skCell_injective _) _
        (fun x ↦ ∃ S b, skCell (trunc128 ω.2.2.1.2.1) S b = x)
        fun p ↦ ⟨p.1, p.2, rfl⟩).trans (hqs i _ _ _ _))
  calc ((∑ a, ∑ x, hitInd G Q i a x : ℕ) : ℝ≥0∞)
      = ((∑ ω : Coord, ∑ s : MasterSeed, ∑ a : SkIdx, ∑ k : X → Z, ∑ k' : X → Z,
          hitInd G Q i a (coordS (((ω, s), k), k')) : ℕ) : ℝ≥0∞) := by
        refine congrArg Nat.cast ?_
        rw [← sum_comm_three]
        exact Finset.sum_congr rfl fun a _ ↦ sum_eq_sum_coords coordS (hitInd G Q i a)
    _ ≤ _ := h
    _ = _ := by
        rw [card_tab_eq, card_masterSeed, Nat.cast_pow, Nat.cast_ofNat]

/-- The tables outside the good set: a bad permutation, a collision, or a read hit. -/
theorem card_sub_card_schemeGood_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Fintype.card Tab - (schemeGood Q).card ≤
      (∑ t : Tab, if ¬PermGood t.1.perm G then 1 else 0) +
        ((∑ x, collInd G x) + ∑ i, ∑ a, ∑ x, hitInd G Q i a x) := by
  refine (card_sub_card_le_sum (schemeGood Q) (fun t ↦ (if ¬PermGood t.1.perm G then 1 else 0) +
    (collInd G (schemeSplit t) + ∑ i, ∑ a, hitInd G Q i a (schemeSplit t))) fun t ht ↦ ?_).trans_eq
    ?_
  · by_cases hG : PermGood t.1.perm G
    · have hG' : PermGood (schemeSplit t).1.1.2 G := by rw [schemeSplit_perm]; exact hG
      rw [mem_schemeGood] at ht
      by_cases hinj : Function.Injective (posOf (schemeSplit t).1 (schemeSplit t).2)
      · obtain ⟨i, a, ha⟩ : ∃ i a, posOf (schemeSplit t).1 (schemeSplit t).2 a ∈
            hCells (pubData Q (schemeSplit t).1 i).2 := by
          by_contra hne
          exact ht ⟨hinj, fun i a ha ↦ hne ⟨i, a, ha⟩⟩
        have h1 : 1 ≤ hitInd G Q i a (schemeSplit t) := by
          rw [hitInd, ite_eq_left (And.intro hG' ha)]
        have h2 : hitInd G Q i a (schemeSplit t) ≤ ∑ a', hitInd G Q i a' (schemeSplit t) :=
          Finset.single_le_sum (f := fun a' ↦ hitInd G Q i a' (schemeSplit t))
            (fun _ _ ↦ Nat.zero_le _) (by simp)
        have h3 : ∑ a', hitInd G Q i a' (schemeSplit t) ≤
            ∑ i', ∑ a', hitInd G Q i' a' (schemeSplit t) :=
          Finset.single_le_sum (f := fun i' ↦ ∑ a', hitInd G Q i' a' (schemeSplit t))
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        omega
      · have h1 : collInd G (schemeSplit t) = 1 := by
          rw [collInd, ite_eq_left (And.intro hG' hinj)]
        omega
    · have h1 : (if ¬PermGood t.1.perm G then 1 else 0) = 1 := ite_eq_left hG
      omega
  · rw [Finset.sum_add_distrib]
    refine congrArg (HAdd.hAdd _) ?_
    rw [Fintype.sum_equiv schemeSplit (fun t ↦ collInd G (schemeSplit t) +
        ∑ i, ∑ a, hitInd G Q i a (schemeSplit t))
      (fun x ↦ collInd G x + ∑ i, ∑ a, hitInd G Q i a x) fun _ ↦ rfl,
      Finset.sum_add_distrib (f := collInd G),
      Finset.sum_comm (f := fun x i ↦ ∑ a, hitInd G Q i a x)]
    refine congrArg (HAdd.hAdd _) ?_
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm (f := fun x a ↦ hitInd G Q i a x)]

/-- The tables with a bad permutation are the fraction of bad permutations. -/
theorem card_mul_sum_tab_not_permGood :
    Fintype.card (Equiv.Perm (X × Z)) * ∑ t : Tab, (if ¬PermGood t.1.perm G then 1 else 0) =
      Fintype.card Tab *
        (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card := by
  have h := card_mul_sum_fst_eq (γ := (SpongeKeys X Z × MasterSeed) × SeedSlots)
    (fun π : Equiv.Perm (X × Z) ↦ if ¬PermGood π G then 1 else 0)
    (Fintype.card (Equiv.Perm (X × Z)))
    (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card
    (by rw [Finset.card_filter])
  rw [Fintype.card_congr permSplit, Fintype.sum_equiv permSplit
    (fun t : Tab ↦ if ¬PermGood t.1.perm G then 1 else 0)
    (fun p ↦ if ¬PermGood p.1 G then 1 else 0) fun _ ↦ rfl]
  exact h

/-- **The bad fraction of the staged swap**: the fraction of tables outside `schemeGood Q` is at
most the fraction of permutations with a rate count above `G`, plus the collisions
`|A|² (G + 1) / |Z|` (`A = SkIdx`), plus per computation `qsᵢ / 2^256 + |A| (G + 1) qᵢ / |Z|`, where
`qᵢ` bounds the reads of `Q i` and `qsᵢ` its reads at `SK.seed`-keyed cells. -/
theorem schemeGood_frac_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i) :
    (Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ((Fintype.card SkIdx * Fintype.card SkIdx * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + Fintype.card SkIdx * (G + 1) * q i / Fintype.card Z) :=
  inv_mul_le_of_parts₁ Fintype.card_ne_zero (card_sub_card_schemeGood_le G Q)
    (natCast_le_mul_div_of_mul_le Fintype.card_ne_zero (card_mul_sum_tab_not_permGood G).le)
    (natCast_le_mul_div_of_mul_le Fintype.card_ne_zero (card_mul_sum_collInd_le G))
    (sum_hitInd_le G Q q qs hq hqs)

end split

/-! ## The secret key's cells, averaged over the table -/

section bound

open scoped Classical

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- The staged swap with `SK.seed` as the hidden coordinate (`SK.prf` public). -/
noncomputable def splitS : Tab ≃ (Pub × HashOutput) × MasterSeed :=
  schemeSplit.trans (((Equiv.refl Pub).prodCongr (Equiv.prodComm _ _)).trans
    (Equiv.prodAssoc _ _ _).symm)

/-- The staged swap with `SK.prf` as the hidden coordinate (`SK.seed` public). -/
noncomputable def splitP : Tab ≃ (Pub × MasterSeed) × HashOutput :=
  schemeSplit.trans (Equiv.prodAssoc _ _ _).symm

theorem splitS_fst_fst (t : Tab) : (splitS t).1.1 = (schemeSplit t).1 :=
  rfl

theorem splitS_snd (t : Tab) : (splitS t).2 = t.1.secretSeed := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [splitS, Equiv.trans_apply, he]
  rfl

theorem splitP_fst_fst (t : Tab) : (splitP t).1.1 = (schemeSplit t).1 :=
  rfl

theorem splitP_snd (t : Tab) : (splitP t).2 = t.1.prfKey := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [splitP, Equiv.trans_apply, he]
  rfl

/-- **The `SK.seed`-keyed cells, end to end.** Let the run of runtime 2 depend on the table only
through `π` and the challenger's honest data `schemeData Q` (computations of `PK.seed` and the
secrets' hashes, with at most `qᵢ` reads and `qsᵢ` at `SK.seed`-keyed `k`-cells), and let
`hid S` be `k`-cells each of which belongs to `hid S` for at most one seed. Then the mass of its
`j`-th call at `hid SK.seed`, averaged over the uniform table, is at most `2^-256` plus the bad
fraction of `schemeGood_frac_le`. -/
theorem avg_hiddenMass_secretSeed_le_of_schemeData {ι : Type} [Fintype ι] {β : ι → Type}
    (G : ℕ)
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i)
    (hid : MasterSeed → Set X)
    (hhid : ∀ x, ∑ S, (hid S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ 1) (m₀ : M)
    (y : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ π d, (ρ π d).PosSemidef) (hρ₁ : ∀ π d, ENNReal.ofReal (ρ π d).trace.re ≤ 1)
    (j : ℕ) :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ * ∑ L : HonestTable, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (hid L.secretSeed) ∅) (y L.perm (schemeData Q L))
        (ρ L.perm (schemeData Q L)) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          ((Fintype.card SkIdx * Fintype.card SkIdx * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 +
            Fintype.card SkIdx * (G + 1) * q i / Fintype.card Z)) := by
  set F : HonestTable → ℝ≥0∞ := fun L ↦ (runtime2 X Z m₀).queryWeight I
    (hiddenMass ∅ (hid L.secretSeed) ∅) (y L.perm (schemeData Q L))
    (ρ L.perm (schemeData Q L)) j
  have h := avg_hiddenMass_seed_le I splitS hid hhid m₀
    (fun t : Tab ↦ y t.1.perm (schemeData Q t.1)) (fun t ↦ ρ t.1.perm (schemeData Q t.1))
    (fun _ ↦ hρ _ _) (fun _ ↦ hρ₁ _ _) (fun p ↦ y p.1.1.2 (pubData Q p.1))
    (fun p ↦ ρ p.1.1.2 (pubData Q p.1)) (fun _ ↦ hρ _ _) (fun _ ↦ hρ₁ _ _) (schemeGood Q)
    (fun t ht ↦ by
      rw [splitS_fst_fst, schemeData_eq_of_mem ht, schemeSplit_perm]
      exact ⟨rfl, rfl⟩) j
  have hs : ∑ t : Tab, (runtime2 X Z m₀).queryWeight I
      (hiddenMass ∅ (hid (splitS t).2) ∅) (y t.1.perm (schemeData Q t.1))
      (ρ t.1.perm (schemeData Q t.1)) j = ∑ t : Tab, F t.1 :=
    Finset.sum_congr rfl fun t _ ↦ congrArg (fun S ↦ (runtime2 X Z m₀).queryWeight I
      (hiddenMass ∅ (hid S) ∅) (y t.1.perm (schemeData Q t.1))
      (ρ t.1.perm (schemeData Q t.1)) j) (splitS_snd t)
  rw [hs, inv_card_mul_sum_fst F] at h
  exact h.trans (add_le_add_right (schemeGood_frac_le G Q q qs hq hqs) _)

/-- **The `SK.prf`-keyed cells, end to end**: as `avg_hiddenMass_secretSeed_le_of_schemeData`,
for `k`-cells `hid R` keyed by `SK.prf`. -/
theorem avg_hiddenMass_prfKey_le_of_schemeData {ι : Type} [Fintype ι] {β : ι → Type}
    (G : ℕ)
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i)
    (hid : HashOutput → Set X)
    (hhid : ∀ x, ∑ R, (hid R).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ 1) (m₀ : M)
    (y : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ π d, (ρ π d).PosSemidef) (hρ₁ : ∀ π d, ENNReal.ofReal (ρ π d).trace.re ≤ 1)
    (j : ℕ) :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ * ∑ L : HonestTable, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (hid L.prfKey) ∅) (y L.perm (schemeData Q L))
        (ρ L.perm (schemeData Q L)) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          ((Fintype.card SkIdx * Fintype.card SkIdx * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 +
            Fintype.card SkIdx * (G + 1) * q i / Fintype.card Z)) := by
  set F : HonestTable → ℝ≥0∞ := fun L ↦ (runtime2 X Z m₀).queryWeight I
    (hiddenMass ∅ (hid L.prfKey) ∅) (y L.perm (schemeData Q L))
    (ρ L.perm (schemeData Q L)) j
  have h := avg_hiddenMass_seed_le I splitP hid hhid m₀
    (fun t : Tab ↦ y t.1.perm (schemeData Q t.1)) (fun t ↦ ρ t.1.perm (schemeData Q t.1))
    (fun _ ↦ hρ _ _) (fun _ ↦ hρ₁ _ _) (fun p ↦ y p.1.1.2 (pubData Q p.1))
    (fun p ↦ ρ p.1.1.2 (pubData Q p.1)) (fun _ ↦ hρ _ _) (fun _ ↦ hρ₁ _ _) (schemeGood Q)
    (fun t ht ↦ by
      rw [splitP_fst_fst, schemeData_eq_of_mem ht, schemeSplit_perm]
      exact ⟨rfl, rfl⟩) j
  have hs : ∑ t : Tab, (runtime2 X Z m₀).queryWeight I
      (hiddenMass ∅ (hid (splitP t).2) ∅) (y t.1.perm (schemeData Q t.1))
      (ρ t.1.perm (schemeData Q t.1)) j = ∑ t : Tab, F t.1 :=
    Finset.sum_congr rfl fun t _ ↦ congrArg (fun R ↦ (runtime2 X Z m₀).queryWeight I
      (hiddenMass ∅ (hid R) ∅) (y t.1.perm (schemeData Q t.1))
      (ρ t.1.perm (schemeData Q t.1)) j) (splitP_snd t)
  rw [hs, inv_card_mul_sum_fst F] at h
  exact h.trans (add_le_add_right (schemeGood_frac_le G Q q qs hq hqs) _)

end bound

end Quantum.Sphincs.Hybrid

end
