module

public import Quantum.Sphincs.Hybrid.View

@[expose] public section

/-!
# leanSPHINCS's secret-key cells, averaged over the table

`Quantum.Sphincs.Hybrid.SchemeSplit` bounds the mass at cells keyed by `SK.seed` or `SK.prf` when
the run depends on the table through `π` and the challenger's honest data `schemeData Q`
(`avg_hiddenMass_secretSeed_le_of_schemeData`), given a bound `qsᵢ` on the `SK.seed`-keyed `k`-reads
of each computation `Q i`. This file counts those reads (leanXMSS's
`card_filter_seedShaped_kCells_le`) and fixes the cells.

* `SkInput P inp`: `inp` is an `SK.seed`-keyed input under `PK.seed = P`. A one-block input's first
  block is an `SK.seed`-keyed cell only if the input is one (`skInput_of_skCell_eq`).
* `card_filter_skCell_kCells_le`: the `SK.seed`-keyed `k`-reads of an honest evaluation come from
  its `SK.seed`-keyed inputs and its inputs of more than one block, at most three reads per block.
  `SK.seed`-keyed inputs have `44` or `80` bytes (`length_skInput`); a tweakable hash at an in-range
  domain is never one (`not_skInput_addressedHashInput`, its address is not a `PRF` address), nor is
  an input of any other length (`not_skInput_of_length`: `H_msg`, `84` bytes, and `PRF_msg`, `93`).
  So a computation that queries no `SK.seed`-keyed input reads such cells only in its multi-block
  inputs (`card_filter_skCell_kCells_le_of_forall`).
* `avg_hiddenMass_skSeedCells_le_of_schemeData`, `avg_hiddenMass_prfKeyCells_le_of_schemeData`:
  the bounds of `Quantum.Sphincs.Hybrid.SchemeSplit` at `skSeedCells` and `prfKeyCells`: `2^-256`
  per call plus the fraction of `schemeGood_frac_le`.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w

open Quantum.SufCma

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput PublicParameter HashInput MasterSeed littleEndianBytes hasherInput)
open Common.SufCma (SchemeHashSpec)
open Quantum.Xmss (X Z blocks blockOf firstBlock_of_lt length_littleEndianBytes)
open LeanVM.Protocol.KeccakHash (padBlock)
open Quantum.Xmss.Hybrid (firstCell kCells runtime2 hiddenMass card_filter_kCells_flatMap_le
  sum_map_le_sum_map kCells_inputReads_of_lt card_kCells_le)

namespace Quantum.Sphincs.Hybrid

/-! ## Counting the `SK.seed`-keyed reads -/

section count

/-- `inp` is an `SK.seed`-keyed input under `PK.seed = P`. -/
def SkInput (P : PublicParameter) (inp : HashInput) : Prop :=
  ∃ S b, skInput P S b = inp

/-- `SK.seed`-keyed inputs have `44` bytes (the key expansion) or `80` (a secret's `PRF` call). -/
theorem length_skInput (P : PublicParameter) (S : MasterSeed) :
    ∀ b : SkIdx, (skInput P S b).length = 44 ∨ (skInput P S b).length = 80
  | none => Or.inl (length_keyDerivationInput S 1)
  | some none => Or.inl (length_keyDerivationInput S 0)
  | some (some d) => Or.inr (length_prfInput P S d)

theorem not_skInput_of_length {P : PublicParameter} {inp : HashInput} (h44 : inp.length ≠ 44)
    (h80 : inp.length ≠ 80) : ¬SkInput P inp := by
  rintro ⟨S, b, rfl⟩
  rcases length_skInput P S b with h | h
  exacts [h44 h, h80 h]

/-- **A tweakable hash is never `SK.seed`-keyed**: its address, at an in-range domain, is not a
`PRF` address. -/
theorem not_skInput_addressedHashInput (P Q : PublicParameter) {d : HashDomain}
    (hd : DomainInRange d) (p : HashInput) :
    ¬SkInput P (addressedHashInput Q (hashDomainFields d) p) := by
  rintro ⟨S, b, h⟩
  have hl := congrArg List.length h
  rw [length_addressedHashInput] at hl
  rcases b with _ | _ | k
  · rw [show (skInput P S none).length = 44 from length_keyDerivationInput S 1] at hl
    omega
  · rw [show (skInput P S (some none)).length = 44 from length_keyDerivationInput S 0] at hl
    omega
  · change addressedHashInput P (keygenDomainFields k) (littleEndianBytes 32 S) = _ at h
    unfold addressedHashInput hasherInput at h
    obtain ⟨h1, -⟩ := List.append_inj h (by simp [length_littleEndianBytes, length_toBytes])
    obtain ⟨-, h2⟩ := List.append_inj h1 (by simp [length_littleEndianBytes])
    exact hashDomainFields_ne_keygenDomainFields hd k (toBytes_injective h2).symm

/-- **A one-block input whose first block is `SK.seed`-keyed is `SK.seed`-keyed.** -/
theorem skInput_of_skCell_eq {P : PublicParameter} {inp : HashInput} (h136 : inp.length < 136)
    {S : MasterSeed} {b : SkIdx} (h : skCell P S b = firstCell inp) : SkInput P inp :=
  ⟨S, b, eq_of_firstCell_eq (length_skInput_lt P S b) h136 h⟩

open scoped Classical in
/-- **`SK.seed`-keyed `k`-reads come from `SK.seed`-keyed and multi-block inputs.** A one-block
input that is not `SK.seed`-keyed is read by `k` at its first block only, which is no
`SK.seed`-keyed cell; the others contribute at most their three reads per block. -/
theorem card_filter_skCell_kCells_le (P : PublicParameter)
    [DecidablePred fun y ↦ ∃ S b, skCell P S b = y] {α : Type}
    (x : OracleComp SchemeHashSpec α) (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) :
    ((kCells (honestEval t π x).2).filter fun y ↦ ∃ S b, skCell P S b = y).card ≤
      ((queries (spongeOut (spongePerm t π)) x).map fun inp ↦
        if inp.length < 136 ∧ ¬SkInput P inp then 0 else 3 * (blocks inp).length).sum := by
  rw [snd_honestEval]
  refine (card_filter_kCells_flatMap_le _ _ _).trans (sum_map_le_sum_map _ _ _ fun inp ↦ ?_)
  split_ifs with hs
  · have hne : ¬∃ S b, skCell P S b = blockOf (padBlock inp) := by
      rintro ⟨S, b, hb⟩
      exact hs.2 (skInput_of_skCell_eq hs.1
        (hb.trans (by rw [firstCell, firstBlock_of_lt _ hs.1])))
    rw [kCells_inputReads_of_lt π t inp hs.1, Finset.filter_singleton, ite_eq_right hne,
      Finset.card_empty]
  · refine (Finset.card_filter_le _ _).trans ((card_kCells_le _).trans ?_)
    rw [inputReads, length_spongeReads]

open scoped Classical in
/-- A computation that queries no `SK.seed`-keyed input reads `SK.seed`-keyed cells only in its
inputs of more than one block, three per block. -/
theorem card_filter_skCell_kCells_le_of_forall (P : PublicParameter)
    [DecidablePred fun y ↦ ∃ S b, skCell P S b = y] {α : Type}
    (x : OracleComp SchemeHashSpec α) (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (hx : ∀ inp ∈ queries (spongeOut (spongePerm t π)) x, ¬SkInput P inp) :
    ((kCells (honestEval t π x).2).filter fun y ↦ ∃ S b, skCell P S b = y).card ≤
      ((queries (spongeOut (spongePerm t π)) x).map fun inp ↦
        if inp.length < 136 then 0 else 3 * (blocks inp).length).sum := by
  refine (card_filter_skCell_kCells_le P x t π).trans (le_of_eq (congrArg List.sum
    (List.map_congr_left fun inp hinp ↦ ?_)))
  by_cases h : inp.length < 136
  · rw [ite_eq_left ⟨h, hx inp hinp⟩, ite_eq_left h]
  · rw [ite_eq_right fun h' ↦ h h'.1, ite_eq_right h]

end count

/-! ## The secret-key cells, end to end -/

section bound

open scoped Classical

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The `SK.seed` cells, end to end**: `avg_hiddenMass_secretSeed_le_of_schemeData` at
`skSeedCells`. -/
theorem avg_hiddenMass_skSeedCells_le_of_schemeData {ι : Type} [Fintype ι] {β : ι → Type}
    (G : ℕ)
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i)
    (m₀ : M)
    (y : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ π d, (ρ π d).PosSemidef) (hρ₁ : ∀ π d, ENNReal.ofReal (ρ π d).trace.re ≤ 1)
    (j : ℕ) :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ * ∑ L : HonestTable, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (skSeedCells L.secretSeed) ∅) (y L.perm (schemeData Q L))
        (ρ L.perm (schemeData Q L)) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          ((Fintype.card SkIdx * Fintype.card SkIdx * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 +
            Fintype.card SkIdx * (G + 1) * q i / Fintype.card Z)) :=
  avg_hiddenMass_secretSeed_le_of_schemeData I G Q q qs hq hqs skSeedCells
    (fun x ↦ (sum_indicator_skSeedCells x).le) m₀ y ρ hρ hρ₁ j

/-- **The `SK.prf` cells, end to end**: `avg_hiddenMass_prfKey_le_of_schemeData` at
`prfKeyCells`, which hold the first blocks of `PRF_msg`. -/
theorem avg_hiddenMass_prfKeyCells_le_of_schemeData {ι : Type} [Fintype ι] {β : ι → Type}
    (G : ℕ)
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i)
    (m₀ : M)
    (y : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ π d, (ρ π d).PosSemidef) (hρ₁ : ∀ π d, ENNReal.ofReal (ρ π d).trace.re ≤ 1)
    (j : ℕ) :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ * ∑ L : HonestTable, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (prfKeyCells L.prfKey) ∅) (y L.perm (schemeData Q L))
        (ρ L.perm (schemeData Q L)) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          ((Fintype.card SkIdx * Fintype.card SkIdx * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 +
            Fintype.card SkIdx * (G + 1) * q i / Fintype.card Z)) :=
  avg_hiddenMass_prfKey_le_of_schemeData I G Q q qs hq hqs prfKeyCells
    (fun x ↦ (sum_indicator_prfKeyCells x).le) m₀ y ρ hρ hρ₁ j

end bound

end Quantum.Sphincs.Hybrid

end
