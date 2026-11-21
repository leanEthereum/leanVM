module

public import Quantum.Sphincs.Hybrid.SchemeSplit

@[expose] public section

/-!
# The key-level cells of leanSPHINCS's hidden-cell hybrid

`Quantum.Xmss.Hybrid.View` bounds the average mass at `k`-cells `hid S` that hold a hidden seed
`S` (`avg_hiddenMass_seed_le`: one seed per cell, `2^-256` per call). This file gives leanSPHINCS's
cells that hold its secret key and its randomizers.

* `skSeedOf x`, `skSeedCells S`: the `SK.seed` a block holds where the `SK.seed`-keyed inputs put
  it, bytes `11` to `42` of a block padded as a `44`-byte input (the key expansion
  `leanSPHINCS ‖ SK.seed ‖ d`) and bytes `48` to `79` otherwise (a secret's `PRF` call
  `PK.seed ‖ ADRS ‖ SK.seed`). Every `SK.seed`-keyed cell holds its seed (`skSeedOf_skCell`); a
  cell lies in `skSeedCells S` for exactly one `S` (`sum_indicator_skSeedCells`).
* `prfMsgCell R o M`, `prfKeyCells R`: the first block of `PRF_msg` on `R ‖ o ‖ M'`, and the blocks
  whose bytes `0` to `31` are `R`. `PRF_msg` under `SK.prf = R` reads `k` first in
  `prfKeyCells R` (`prfMsgCell_mem_prfKeyCells`), in particular the honest randomizers'
  (`randomizerCell_mem_prfKeyCells`); one key per cell (`sum_indicator_prfKeyCells`).
* `hmsgCell R P root M i`: the first (only) block of `H_msg` call `i`. Under the key
  (`P = PK.seed`, `root = PK.root`) it names its message (`hmsgMsg_hmsgCell`, `hmsgMsg` reads the
  slot of a one-block tail) and holds its randomizer in bytes `0` to `15` (`rndOf_hmsgCell`); the
  honest calls hold `R(M)` (`hmsgMsg_digestCell`, `rndOf_digestCell`).
* `avg_hiddenMass_skSeed_le`, `avg_hiddenMass_prfKey_le`: the seed-level view lemma at
  `skSeedCells` and `prfKeyCells` for a reparametrization hiding `SK.seed`, respectively `SK.prf`.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput MasterSeed
  littleEndianBytes hasherInput)
open Sphincs.KeyGenerationAndSigning (keyDerivationInput)
open Quantum.Xmss (X Z rateSlice blockOf firstBlock firstBlock_of_lt length_littleEndianBytes)
open Quantum.Xmss.Hybrid (firstCell runtime2 hiddenMass avg_hiddenMass_seed_le)

namespace Quantum.Sphincs.Hybrid

/-! ## The `SK.seed`-keyed cells -/

section skSeed

/-- **The `SK.seed` a block holds**: bits `88` to `343` (bytes `11` to `42`) of a block padded as
a `44`-byte input, where the key expansion `leanSPHINCS ‖ SK.seed ‖ d` puts it; bits `384` to `639`
(bytes `48` to `79`) otherwise, where a secret's `PRF` call `PK.seed ‖ ADRS ‖ SK.seed` puts it. -/
def skSeedOf (x : X) : MasterSeed :=
  if PadShaped 44 x then rateSlice x 88 (8 * 32) (by norm_num)
  else rateSlice x 384 (8 * 32) (by norm_num)

/-- The cells holding `SK.seed = S`. -/
def skSeedCells (S : MasterSeed) : Set X :=
  {x | skSeedOf x = S}

/-- A cell lies in `skSeedCells S` for exactly one `S`. -/
theorem sum_indicator_skSeedCells (x : X) :
    ∑ S, (skSeedCells S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x = 1 := by
  classical
  simp only [Set.indicator_apply, skSeedCells, Set.mem_ofPred_eq]
  rw [Finset.sum_ite_eq]
  simp

/-- A one-block input's first cell is padded at its length. -/
theorem padShaped_firstCell (input : HashInput) (h : input.length < 136) :
    PadShaped input.length (firstCell input) := by
  rw [firstCell, firstBlock_of_lt _ h]
  exact padShaped_padBlock input h

theorem skSeedOf_of_padShaped {x : X} (h : PadShaped 44 x) :
    skSeedOf x = rateSlice x 88 (8 * 32) (by norm_num) :=
  ite_eq_left h

theorem skSeedOf_of_not_padShaped {x : X} (h : ¬PadShaped 44 x) :
    skSeedOf x = rateSlice x 384 (8 * 32) (by norm_num) :=
  ite_eq_right h

/-- **Every `SK.seed`-keyed cell holds its seed.** -/
theorem skSeedOf_skCell (P : PublicParameter) (S : MasterSeed) (b : SkIdx) :
    skSeedOf (skCell P S b) = S := by
  have h136 := length_skInput_lt P S b
  have hshape := padShaped_firstCell _ h136
  rcases b with _ | _ | d
  · rw [show (skInput P S none).length = 44 from length_keyDerivationInput S 1] at hshape
    exact (skSeedOf_of_padShaped hshape).trans (rateSlice_firstBlock
      (input := skInput P S none) (a := seedTag) (s := 88) (n := 32) ⟨[1], rfl⟩ (by rfl)
      (by norm_num))
  · rw [show (skInput P S (some none)).length = 44 from length_keyDerivationInput S 0] at hshape
    exact (skSeedOf_of_padShaped hshape).trans (rateSlice_firstBlock
      (input := skInput P S (some none)) (a := seedTag) (s := 88) (n := 32) ⟨[0], rfl⟩ (by rfl)
      (by norm_num))
  · rw [show (skInput P S (some (some d))).length = 80 from length_prfInput P S d] at hshape
    refine (skSeedOf_of_not_padShaped fun h ↦ absurd
      (padShaped_unique (by norm_num) (by norm_num) hshape h) (by norm_num)).trans
      (rateSlice_firstBlock (input := skInput P S (some (some d)))
        (a := littleEndianBytes 16 P ++ (keygenDomainFields d).toBytes) (s := 384) (n := 32)
        ⟨[], List.append_nil _⟩ ?_ (by norm_num))
    rw [List.length_append, length_littleEndianBytes, length_toBytes]

theorem skCell_mem_skSeedCells (P : PublicParameter) (S : MasterSeed) (b : SkIdx) :
    skCell P S b ∈ skSeedCells S :=
  skSeedOf_skCell P S b

end skSeed

/-! ## The `SK.prf`-keyed cells -/

section prfKey

/-- The first (only) block of `PRF_msg` on `R ‖ o ‖ M'`. -/
def prfMsgCell (R : HashOutput) (o : Digest) (M : Message) : X :=
  firstCell (prfMessageInput R o M)

/-- **The `SK.prf` a block holds**: bits `0` to `255`, where `PRF_msg` puts it. -/
def prfKeyOf (x : X) : HashOutput :=
  rateSlice x 0 (8 * 32) (by norm_num)

/-- The cells holding `SK.prf = R`. -/
def prfKeyCells (R : HashOutput) : Set X :=
  {x | prfKeyOf x = R}

/-- A cell lies in `prfKeyCells R` for exactly one `R`. -/
theorem sum_indicator_prfKeyCells (x : X) :
    ∑ R, (prfKeyCells R).indicator (fun _ ↦ (1 : ℝ≥0∞)) x = 1 := by
  classical
  simp only [Set.indicator_apply, prfKeyCells, Set.mem_ofPred_eq]
  rw [Finset.sum_ite_eq]
  simp

theorem prfKeyOf_prfMsgCell (R : HashOutput) (o : Digest) (M : Message) :
    prfKeyOf (prfMsgCell R o M) = R :=
  rateSlice_firstBlock (input := prfMessageInput R o M) (a := []) (n := 32)
    (by simp [prfMessageInput, List.append_assoc]) rfl (by norm_num)

/-- **`PRF_msg` under `SK.prf = R` reads `k` first in `prfKeyCells R`.** -/
theorem prfMsgCell_mem_prfKeyCells (R : HashOutput) (o : Digest) (M : Message) :
    prfMsgCell R o M ∈ prfKeyCells R :=
  prfKeyOf_prfMsgCell R o M

/-- The honest randomizer `R(M)` is `PRF_msg` on the first block `prfMsgCell SK.prf PK.seed M`,
which holds `SK.prf`. -/
theorem randomizerCell_mem_prfKeyCells (L : HonestTable) (M : Message) :
    prfMsgCell L.prfKey L.publicSeed M ∈ prfKeyCells L.prfKey :=
  prfMsgCell_mem_prfKeyCells _ _ _

end prfKey

/-! ## The `H_msg` cells -/

section hmsg

/-- The first (only) block of `H_msg` call `i` on `R ‖ P ‖ root ‖ M`. -/
def hmsgCell (R : Randomizer) (P : PublicParameter) (root : Digest) (M : Message)
    (i : DigestCall) : X :=
  firstCell (messageDigestInput R P root M i)

/-- The randomizer a block holds where an `H_msg` input puts it: bits `0` to `127`. -/
def rndOf (x : X) : Randomizer :=
  rateSlice x 0 (8 * 16) (by norm_num)

/-- The message a one-block tail names for the key `pk`, when its slot is an `H_msg` call. -/
def hmsgMsg (pk : PublicKey) (x : X) : Option Message :=
  match slotOfOneBlock pk x with
  | some (.hmsg _ M _) => some M
  | _ => none

theorem rndOf_hmsgCell (R : Randomizer) (P : PublicParameter) (root : Digest) (M : Message)
    (i : DigestCall) : rndOf (hmsgCell R P root M i) = R :=
  rateSlice_firstBlock (input := messageDigestInput R P root M i) (a := []) (n := 16)
    (by simp [messageDigestInput, List.append_assoc]) rfl (by norm_num)

/-- **An `H_msg` call under the key is an `hmsg` slot**, read from its only block. -/
theorem slotOfOneBlock_hmsgCell (pk : PublicKey) (R : Randomizer) (M : Message)
    (i : DigestCall) :
    slotOfOneBlock pk (hmsgCell R pk.publicSeed pk.root M i) = some (.hmsg R M i) := by
  have h136 : (messageDigestInput R pk.publicSeed pk.root M i).length < 136 := by
    rw [length_messageDigestInput]
    norm_num
  have h := slotOf_messageDigestInput_self (Equiv.refl _) pk R M i
  rwa [absorbTail_blocks_of_lt _ _ h136, slotOf_singleton, ← firstBlock_of_lt _ h136] at h

/-- A one-block tail whose slot is an `H_msg` call names its message. -/
theorem hmsgMsg_of_slotOfOneBlock {pk : PublicKey} {x : X} {R : Randomizer} {M : Message}
    {i : DigestCall} (h : slotOfOneBlock pk x = some (.hmsg R M i)) : hmsgMsg pk x = some M := by
  unfold hmsgMsg
  rw [h]

/-- **An `H_msg` block under the key names its message.** -/
theorem hmsgMsg_hmsgCell (pk : PublicKey) (R : Randomizer) (M : Message) (i : DigestCall) :
    hmsgMsg pk (hmsgCell R pk.publicSeed pk.root M i) = some M :=
  hmsgMsg_of_slotOfOneBlock (slotOfOneBlock_hmsgCell pk R M i)

/-- The honest `H_msg` calls name their message. -/
theorem hmsgMsg_digestCell (L : HonestTable) (M : Message) (i : DigestCall) :
    hmsgMsg L.publicKey (hmsgCell (L.randomizer M) L.publicSeed L.root M i) = some M :=
  hmsgMsg_hmsgCell L.publicKey (L.randomizer M) M i

/-- The honest `H_msg` calls hold `R(M)`. -/
theorem rndOf_digestCell (L : HonestTable) (M : Message) (i : DigestCall) :
    rndOf (hmsgCell (L.randomizer M) L.publicSeed L.root M i) = L.randomizer M :=
  rndOf_hmsgCell _ _ _ _ _

end hmsg

/-! ## The key-level mass bounds -/

section bound

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The `SK.seed` cells.** For a reparametrization `e` whose hidden coordinate is `SK.seed`, if on
`G` the run is a function of the public part, the mass of the `j`-th call of runtime 2 at
`skSeedCells SK.seed` (the first blocks of `SK.prf`'s, `PK.seed`'s and the secrets' derivations),
averaged over the tables, is at most `2^-256` plus the fraction of tables outside `G`. -/
theorem avg_hiddenMass_skSeed_le {Θ P : Type*} [Fintype Θ] [Fintype P]
    (e : Θ ≃ P × MasterSeed) (m₀ : M) (xθ : Θ → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρθ : Θ → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρθ : ∀ θ, (ρθ θ).PosSemidef) (hρθ₁ : ∀ θ, ENNReal.ofReal (ρθ θ).trace.re ≤ 1)
    (x : P → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : P → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ p, (ρ p).PosSemidef) (hρ₁ : ∀ p, ENNReal.ofReal (ρ p).trace.re ≤ 1)
    (G : Finset Θ) (hG : ∀ θ ∈ G, xθ θ = x (e θ).1 ∧ ρθ θ = ρ (e θ).1) (j : ℕ) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (skSeedCells (e θ).2) ∅) (xθ θ) (ρθ θ) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) :=
  avg_hiddenMass_seed_le I e skSeedCells (fun x ↦ (sum_indicator_skSeedCells x).le) m₀
    xθ ρθ hρθ hρθ₁ x ρ hρ hρ₁ G hG j

/-- **The `SK.prf` cells.** As `avg_hiddenMass_skSeed_le`, for a reparametrization whose hidden
coordinate is `SK.prf`, at `prfKeyCells SK.prf` (the first blocks of `PRF_msg`). -/
theorem avg_hiddenMass_prfKey_le {Θ P : Type*} [Fintype Θ] [Fintype P]
    (e : Θ ≃ P × HashOutput) (m₀ : M) (xθ : Θ → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρθ : Θ → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρθ : ∀ θ, (ρθ θ).PosSemidef) (hρθ₁ : ∀ θ, ENNReal.ofReal (ρθ θ).trace.re ≤ 1)
    (x : P → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : P → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ p, (ρ p).PosSemidef) (hρ₁ : ∀ p, ENNReal.ofReal (ρ p).trace.re ≤ 1)
    (G : Finset Θ) (hG : ∀ θ ∈ G, xθ θ = x (e θ).1 ∧ ρθ θ = ρ (e θ).1) (j : ℕ) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (prfKeyCells (e θ).2) ∅) (xθ θ) (ρθ θ) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) :=
  avg_hiddenMass_seed_le I e prfKeyCells (fun x ↦ (sum_indicator_prfKeyCells x).le) m₀
    xθ ρθ hρθ hρθ₁ x ρ hρ hρ₁ G hG j

end bound

end Quantum.Sphincs.Hybrid

end
