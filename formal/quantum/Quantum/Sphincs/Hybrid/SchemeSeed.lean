module

public import Quantum.Xmss.Hybrid.SchemeSplit
public import Quantum.Sphincs.HonestTable

@[expose] public section

/-!
# Hiding leanSPHINCS's secret key: the `SK.seed`-keyed cells

The exchanges of `h`-cells with extra slots (`fiberEquiv`, `xch`, `stage1`, `stageN`), the
capacities and rates of one-block inputs (`capOf`, `rateOf`) and their collision and read counts
(`card_mul_sum_capOf_eq_le`, `sum_capOf_mem_le`) are `Quantum.Xmss.Hybrid`'s, over abstract types.
This file adds leanSPHINCS's cells keyed by the secret key `SK.seed`:

* `instFintypeHonestTable`, `instFintypeKeygenDomain`: the tables and the secrets' domains are
  finite; `card_keygenDomain`, `card_skIdx_le` (`2^44` derivations).
* `skInput P S`, indexed by `SkIdx = Option (Option KeygenDomain)`: the derivation of `SK.prf`
  (`none`, `leanSPHINCS ‖ S ‖ 1`), of `PK.seed` (`some none`, `leanSPHINCS ‖ S ‖ 0`), and the
  secrets' `PRF` calls (`some (some d)`, `P ‖ ADRS(d) ‖ S`); all one block (`length_skInput_lt`).
* `skCell P S b`: their first blocks, the `k`-cells their hashing reads first. Distinct over the
  seed and the index (`skCell_injective`).
* `hash_of_lt`: a one-block hash is `out256` of the rate after its round plus `h` at its capacity.
  `prfKey_eq`, `publicSeed_eq`, `secret_eq`: the table's `SK.prf`, `PK.seed` and secrets are the
  hashes of `skInput`.
-/

open Quantum.Sponge Sphincs
open HashSig (Digest HashOutput PublicParameter HashInput MasterSeed littleEndianBytes
  truncateHash)
open Sphincs.KeyGenerationAndSigning (keyDerivationInput)
open Quantum.Xmss (X Z out256 trunc128 blocks blocks_injective length_littleEndianBytes)
open Quantum.Xmss.Hybrid (firstCell blocks_of_lt capOf rateOf)

namespace Quantum.Sphincs.Hybrid

/-! ## Finiteness -/

section finite

/-- The honest table as its fields. -/
def tableEquiv : HonestTable ≃ (SpongeKeys X Z × Equiv.Perm (X × Z)) × MasterSeed where
  toFun L := ((L.keys, L.perm), L.secretSeed)
  invFun q := ⟨q.1.1, q.1.2, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeHonestTable : Fintype HonestTable :=
  Fintype.ofEquiv _ tableEquiv.symm

instance instNonemptyHonestTable : Nonempty HonestTable :=
  ⟨⟨(fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0), Equiv.refl _, 0⟩⟩

/-- The secrets' domains: the chain starts and the FORS secrets. -/
def keygenDomainEquiv : KeygenDomain ≃
    (Layer × TreeIndex × TreeLeafIndex × ChainIndex) ⊕ (Index × ForsTreeIndex × ForsLeafIndex) where
  toFun
    | .oneTimeChain l τ e i => .inl (l, τ, e, i)
    | .forsSecret idx κ s => .inr (idx, κ, s)
  invFun
    | .inl (l, τ, e, i) => .oneTimeChain l τ e i
    | .inr (idx, κ, s) => .forsSecret idx κ s
  left_inv d := by cases d <;> rfl
  right_inv p := by rcases p with ⟨l, τ, e, i⟩ | ⟨idx, κ, s⟩ <;> rfl

instance instFintypeKeygenDomain : Fintype KeygenDomain :=
  Fintype.ofEquiv _ keygenDomainEquiv.symm

/-- The secrets: `3 · 2^26 · 2^10 · 64` chain starts and `2^26 · 24 · 2^10` FORS secrets (the
domains range over all trees and leaves). -/
theorem card_keygenDomain :
    Fintype.card KeygenDomain = 3 * 2 ^ 26 * 2 ^ 10 * 64 + 2 ^ 26 * 24 * 2 ^ 10 := by
  rw [Fintype.card_congr keygenDomainEquiv, Fintype.card_sum]
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount, indexBits, layerHeight, topLayer, chainCount, forsTreeCount,
    forsTreeHeight]

end finite

/-! ## The `SK.seed`-keyed cells -/

section cells

/-- The `SK.seed`-keyed derivations: `SK.prf` (`none`), `PK.seed` (`some none`), and the secrets
(`some (some d)`). -/
abbrev SkIdx : Type := Option (Option KeygenDomain)

theorem card_skIdx : Fintype.card SkIdx = Fintype.card KeygenDomain + 1 + 1 := by
  rw [Fintype.card_option, Fintype.card_option]

/-- At most `2^44` `SK.seed`-keyed derivations. -/
theorem card_skIdx_le : Fintype.card SkIdx ≤ 2 ^ 44 := by
  rw [card_skIdx, card_keygenDomain]
  norm_num

/-- A secret's `PRF` call `P ‖ ADRS(d) ‖ S`. -/
def prfInput (P : PublicParameter) (S : MasterSeed) (d : KeygenDomain) : HashInput :=
  addressedHashInput P (keygenDomainFields d) (littleEndianBytes 32 S)

/-- The `SK.seed`-keyed inputs: `leanSPHINCS ‖ S ‖ 1` (`SK.prf`), `leanSPHINCS ‖ S ‖ 0`
(`PK.seed`), and the secrets' `PRF` calls under the public seed `P`. -/
def skInput (P : PublicParameter) (S : MasterSeed) : SkIdx → HashInput
  | none => keyDerivationInput S 1
  | some none => keyDerivationInput S 0
  | some (some d) => prfInput P S d

/-- The `SK.seed`-keyed cells: the first blocks of the `SK.seed`-keyed inputs. -/
def skCell (P : PublicParameter) (S : MasterSeed) (b : SkIdx) : X :=
  firstCell (skInput P S b)

theorem length_prfInput (P : PublicParameter) (S : MasterSeed) (d : KeygenDomain) :
    (prfInput P S d).length = 80 := by
  rw [prfInput, length_addressedHashInput, length_littleEndianBytes]

theorem length_skInput_lt (P : PublicParameter) (S : MasterSeed) :
    ∀ b : SkIdx, (skInput P S b).length < 136
  | none => by rw [skInput, length_keyDerivationInput]; norm_num
  | some none => by rw [skInput, length_keyDerivationInput]; norm_num
  | some (some d) => by rw [skInput, length_prfInput]; norm_num

/-- One-block inputs with the same first block are equal. -/
theorem eq_of_firstCell_eq {a b : HashInput} (ha : a.length < 136) (hb : b.length < 136)
    (h : firstCell a = firstCell b) : a = b :=
  blocks_injective (by rw [blocks_of_lt a ha, blocks_of_lt b hb, h])

/-- **The `SK.seed`-keyed inputs are distinct**: an input names its seed and its derivation. -/
theorem skInput_injective (P : PublicParameter) :
    Function.Injective fun q : MasterSeed × SkIdx ↦ skInput P q.1 q.2 := by
  rintro ⟨S, b⟩ ⟨S', b'⟩ h
  simp only at h
  have hl := congrArg List.length h
  rcases b with _ | _ | d <;> rcases b' with _ | _ | d' <;>
    simp only [skInput] at h hl
  · rw [(keyDerivationInput_injective h).1]
  · exact absurd (keyDerivationInput_injective h).2 (by decide)
  · rw [length_keyDerivationInput, length_prfInput] at hl
    exact absurd hl (by norm_num)
  · exact absurd (keyDerivationInput_injective h).2 (by decide)
  · rw [(keyDerivationInput_injective h).1]
  · rw [length_keyDerivationInput, length_prfInput] at hl
    exact absurd hl (by norm_num)
  · rw [length_keyDerivationInput, length_prfInput] at hl
    exact absurd hl (by norm_num)
  · rw [length_keyDerivationInput, length_prfInput] at hl
    exact absurd hl (by norm_num)
  · obtain ⟨ha, hp⟩ := addressedHashInput_injective P h
    rw [keygenDomainFields_injective ha, littleEndianBytes_injective 32 hp]

/-- **The `SK.seed`-keyed cells are distinct.** -/
theorem skCell_injective (P : PublicParameter) :
    Function.Injective fun q : MasterSeed × SkIdx ↦ skCell P q.1 q.2 := fun q q' h ↦
  skInput_injective P (eq_of_firstCell_eq (length_skInput_lt P q.1 q.2)
    (length_skInput_lt P q'.1 q'.2) h)

theorem skCell_injective_idx (P : PublicParameter) (S : MasterSeed) :
    Function.Injective (skCell P S) := fun b b' h ↦
  congrArg Prod.snd (skCell_injective P (a₁ := (S, b)) (a₂ := (S, b')) h)

/-- **The hash of a one-block input**: `out256` of the rate after its round plus `h` at its
capacity. -/
theorem hash_of_lt (L : HonestTable) (inp : HashInput) (h : inp.length < 136) :
    L.hash inp = out256 (rateOf L.keys.2.1 L.perm (firstCell inp) +
      L.keys.1 (capOf L.keys.2.1 L.keys.2.2 L.perm (firstCell inp))) := by
  show out256 (spongeHash (spongePerm L.keys L.perm) (blocks inp)) = _
  rw [blocks_of_lt inp h]
  simp only [spongeHash, absorb, List.foldl_cons, List.foldl_nil, absorbStep, spongePerm,
    Equiv.Perm.mul_apply, rateRound_apply, capacityRound_apply, zero_add, rateOf, capOf]

/-- The hash of an `SK.seed`-keyed input. -/
theorem hash_skInput (L : HonestTable) (P : PublicParameter) (S : MasterSeed) (b : SkIdx) :
    L.hash (skInput P S b) = out256 (rateOf L.keys.2.1 L.perm (skCell P S b) +
      L.keys.1 (capOf L.keys.2.1 L.keys.2.2 L.perm (skCell P S b))) :=
  hash_of_lt L _ (length_skInput_lt P S b)

theorem prfKey_eq (L : HonestTable) (P : PublicParameter) :
    L.prfKey = L.hash (skInput P L.secretSeed none) :=
  rfl

theorem publicSeed_eq (L : HonestTable) (P : PublicParameter) :
    L.publicSeed = truncateHash (L.hash (skInput P L.secretSeed (some none))) :=
  rfl

theorem secret_eq (L : HonestTable) (d : KeygenDomain) :
    L.secret d = truncateHash (L.hash (skInput L.publicSeed L.secretSeed (some (some d)))) :=
  rfl

theorem trunc128_eq_truncateHash (x : X) : trunc128 x = truncateHash (out256 x) :=
  rfl

end cells

end Quantum.Sphincs.Hybrid

end
