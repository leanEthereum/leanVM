module

public import Quantum.Sphincs.Assembly.ReparamFull.Coords

@[expose] public section

/-!
# The composed reparametrization of leanSPHINCS's tables: the stages' facts

What the stages of `Quantum.Sphincs.Assembly.ReparamFull.Coords` do, in the projections later
proofs read.

* **The fix-ups** (`rHiE_spec`, `sHiE_spec`): each replaces `h` and its slots; the slots keep
  their first `256` bits; at a fixed capacity the new `h` value has the bits from `256` on of the
  slot plus the shift; elsewhere `h` is kept.
* **SchemeSplit's slots** (`skSlotsX_schemeSplit`): when the hidden capacities are distinct, the
  slot of each `SK.seed`-keyed path is its rate plus the table's `h` at its capacity.
-/

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed truncateHash)
open Quantum.Xmss (X Z out256 trunc128)
open Common.SufCma (SchemeHashSpec)
open Quantum.Xmss.Hybrid (CoinSlots IsFirst capOf rateOf xch xch_snd_mk)
open Quantum.Sphincs.Hybrid (DSt DTab DF PubSlots Secret SeedKS SkIdx Tab DLab rOrd
  rCell dPre dGood mem_dGood rGood mem_rGood rSplit rSplit_keys_eq
  pCellK_rSplit pCellH_rSplit pCellK' rCellK rCellK' rCellH cellP rSplit_slots rSplit_snd
  rSplit_perm rSplit_coords rCell_injective skCell_ne_rCell schemeSplit_keys_snd
  skCell posOf schemeSplit schemeSplit_of_injective posOf_schemeSplit
  schemeSplit_transfer pubParam pCellH pCellK slot0 slot1 capR capP posB shB wB hA out256_slot0
  skCell_none skCell_some_none skCell_some_some prfKeyCell pubSeedCell secretCell rB mem_rB)

namespace Quantum.Sphincs.Assembly

/-! ## The fix-ups -/

section fixes

/-- `h` and the randomizer slots replaced. -/
def setHR (y : DS) (h : Z → X) (rhc : Message → X) : DS :=
  (((((h, y.1.1.1.1.2), y.1.1.1.2), y.1.1.2), y.1.2), ((y.2.1.1, y.2.1.2.1, rhc), y.2.2))

/-- The randomizer labels' capacities read off the coordinates (DigestStage's `dRCap`). -/
def rPosY (y : DS) (M : Message) : Z :=
  (y.1.1.1.2 (rCell M (trunc128 y.1.1.2.2.1) y.2.2.2, y.2.1.1 M)).2 + y.2.1.2.1 M

/-- The randomizer labels' rates read off the coordinates. -/
def rShY (y : DS) (M : Message) : X :=
  (y.1.1.1.2 (rCell M (trunc128 y.1.1.2.2.1) y.2.2.2, y.2.1.1 M)).1

/-- **The randomizer fix**: `h` and the randomizer slots replaced, as the digest fix. -/
theorem rHiE_spec (y : DS) :
    ∃ (h' : Z → X) (rhc' : Message → X), rHiE y = setHR y h' rhc' ∧
      (∀ M, out256 (rhc' M) = out256 (y.2.1.2.2 M)) ∧
      (∀ M, IsFirst rOrd (rPosY y) M →
        h' (rPosY y M) = hiMix (y.1.1.1.1.1 (rPosY y M)) (y.2.1.2.2 M + rShY y M)) ∧
      ∀ z, (∀ M, IsFirst rOrd (rPosY y) M → rPosY y M ≠ z) → h' z = y.1.1.1.1.1 z := by
  obtain ⟨h', u', he, h1, h2, -, h4⟩ := hiStageOn_spec rFW rPosW rShW rFW_inj y.1.1.1.1.1
    y.2.1.2.2 (rView y).2
  refine ⟨h', u', ?_, h1, fun a ha ↦ (h2 a ha).2, h4⟩
  show rView.symm (hiStageOn rFW rPosW rShW rFW_inj ((y.1.1.1.1.1, y.2.1.2.2), (rView y).2)) = _
  rw [he]
  rfl

/-- `h` and SchemeSplit's slots replaced. -/
def setHS (y : DS) (h : Z → X) (sl : SkIdx → X) : DS :=
  sView.symm ((h, sl), (sView y).2)

/-- The `SK.seed`-keyed capacities read off the coordinates. -/
def sPosY (y : DS) (a : SkIdx) : Z :=
  capOf y.1.1.1.1.2.1 y.1.1.1.1.2.2 y.1.1.1.2 (skCell (trunc128 y.1.1.2.2.1) y.2.2.1 a)

/-- The `SK.seed`-keyed rates read off the coordinates. -/
def sShY (y : DS) (a : SkIdx) : X :=
  rateOf y.1.1.1.1.2.1 y.1.1.1.2 (skCell (trunc128 y.1.1.2.2.1) y.2.2.1 a)

/-- **The scheme fix**: `h` and SchemeSplit's slots replaced, as the digest fix, when the
capacities are distinct; otherwise `h` is kept. -/
theorem sHiE_spec (y : DS) :
    ∃ (h' : Z → X) (sl' : SkIdx → X), sHiE y = setHS y h' sl' ∧
      (∀ a, out256 (sl' a) = out256 (skSlots y a)) ∧
      (Function.Injective (sPosY y) → ∀ a,
        h' (sPosY y a) = hiMix (y.1.1.1.1.1 (sPosY y a)) (skSlots y a + sShY y a)) ∧
      ∀ z, (Function.Injective (sPosY y) → ∀ a, sPosY y a ≠ z) → h' z = y.1.1.1.1.1 z := by
  obtain ⟨h', u', he, h1, h2, -, h4⟩ := hiStageOn_spec sFW sPosW sShW sFW_inj y.1.1.1.1.1
    (skSlots y) (sView y).2
  refine ⟨h', u', ?_, h1, fun hi a ↦ (h2 a hi).2, fun z hz ↦ h4 z fun a ha ↦ hz ha a⟩
  show sView.symm (hiStageOn sFW sPosW sShW sFW_inj ((y.1.1.1.1.1, skSlots y), (sView y).2)) = _
  rw [he]
  rfl

theorem setHS_h (y : DS) (h : Z → X) (sl : SkIdx → X) : (setHS y h sl).1.1.1.1.1 = h :=
  rfl

theorem setHS_kk' (y : DS) (h : Z → X) (sl : SkIdx → X) :
    (setHS y h sl).1.1.1.1.2 = y.1.1.1.1.2 :=
  rfl

theorem setHS_perm (y : DS) (h : Z → X) (sl : SkIdx → X) : (setHS y h sl).1.1.1.2 = y.1.1.1.2 :=
  rfl

theorem setHS_dc (y : DS) (h : Z → X) (sl : SkIdx → X) : (setHS y h sl).1.2 = y.1.2 :=
  rfl

theorem setHS_rc (y : DS) (h : Z → X) (sl : SkIdx → X) : (setHS y h sl).2.1 = y.2.1 := by
  obtain ⟨⟨⟨⟨t, π⟩, sl0⟩, dc⟩, rc, sd⟩ := y
  rfl

theorem setHS_seed (y : DS) (h : Z → X) (sl : SkIdx → X) : (setHS y h sl).2.2.1 = y.2.2.1 := by
  obtain ⟨⟨⟨⟨t, π⟩, sl0⟩, dc⟩, rc, S, prf⟩ := y
  rfl

theorem setHS_slot1 (y : DS) (h : Z → X) (sl : SkIdx → X) :
    (setHS y h sl).1.1.2.2.1 = sl (some none) :=
  rfl

theorem setHS_sec (y : DS) (h : Z → X) (sl : SkIdx → X) (d : KeygenDomain) :
    (setHS y h sl).1.1.2.2.2 d = sl (some (some d)) :=
  rfl

theorem setHS_prf (y : DS) (h : Z → X) (sl : SkIdx → X) :
    (setHS y h sl).2.2.2 = out256 (sl none) :=
  rfl

end fixes

/-! ## SchemeSplit's slots -/

section scheme

/-- SchemeSplit's slots by index, from its coordinates. -/
def skSlotsX (x : Hybrid.Pub × Secret) : SkIdx → X
  | none => outSplit.symm (x.2.2, x.1.2.1)
  | some none => x.1.2.2.1
  | some (some d) => x.1.2.2.2 d

/-- **SchemeSplit's slots hold the paths' outputs**: when the hidden capacities are distinct, the
slot of each `SK.seed`-keyed path is its rate plus the table's `h` at its capacity. -/
theorem skSlotsX_schemeSplit (t : Tab)
    (hinj : Function.Injective (posOf (schemeSplit t).1 (schemeSplit t).2)) (a : SkIdx) :
    skSlotsX (schemeSplit t) a =
      rateOf t.1.keys.2.1 t.1.perm (skCell t.1.publicSeed t.1.secretSeed a) +
        t.1.keys.1 (posOf (schemeSplit t).1 (schemeSplit t).2 a) := by
  have hP := (schemeSplit_transfer t hinj).1
  have hpos := posOf_schemeSplit t
  have hP1 : trunc128 (slot1 t) = t.1.publicSeed := by
    rw [← Quantum.Sphincs.Hybrid.pubParam_schemeSplit t]
    exact hP
  have hinj' : Function.Injective fun a ↦ capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.secretSeed a) :=
    fun a b hab ↦ hinj ((hpos a).trans (hab.trans (hpos b).symm))
  have hPR : capP t ≠ capR t := fun h ↦
    absurd (hinj' (a₁ := some none) (a₂ := none) h) (by simp)
  have hBinj : Function.Injective (Quantum.Sphincs.Hybrid.posB (wB t)) := fun d d' hd ↦
    Option.some_injective _ (Option.some_injective _
      (hinj' (a₁ := some (some d)) (a₂ := some (some d')) hd))
  have hsplit := schemeSplit_of_injective t hBinj
  rw [hpos, hP1.symm]
  rcases a with _ | _ | d
  · rw [hsplit]
    show outSplit.symm (t.1.prfKey, (outSplit (slot0 t)).2) = _
    rw [← out256_slot0, ← Quantum.Sphincs.outSplit_fst, Prod.mk.eta, Equiv.symm_apply_apply]
    rfl
  · rw [hsplit]
    show slot1 t = _
    rw [slot1, Function.update_of_ne hPR]
    rfl
  · have hneR : capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
        (skCell (trunc128 (slot1 t)) t.1.secretSeed (some (some d))) ≠ capR t := fun h ↦
      absurd (hinj' (a₁ := some (some d)) (a₂ := none) h) (by simp)
    have hneP : capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
        (skCell (trunc128 (slot1 t)) t.1.secretSeed (some (some d))) ≠ capP t := fun h ↦
      absurd (hinj' (a₁ := some (some d)) (a₂ := some none) h) (by simp)
    rw [hsplit]
    show (xch (Quantum.Sphincs.Hybrid.posB (wB t)) hBinj (shB (wB t)) (hA t, t.2.2.2)).2 d = _
    rw [xch_snd_mk]
    show shB (wB t) d + hA t (capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.secretSeed (some (some d)))) = _
    rw [hA, Function.update_of_ne hneP, Function.update_of_ne hneR]
    rfl

end scheme

/-! ## The composite of the fix-ups -/

section composite

/-- **The stages before Reparam, in coordinates**: `dFull` is the coordinates before the digest
stage with new `h` and randomizer slots (randomizer fix), then new `h` and SchemeSplit's slots
(scheme fix). -/
theorem dFull_eq (θ : DTab Message DLab) :
    ∃ (h₅ : Z → X) (rhc₅ : Message → X) (h₆ : Z → X) (sl₆ : SkIdx → X),
      dFull θ = setHS (setHR (dPre rCell rOrd θ) h₅ rhc₅) h₆ sl₆ ∧
      (∀ M, out256 (rhc₅ M) = out256 ((dPre rCell rOrd θ).2.1.2.2 M)) ∧
      (∀ M, IsFirst rOrd (rPosY (dPre rCell rOrd θ)) M →
        h₅ (rPosY (dPre rCell rOrd θ) M) =
          hiMix ((dPre rCell rOrd θ).1.1.1.1.1 (rPosY (dPre rCell rOrd θ) M))
            ((dPre rCell rOrd θ).2.1.2.2 M + rShY (dPre rCell rOrd θ) M)) ∧
      (∀ z, (∀ M, IsFirst rOrd (rPosY (dPre rCell rOrd θ)) M →
          rPosY (dPre rCell rOrd θ) M ≠ z) → h₅ z = (dPre rCell rOrd θ).1.1.1.1.1 z) ∧
      (∀ a, out256 (sl₆ a) = out256 (skSlots (setHR (dPre rCell rOrd θ) h₅ rhc₅) a)) ∧
      (Function.Injective (sPosY (setHR (dPre rCell rOrd θ) h₅ rhc₅)) → ∀ a,
        h₆ (sPosY (setHR (dPre rCell rOrd θ) h₅ rhc₅) a) =
          hiMix (h₅ (sPosY (setHR (dPre rCell rOrd θ) h₅ rhc₅) a))
            (skSlots (setHR (dPre rCell rOrd θ) h₅ rhc₅) a +
              sShY (setHR (dPre rCell rOrd θ) h₅ rhc₅) a)) ∧
      ∀ z, (Function.Injective (sPosY (setHR (dPre rCell rOrd θ) h₅ rhc₅)) →
          ∀ a, sPosY (setHR (dPre rCell rOrd θ) h₅ rhc₅) a ≠ z) → h₆ z = h₅ z := by
  obtain ⟨h₅, rhc₅, e5, f51, f52, f53⟩ := rHiE_spec (dPre rCell rOrd θ)
  obtain ⟨h₆, sl₆, e6, f61, f62, f63⟩ := sHiE_spec (setHR (dPre rCell rOrd θ) h₅ rhc₅)
  refine ⟨h₅, rhc₅, h₆, sl₆, ?_, f51, f52, f53, f61, f62, f63⟩
  show sHiE (rHiE (dPre rCell rOrd θ)) = _
  rw [e5, e6]

end composite

/-! ## Projections -/

section proj

theorem setHR_kk' (y : DS) (h : Z → X) (rhc : Message → X) :
    (setHR y h rhc).1.1.1.1.2 = y.1.1.1.1.2 :=
  rfl

theorem setHR_perm (y : DS) (h : Z → X) (rhc : Message → X) :
    (setHR y h rhc).1.1.1.2 = y.1.1.1.2 :=
  rfl

theorem setHR_slots (y : DS) (h : Z → X) (rhc : Message → X) : (setHR y h rhc).1.1.2 = y.1.1.2 :=
  rfl

theorem setHR_secret (y : DS) (h : Z → X) (rhc : Message → X) : (setHR y h rhc).2.2 = y.2.2 :=
  rfl

theorem dPre_kk' (θ : DTab Message DLab) :
    (dPre rCell rOrd θ).1.1.1.1.2 = (rSplit rCell rOrd θ.1).1.1.1.1.2 :=
  rfl

theorem dPre_h (θ : DTab Message DLab) :
    (dPre rCell rOrd θ).1.1.1.1.1 = (rSplit rCell rOrd θ.1).1.1.1.1.1 :=
  rfl

theorem dPre_perm (θ : DTab Message DLab) :
    (dPre rCell rOrd θ).1.1.1.2 = (rSplit rCell rOrd θ.1).1.1.1.2 :=
  rfl

theorem dPre_slots (θ : DTab Message DLab) :
    (dPre rCell rOrd θ).1.1.2 = (rSplit rCell rOrd θ.1).1.1.2 :=
  rfl

theorem dPre_dc (θ : DTab Message DLab) : (dPre rCell rOrd θ).1.2 = θ.2 :=
  rfl

theorem dPre_rc (θ : DTab Message DLab) : (dPre rCell rOrd θ).2.1 = (rSplit rCell rOrd θ.1).1.2 :=
  rfl

theorem dPre_secret (θ : DTab Message DLab) :
    (dPre rCell rOrd θ).2.2 = (rSplit rCell rOrd θ.1).2 :=
  rfl

end proj

/-! ## The stages on the good set -/

section good

/-- In characteristic `2` a shift cancels. -/
theorem add_add_cancel_X (r w : X) : r + w + r = w := by
  funext j
  show r j + w j + r j = w j
  generalize r j = a
  generalize w j = b
  revert a b
  decide

variable {ι : Type} {β : ι → Type}
  {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
  {θ : DTab Message DLab} (hθ : θ ∈ dGood (J := DLab) rCell rOrd Q)

include hθ

theorem rGood_of_dGood : θ.1 ∈ rGood rCell rOrd Q :=
  ((mem_dGood rCell rOrd).mp hθ).1

/-- On the good set the hidden capacities are distinct. -/
theorem posOf_injective_of_dGood :
    Function.Injective (posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2) :=
  (mem_rGood.mp (rGood_of_dGood hθ)).1.1

/-- On the good set the slot of `PK.seed` gives the table's. -/
theorem trunc128_slot1_of_dGood :
    trunc128 (schemeSplit θ.1.1).1.2.2.1 = θ.1.1.1.publicSeed :=
  (schemeSplit_transfer θ.1.1 (posOf_injective_of_dGood hθ)).1

/-- On the good set the hidden capacities are the table's `SK.seed`-keyed capacities. -/
theorem posOf_of_dGood (a : SkIdx) :
    posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2 a =
      capOf θ.1.1.1.keys.2.1 θ.1.1.1.keys.2.2 θ.1.1.1.perm
        (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a) := by
  rw [posOf_schemeSplit, ← Quantum.Sphincs.Hybrid.pubParam_schemeSplit,
    (schemeSplit_transfer θ.1.1 (posOf_injective_of_dGood hθ)).1]

/-- **The randomizer stage keeps `k` off the randomizer cells.** -/
theorem rSplit_k_of_dGood (x : X) (hx : ∀ M, rCellK rCell θ.1.1.1 M ≠ x) :
    (rSplit rCell rOrd θ.1).1.1.1.1.2.1 x = θ.1.1.1.keys.2.1 x := by
  have hR := rGood_of_dGood hθ
  have hk := (rSplit_keys_eq rCell rOrd θ.1 rCell_injective
    (mem_rGood.mp hR).2.1.1).1 x fun a h ↦ hx a ((pCellK_rSplit rCell_injective hR a).symm.trans h)
  rw [hk, schemeSplit_keys_snd]

/-- The randomizer paths' rates read off the coordinates are the table's. -/
theorem pCellK'_rSplit_of_dGood (M : Message) :
    pCellK' (cellP rCell) (rSplit rCell rOrd θ.1) M = rCellK' rCell θ.1.1.1 M := by
  have hR := rGood_of_dGood hθ
  show ((rSplit rCell rOrd θ.1).1.1.1.2 (pCellK (cellP rCell) (rSplit rCell rOrd θ.1) M,
    (rSplit rCell rOrd θ.1).1.2.1 M)).1 = _
  rw [pCellK_rSplit rCell_injective hR, rSplit_perm, (rSplit_coords rCell_injective hR).2.1 M]
  rfl

/-- **The randomizer stage keeps `k'` off the randomizer rates.** -/
theorem rSplit_k'_of_dGood (x : X) (hx : ∀ M, rCellK' rCell θ.1.1.1 M ≠ x) :
    (rSplit rCell rOrd θ.1).1.1.1.1.2.2 x = θ.1.1.1.keys.2.2 x := by
  have hR := rGood_of_dGood hθ
  have hk := (rSplit_keys_eq rCell rOrd θ.1 rCell_injective
    (mem_rGood.mp hR).2.1.1).2.1 x fun a h ↦
      hx a ((pCellK'_rSplit_of_dGood hθ a).symm.trans h)
  rw [hk, schemeSplit_keys_snd]

/-- **The randomizer stage keeps `h` off the randomizer capacities.** -/
theorem rSplit_h_of_dGood (z : Z) (hz : ∀ M, rCellH rCell θ.1.1.1 M ≠ z) :
    (rSplit rCell rOrd θ.1).1.1.1.1.1 z = (schemeSplit θ.1.1).1.1.1.1 z :=
  (rSplit_keys_eq rCell rOrd θ.1 rCell_injective
    (mem_rGood.mp (rGood_of_dGood hθ)).2.1.1).2.2 z fun a h ↦
      hz a ((pCellH_rSplit rCell_injective (rGood_of_dGood hθ) a).symm.trans h)

/-- **SchemeSplit keeps `h` off the hidden capacities.** -/
theorem schemeSplit_h_of_dGood (z : Z)
    (hz : ∀ a, posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2 a ≠ z) :
    (schemeSplit θ.1.1).1.1.1.1 z = θ.1.1.1.keys.1 z :=
  (schemeSplit_transfer θ.1.1 (posOf_injective_of_dGood hθ)).2.2 z hz

/-- The randomizer and `SK.seed`-keyed rates are distinct on the good set. -/
theorem rRate_ne_seedRate_of_dGood (M : Message) (b : SkIdx) :
    rCellK' rCell θ.1.1.1 M ≠
      rateOf θ.1.1.1.keys.2.1 θ.1.1.1.perm (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed b) := by
  have hR := rGood_of_dGood hθ
  have hrate := ((mem_dGood rCell rOrd).mp hθ).2
  have hP : trunc128 (rSplit rCell rOrd θ.1).1.1.2.2.1 = θ.1.1.1.publicSeed := by
    rw [rSplit_slots]
    exact trunc128_slot1_of_dGood hθ
  have hS := rSplit_snd rCell rOrd θ.1
  intro h
  have e := hrate (a₁ := Sum.inl M) (a₂ := Sum.inr b)
  refine absurd (e ?_) (by simp)
  show ((rSplit rCell rOrd θ.1).1.1.1.2 (rCell M (trunc128 (rSplit rCell rOrd θ.1).1.1.2.2.1)
      (rSplit rCell rOrd θ.1).2.2, (rSplit rCell rOrd θ.1).1.2.1 M)).1 =
    ((rSplit rCell rOrd θ.1).1.1.1.2 (skCell (trunc128 (rSplit rCell rOrd θ.1).1.1.2.2.1)
      (rSplit rCell rOrd θ.1).2.1 b, (rSplit rCell rOrd θ.1).1.1.1.1.2.1
        (skCell (trunc128 (rSplit rCell rOrd θ.1).1.1.2.2.1) (rSplit rCell rOrd θ.1).2.1 b))).1
  rw [hP, hS, (rSplit_coords rCell_injective hR).2.1 M,
    rSplit_k_of_dGood hθ _ fun M' h' ↦ skCell_ne_rCell _ _ b M' _ h'.symm, rSplit_perm]
  exact h

/-- The `SK.seed`-keyed capacities after the randomizer stage are the hidden capacities. -/
theorem capOf_rSplit_seed (a : SkIdx) :
    capOf (rSplit rCell rOrd θ.1).1.1.1.1.2.1 (rSplit rCell rOrd θ.1).1.1.1.1.2.2
        (rSplit rCell rOrd θ.1).1.1.1.2
        (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a) =
      posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2 a := by
  have hk : (rSplit rCell rOrd θ.1).1.1.1.1.2.1 (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a) =
      θ.1.1.1.keys.2.1 (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a) :=
    rSplit_k_of_dGood hθ _ fun M h ↦ skCell_ne_rCell _ _ a M _ h.symm
  have hk' : (rSplit rCell rOrd θ.1).1.1.1.1.2.2
        (rateOf θ.1.1.1.keys.2.1 θ.1.1.1.perm (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a)) =
      θ.1.1.1.keys.2.2
        (rateOf θ.1.1.1.keys.2.1 θ.1.1.1.perm (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a)) :=
    rSplit_k'_of_dGood hθ _ fun M ↦ rRate_ne_seedRate_of_dGood hθ M a
  rw [posOf_of_dGood hθ]
  unfold capOf
  rw [rSplit_perm, hk]
  exact congrArg _ hk'

/-- The `SK.seed`-keyed rates after the randomizer stage are the table's. -/
theorem rateOf_rSplit_seed (a : SkIdx) :
    rateOf (rSplit rCell rOrd θ.1).1.1.1.1.2.1 (rSplit rCell rOrd θ.1).1.1.1.2
        (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a) =
      rateOf θ.1.1.1.keys.2.1 θ.1.1.1.perm (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a) := by
  unfold rateOf
  rw [rSplit_perm, rSplit_k_of_dGood hθ _ fun M h ↦ skCell_ne_rCell _ _ a M _ h.symm]

/-- The randomizer fix's capacities are the table's randomizer capacities. -/
theorem rPosY_good : rPosY (dPre rCell rOrd θ) = rCellH rCell θ.1.1.1 := by
  funext M
  show pCellH (cellP rCell) (rSplit rCell rOrd θ.1) M = _
  exact pCellH_rSplit rCell_injective (rGood_of_dGood hθ) M

/-- The randomizer fix's shifts are the table's randomizer rates. -/
theorem rShY_good (M : Message) :
    rShY (dPre rCell rOrd θ) M =
      rateOf θ.1.1.1.keys.2.1 θ.1.1.1.perm (rCellK rCell θ.1.1.1 M) := by
  have hR := rGood_of_dGood hθ
  show ((rSplit rCell rOrd θ.1).1.1.1.2 (pCellK (cellP rCell) (rSplit rCell rOrd θ.1) M,
    (rSplit rCell rOrd θ.1).1.2.1 M)).1 = _
  rw [pCellK_rSplit rCell_injective hR, rSplit_perm, (rSplit_coords rCell_injective hR).2.1 M]
  rfl

/-- The scheme fix's capacities are the hidden capacities. -/
theorem sPosY_good (h₅ : Z → X) (rhc₅ : Message → X) (a : SkIdx) :
    sPosY (setHR (dPre rCell rOrd θ) h₅ rhc₅) a =
      posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2 a := by
  have hP : trunc128 (rSplit rCell rOrd θ.1).1.1.2.2.1 = θ.1.1.1.publicSeed := by
    rw [rSplit_slots]
    exact trunc128_slot1_of_dGood hθ
  have hS : (rSplit rCell rOrd θ.1).2.1 = θ.1.1.1.secretSeed := by
    rw [rSplit_snd]
  simp only [sPosY, setHR_kk', setHR_perm, setHR_slots, setHR_secret, dPre_kk', dPre_perm,
    dPre_slots, dPre_secret]
  rw [hP, hS]
  exact capOf_rSplit_seed hθ a

/-- The scheme fix's shifts are the table's `SK.seed`-keyed rates. -/
theorem sShY_good (h₅ : Z → X) (rhc₅ : Message → X) (a : SkIdx) :
    sShY (setHR (dPre rCell rOrd θ) h₅ rhc₅) a =
      rateOf θ.1.1.1.keys.2.1 θ.1.1.1.perm (skCell θ.1.1.1.publicSeed θ.1.1.1.secretSeed a) := by
  have hP : trunc128 (rSplit rCell rOrd θ.1).1.1.2.2.1 = θ.1.1.1.publicSeed := by
    rw [rSplit_slots]
    exact trunc128_slot1_of_dGood hθ
  have hS : (rSplit rCell rOrd θ.1).2.1 = θ.1.1.1.secretSeed := by
    rw [rSplit_snd]
  simp only [sShY, setHR_kk', setHR_perm, setHR_slots, setHR_secret, dPre_kk', dPre_perm,
    dPre_slots, dPre_secret]
  rw [hP, hS]
  exact rateOf_rSplit_seed hθ a

omit hθ in
/-- The scheme fix's slots are SchemeSplit's. -/
theorem skSlots_good (h₅ : Z → X) (rhc₅ : Message → X) (a : SkIdx) :
    skSlots (setHR (dPre rCell rOrd θ) h₅ rhc₅) a =
      skSlotsX (schemeSplit θ.1.1) a := by
  have hsl := rSplit_slots rCell rOrd θ.1
  have hS : (rSplit rCell rOrd θ.1).2 = (schemeSplit θ.1.1).2 := by
    rw [rSplit_snd, Quantum.Sphincs.Hybrid.schemeSplit_snd]
  rcases a with _ | _ | d
  · show outSplit.symm ((rSplit rCell rOrd θ.1).2.2, (rSplit rCell rOrd θ.1).1.1.2.1) =
      outSplit.symm ((schemeSplit θ.1.1).2.2, (schemeSplit θ.1.1).1.2.1)
    rw [hsl, hS]
  · show (rSplit rCell rOrd θ.1).1.1.2.2.1 = (schemeSplit θ.1.1).1.2.2.1
    rw [hsl]
  · show (rSplit rCell rOrd θ.1).1.1.2.2.2 d = (schemeSplit θ.1.1).1.2.2.2 d
    rw [hsl]

/-- **The bits of `h` from `256` on are the table's** after the stages. -/
theorem dFull_hiEq (z : Z) : HiEq ((dFull θ).1.1.1.1.1 z) (θ.1.1.1.keys.1 z) := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, -, f52, f53, -, f62, f63⟩ := dFull_eq θ
  have hsp := sPosY_good hθ h₅ rhc₅
  have hsinj : Function.Injective (sPosY (setHR (dPre rCell rOrd θ) h₅ rhc₅)) :=
    fun a b h ↦ posOf_injective_of_dGood hθ ((hsp a).symm.trans (h.trans (hsp b)))
  rw [e, setHS_h]
  by_cases hS : ∃ a, posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2 a = z
  · obtain ⟨a, rfl⟩ := hS
    rw [← hsp a, f62 hsinj a, hsp a, skSlots_good, sShY_good hθ,
      skSlotsX_schemeSplit θ.1.1 (posOf_injective_of_dGood hθ), add_add_cancel_X]
    exact hiEq_hiMix _ _
  · have hS' : ∀ a, posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2 a ≠ z := fun a h ↦
      hS ⟨a, h⟩
    rw [f63 z fun _ a h ↦ hS' a ((hsp a).symm.trans h)]
    rw [rPosY_good hθ] at f52 f53
    by_cases hR : ∃ M, IsFirst rOrd (rCellH rCell θ.1.1.1) M ∧ rCellH rCell θ.1.1.1 M = z
    · obtain ⟨M, hM, rfl⟩ := hR
      have hMB : M ∉ rB rCell rOrd θ.1.1.1 := fun h ↦ (mem_rB rCell rOrd).mp h hM
      rw [f52 M hM, show (dPre rCell rOrd θ).2.1.2.2 M = (rSplit rCell rOrd θ.1).1.2.2.2 M from rfl,
        (rSplit_coords rCell_injective (rGood_of_dGood hθ)).2.2.2.1 M hMB, rShY_good hθ,
        add_add_cancel_X]
      exact hiEq_hiMix _ _
    · have hR' : ∀ M, rCellH rCell θ.1.1.1 M ≠ z := fun M h ↦ by
        obtain ⟨M', hM', he⟩ := Quantum.Xmss.Hybrid.exists_isFirst rOrd (rCellH rCell θ.1.1.1) M
        exact hR ⟨M', hM', he.trans h⟩
      rw [f53 z fun M _ h ↦ hR ⟨M, ‹_›, h⟩, dPre_h,
        (rSplit_h_of_dGood hθ z hR').trans (schemeSplit_h_of_dGood hθ z hS')]
      exact HiEq.refl _

/-- **Off the staged capacities `h` is the table's** after the stages. -/
theorem dFull_h_eq (z : Z) (hS : ∀ a, posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2 a ≠ z)
    (hR : ∀ M, rCellH rCell θ.1.1.1 M ≠ z) :
    (dFull θ).1.1.1.1.1 z = θ.1.1.1.keys.1 z := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, -, -, f53, -, -, f63⟩ := dFull_eq θ
  have hsp := sPosY_good hθ h₅ rhc₅
  rw [e, setHS_h, f63 z fun _ a h ↦ hS a ((hsp a).symm.trans h)]
  rw [f53 z fun M _ h ↦ hR M ((congrFun (rPosY_good hθ) M).symm.trans h)]
  exact (rSplit_h_of_dGood hθ z hR).trans (schemeSplit_h_of_dGood hθ z hS)

omit hθ in
/-- **The stages keep the randomizer stage's `k` and `k'`.** -/
theorem dFull_kk' : (dFull θ).1.1.1.1.2 = (rSplit rCell rOrd θ.1).1.1.1.1.2 := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, -⟩ := dFull_eq θ
  rw [e, setHS_kk', setHR_kk', dPre_kk']

omit hθ in
/-- The stages keep `π`. -/
theorem dFull_perm : (dFull θ).1.1.1.2 = θ.1.1.1.perm := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, -⟩ := dFull_eq θ
  rw [e, setHS_perm, setHR_perm, dPre_perm, rSplit_perm]

omit hθ in
/-- The randomizer slots keep their first `256` bits. -/
theorem dFull_rhc (M : Message) :
    out256 ((dFull θ).2.1.2.2 M) = out256 ((rSplit rCell rOrd θ.1).1.2.2.2 M) := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, f51, -⟩ := dFull_eq θ
  rw [e, setHS_rc]
  exact f51 M

omit hθ in
/-- The stages keep the digest coin slots. -/
theorem dFull_dc : (dFull θ).1.2 = θ.2 := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, -⟩ := dFull_eq θ
  rw [e, setHS_dc]
  rfl

omit hθ in
/-- **The stages keep the coin slots' `k`- and `k'`-parts**: the digest stage's pads and the
randomizer stage's. -/
theorem dFull_coins : (dFull θ).1.2.1 = θ.2.1 ∧ (dFull θ).1.2.2.1 = θ.2.2.1 ∧
    (dFull θ).2.1.1 = (rSplit rCell rOrd θ.1).1.2.1 ∧
    (dFull θ).2.1.2.1 = (rSplit rCell rOrd θ.1).1.2.2.1 := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, -⟩ := dFull_eq θ
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩

omit hθ in
/-- SchemeSplit's slots keep their first `256` bits through the stages. -/
theorem dFull_out256_skSlots (a : SkIdx) :
    out256 (skSlots (dFull θ) a) = out256 (skSlotsX (schemeSplit θ.1.1) a) := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, -, -, -, f61, -⟩ := dFull_eq θ
  rw [← skSlots_good h₅ rhc₅ a, ← f61 a, e]
  rcases a with _ | _ | d
  · show out256 (outSplit.symm (out256 (sl₆ none), (outSplit (sl₆ none)).2)) = _
    rw [← Quantum.Sphincs.outSplit_fst (outSplit.symm _), Equiv.apply_symm_apply]
  · rfl
  · rfl

/-- **The stages keep `PK.seed`.** -/
theorem dFull_slot1 : trunc128 (dFull θ).1.1.2.2.1 = θ.1.1.1.publicSeed := by
  have h := dFull_out256_skSlots (θ := θ) (some none)
  show truncateHash (out256 (skSlots (dFull θ) (some none))) = _
  rw [h]
  exact trunc128_slot1_of_dGood hθ

/-- **The stages keep the secrets' hashes.** -/
theorem dFull_sec (d : KeygenDomain) :
    out256 ((dFull θ).1.1.2.2.2 d) = Quantum.Sphincs.Hybrid.secHash θ.1.1.1 d := by
  have h := dFull_out256_skSlots (θ := θ) (some (some d))
  refine h.trans ?_
  exact congrFun (schemeSplit_transfer θ.1.1 (posOf_injective_of_dGood hθ)).2.1 d

omit hθ in
/-- **The stages keep `(SK.seed, SK.prf)`.** -/
theorem dFull_secret : (dFull θ).2.2 = (θ.1.1.1.secretSeed, θ.1.1.1.prfKey) := by
  obtain ⟨h₅, rhc₅, h₆, sl₆, e, -⟩ := dFull_eq θ
  have hp := dFull_out256_skSlots (θ := θ) none
  have hS : (dFull θ).2.2.1 = θ.1.1.1.secretSeed := by
    rw [e, setHS_seed, setHR_secret, dPre_secret, rSplit_snd]
  have hprf : (dFull θ).2.2.2 = θ.1.1.1.prfKey := by
    have h1 : (dFull θ).2.2.2 = out256 (skSlots (dFull θ) none) := by
      rw [e]
      show out256 (sl₆ none) = out256 (outSplit.symm (out256 (sl₆ none), (outSplit (sl₆ none)).2))
      rw [← Quantum.Sphincs.outSplit_fst (outSplit.symm _), Equiv.apply_symm_apply]
    rw [h1, hp]
    show out256 (outSplit.symm ((schemeSplit θ.1.1).2.2, (schemeSplit θ.1.1).1.2.1)) = _
    rw [← Quantum.Sphincs.outSplit_fst (outSplit.symm _), Equiv.apply_symm_apply,
      Quantum.Sphincs.Hybrid.schemeSplit_snd]
  exact Prod.ext hS hprf

end good

end Quantum.Sphincs.Assembly

end
