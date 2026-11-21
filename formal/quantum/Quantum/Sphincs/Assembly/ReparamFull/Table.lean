module

public import Quantum.Sphincs.Assembly.ReparamFull.Facts
public import Quantum.Sphincs.Assembly.ReparamFull.Comp
public import Quantum.Sphincs.Assembly.ReparamFull.Keys

@[expose] public section

/-!
# The composed reparametrization of leanSPHINCS's tables: the table's data at the coordinates

On the stage good sets (`StageGood`: DigestStage's `dGood` and SeedStage's `seedKGood` for the
computations `compQ`), the coordinates of `fullE` carry the table's data:

* `pathKeys_of_stageGood`: Reparam's table `phiE t` has keys agreeing with the table's on its
  in-table paths (`PathKeys`): the staged cells (the randomizer and `SK.seed`-keyed paths' cells,
  the hidden and staged capacities) are read by no computation of `compQ`, which reads every
  in-table path (`cells_mem_compQ`).
* `pads_of_stageGood`: Reparam's pad holds the table's secrets at the secret positions.
* The hidden values (`fullE t`): `val_fullE` (the table's at the live positions, so `PK.root`),
  `rnd_fullE` (the table's randomizer at a first message). The digest stage after Reparam
  (`dLast_eq`) keeps everything but `h` and the digest slots.
-/

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed truncateHash)
open Quantum.Xmss (X Z out256 trunc128)
open Common.SufCma (SchemeHashSpec)
open Quantum.Xmss.Hybrid (CoinSlots IsFirst capOf rateOf r0SlotEquiv r0SlotEquiv_fst kCells k'Cells
  hCells)
open Quantum.Xmss.Assembly (fwd fwd_fst_snd fwd_snd fwd_fst_fst setAt XW)
open Quantum.Sphincs.Hybrid (DTab Secret SeedKS SkIdx Tab DLab rCell rOrd
  skCell posOf schemeSplit dGood mem_dGood rGood mem_rGood rSplit pCellK_rSplit pCellH_rSplit
  rCellK rCellK' rCellH rB seedKStages seedKStages_spec' seedKGood mem_seedKGood
  seedKGood_paths seedKSplit seedKSplit_slots seedKSplit_secret seedKSplit_coords
  schemeData_eq_pubData_seedKSplit schemeData_eq_pubData_rSplit
  schemeData_eq_of_mem mem_schemeGood schemeData pubData qReads secHash secret_eq_secHash
  randomizer_eq_rCoord rCell_injective skCell_ne_rCell
  seedCellK seedCellK' rSplit_perm dLabOrd)

namespace Quantum.Sphincs.Assembly

/-! ## The seed stage and the secrets' exchange -/

section seed

/-- `k` and `k'` replaced. -/
def setKK (y : DS) (k k' : X → Z) : DS :=
  (((((y.1.1.1.1.1, k, k'), y.1.1.1.2), y.1.1.2), y.1.2), y.2)

/-- **SeedStage's stages on the digest stage's coordinates**: `k` and `k'` replaced, keeping their
values off the `SK.seed`-keyed paths' first blocks and (when distinct) rates. -/
theorem seedE_spec (y : DS) (sk : SeedKS) :
    ∃ (k₂ k'₂ : X → Z) (sk₂ : SeedKS), seedE (y, sk) = (setKK y k₂ k'₂, sk₂) ∧
      (∀ x, (∀ b, skCell (trunc128 y.1.1.2.2.1) y.2.2.1 b ≠ x) → k₂ x = y.1.1.1.1.2.1 x) ∧
      (Function.Injective (fun b ↦
          rateOf y.1.1.1.1.2.1 y.1.1.1.2 (skCell (trunc128 y.1.1.2.2.1) y.2.2.1 b)) →
        ∀ x, (∀ b, rateOf y.1.1.1.1.2.1 y.1.1.1.2 (skCell (trunc128 y.1.1.2.2.1) y.2.2.1 b) ≠ x) →
          k'₂ x = y.1.1.1.1.2.2 x) := by
  obtain ⟨k₂, k'₂, sk₂, hE, -, f2, f3⟩ := seedKStages_spec' ((y.1.1, y.2.2), sk)
  refine ⟨k₂, k'₂, sk₂, ?_, f2, fun hi ↦ (f3 hi).2⟩
  show seedView.symm (seedKStages ((y.1.1, y.2.2), sk), (y.1.2, y.2.1)) = _
  rw [hE]
  rfl

theorem stagesE_apply (t : FT) :
    stagesE t = (secXE (seedE (dFull t.1.1.1, t.1.1.2), t.1.2), t.2) := by
  simp only [stagesE, Equiv.prodCongr_apply, Equiv.trans_apply, Prod.map, Equiv.refl_apply]

theorem phiE_apply (t : FT) : phiE t = tabR (stagesE t) := by
  rw [phiE, Equiv.trans_apply]

/-- The table of a padded table. -/
abbrev tabOf (t : FT) : HonestTable :=
  t.1.1.1.1.1.1

/-- **Reparam's table and the rest of a padded table**, in terms of `dFull`. -/
theorem phiE_spec (t : FT) :
    ∃ (k₂ k'₂ : X → Z) (sk₂ : SeedKS),
      (phiE t).1 = (((dFull t.1.1.1).1.1.1.1.1, secU (dFull t.1.1.1).1.1.2.2.2 t.1.2),
        ((r0SlotEquiv (dFull t.1.1.1).1.1.2.2.1).1, (dFull t.1.1.1).1.1.1.2, k₂, k'₂)) ∧
      (phiE t).2.2 = ((dFull t.1.1.1).1.2, (dFull t.1.1.1).2.1, (dFull t.1.1.1).2.2, sk₂, t.2) ∧
      (∀ x, (∀ b, skCell (trunc128 (dFull t.1.1.1).1.1.2.2.1) (dFull t.1.1.1).2.2.1 b ≠ x) →
        k₂ x = (dFull t.1.1.1).1.1.1.1.2.1 x) ∧
      (Function.Injective (fun b ↦ rateOf (dFull t.1.1.1).1.1.1.1.2.1 (dFull t.1.1.1).1.1.1.2
          (skCell (trunc128 (dFull t.1.1.1).1.1.2.2.1) (dFull t.1.1.1).2.2.1 b)) →
        ∀ x, (∀ b, rateOf (dFull t.1.1.1).1.1.1.1.2.1 (dFull t.1.1.1).1.1.1.2
            (skCell (trunc128 (dFull t.1.1.1).1.1.2.2.1) (dFull t.1.1.1).2.2.1 b) ≠ x) →
          k'₂ x = (dFull t.1.1.1).1.1.1.1.2.2 x) := by
  obtain ⟨k₂, k'₂, sk₂, hE, f2, f3⟩ := seedE_spec (dFull t.1.1.1) t.1.1.2
  refine ⟨k₂, k'₂, sk₂, ?_, ?_, f2, f3⟩
  · rw [phiE_apply, stagesE_apply, hE]
    rfl
  · rw [phiE_apply, stagesE_apply, hE]
    rfl

end seed

/-! ## The stage good set and the table's data -/

section good

/-- `rCell` as SeedStage's label family (read off `(SK.seed, SK.prf)`). -/
def rCellS (M : Message) (P : PublicParameter) (s : Secret) : X :=
  rCell M P s.2

/-- **The stage good set**: DigestStage's and SeedStage's good sets for the computations
`compQ`. -/
def StageGood (t : FT) : Prop :=
  t.1.1.1 ∈ dGood (J := DLab) rCell rOrd compQ ∧
    (t.1.1.1.1.1, t.1.1.2) ∈ seedKGood rCellS compQ

variable {t : FT} (ht : StageGood t)

include ht

/-- The randomizer stage's reads miss the in-table paths: no randomizer cell is a cell of a
computation's reads. -/
theorem rReads_of_stageGood (i : CIdx) (M : Message) :
    rCellK rCell (tabOf t) M ∉ kCells (schemeData compQ (tabOf t) i).2 ∧
      rCellK' rCell (tabOf t) M ∉ k'Cells (schemeData compQ (tabOf t) i).2 ∧
      rCellH rCell (tabOf t) M ∉ hCells (schemeData compQ (tabOf t) i).2 := by
  have hR := rGood_of_dGood ht.1
  obtain ⟨-, -, hread⟩ := mem_rGood.mp hR
  have hsd := schemeData_eq_pubData_rSplit rCell_injective hR
  obtain ⟨h1, h2, h3⟩ := hread i M
  rw [pCellK_rSplit rCell_injective hR] at h1
  rw [pCellK'_rSplit_of_dGood ht.1] at h2
  rw [pCellH_rSplit rCell_injective hR] at h3
  refine ⟨?_, ?_, ?_⟩ <;> rw [hsd] <;> assumption

/-- The hidden capacities miss the in-table paths' `h`-cells. -/
theorem sReads_of_stageGood (i : CIdx) (a : SkIdx) :
    posOf (schemeSplit t.1.1.1.1.1).1 (schemeSplit t.1.1.1.1.1).2 a ∉
      hCells (schemeData compQ (tabOf t) i).2 := by
  have hR := rGood_of_dGood ht.1
  have hg := (mem_rGood.mp hR).1
  rw [schemeData_eq_of_mem (mem_schemeGood.mpr hg)]
  exact hg.2 i a

/-- SeedStage's reads miss the in-table paths: no `SK.seed`-keyed first block or rate is a cell
of a computation's reads. -/
theorem seedReads_of_stageGood (i : CIdx) (b : SkIdx) :
    skCell (tabOf t).publicSeed (tabOf t).secretSeed b ∉
        kCells (schemeData compQ (tabOf t) i).2 ∧
      rateOf (tabOf t).keys.2.1 (tabOf t).perm (skCell (tabOf t).publicSeed (tabOf t).secretSeed b)
        ∉ k'Cells (schemeData compQ (tabOf t) i).2 := by
  have hs := ht.2
  obtain ⟨-, -, hread⟩ := mem_seedKGood.mp hs
  have hsd := schemeData_eq_pubData_seedKSplit hs
  obtain ⟨hc, -, -, -⟩ := seedKGood_paths hs
  obtain ⟨hk, -⟩ := seedKSplit_coords hs
  have e1 : seedCellK (seedKSplit (t.1.1.1.1.1, t.1.1.2)) b =
      skCell (tabOf t).publicSeed (tabOf t).secretSeed b := by
    show Quantum.Sphincs.Hybrid.seedCell (seedKSplit (t.1.1.1.1.1, t.1.1.2)).1 b = _
    rw [← hc b]
    show skCell (trunc128 (seedKSplit (t.1.1.1.1.1, t.1.1.2)).1.1.2.2.1)
      (seedKSplit (t.1.1.1.1.1, t.1.1.2)).1.2.1 b =
        skCell (trunc128 (schemeSplit t.1.1.1.1.1).1.2.2.1)
        (schemeSplit t.1.1.1.1.1).2.1 b
    rw [seedKSplit_slots, seedKSplit_secret, Quantum.Sphincs.Hybrid.schemeSplit_snd]
  have e2 : seedCellK' (seedKSplit (t.1.1.1.1.1, t.1.1.2)) b =
      rateOf (tabOf t).keys.2.1 (tabOf t).perm
      (skCell (tabOf t).publicSeed (tabOf t).secretSeed b) := by
    show ((seedKSplit (t.1.1.1.1.1, t.1.1.2)).1.1.1.2
      (seedCellK (seedKSplit (t.1.1.1.1.1, t.1.1.2)) b,
      (seedKSplit (t.1.1.1.1.1, t.1.1.2)).2.1 b)).1 = _
    rw [e1, hk b, Quantum.Sphincs.Hybrid.seedKSplit_perm]
    rfl
  obtain ⟨h1, h2⟩ := hread i b
  rw [e1] at h1
  rw [e2] at h2
  rw [hsd]
  exact ⟨h1, h2⟩

/-- **The public `k` is the table's** off the randomizer and `SK.seed`-keyed first blocks. -/
theorem kPub_eq (x : X) (hr : ∀ M, rCellK rCell (tabOf t) M ≠ x)
    (hs : ∀ b, skCell (tabOf t).publicSeed (tabOf t).secretSeed b ≠ x) :
    (phiE t).1.2.2.2.1 x = (tabOf t).keys.2.1 x := by
  obtain ⟨k₂, k'₂, sk₂, he, -, f2, -⟩ := phiE_spec t
  have hP := dFull_slot1 ht.1
  have hS : (dFull t.1.1.1).2.2.1 = (tabOf t).secretSeed := by rw [dFull_secret]
  rw [he]
  show k₂ x = _
  rw [f2 x fun b ↦ by rw [hP, hS]; exact hs b, dFull_kk']
  exact rSplit_k_of_dGood ht.1 x hr

/-- **The public `k'` is the table's** off the randomizer and `SK.seed`-keyed rates. -/
theorem k'Pub_eq (x : X) (hr : ∀ M, rCellK' rCell (tabOf t) M ≠ x)
    (hs : ∀ b, rateOf (tabOf t).keys.2.1 (tabOf t).perm
      (skCell (tabOf t).publicSeed (tabOf t).secretSeed b) ≠ x) :
    (phiE t).1.2.2.2.2 x = (tabOf t).keys.2.2 x := by
  obtain ⟨k₂, k'₂, sk₂, he, -, -, f3⟩ := phiE_spec t
  have hP := dFull_slot1 ht.1
  have hS : (dFull t.1.1.1).2.2.1 = (tabOf t).secretSeed := by rw [dFull_secret]
  have hrate : ∀ b, rateOf (dFull t.1.1.1).1.1.1.1.2.1 (dFull t.1.1.1).1.1.1.2
      (skCell (trunc128 (dFull t.1.1.1).1.1.2.2.1) (dFull t.1.1.1).2.2.1 b) =
      rateOf (tabOf t).keys.2.1 (tabOf t).perm
        (skCell (tabOf t).publicSeed (tabOf t).secretSeed b) := fun b ↦ by
    rw [hP, hS, dFull_kk', dFull_perm]
    unfold rateOf
    rw [rSplit_k_of_dGood ht.1 _ fun M h ↦ skCell_ne_rCell _ _ b M _ h.symm]
  have hinj : Function.Injective (fun b ↦ rateOf (dFull t.1.1.1).1.1.1.1.2.1
      (dFull t.1.1.1).1.1.1.2
        (skCell (trunc128 (dFull t.1.1.1).1.1.2.2.1) (dFull t.1.1.1).2.2.1 b)) :=
    fun a b h ↦ (seedKGood_paths ht.2).2.2.2 (((hrate a).symm.trans h).trans (hrate b))
  rw [he]
  show k'₂ x = _
  rw [f3 hinj x fun b h ↦ hs b ((hrate b).symm.trans h), dFull_kk']
  exact rSplit_k'_of_dGood ht.1 x hr

/-- The public data's `PK.seed` is the table's. -/
theorem wPub_seed : (phiE t).1.2.1 = (tabOf t).publicSeed := by
  obtain ⟨k₂, k'₂, sk₂, he, -⟩ := phiE_spec t
  rw [he]
  show (r0SlotEquiv (dFull t.1.1.1).1.1.2.2.1).1 = _
  rw [r0SlotEquiv_fst]
  exact dFull_slot1 ht.1

omit ht in
/-- The public data's `π` is the table's. -/
theorem wPub_perm : (phiE t).1.2.2.1 = (tabOf t).perm := by
  obtain ⟨k₂, k'₂, sk₂, he, -⟩ := phiE_spec t
  rw [he]
  exact dFull_perm

omit ht in
/-- Reparam's `h` is the stages'. -/
theorem hPre_eq : (phiE t).1.1.1 = (dFull t.1.1.1).1.1.1.1.1 := by
  obtain ⟨k₂, k'₂, sk₂, he, -⟩ := phiE_spec t
  rw [he]

/-- **The public keys agree with the table's on its in-table paths.** -/
theorem pathKeys_of_stageGood : PathKeys (tabOf t) (phiE t).1.2 (phiE t).1.1.1 := by
  refine ⟨wPub_seed ht, wPub_perm, fun s hs j hj ↦ ?_⟩
  obtain ⟨i, hi⟩ := cells_mem_compQ (tabOf t) hs
  obtain ⟨mk, mk', mh⟩ := hi j hj
  refine ⟨kPub_eq ht _ (fun M h ↦ (rReads_of_stageGood ht i M).1 (h ▸ mk))
    (fun b h ↦ (seedReads_of_stageGood ht i b).1 (h ▸ mk)),
    k'Pub_eq ht _ (fun M h ↦ (rReads_of_stageGood ht i M).2.1 (h ▸ mk'))
    (fun b h ↦ (seedReads_of_stageGood ht i b).2 (h ▸ mk')), ?_⟩
  rw [hPre_eq]
  exact dFull_h_eq ht.1 _ (fun a h ↦ sReads_of_stageGood ht i a (h ▸ mh))
    (fun M h ↦ (rReads_of_stageGood ht i M).2.2 (h ▸ mh))

omit ht in
/-- The table's value at a secret's position is the secret. -/
theorem valuePos_secPos (L : HonestTable) (d : KeygenDomain) :
    valuePos L (secPos d) = L.secret d := by
  cases d <;> rfl

/-- **Reparam's pad holds the table's secrets.** -/
theorem pads_of_stageGood (q : ValPos) (hq : SecretPos q) :
    (phiE t).1.1.2 q = valuePos (tabOf t) q := by
  obtain ⟨k₂, k'₂, sk₂, he, -⟩ := phiE_spec t
  obtain ⟨d, hd⟩ := secOf_of_secretPos hq
  rw [he]
  show secU (dFull t.1.1.1).1.1.2.2.2 t.1.2 q = _
  rw [secU_of_some hd, ← secPos_of_secOf hd, valuePos_secPos, secret_eq_secHash, ← dFull_sec ht.1]
  rfl

omit ht in
/-- **The digest stage keeps everything but `h` and the digest slots.** -/
theorem dLast_eq (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) :
    ∃ (h₃ : Z → X) (hc₃ : DLab → X),
      dLast y = (((h₃, y.1.1.2), y.1.2), (y.2.1, (y.2.2.1.1, y.2.2.1.2.1, hc₃), y.2.2.2)) := by
  obtain ⟨h₃, hc₃, e, -⟩ := pFull_eq dcY dLabOrd (yView y)
  refine ⟨h₃, hc₃, ?_⟩
  show yView.symm (pFull dcY dLabOrd (yView y)) = _
  rw [e]
  rfl

omit ht in
/-- The hidden values at the positions are Reparam's values. -/
theorem fullE_val (q : ValPos) :
    (fullE t).2.1 (.val q) = sVal (phiE t).1.2 (phiE t).1.1.1 (phiE t).1.1.2 q := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq (yOf t)
  show (psiE (dLast (yOf t))).2.1 (.val q) = _
  rw [e]
  rfl

/-- **The hidden values at the live positions are the table's.** -/
theorem val_fullE (q : ValPos) (hq : Live q) : (fullE t).2.1 (.val q) = valuePos (tabOf t) q :=
  (fullE_val q).trans (sVal_eq_valuePos_keys (pathKeys_of_stageGood ht) (pads_of_stageGood ht) q hq)

/-- **The hidden root is `PK.root`.** -/
theorem root_fullE : (fullE t).2.1 (.val rootPos) = (tabOf t).root :=
  (val_fullE ht rootPos (live_of_fullPos fullPos_rootPos)).trans (valuePos_rootPos _)

/-- **The hidden randomizer of a first message is the table's.** -/
theorem rnd_fullE (M : Message) (hM : M ∉ rB rCell rOrd (tabOf t)) :
    (fullE t).2.1 (.rnd M) = (tabOf t).randomizer M := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq (yOf t)
  obtain ⟨k₂, k'₂, sk₂, -, he2, -⟩ := phiE_spec t
  show (psiE (dLast (yOf t))).2.1 (.rnd M) = _
  rw [e]
  show truncateHash (out256 ((phiE t).2.2.2.1.2.2 M)) = _
  rw [he2]
  show truncateHash (out256 ((dFull t.1.1.1).2.1.2.2 M)) = _
  rw [dFull_rhc]
  exact (randomizer_eq_rCoord (rGood_of_dGood ht.1) M hM).symm

omit ht in
/-- `fwd`'s public `h` agrees with the table's `h` from bit `256` on. -/
theorem hiEq_fwd (θ : RTabS) (z : Z) : HiEq ((fwd sphFix sO θ).1.1 z) (θ.1.1 z) := by
  rw [fwd_fst_fst]
  unfold setAt
  split_ifs with hz
  · have h1 := hiEq_cor128 (θ.1.2 hz.choose)
      (sO.rate θ.2 θ.1.1 (sO.val θ.2 θ.1.1 θ.1.2) hz.choose)
      (θ.1.1 (sO.cap θ.2 θ.1.1 (sO.val θ.2 θ.1.1 θ.1.2) hz.choose))
    refine h1.trans ?_
    rw [hz.choose_spec.2]
    exact HiEq.refl _
  · exact HiEq.refl _


end good

end Quantum.Sphincs.Assembly

end
