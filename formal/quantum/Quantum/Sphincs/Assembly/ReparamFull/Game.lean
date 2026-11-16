module

public import Quantum.Sphincs.Assembly.ReparamFull.Table
public import Quantum.Sphincs.Assembly.ReparamFull.RateSep
public import Quantum.Sphincs.Assembly.GameCongr
public import Quantum.Sphincs.Assembly.GameR

@[expose] public section

/-!
# The composed reparametrization of leanSPHINCS's tables: the game

On the core good set (`FullGCore`: the stage good set, a good permutation, `HRateSep` and Reparam's
`XGood`), the canonical runtime-2 game at the table (`gameR msgPol A (pubOf L) (valueAt L)`) is the
canonical game at the public data `pubP (fullE t).1`, realized at hidden values `trueV` that agree
with `fullE`'s off the charged coordinates `chgB t` (the randomizers of the non-first messages and
the `H_msg` outputs of the non-first messages and of the charged labels at `PK.root`).

* **The ports agree** (`slotPorts_agree`, `hmsgPorts_agree`): a structural slot's ports at the
  public data program the table's cells and values (Reparam's `rounds_fwd`, the keys agreeing on the
  paths); an `H_msg` call's ports program the table's `k`- and `k'`-cells (no stage moved them:
  `kPub_hmsg`, `k'Pub_hmsg` by `HRateSep`) and, at its `h`-cell, the public `h` value corrected by
  `cor256` to the table's output, which gives back the table's `h` value since the public `h`
  agrees with the table's from bit `256` on (`hiEq_pubP`).
* `hgame_fullE`: the game congruence (GameCongr's `realizeT_gameT_congr`).
-/

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed truncateHash)
open Quantum.Xmss (X Z out256 trunc128)
open Quantum.Xmss.Hybrid (IsFirst capOf rateOf LazyProg Agree)
open Quantum.Xmss.Assembly (fwd rnK rnR rnZ rnK_zero XW)
open Quantum.Sphincs.Hybrid (Tab DLab rCell rOrd dLabCell dLabMsg dLabOrd skCell posOf schemeSplit
  dSplit rB dBX rCell_ne_dLabCell skCell_ne_dLabCell)

namespace Quantum.Sphincs.Assembly

/-! ## The `H_msg` cells at the public keys -/

section hmsg

variable {t : FT} (ht : StageGood t)

include ht

/-- **The public `k` is the table's at every `H_msg` cell.** -/
theorem kPub_hmsg (a : DLab) (R : Randomizer) :
    (phiE t).1.2.2.2.1 (dLabCell a (tabOf t).publicSeed R) =
      (tabOf t).keys.2.1 (dLabCell a (tabOf t).publicSeed R) :=
  kPub_eq ht _ (fun M h ↦ rCell_ne_dLabCell M _ _ a _ _ h)
    (fun b h ↦ skCell_ne_dLabCell _ _ b a _ _ h)

/-- **The public `k'` is the table's at every `H_msg` rate.** -/
theorem k'Pub_hmsg (hrs : HRateSep (schemeSplit t.1.1.1.1.1)) (a : DLab) (R : Randomizer) :
    (phiE t).1.2.2.2.2
        (rateOf (tabOf t).keys.2.1 (tabOf t).perm (dLabCell a (tabOf t).publicSeed R)) =
      (tabOf t).keys.2.2
        (rateOf (tabOf t).keys.2.1 (tabOf t).perm (dLabCell a (tabOf t).publicSeed R)) := by
  have hsep := hRateSep_table (posOf_injective_of_dGood ht.1) hrs a R
  exact k'Pub_eq ht _ (fun M h ↦ hsep.1 M h.symm) (fun b h ↦ hsep.2 b h.symm)

end hmsg

/-! ## The template's hidden values at a table -/

/-- The hidden values with the table's randomizers and `H_msg` outputs. -/
def trueV (L : HonestTable) (v : (s : HPos) → XD s) : (s : HPos) → XD s
  | .val q => v (.val q)
  | .rnd M => L.randomizer M
  | .dig M i => L.digestOutput M i
  | .str j i => v (.str j i)
  | .asg M j => v (.asg M j)

/-- **The charged coordinates**: the randomizers of the non-first messages, the `H_msg` outputs of
the non-first messages and of the charged labels at `PK.root`. -/
def IsChg (t : FT) : HPos → Prop
  | .rnd M => M ∈ rB rCell rOrd (tabOf t)
  | .dig M i => M ∈ rB rCell rOrd (tabOf t) ∨
      ((tabOf t).root, M, i) ∈
        dBX rCell dLabCell dLabMsg dLabOrd (dSplit rCell rOrd dLabCell dLabMsg dLabOrd t.1.1.1)
  | _ => False

open scoped Classical in
/-- The charged coordinates as a finite set. Irreducible: membership does not unfold the
enumeration of the coordinates. -/
@[irreducible]
noncomputable def chgB (t : FT) : Finset HPos :=
  Finset.univ.filter (IsChg t)

theorem mem_chgB {t : FT} {s : HPos} : s ∈ chgB t ↔ IsChg t s := by
  unfold chgB
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Families agreeing off `B` agree on `univ \ B` (over abstract types: membership in `univ` never
unfolds). -/
theorem agree_univ_sdiff_dep {S : Type} [Fintype S] [DecidableEq S] {D : S → Type}
    {B : Finset S} {w w' : (s : S) → D s} (h : ∀ s, s ∉ B → w s = w' s) :
    Agree (Finset.univ \ B) w w' :=
  fun s hs ↦ h s (Finset.mem_sdiff.mp hs).2

/-- **Off the charged coordinates `trueV` is `fullE`'s.** -/
theorem agree_trueV {t : FT} (ht : StageGood t) :
    Agree (Finset.univ \ chgB t) (trueV (tabOf t) (fullE t).2.1) (fullE t).2.1 := by
  refine agree_univ_sdiff_dep fun s hs ↦ ?_
  have hn : ¬IsChg t s := fun h ↦ hs (mem_chgB.mpr h)
  cases s with
  | val q => rfl
  | rnd M => exact (rnd_fullE ht M hn).symm
  | dig M i =>
    have h1 : M ∉ rB rCell rOrd (tabOf t) := fun h ↦ hn (Or.inl h)
    have h2 : ((tabOf t).root, M, i) ∉
        dBX rCell dLabCell dLabMsg dLabOrd (dSplit rCell rOrd dLabCell dLabMsg dLabOrd t.1.1.1) :=
      fun h ↦ hn (Or.inr h)
    exact (dig_fullE ht M i h1 h2).symm
  | str j i => rfl
  | asg M j => rfl

/-! ## The ports agree -/

section ports

/-- The first round's rate of an absorption. -/
theorem rnR_zero (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z) (b : ℕ → X) :
    rnR π h k k' b 0 = rateOf k π (b 0) := by
  show (π ((0 : X) + b 0, (0 : Z) + k ((0 : X) + b 0))).1 = _
  rw [zero_add, zero_add]
  rfl

/-- The first round's capacity of an absorption. -/
theorem rnZ_zero (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z) (b : ℕ → X) :
    rnZ π h k k' b 0 = capOf k k' π (b 0) := by
  show (π ((0 : X) + b 0, (0 : Z) + k ((0 : X) + b 0))).2 +
    k' (π ((0 : X) + b 0, (0 : Z) + k ((0 : X) + b 0))).1 = _
  rw [zero_add, zero_add]
  rfl

/-- An `H_msg` call's block is its `H_msg` cell. -/
theorem slotBlk_hmsg_zero (P : PublicParameter) (R : Randomizer) (M : Message) (i : DigestCall)
    (f : ValPos → Digest) : slotBlk P (.hmsg R M i) f 0 = dLabCell (f rootPos, M, i) P R :=
  slotBlk_zero P _ f

variable {t : FT} (ht : StageGood t)

omit ht in
/-- The public data's `π` is the table's. -/
theorem pubP_perm : (pubP (fullE t).1).perm = (tabOf t).perm :=
  wPub_perm

include ht

/-- The public data's `PK.seed` is the table's. -/
theorem pubP_seed : (pubP (fullE t).1).seed = (tabOf t).publicSeed :=
  wPub_seed ht

/-- **A structural slot's ports agree**: at the table and at the public data they program the
table's cells and values. -/
theorem slotPorts_agree (hθ : XGood (phiE t).1) {s : Slot} (hs : InTable s) :
    (slotPorts (pubOf (tabOf t)) s).map (LazyProg.realize (valueAt (tabOf t))) =
      (slotPorts (pubP (fullE t).1) s).map
        (LazyProg.realize (trueV (tabOf t) (fullE t).2.1)) := by
  have hk := pathKeys_of_stageGood ht
  have hu := pads_of_stageGood ht
  have hw1 : (phiE t).1.2.1 = (tabOf t).publicSeed := wPub_seed ht
  have hkL : PathKeys (tabOf t) (tabW (tabOf t)) (tabOf t).keys.1 :=
    ⟨rfl, rfl, fun _ _ _ _ ↦ ⟨rfl, rfl, rfl⟩⟩
  rw [realize_slotPorts (pubOf (tabOf t)) hs, realize_slotPorts _ hs, pubP_seed ht]
  refine pathCells_congr fun j hj ↦ ?_
  have hr := rounds_fwd (h := (phiE t).1.1.1) (u := (phiE t).1.1.2) (w := (phiE t).1.2) hθ hs
    (j := j) (by rw [hw1]; exact hj)
  rw [hw1] at hr
  obtain ⟨c1, c2, c3⟩ := cells_eq_keys hk hu hs hj
  obtain ⟨v1, v2, v3⟩ := cellVals_eq_keys hk hu hs hj
  have hT := cellH_table (tabW (tabOf t)) (tabOf t).keys.1 (valuePos (tabOf t))
    (inPos_slotOutPos hs) j
  have hb : slotBlk (tabW (tabOf t)).1 s (sVal (tabW (tabOf t)) (tabOf t).keys.1
      (valuePos (tabOf t))) = slotBlk (tabOf t).publicSeed s (valuePos (tabOf t)) :=
    slotBlk_sVal_tabW (tabOf t) (valuePos (tabOf t)) (fun _ _ ↦ rfl) hs
  rw [outSlot_slotOutPos hs, hb, sVal_tabW (tabOf t) _ (fun _ _ ↦ rfl) _
    (Or.inl (inPos_slotOutPos hs)), (cells_eq_of_slotBlk hkL hs hb hj).2.2] at hT
  have l1 : cellK (pubOf (tabOf t)) (slotBlk (tabOf t).publicSeed s (valuePos (tabOf t))) j =
      (sCellK (tabW (tabOf t)) (tabOf t).keys.1 s (valuePos (tabOf t)) j,
        (tabOf t).keys.2.1 (sCellK (tabW (tabOf t)) (tabOf t).keys.1 s (valuePos (tabOf t)) j)) :=
    rfl
  have l2 : cellK' (pubOf (tabOf t)) (slotBlk (tabOf t).publicSeed s (valuePos (tabOf t))) j =
      (sCellR (tabW (tabOf t)) (tabOf t).keys.1 s (valuePos (tabOf t)) j,
        (tabOf t).keys.2.2 (sCellR (tabW (tabOf t)) (tabOf t).keys.1 s (valuePos (tabOf t)) j)) :=
    rfl
  exact ⟨l1.trans ((congrArg₂ Prod.mk c1.symm v1.symm).trans hr.1.symm),
    l2.trans ((congrArg₂ Prod.mk c2.symm v2.symm).trans hr.2.1.symm),
    hT.trans ((congrArg₂ Prod.mk c3.symm v3.symm).trans hr.2.2.symm)⟩

/-- **An `H_msg` call's ports agree**: at the table and at the public data they program the table's
cells and, at its `h`-cell, the table's `h` value. -/
theorem hmsgPorts_agree (hrs : HRateSep (schemeSplit t.1.1.1.1.1)) (T : Finset HPos) (M : Message)
    (i : DigestCall) :
    (hmsgPorts (pubOf (tabOf t)) msgPol T M i).map (LazyProg.realize (valueAt (tabOf t))) =
      (hmsgPorts (pubP (fullE t).1) msgPol T M i).map
        (LazyProg.realize (trueV (tabOf t) (fullE t).2.1)) := by
  rw [realize_hmsgPorts, realize_hmsgPorts]
  have hroot : (fullE t).2.1 (.val rootPos) = valuePos (tabOf t) rootPos :=
    val_fullE ht rootPos (live_of_fullPos fullPos_rootPos)
  have hb : slotBlk (pubP (fullE t).1).seed (.hmsg ((tabOf t).randomizer M) M i)
      (valsOf (trueV (tabOf t) (fullE t).2.1)) =
      slotBlk (tabOf t).publicSeed (.hmsg ((tabOf t).randomizer M) M i) (valuePos (tabOf t)) := by
    rw [pubP_seed ht]
    funext j
    unfold slotBlk
    rw [slotInput_congr _ fun q hq ↦ ?_]
    simp only [slotNeed, Finset.mem_singleton] at hq
    subst hq
    exact hroot
  show pathCells (pubOf (tabOf t))
      (slotBlk (tabOf t).publicSeed (.hmsg ((tabOf t).randomizer M) M i) (valuePos (tabOf t)))
      (cor256 ((tabOf t).digestOutput M i)) 1 =
    pathCells (pubP (fullE t).1) (slotBlk (pubP (fullE t).1).seed
      (.hmsg ((tabOf t).randomizer M) M i) (valsOf (trueV (tabOf t) (fullE t).2.1)))
      (cor256 ((tabOf t).digestOutput M i)) 1
  rw [hb]
  set b := slotBlk (tabOf t).publicSeed (.hmsg ((tabOf t).randomizer M) M i) (valuePos (tabOf t))
    with hbdef
  have hb0 :
      b 0 = dLabCell ((tabOf t).root, M, i) (tabOf t).publicSeed ((tabOf t).randomizer M) := by
    rw [hbdef, slotBlk_hmsg_zero, valuePos_rootPos]
  have hk := kPub_hmsg ht ((tabOf t).root, M, i) ((tabOf t).randomizer M)
  have hk' := k'Pub_hmsg ht hrs ((tabOf t).root, M, i) ((tabOf t).randomizer M)
  rw [← hb0] at hk hk'
  have hπ : (pubP (fullE t).1).perm = (tabOf t).perm := pubP_perm
  have hkP : (pubP (fullE t).1).keys.2.1 (b 0) = (tabOf t).keys.2.1 (b 0) := hk
  have hrate : rateOf (pubP (fullE t).1).keys.2.1 (pubP (fullE t).1).perm (b 0) =
      rateOf (tabOf t).keys.2.1 (tabOf t).perm (b 0) := by
    unfold rateOf
    rw [hπ, hkP]
  have hk'P : (pubP (fullE t).1).keys.2.2 (rateOf (tabOf t).keys.2.1 (tabOf t).perm (b 0)) =
      (tabOf t).keys.2.2 (rateOf (tabOf t).keys.2.1 (tabOf t).perm (b 0)) := hk'
  have hcap : capOf (pubP (fullE t).1).keys.2.1 (pubP (fullE t).1).keys.2.2
      (pubP (fullE t).1).perm (b 0) =
        capOf (tabOf t).keys.2.1 (tabOf t).keys.2.2 (tabOf t).perm (b 0) := by
    have e : capOf (pubP (fullE t).1).keys.2.1 (pubP (fullE t).1).keys.2.2
        (pubP (fullE t).1).perm (b 0) = ((pubP (fullE t).1).perm (b 0,
          (pubP (fullE t).1).keys.2.1 (b 0))).2 + (pubP (fullE t).1).keys.2.2
          (rateOf (pubP (fullE t).1).keys.2.1 (pubP (fullE t).1).perm (b 0)) := rfl
    rw [e, hrate, hk'P, hπ, hkP]
    rfl
  have hy : (tabOf t).digestOutput M i = out256 (rateOf (tabOf t).keys.2.1 (tabOf t).perm (b 0) +
      (tabOf t).keys.1 (capOf (tabOf t).keys.2.1 (tabOf t).keys.2.2 (tabOf t).perm (b 0))) := by
    rw [hb0]
    exact Quantum.Sphincs.Hybrid.hash_of_lt _ _
      (Quantum.Sphincs.Hybrid.length_messageDigestInput_lt _ _ _ _ _)
  refine pathCells_congr fun j hj ↦ ?_
  obtain rfl : j = 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · show (rnK (tabOf t).perm (tabOf t).keys.1 (tabOf t).keys.2.1 (tabOf t).keys.2.2 b 0,
        (tabOf t).keys.2.1 (rnK (tabOf t).perm (tabOf t).keys.1 (tabOf t).keys.2.1
          (tabOf t).keys.2.2 b 0)) =
      (rnK (pubP (fullE t).1).perm (pubP (fullE t).1).keys.1 (pubP (fullE t).1).keys.2.1
          (pubP (fullE t).1).keys.2.2 b 0, (pubP (fullE t).1).keys.2.1 (rnK (pubP (fullE t).1).perm
            (pubP (fullE t).1).keys.1 (pubP (fullE t).1).keys.2.1 (pubP (fullE t).1).keys.2.2 b 0))
    rw [rnK_zero, rnK_zero, hkP]
  · show (rnR (tabOf t).perm (tabOf t).keys.1 (tabOf t).keys.2.1 (tabOf t).keys.2.2 b 0,
        (tabOf t).keys.2.2 (rnR (tabOf t).perm (tabOf t).keys.1 (tabOf t).keys.2.1
          (tabOf t).keys.2.2 b 0)) =
      (rnR (pubP (fullE t).1).perm (pubP (fullE t).1).keys.1 (pubP (fullE t).1).keys.2.1
          (pubP (fullE t).1).keys.2.2 b 0, (pubP (fullE t).1).keys.2.2 (rnR (pubP (fullE t).1).perm
            (pubP (fullE t).1).keys.1 (pubP (fullE t).1).keys.2.1 (pubP (fullE t).1).keys.2.2 b 0))
    rw [rnR_zero, rnR_zero, hrate, hk'P]
  · rw [cellH, cellH, ite_eq_left rfl, ite_eq_left rfl]
    dsimp only [pubOf]
    rw [rnR_zero, rnR_zero, rnZ_zero, rnZ_zero, hrate, hcap,
      cor256_eq_of_hiEq (HiEq.refl _) hy, cor256_eq_of_hiEq (hiEq_pubP ht _) hy]

end ports

/-! ## The game -/

/-- **The core good set**: the stage good set, a good permutation, `HRateSep`, and Reparam's good
set. -/
def FullGCore (t : FT) : Prop :=
  StageGood t ∧ PermGood (tabOf t).perm 18 ∧ HRateSep (schemeSplit t.1.1.1.1.1) ∧ XGood (phiE t).1

/-- **`hgame`**: on the core good set, the canonical game at the table is the canonical game at the
public data `pubP (fullE t).1`, realized at hidden values agreeing with `fullE`'s off the charged
coordinates. -/
theorem hgame_fullE (A : SAdversary) {t : FT} (ht : FullGCore t) :
    ∃ v : (s : HPos) → XD s, Agree (Finset.univ \ chgB t) v (fullE t).2.1 ∧
      gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)) =
        gameR msgPol A (pubP (fullE t).1) v := by
  obtain ⟨hs, -, hrs, hθ⟩ := ht
  refine ⟨trueV (tabOf t) (fullE t).2.1, agree_trueV hs, ?_⟩
  refine realizeT_gameT_congr Selections cwUpd msgPol A (pubP_seed hs).symm pubP_perm.symm
    (fun q hq ↦ (val_fullE hs q (live_of_fullPos hq)).symm) (fun _ ↦ rfl) (fun T M s hm ↦ ?_)
    (fun s hs' ↦ slotPorts_agree hs hθ hs') (fun T M i ↦ hmsgPorts_agree hs hrs T M i)
  simp only [DigestPolicy.need, msgPol, Finset.mem_insert] at hm
  rcases hm with rfl | rfl | h
  · rfl
  · rfl
  · exact absurd h (Finset.notMem_empty _)

end Quantum.Sphincs.Assembly

end
