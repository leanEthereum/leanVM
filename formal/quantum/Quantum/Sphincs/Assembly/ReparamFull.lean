module

public import Quantum.Sphincs.Assembly.ReparamFull.Bad

@[expose] public section

/-!
# The composed reparametrization of leanSPHINCS's tables

The hybrid side of the leanSPHINCS chain (step 2: the masked graded hybrid at `msgPol`, averaged
over the good set of the composed reparametrization, the bad fraction paid once) needs the padded
tables reparametrized into public data, hidden values `(s : HPos) → XD s` and a never-revealed
part, with the canonical game at a table equal to the canonical game at the public data. The
pieces:

* `ReparamFull.HiFix`: the fix-up exchange `hiStageOn` (the bits of `h` from `256` on), `cor256`
  against agreeing high bits (`cor256_eq_of_hiEq`), the path stages' `setHC`, and `pFull` (the
  path stages, the fix-up and the undoing of the `k`- and `k'`-stages).
* `ReparamFull.Coords`: the padded tables `FT`, the stages before Reparam `stagesE` (the
  randomizer stage, the randomizer and scheme fix-ups, SeedStage's `seedKStages`, the secrets'
  exchange with Reparam's pad), Reparam's table `phiE`, the digest stage `dLast` after Reparam
  (`pFull` at the labels `(M, i)`, keyed by the hidden root at `rootPos`), the final coordinates
  `psiE` (the hidden value `.dig M i` is the first `256` bits of the digest slot `(M, i)`), the
  reparametrization `fullE`, `fullE_injOn`, `coordEquiv`.
* `ReparamFull.Facts`, `ReparamFull.Table`: on the stage good set (`StageGood`: `dGood` and
  `seedKGood` for the computations `compQ` of `ReparamFull.Comp`, with `rCell` as SeedStage's label
  family, so `hsep` and `SeedRateInj` cover the randomizer stage), the public keys agree with the
  table's on its in-table paths (`pathKeys_of_stageGood`), the pad holds the table's secrets
  (`pads_of_stageGood`), the hidden values are the table's (`val_fullE`, `rnd_fullE` at a first
  message).
* `ReparamFull.DStage`: the digest stage's good set `DGoodYS` and its facts (`dig_fullE` at an
  uncharged label `dBX`, `hiEq_pubP`, `cells_pubP_eq`, `pathsAvoid_pubP`).
* `ReparamFull.Game`: `hgame_fullE`, through GameCongr's `realizeT_gameT_congr`; the `H_msg`
  ports need `HRateSep` (`ReparamFull.RateSep`: every `H_msg` rate apart from the randomizer and
  `SK.seed`-keyed rates, `2^-318`).
* `ReparamFull.DBad`, `ReparamFull.Bad`: the digest stage's bad fraction; the good set `FullG S`
  (with PathsDisjoint's `PathsDisjoint` and a static slot `S` for SP-PF1's good-data conditions),
  `pathsAvoid_fullE`, `fullG_frac_le_keccak`.

Here: the coordinates are as many as the padded tables (`card_coords`), and the average
corollary's hypotheses in one statement (`fullE_spec`).
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Message)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (XW)
open Quantum.Xmss.Hybrid (Agree)

namespace Quantum.Sphincs.Assembly

/-! ## Finiteness and the count of the coordinates -/

section count

open scoped Classical in
noncomputable instance instFintypePP : Fintype PP :=
  inferInstanceAs (Fintype (((Z → X) × XW) × PubR))

open scoped Classical in
noncomputable instance instFintypeKK : Fintype KK :=
  inferInstanceAs (Fintype (Hybrid.Secret × Hybrid.SeedKS × (Message → Z) × (Message → Z) ×
    (Message → Fin 960 → ZMod 2) × (Hybrid.DLab → Z) × (Hybrid.DLab → Z) ×
    (Hybrid.DLab → Fin 832 → ZMod 2)))

noncomputable instance instFintypeHidVals : Fintype ((s : HPos) → XD s) :=
  Pi.instFintype

noncomputable instance instFintypeHidKK : Fintype (((s : HPos) → XD s) × KK) :=
  instFintypeProd _ _

/-- **`hcard`**: the coordinates are as many as the padded tables. -/
theorem card_coords :
    Fintype.card PP * Fintype.card (((s : HPos) → XD s) × KK) = Fintype.card FT := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr coordEquiv

end count

/-! ## The reparametrization's facts in one statement -/

/-- **The composed reparametrization** at the good set `FullG S`: injective, with the canonical game
at the table equal to the canonical game at the public data realized at hidden values agreeing
with `fullE`'s off the charged coordinates, the permutation the table's, and the template data
avoiding the output cells. -/
theorem fullE_spec (S : PP → ((s : HPos) → XD s) → Prop) (A : SAdversary) :
    Set.InjOn fullE {t | FullG S t} ∧
      ∀ t, FullG S t →
        (∃ v : (s : HPos) → XD s, Agree (Finset.univ \ chgB t) v (fullE t).2.1 ∧
          gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)) =
            gameR msgPol A (pubP (fullE t).1) v) ∧
        (pubP (fullE t).1).perm = (tabOf t).perm ∧
        PathsAvoid (pubP (fullE t).1).xw (pubP (fullE t).1).keys.1 (valsOf (fullE t).2.1) ∧
        PathsDisjoint (pubP (fullE t).1).xw (pubP (fullE t).1).keys.1 (valsOf (fullE t).2.1) :=
  ⟨fullE_injOn.mono fun _ h ↦ h.1.2.2.2, fun _ h ↦
    ⟨hgame_fullE A h.1, pubP_perm, pathsAvoid_fullE h.1, h.2.1⟩⟩

end Quantum.Sphincs.Assembly

end
