module

public import Quantum.Xmss.Assembly.Reparam
public import Quantum.Sphincs.Assembly.Template.Exempt

@[expose] public section

/-!
# Reparametrizing leanSPHINCS's table into public data and hidden values

`Quantum.Xmss.Assembly.Reparam`'s generic reparametrization (`DigestFix`, `Outputs`, `fwd`, `back`,
the good sets `GoodWith`, `GoodPVWith`, `card_not_eq_of_maps`, `uavg_le_of_good`) applied to
leanSPHINCS's structural slots (contract C1, `Quantum.Sphincs.HonestTable`) and the template of
contract C2 (`Quantum.Sphincs.Assembly.Template`). A table is `((h, u), w)`: the rate key `h`, a
pad `u : ValPos → Digest` and `w = (PK.seed, π, k, k')` (`XW`).

* `sphFix`: the digest of the output rate `r + w` is `trunc128 (r + w)`; the correction is the
  template's `cor128` (`cor128 d r w`).
* **The values** `sVal w h u`: at an in-table output (`InPos`, `xI` of
  `Quantum.Sphincs.Assembly.PathBad`) the digest of its slot's input at the values of lower rank
  (`sRank`: chain positions by index, hypertree values above them by level, FORS values by height
  above the secrets, the FORS keys on top), the pad elsewhere (chain starts, FORS secrets, junk
  positions). `slotInput_congr_live`: an in-table slot's input reads only positions of lower rank
  that are in-table outputs or secrets (`Live`, `SecretPos`).
* `sO`: the outputs `xI`, the values `sVal`, the output cell `sOutCap` and rate `sOutRate` of
  PathBad's paths; `sO_consistent`, `sO_ranked`.
* **The good set** `XGood` (`XGoodPV` in the public coordinates): distinct output cells and
  PathBad's `PathsAvoid`, which gives local paths (`local_of_pathsAvoid`, `pathsAvoid_congr`).
  `back_fwd`, `fwd_back`: `fwd sphFix sO` and `back sphFix sO` are inverse on the good sets.
* **The template** (`sPub w h` the public data, `pubOf_eq`): the realized ports of a structural
  slot are PathBad's cells (`realize_slotPorts_cells`: `k`-, `k'`-, `h`-cells `sCellK`, `sCellR`,
  `sCellZ`, the last `h`-cell `sOutCap`; `cellK_fst`, `cellK'_fst`, `cellH_fst_eq`,
  `cellH_last_fst`, definitionally). `rounds_fwd`: on `XGood`, the template's cells at the
  public data of `fwd` and the values `sVal w h u` are the table's honest cells (the corrected
  final value gives back `h`, `cor_fwd`); `cellH_table`: at the table's own public data the
  correction vanishes. `pathsAvoid_fwd`, `pathsAvoid_of_xGoodPV`: the template data of the good
  set satisfy `PathsAvoid pub.xw pub.keys.1 (valsOf v)` (the hypothesis of
  `finalSep_of_pathsAvoid`).
* **The honest table**: `sVal_tabW`: with the chain starts and FORS secrets in the pad, the values
  are `valuePos L` on `Live` positions (on `xI` in particular); `slotBlk_sVal_tabW`.
* **The bad fraction**: `¬XGoodPV` is PathBad's `PathBad` (`not_xGoodPV_iff`), so
  `xGood_bad_frac_le`: at most `2^-400` of the tables are outside `XGood`
  (`pathBad_frac_le_keccak`); `uavg_not_pathsAvoid_le`: the public coordinates without
  `PathsAvoid` weigh at most `2^-400`; `uavg_le_sph`: the averaging corollary.
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest PublicParameter chainLength littleEndianBytes digestsPayload)
open HashSig.OverPermutation (nodePayload)
open Quantum.Xmss (X Z blocks trunc128)
open Quantum.Xmss.Hybrid (LazyProg uavg uavg_mono uavg_ite_zero_one)
open Quantum.Xmss.Assembly (DigestFix Outputs AgreeOff fwd back agreeOff_fwd cor_fwd good_of_with
  goodPV_of_with goodPVWith_fwd goodWith_back card_not_eq_of_maps uavg_le_of_good card_tab_eq
  xmssFix xmssFix_cor_dig rnK rnR rnZ RnAgree rnK_congr rnR_congr rnZ_congr rnSt_succ XW)

namespace Quantum.Sphincs.Assembly

/-! ## The digest correction -/

/-- **leanSPHINCS's digest correction**: the digest of the output rate `r + w` is its first 128
bits; the correction is the template's `cor128`. -/
def sphFix : DigestFix X Digest where
  dig r w := trunc128 (r + w)
  cor r w d := cor128 d r w
  dig_cor r w d := trunc128_cor128 d r w
  cor_cor := xmssFix.cor_cor

/-- At the table's own digest the correction vanishes. -/
theorem sphFix_cor_dig (r w : X) : sphFix.cor r w (sphFix.dig r w) = w :=
  xmssFix_cor_dig r w

/-! ## Ranks and live positions -/

/-- **The rank of a position**: chain positions by their index, hypertree values above them by
level, FORS secrets at `0`, FORS values by height above them, the FORS keys on top. -/
def sRank : ValPos → ℕ
  | .chain _ _ _ _ j => j.val
  | .tree _ _ level _ => chainLength + level.val
  | .forsSecret .. => 0
  | .forsTree _ _ height _ => height.val + 1
  | .forsKey _ => forsTreeHeight + 2

/-- **A secret position** of the table: an in-range chain start or a FORS secret. -/
def SecretPos : ValPos → Prop
  | .chain l τ e _ j => j.val = 0 ∧ τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l
  | .forsSecret .. => True
  | _ => False

/-- **A live position**: an in-table output or a secret. -/
def Live (q : ValPos) : Prop :=
  InPos q ∨ SecretPos q

theorem sRank_cpos (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) {j : ℕ}
    (hj : j < chainLength) : sRank (cpos l τ e i j) = j :=
  Nat.mod_eq_of_lt hj

theorem sRank_tpos (l : Layer) (τ : TreeIndex) {lev c : ℕ} (hl : lev ≤ layerHeight topLayer) :
    sRank (tpos l τ lev c) = chainLength + lev := by
  show chainLength + lev % (layerHeight topLayer + 1) = chainLength + lev
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hl)]

theorem sRank_fpos (idx : Index) (κ : ForsTreeIndex) {lev c : ℕ} (hl : lev ≤ forsTreeHeight) :
    sRank (fpos idx κ lev c) = lev + 1 := by
  show lev % (forsTreeHeight + 1) + 1 = lev + 1
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hl)]

theorem live_cpos {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} (i : ChainIndex)
    (hτ : τ.val < 2 ^ treeBits l) (he : e.val < 2 ^ layerHeight l) {j : ℕ} (hj : j < chainLength) :
    Live (cpos l τ e i j) := by
  rcases j with _ | k
  · exact Or.inr (show 0 % chainLength = 0 ∧ τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l
      from ⟨Nat.zero_mod _, hτ, he⟩)
  · have hk : k < chainLength - 1 := by omega
    exact Or.inl (inPos_slotOutPos (s := .chain l τ e i ⟨k, hk⟩)
      (show τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l from ⟨hτ, he⟩))

theorem live_tpos {l : Layer} {τ : TreeIndex} (hτ : τ.val < 2 ^ treeBits l) {lev c : ℕ}
    (hl : lev ≤ layerHeight l) (hc : c < 2 ^ (layerHeight l - lev)) : Live (tpos l τ lev c) := by
  rcases lev with _ | m
  · rw [Nat.sub_zero] at hc
    exact Or.inl (inPos_slotOutPos (s := .leaf l τ ⟨c, lt_of_lt_of_le hc
      (two_pow_layerHeight_le l)⟩)
      (show τ.val < 2 ^ treeBits l ∧ c < 2 ^ layerHeight l from ⟨hτ, hc⟩))
  · exact Or.inl (inPos_slotOutPos (s := .node l τ (m + 1) c)
      (show τ.val < 2 ^ treeBits l ∧ 1 ≤ m + 1 ∧ m + 1 ≤ layerHeight l ∧
        c < 2 ^ (layerHeight l - (m + 1)) from ⟨hτ, by omega, hl, hc⟩))

theorem live_fpos (idx : Index) (κ : ForsTreeIndex) {lev c : ℕ} (hl : lev ≤ forsTreeHeight)
    (hc : c < 2 ^ (forsTreeHeight - lev)) : Live (fpos idx κ lev c) := by
  rcases lev with _ | m
  · rw [Nat.sub_zero] at hc
    exact Or.inl (inPos_slotOutPos (s := .forsLeaf idx κ ⟨c, hc⟩) trivial)
  · exact Or.inl (inPos_slotOutPos (s := .forsNode idx κ (m + 1) c)
      (show 1 ≤ m + 1 ∧ m + 1 ≤ forsTreeHeight ∧ c < 2 ^ (forsTreeHeight - (m + 1)) from
        ⟨by omega, hl, hc⟩))

/-- The children of a node at height `h ≥ 1` are in range one level below. -/
theorem child_lt {a h n : ℕ} (h1 : 1 ≤ h) (ha : h ≤ a) (hn : n < 2 ^ (a - h)) :
    2 * n + 1 < 2 ^ (a - (h - 1)) := by
  rw [show a - (h - 1) = a - h + 1 by omega, pow_succ]
  omega

/-- **An in-table slot's input reads only live positions of lower rank** than its output. -/
theorem slotInput_congr_live (P : PublicParameter) {s : Slot} (hs : InTable s)
    {f g : ValPos → Digest} (h : ∀ q, Live q → sRank q < sRank (slotOutPos s) → f q = g q) :
    slotInput P s f = slotInput P s g := by
  have ht : layerHeight topLayer = 10 := rfl
  cases s with
  | chain l τ e i step =>
    obtain ⟨hτ, he⟩ := hs
    have hstep := step.isLt
    have hr : sRank (cpos l τ e i step.val) < sRank (cpos l τ e i (step.val + 1)) := by
      rw [sRank_cpos _ _ _ _ (by omega), sRank_cpos _ _ _ _ (by omega)]
      omega
    change addressedHashInput _ _ (littleEndianBytes 16 (f _)) =
      addressedHashInput _ _ (littleEndianBytes 16 (g _))
    rw [h _ (live_cpos i hτ he (by omega)) hr]
  | leaf l τ e =>
    obtain ⟨hτ, he⟩ := hs
    have hr : ∀ i, sRank (cpos l τ e i (chainLength - 1)) < sRank (tpos l τ 0 e.val) := fun i ↦ by
      rw [sRank_cpos _ _ _ _ (by decide), sRank_tpos _ _ (Nat.zero_le _)]
      decide
    change addressedHashInput _ _ (digestsPayload fun i ↦ f _) =
      addressedHashInput _ _ (digestsPayload fun i ↦ g _)
    exact congrArg (addressedHashInput _ _) (congrArg digestsPayload (funext fun i ↦
      h _ (live_cpos i hτ he (by decide)) (hr i)))
  | node l τ height index =>
    obtain ⟨hτ, h1, h2, h3⟩ := hs
    have hl := layerHeight_le l
    have hc := child_lt h1 h2 h3
    have hr : ∀ c, sRank (tpos l τ (height - 1) c) < sRank (tpos l τ height index) := fun c ↦ by
      rw [sRank_tpos _ _ (by omega), sRank_tpos _ _ (by omega)]
      omega
    change addressedHashInput _ _ (nodePayload (f _) (f _)) =
      addressedHashInput _ _ (nodePayload (g _) (g _))
    rw [h _ (live_tpos hτ (by omega) (by omega : 2 * index < _)) (hr _),
      h _ (live_tpos hτ (by omega) hc) (hr _)]
  | forsLeaf idx κ s =>
    have hr : sRank (.forsSecret idx κ s) < sRank (fpos idx κ 0 s.val) := by
      rw [sRank_fpos _ _ (Nat.zero_le _)]
      exact Nat.succ_pos _
    change addressedHashInput _ _ (littleEndianBytes 16 (f _)) =
      addressedHashInput _ _ (littleEndianBytes 16 (g _))
    rw [h (.forsSecret idx κ s) (Or.inr trivial) hr]
  | forsNode idx κ height node =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hc := child_lt h1 h2 h3
    have hr : ∀ c, sRank (fpos idx κ (height - 1) c) < sRank (fpos idx κ height node) := fun c ↦ by
      rw [sRank_fpos _ _ (by omega), sRank_fpos _ _ h2]
      omega
    change addressedHashInput _ _ (nodePayload (f _) (f _)) =
      addressedHashInput _ _ (nodePayload (g _) (g _))
    rw [h _ (live_fpos idx κ (by omega) (by omega : 2 * node < _)) (hr _),
      h _ (live_fpos idx κ (by omega) hc) (hr _)]
  | forsRoots idx =>
    have hr : ∀ κ, sRank (fpos idx κ forsTreeHeight 0) < sRank (.forsKey idx) := fun κ ↦ by
      rw [sRank_fpos _ _ le_rfl]
      exact Nat.lt_succ_self _
    have hz : 0 < 2 ^ (forsTreeHeight - forsTreeHeight) := Nat.two_pow_pos _
    change addressedHashInput _ _ (digestsPayload fun κ ↦ f _) =
      addressedHashInput _ _ (digestsPayload fun κ ↦ g _)
    exact congrArg (addressedHashInput _ _) (congrArg digestsPayload (funext fun κ ↦
      h _ (live_fpos idx κ le_rfl hz) (hr κ)))
  | _ => exact hs.elim

/-- `slotInput_congr_live` for the blocks. -/
theorem slotBlk_congr_live (P : PublicParameter) {s : Slot} (hs : InTable s)
    {f g : ValPos → Digest} (h : ∀ q, Live q → sRank q < sRank (slotOutPos s) → f q = g q) :
    slotBlk P s f = slotBlk P s g :=
  congrArg (fun x j ↦ (blocks x).getD j 0) (slotInput_congr_live P hs h)

/-- `slotBlk_congr_live` at an in-table output's slot. -/
theorem slotBlk_congr_inPos (P : PublicParameter) {p : ValPos} (hp : InPos p)
    {f g : ValPos → Digest} (h : ∀ q, Live q → sRank q < sRank p → f q = g q) :
    slotBlk P (outSlot p) f = slotBlk P (outSlot p) g :=
  slotBlk_congr_live P hp.1 fun q hq hr ↦ h q hq (hp.2 ▸ hr)

/-! ## The table's values and outputs -/

/-- **The output rate** of slot `s`: the rate after `π` in its last round. -/
def sOutRate (w : XW) (h : Z → X) (s : Slot) (v : ValPos → Digest) : X :=
  sCellR w h s v (nBlk w.1 s - 1)

/-- The output cell and rate depend on the values through the blocks only. -/
theorem sOut_congr {w : XW} {h : Z → X} {s : Slot} {f g : ValPos → Digest}
    (hb : slotBlk w.1 s f = slotBlk w.1 s g) :
    sOutCap w h s f = sOutCap w h s g ∧ sOutRate w h s f = sOutRate w h s g := by
  unfold sOutCap sOutRate sCellZ sCellR
  rw [hb]
  exact ⟨rfl, rfl⟩

/-- **The table's values**: at an in-table output, the digest at its output cell, computed from
the values of lower rank; the pad elsewhere. -/
noncomputable def sVal (w : XW) (h : Z → X) (u : ValPos → Digest) (p : ValPos) : Digest :=
  if InPos p then
    sphFix.dig (sOutRate w h (outSlot p) fun q ↦ if sRank q < sRank p then sVal w h u q else 0)
      (h (sOutCap w h (outSlot p) fun q ↦ if sRank q < sRank p then sVal w h u q else 0))
  else u p
termination_by sRank p
decreasing_by all_goals assumption

theorem sVal_of_not_inPos (w : XW) (h : Z → X) (u : ValPos → Digest) {p : ValPos}
    (hp : ¬InPos p) : sVal w h u p = u p := by
  rw [sVal, ite_eq_right hp]

/-- **An in-table output's value is the digest at its output cell.** -/
theorem sVal_of_inPos (w : XW) (h : Z → X) (u : ValPos → Digest) {p : ValPos} (hp : InPos p) :
    sVal w h u p = sphFix.dig (sOutRate w h (outSlot p) (sVal w h u))
      (h (sOutCap w h (outSlot p) (sVal w h u))) := by
  rw [sVal, ite_eq_left hp]
  have hb : slotBlk w.1 (outSlot p) (fun q ↦ if sRank q < sRank p then sVal w h u q else 0) =
      slotBlk w.1 (outSlot p) (sVal w h u) :=
    slotBlk_congr_inPos w.1 hp fun q _ hq ↦ by simp only [hq, ↓reduceIte]
  obtain ⟨e1, e2⟩ := sOut_congr (h := h) hb
  rw [e1, e2]

/-- **leanSPHINCS's honest outputs.** -/
noncomputable def sO : Outputs X Z Digest ValPos XW where
  I := xI
  val := sVal
  cap w h v p := sOutCap w h (outSlot p) v
  rate w h v p := sOutRate w h (outSlot p) v

/-- **The table's values are its outputs' digests** (`Consistent`). -/
theorem sO_consistent : sO.Consistent sphFix := by
  intro w h u p
  show sVal w h u p = if p ∈ xI then sphFix.dig (sOutRate w h (outSlot p) (sVal w h u))
    (h (sOutCap w h (outSlot p) (sVal w h u))) else u p
  by_cases hp : InPos p
  · rw [ite_eq_left (mem_xI.mpr hp)]
    exact sVal_of_inPos w h u hp
  · rw [ite_eq_right fun hm ↦ hp (mem_xI.mp hm)]
    exact sVal_of_not_inPos w h u hp

/-- **The values are ranked**: an output's cell and rate depend on lower values only. -/
theorem sO_ranked : sO.Ranked sRank := fun w _ _ _ _ hp hlow ↦
  sOut_congr (slotBlk_congr_inPos w.1 (mem_xI.mp hp) fun q _ hq ↦ hlow q hq)

/-- The sponge's digest of a slot's input is the digest at its output cell. -/
theorem trunc128_spongeHash_slot (w : XW) (h : Z → X) (s : Slot) (f : ValPos → Digest) :
    trunc128 (spongeHash (spongePerm (h, w.2.2.1, w.2.2.2) w.2.1) (blocks (slotInput w.1 s f))) =
      sphFix.dig (sOutRate w h s f) (h (sOutCap w h s f)) := by
  have hl := length_blocks_slotInput w.1 s f
  have hp := nBlk_pos w.1 s
  obtain ⟨m, hm⟩ : ∃ m, nBlk w.1 s = m + 1 := ⟨nBlk w.1 s - 1, by omega⟩
  have e := absorb_take_eq_rnSt w.2.1 h w.2.2.1 w.2.2.2 (blocks (slotInput w.1 s f)) _ le_rfl
  rw [List.take_length, hl, hm, rnSt_succ] at e
  have hs : spongeHash (spongePerm (h, w.2.2.1, w.2.2.2) w.2.1) (blocks (slotInput w.1 s f)) =
      rnR w.2.1 h w.2.2.1 w.2.2.2 (slotBlk w.1 s f) m +
        h (rnZ w.2.1 h w.2.2.1 w.2.2.2 (slotBlk w.1 s f) m) :=
    congrArg Prod.fst e
  show trunc128 _ = trunc128 (sOutRate w h s f + h (sOutCap w h s f))
  unfold sOutRate sOutCap sCellR sCellZ
  rw [hs, hm, Nat.add_sub_cancel]

/-! ## Local paths -/

/-- Avoiding paths keep their output cell and rate when `h` changes off the output cells. -/
theorem sOut_congr_of_pathsAvoid {w : XW} {h h₂ : Z → X} {v : ValPos → Digest}
    (hA : PathsAvoid w h v) (hag : AgreeOff sO.I (sO.cap w h v) h h₂) {p : ValPos} (hp : p ∈ xI) :
    sOutCap w h₂ (outSlot p) v = sOutCap w h (outSlot p) v ∧
      sOutRate w h₂ (outSlot p) v = sOutRate w h (outSlot p) v := by
  have hR : RnAgree w.2.1 h w.2.2.1 w.2.2.2 h₂ w.2.2.1 w.2.2.2 (slotBlk w.1 (outSlot p) v)
      (nBlk w.1 (outSlot p) - 1) := fun i hi ↦
    ⟨rfl, rfl, hag _ fun q hq e ↦ hA p hp q hq i (show i + 1 < nBlk w.1 (outSlot p) by omega)
      e.symm⟩
  exact ⟨rnZ_congr hR rfl rfl, rnR_congr hR rfl⟩

/-- **Avoiding paths are local.** -/
theorem local_of_pathsAvoid {w : XW} {h : Z → X} {v : ValPos → Digest} (hA : PathsAvoid w h v) :
    sO.Local w h v := fun _ hag _ hp ↦ sOut_congr_of_pathsAvoid hA hag hp

/-- Avoiding paths stay avoiding when `h` changes off the output cells. -/
theorem pathsAvoid_congr {w : XW} {h h₂ : Z → X} {v : ValPos → Digest} (hA : PathsAvoid w h v)
    (hag : AgreeOff sO.I (sO.cap w h v) h h₂) : PathsAvoid w h₂ v := by
  intro p hp q hq j hj
  have hj' : j + 1 < nBlk w.1 (outSlot p) := hj
  have hR : RnAgree w.2.1 h w.2.2.1 w.2.2.2 h₂ w.2.2.1 w.2.2.2 (slotBlk w.1 (outSlot p) v) j :=
    fun i hi ↦ ⟨rfl, rfl, hag _ fun q' hq' e ↦ hA p hp q' hq' i (by omega) e.symm⟩
  have hz : sCellZ w h₂ (outSlot p) v j = sCellZ w h (outSlot p) v j := rnZ_congr hR rfl rfl
  rw [hz, (sOut_congr_of_pathsAvoid hA hag hq).1]
  exact hA p hp q hq j hj

/-- **leanSPHINCS's good set, in the public coordinates**: distinct output cells, and paths
avoiding them. -/
abbrev XGoodPV : ((Z → X) × XW) × (ValPos → Digest) → Prop :=
  sO.GoodPVWith PathsAvoid

/-- **leanSPHINCS's good set of tables.** -/
abbrev XGood : ((Z → X) × (ValPos → Digest)) × XW → Prop :=
  sO.GoodWith PathsAvoid

theorem sPL : ∀ w h v, PathsAvoid w h v → sO.Local w h v :=
  fun _ _ _ hA ↦ local_of_pathsAvoid hA

theorem sPC : ∀ w h h₂ v, PathsAvoid w h v → AgreeOff sO.I (sO.cap w h v) h h₂ →
    PathsAvoid w h₂ v :=
  fun _ _ _ _ hA hag ↦ pathsAvoid_congr hA hag

theorem good_of_xGood {θ : ((Z → X) × (ValPos → Digest)) × XW} (hθ : XGood θ) : sO.Good θ :=
  good_of_with sPL hθ

theorem xGoodPV_fwd {θ : ((Z → X) × (ValPos → Digest)) × XW} (hθ : XGood θ) :
    XGoodPV (fwd sphFix sO θ) :=
  goodPVWith_fwd sPL sPC hθ

theorem xGood_back {y : ((Z → X) × XW) × (ValPos → Digest)} (hy : XGoodPV y) :
    XGood (back sphFix sO y) :=
  goodWith_back sPL sPC sO_consistent sO_ranked hy

/-- **The inverse on the good set**: `back (fwd θ) = θ`. -/
theorem back_fwd {θ : ((Z → X) × (ValPos → Digest)) × XW} (hθ : XGood θ) :
    back sphFix sO (fwd sphFix sO θ) = θ :=
  Quantum.Xmss.Assembly.back_fwd sO_consistent (good_of_xGood hθ)

/-- **The inverse on the good set of the public coordinates**: `fwd (back y) = y`. -/
theorem fwd_back {y : ((Z → X) × XW) × (ValPos → Digest)} (hy : XGoodPV y) :
    fwd sphFix sO (back sphFix sO y) = y :=
  Quantum.Xmss.Assembly.fwd_back sO_consistent sO_ranked (goodPV_of_with sPL hy)

/-- The hidden coordinate of `fwd` is the table's values. -/
theorem fwd_snd (h : Z → X) (u : ValPos → Digest) (w : XW) :
    (fwd sphFix sO ((h, u), w)).2 = sVal w h u :=
  rfl

/-- The public data of `fwd` keeps `w`. -/
theorem fwd_fst_snd (h : Z → X) (u : ValPos → Digest) (w : XW) :
    (fwd sphFix sO ((h, u), w)).1.2 = w :=
  rfl

/-! ## The template's cells -/

/-- **The template's public data** at `w = (PK.seed, π, k, k')` and `h`. -/
def sPub (w : XW) (h : Z → X) : Pub :=
  ⟨w.1, w.2.1, (h, w.2.2.1, w.2.2.2)⟩

theorem sPub_xw (w : XW) (h : Z → X) : (sPub w h).xw = w :=
  rfl

theorem sPub_keys_fst (w : XW) (h : Z → X) : (sPub w h).keys.1 = h :=
  rfl

theorem sPub_xw_keys (pub : Pub) : sPub pub.xw pub.keys.1 = pub :=
  rfl

/-- **The public data of an honest table is `sPub` at its data.** -/
theorem pubOf_eq (L : HonestTable) : pubOf L = sPub (tabW L) L.keys.1 :=
  rfl

section cells

variable (pub : Pub) (s : Slot) (f : ValPos → Digest)

/-- The template's `k`-cells are PathBad's `sCellK`. -/
theorem cellK_fst (j : ℕ) :
    (cellK pub (slotBlk pub.seed s f) j).1 = sCellK pub.xw pub.keys.1 s f j :=
  rfl

/-- The template's `k'`-cells are PathBad's `sCellR`. -/
theorem cellK'_fst (j : ℕ) :
    (cellK' pub (slotBlk pub.seed s f) j).1 = sCellR pub.xw pub.keys.1 s f j :=
  rfl

/-- **The template's `h`-cells are PathBad's `sCellZ`.** -/
theorem cellH_fst_eq (last : ℕ) (cor : X → X → X) (j : ℕ) :
    (cellH pub (slotBlk pub.seed s f) last cor j).1 = sCellZ pub.xw pub.keys.1 s f j :=
  cellH_fst pub _ last cor j

/-- **The template's output cell is PathBad's `sOutCap`.** -/
theorem cellH_last_fst (cor : X → X → X) :
    (cellH pub (slotBlk pub.seed s f) (nBlk pub.seed s - 1) cor (nBlk pub.seed s - 1)).1 =
      sOutCap pub.xw pub.keys.1 s f :=
  cellH_fst pub _ _ cor _

/-- The template's final `h` value is the corrected public value at the output cell. -/
theorem cellH_last_snd (cor : X → X → X) :
    (cellH pub (slotBlk pub.seed s f) (nBlk pub.seed s - 1) cor (nBlk pub.seed s - 1)).2 =
      cor (sOutRate pub.xw pub.keys.1 s f) (pub.keys.1 (sOutCap pub.xw pub.keys.1 s f)) := by
  rw [cellH_snd, ite_eq_left rfl]
  rfl

/-- **The realized ports of a structural slot** are PathBad's cells of its path at the values:
`sCellK`, `sCellR`, `sCellZ` with their key values, the last `h` value (at `sOutCap`) corrected
to the value at the output position. -/
theorem realize_slotPorts_cells {s : Slot} (hs : InTable s) (v : (s : HPos) → XD s) :
    (slotPorts pub s).map (LazyProg.realize v) =
      (List.range (nBlk pub.seed s)).flatMap fun j ↦
        [.programK (sCellK pub.xw pub.keys.1 s (valsOf v) j)
            (pub.keys.2.1 (sCellK pub.xw pub.keys.1 s (valsOf v) j)),
          .programK' (sCellR pub.xw pub.keys.1 s (valsOf v) j)
            (pub.keys.2.2 (sCellR pub.xw pub.keys.1 s (valsOf v) j)),
          .programH (sCellZ pub.xw pub.keys.1 s (valsOf v) j)
            (if j = nBlk pub.seed s - 1 then
              cor128 (valsOf v (slotOutPos s)) (sCellR pub.xw pub.keys.1 s (valsOf v) j)
                (pub.keys.1 (sCellZ pub.xw pub.keys.1 s (valsOf v) j))
            else pub.keys.1 (sCellZ pub.xw pub.keys.1 s (valsOf v) j))] := by
  rw [realize_slotPorts pub hs v, pathCells]
  congr 1
  funext j
  rw [cellH_fst, cellH_snd]
  rfl

end cells

/-- **At the table's own public data the correction vanishes**: every `h`-cell of an in-table
output's path is programmed with the table's value of `h`. -/
theorem cellH_table (w : XW) (h : Z → X) (u : ValPos → Digest) {p : ValPos} (hp : InPos p)
    (j : ℕ) :
    cellH (sPub w h) (slotBlk w.1 (outSlot p) (sVal w h u)) (nBlk w.1 (outSlot p) - 1)
        (cor128 (sVal w h u p)) j =
      (sCellZ w h (outSlot p) (sVal w h u) j, h (sCellZ w h (outSlot p) (sVal w h u) j)) := by
  refine Prod.ext (cellH_fst _ _ _ _ j) ?_
  rw [cellH_snd]
  split_ifs with hl
  · subst hl
    rw [sVal_of_inPos w h u hp]
    exact sphFix_cor_dig (sOutRate w h (outSlot p) (sVal w h u))
      (h (sOutCap w h (outSlot p) (sVal w h u)))
  · rfl

/-- `rounds_fwd` at an in-table output's slot. -/
theorem rounds_fwd_pos {h : Z → X} {u : ValPos → Digest} {w : XW} (hθ : XGood ((h, u), w))
    {p : ValPos} (hp : p ∈ xI) {j : ℕ} (hj : j < nBlk w.1 (outSlot p)) :
    cellK (sPub w (fwd sphFix sO ((h, u), w)).1.1) (slotBlk w.1 (outSlot p) (sVal w h u)) j =
        (sCellK w h (outSlot p) (sVal w h u) j,
          w.2.2.1 (sCellK w h (outSlot p) (sVal w h u) j)) ∧
      cellK' (sPub w (fwd sphFix sO ((h, u), w)).1.1) (slotBlk w.1 (outSlot p) (sVal w h u)) j =
        (sCellR w h (outSlot p) (sVal w h u) j,
          w.2.2.2 (sCellR w h (outSlot p) (sVal w h u) j)) ∧
      cellH (sPub w (fwd sphFix sO ((h, u), w)).1.1) (slotBlk w.1 (outSlot p) (sVal w h u))
          (nBlk w.1 (outSlot p) - 1) (cor128 (sVal w h u p)) j =
        (sCellZ w h (outSlot p) (sVal w h u) j, h (sCellZ w h (outSlot p) (sVal w h u) j)) := by
  have hag : ∀ i, i + 1 < nBlk w.1 (outSlot p) →
      (fwd sphFix sO ((h, u), w)).1.1 (sCellZ w h (outSlot p) (sVal w h u) i) =
        h (sCellZ w h (outSlot p) (sVal w h u) i) := fun i hi ↦
    agreeOff_fwd sphFix sO ((h, u), w) _ fun q hq e ↦ hθ.2 p hp q hq i hi e.symm
  have hR : ∀ m, m < nBlk w.1 (outSlot p) → RnAgree w.2.1 h w.2.2.1 w.2.2.2
      (fwd sphFix sO ((h, u), w)).1.1 w.2.2.1 w.2.2.2 (slotBlk w.1 (outSlot p) (sVal w h u)) m :=
    fun m hm i hi ↦ ⟨rfl, rfl, hag i (by omega)⟩
  refine ⟨Prod.ext (rnK_congr (hR j hj)) (congrArg w.2.2.1 (rnK_congr (hR j hj))),
    Prod.ext (rnR_congr (hR j hj) rfl) (congrArg w.2.2.2 (rnR_congr (hR j hj) rfl)),
    Prod.ext ((cellH_fst _ _ _ _ j).trans (rnZ_congr (hR j hj) rfl rfl)) ?_⟩
  rw [cellH_snd]
  split_ifs with hl
  · subst hl
    exact cor_fwd sO_consistent (good_of_xGood hθ) hp
  · exact (congrArg (fwd sphFix sO ((h, u), w)).1.1 (rnZ_congr (hR j hj) rfl rfl)).trans
      (hag j (by omega))

/-- **The template at the public data of `fwd` programs the table's cells.** On the good set, for
every structural slot and every round of its honest path at the values `sVal w h u` (the hidden
coordinate of `fwd`, `fwd_snd`), the template's `k`-, `k'`- and `h`-cells at the public data
`sPub w h''` (`h''` the public `h` of `fwd`) are the table's honest cells with the table's key
values: the corrected final value gives back `h` (`cor_fwd`). -/
theorem rounds_fwd {h : Z → X} {u : ValPos → Digest} {w : XW} (hθ : XGood ((h, u), w))
    {s : Slot} (hs : InTable s) {j : ℕ} (hj : j < nBlk w.1 s) :
    cellK (sPub w (fwd sphFix sO ((h, u), w)).1.1) (slotBlk w.1 s (sVal w h u)) j =
        (sCellK w h s (sVal w h u) j, w.2.2.1 (sCellK w h s (sVal w h u) j)) ∧
      cellK' (sPub w (fwd sphFix sO ((h, u), w)).1.1) (slotBlk w.1 s (sVal w h u)) j =
        (sCellR w h s (sVal w h u) j, w.2.2.2 (sCellR w h s (sVal w h u) j)) ∧
      cellH (sPub w (fwd sphFix sO ((h, u), w)).1.1) (slotBlk w.1 s (sVal w h u))
          (nBlk w.1 s - 1) (cor128 (sVal w h u (slotOutPos s))) j =
        (sCellZ w h s (sVal w h u) j, h (sCellZ w h s (sVal w h u) j)) := by
  have hr := fun hj' ↦ rounds_fwd_pos hθ (mem_xI.mpr (inPos_slotOutPos hs)) (j := j) hj'
  rw [outSlot_slotOutPos hs] at hr
  exact hr hj

/-- **The template data of the good set avoid the output cells**: at the public data of `fwd` and
the values `sVal w h u`, PathBad's `PathsAvoid` (the hypothesis of `finalSep_of_pathsAvoid`). -/
theorem pathsAvoid_fwd {h : Z → X} {u : ValPos → Digest} {w : XW} (hθ : XGood ((h, u), w)) :
    PathsAvoid (sPub w (fwd sphFix sO ((h, u), w)).1.1).xw
      (sPub w (fwd sphFix sO ((h, u), w)).1.1).keys.1 (sVal w h u) :=
  (xGoodPV_fwd hθ).2

/-- The template data `(pub, v)` of a good public coordinate avoid the output cells. -/
theorem pathsAvoid_of_xGoodPV {pub : Pub} {v : (s : HPos) → XD s}
    (hy : XGoodPV ((pub.keys.1, pub.xw), valsOf v)) :
    PathsAvoid pub.xw pub.keys.1 (valsOf v) :=
  hy.2

/-! ## The honest table's values -/

/-- **The values of an honest table**: with its chain starts and FORS secrets in the pad, the
table's values are `valuePos L` at every live position. -/
theorem sVal_tabW (L : HonestTable) (u : ValPos → Digest)
    (hu : ∀ q, SecretPos q → u q = valuePos L q) :
    ∀ q, Live q → sVal (tabW L) L.keys.1 u q = valuePos L q := by
  intro q
  induction hn : sRank q using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    intro hq
    by_cases hp : InPos q
    · rw [sVal_of_inPos _ _ _ hp]
      have hb : slotBlk L.publicSeed (outSlot q) (sVal (tabW L) L.keys.1 u) =
          slotBlk L.publicSeed (outSlot q) (valuePos L) :=
        slotBlk_congr_inPos _ hp fun r hr hrq ↦ ih (sRank r) (hn ▸ hrq) r rfl hr
      obtain ⟨e1, e2⟩ := sOut_congr (w := tabW L) (h := L.keys.1) hb
      rw [e1, e2, ← trunc128_spongeHash_slot (tabW L) L.keys.1 (outSlot q) (valuePos L)]
      have ht := L.target_eq_some hp.1
      rw [HonestTable.target, L.honestInput_eq_slotInput hp.1, Option.map_some, hp.2] at ht
      exact Option.some.inj ht
    · rw [sVal_of_not_inPos _ _ _ hp]
      exact hu q (hq.resolve_left hp)

/-- At an honest table, the blocks of a structural slot at the table's values are those at
`valuePos L`. -/
theorem slotBlk_sVal_tabW (L : HonestTable) (u : ValPos → Digest)
    (hu : ∀ q, SecretPos q → u q = valuePos L q) {s : Slot} (hs : InTable s) :
    slotBlk L.publicSeed s (sVal (tabW L) L.keys.1 u) = slotBlk L.publicSeed s (valuePos L) :=
  slotBlk_congr_live _ hs fun q hq _ ↦ sVal_tabW L u hu q hq

/-! ## The bad fraction -/

/-- Distinct output cells are PathBad's `OutSep`. -/
theorem injOn_iff_outSep (w : XW) (h : Z → X) (v : ValPos → Digest) :
    Set.InjOn (sO.cap w h v) xI ↔ OutSep w h v :=
  ⟨fun hi _ hp _ hq hne e ↦ hne (hi (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) e),
    fun hs _ ha _ hb e ↦ by_contra fun hne ↦
      hs _ (Finset.mem_coe.mp ha) _ (Finset.mem_coe.mp hb) hne e⟩

/-- **Outside the good set of the public coordinates is PathBad's event.** -/
theorem not_xGoodPV_iff (y : ((Z → X) × XW) × (ValPos → Digest)) : ¬XGoodPV y ↔ PathBad y := by
  show ¬(Set.InjOn (sO.cap y.1.2 y.1.1 y.2) xI ∧ PathsAvoid y.1.2 y.1.1 y.2) ↔
    ¬OutSep y.1.2 y.1.1 y.2 ∨ ¬PathsAvoid y.1.2 y.1.1 y.2
  rw [injOn_iff_outSep, not_and_or]

open scoped Classical in
/-- **The bad fraction of the public coordinates**: at most `2^-400`. -/
theorem xGoodPV_bad_frac_le :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y ↦ ¬XGoodPV y).card ≤ ENNReal.ofReal (1 / 2 ^ 400) := by
  rw [Finset.filter_congr fun y _ ↦ not_xGoodPV_iff y]
  exact pathBad_frac_le_keccak

open scoped Classical in
/-- **The bad fraction of leanSPHINCS's reparametrization**: at most `2^-400` of the tables are
outside `XGood`. -/
theorem xGood_bad_frac_le :
    (Fintype.card (((Z → X) × (ValPos → Digest)) × XW) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun θ ↦ ¬XGood θ).card ≤ ENNReal.ofReal (1 / 2 ^ 400) := by
  rw [card_not_eq_of_maps sO_consistent sO_ranked XGood XGoodPV (fun _ h ↦ good_of_xGood h)
    (fun _ h ↦ goodPV_of_with sPL h) (fun _ h ↦ xGoodPV_fwd h) (fun _ h ↦ xGood_back h),
    card_tab_eq]
  exact xGoodPV_bad_frac_le

open scoped Classical in
/-- **The debt `PathsAvoid` on the public coordinates**: the coordinates whose in-table paths
meet an output cell weigh at most `2^-400`. -/
theorem uavg_not_pathsAvoid_le :
    uavg (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
        if PathsAvoid y.1.2 y.1.1 y.2 then (0 : ℝ≥0∞) else 1) ≤ ENNReal.ofReal (1 / 2 ^ 400) := by
  calc uavg (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
        if PathsAvoid y.1.2 y.1.1 y.2 then (0 : ℝ≥0∞) else 1)
      ≤ uavg (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          if XGoodPV y then (0 : ℝ≥0∞) else 1) := uavg_mono fun y ↦ by
        by_cases hy : XGoodPV y
        · rw [ite_eq_left hy.2, ite_eq_left hy]
        · rw [ite_eq_right hy]
          split_ifs
          exacts [zero_le_one, le_rfl]
    _ = _ := uavg_ite_zero_one _
    _ ≤ _ := xGoodPV_bad_frac_le

open scoped Classical in
/-- **The averaging corollary for leanSPHINCS**: if `f ≤ g ∘ fwd` on `XGood` and `f ≤ 1`
elsewhere, the average of `f` over the tables is at most the average over the public data of the
average over the hidden values of `g`, plus `2^-400`. -/
theorem uavg_le_sph (f : ((Z → X) × (ValPos → Digest)) × XW → ℝ≥0∞)
    (g : ((Z → X) × XW) × (ValPos → Digest) → ℝ≥0∞)
    (hfg : ∀ θ, XGood θ → f θ ≤ g (fwd sphFix sO θ)) (hf : ∀ θ, ¬XGood θ → f θ ≤ 1) :
    uavg f ≤ uavg (fun p : (Z → X) × XW ↦ uavg fun v : ValPos → Digest ↦ g (p, v)) +
      ENNReal.ofReal (1 / 2 ^ 400) :=
  (uavg_le_of_good sO_consistent XGood (fun _ h ↦ good_of_xGood h) f g hfg hf).trans
    (add_le_add le_rfl xGood_bad_frac_le)

end Quantum.Sphincs.Assembly

end
