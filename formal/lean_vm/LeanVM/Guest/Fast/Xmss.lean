module

public import LeanVM.Guest.Fast.XmssTables
public import LeanVM.Guest.Fast.LogG
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.B1.Sig.XmssSegT
public import LeanVM.Guest.B1.Sig.XmssScheme
public import LeanVM.Guest.Fast.XmssTablesCheck
public import LeanVM.Guest.B1.Sig.XmssSegSound

/-!
# leanXMSS's signature reader, computable

The leanXMSS check is inline in `main`'s raw-signature loop `__loop2` (main 40f877dc,
`B1/Sig/XmssSegT.lean`: `xSeg`, statements `9` to `321` of its body), so a signature is read off
an iteration's frame `σ`, at the cells the template gives:

* the leaf index from the four windows' dispatches: window `w`'s word `σ (.n (71 + w)) = g^k`,
  `k < 256` its `8` bits (`lxIndex`);
* per layer (bottom at base `88`, top at base `62605`): the randomizer `ρ`; chain `4p + r`'s
  start in the arm `k` group `p`'s dispatch takes (its digit word `σ (.n (dg + p)) = g^k`), at the
  group's base (`lxGroupBase`) plus its offset off the literal tables (`lxFold`, `lxRest`,
  `lxTail`, `Fast/XmssTables.lean`); level `l`'s sibling in the arm window `2·layer + l / 8` takes
  (`lxArmBase`, `lxSibAt`: arm `0` holds the window's output, the other arms one size).

`xmssSigOfA T σ` reads it off the tables `T` as arrays (`XmssTabs`: the lanes of `g^k` and the
chain-start tables), built once by the caller (`xmssTabs`); each dispatch's exponent is read once
off the lanes (`logGTWith`).

**`xmssSigOfN_eq`**: the reader is `xmssSigOf` (`B1/Sig/XmssSegSound.lean`), the signature the
check's soundness reads: the arms' bases are numbers relative to their group's (`armBaseM_eq`,
`lxArmOff_add`), the groups' bases `lxGroupBase` (`sSt_vb`), the chain starts the tables'
(`sStart_eq`, the tables checked in `Fast/XmssTablesCheck.lean`), the path's arms one size apart
after arm `0` (`lxArmB_zero`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-- leanXMSS's tables, as arrays: the lanes of `g^k` (`gLanes`), the chain starts of group `0`,
of groups `1` to `13` and of group `14` (`lxFold`, `lxRest`, `lxTail`). -/
structure XmssTabs where
  lanes : List ℕ
  fold : Array (Array ℕ)
  rest : Array (Array ℕ)
  tail : Array (Array ℕ)

/-- **leanXMSS's tables**, built from the literals. -/
def xmssTabs : XmssTabs := ⟨gLanes, tabA lxFold, tabA lxRest, tabA lxTail⟩

/-- Layer `layer`'s first value (`sLayer`'s base): `88`, then `62605`. -/
def lxLayerBase (layer : ℕ) : ℕ := if layer = 0 then 88 else 62605

/-- Layer `layer`'s randomizer cell (`sRho`). -/
def lxRhoCell (layer : ℕ) : ℕ := if layer = 0 then 88 else 62607

/-- Layer `layer`'s first digit word (`sCw`'s `dg`). -/
def lxDigitBase (layer : ℕ) : ℕ := if layer = 0 then 110 else 62618

/-- Group `p`'s base, the groups' first at `vb0`: group `0` takes `2829` values, the others
`2573`. -/
def lxGroupBase (vb0 p : ℕ) : ℕ := if p = 0 then vb0 else vb0 + 2829 + 2573 * (p - 1)

/-- Group `p`'s table of chain starts. -/
def lxGroupTab (T : XmssTabs) (p : ℕ) : Array (Array ℕ) :=
  if p = 0 then T.fold else if p < 14 then T.rest else T.tail

/-- The arms the `15` dispatches of a layer take, its digit words from `dg`. -/
def lxArmsTaken (lanes : List ℕ) (σ : Val) (dg : ℕ) : List ℕ :=
  (List.range 15).map fun p ↦ logGTWith lanes (σ (.n (dg + p))) 256

/-- Chain `i`'s start cell, the arms taken `ks`, the groups from `vb0`. -/
def lxChainCell (T : XmssTabs) (ks : List ℕ) (vb0 i : ℕ) : ℕ :=
  lxGroupBase vb0 (i / 4) + offAtA (lxGroupTab T (i / 4)) (i % 4) (ks.getD (i / 4) 0)

/-- Window `w`'s base (`lxWindowT`'s). -/
def lxWinBase (w : ℕ) : ℕ :=
  if w = 0 then 38021 else if w = 1 then 50313 else if w = 2 then 100529 else 112821

/-- Arm `k`'s base in window `w`: arm `0` from the window's base plus `5`, its size `47` (`32` in
the top window), the others `48` (`31`). -/
def lxArmBase (w k : ℕ) : ℕ :=
  lxWinBase w + 5 +
    (if k = 0 then 0 else (if w = 3 then 32 else 47) + (if w = 3 then 31 else 48) * (k - 1))

/-- Level `r`'s hinted sibling in arm `k` of window `w`: levels `6` values apart (`4` in the
top window), the sibling the level's fourth value (its first in the top window, the last level's
third elsewhere). -/
def lxSibAt (w k r : ℕ) : ℕ :=
  if w = 3 then lxArmBase w k + 4 * r
  else if r = 7 then lxArmBase w k + 6 * r + 2 else lxArmBase w k + 6 * r + 3

/-- **A layer's signature, off the tables `T`**: the windows' arms `kw` given. -/
def xPartA (T : XmssTabs) (kw : List ℕ) (layer : ℕ) (σ : Val) : LeanXmss.LayerSignature :=
  let ks := lxArmsTaken T.lanes σ (lxDigitBase layer)
  ⟨xv (σ (.n (lxRhoCell layer))),
    fun i ↦ xv (σ (.n (lxChainCell T ks (lxDigitBase layer + 70) i.val))),
    fun l ↦ xv (σ (.n (lxSibAt (2 * layer + l.val / 8) (kw.getD (2 * layer + l.val / 8) 0)
      (l.val % 8))))⟩

/-- The leaf index from the windows' arms `kw` (`lxIndex`), below `2^32`. -/
def lxLeafOf (kw : List ℕ) : ℕ :=
  (kw.getD 0 0 + 256 * kw.getD 1 0 + 65536 * kw.getD 2 0 + 16777216 * kw.getD 3 0) % 2 ^ 32

theorem lxLeafOf_eq (kw : List ℕ) : lxLeafOf kw = lxIndex (fun w ↦ kw.getD w 0) % 2 ^ 32 := rfl

theorem lxLeafOf_lt (kw : List ℕ) :
    lxLeafOf kw < LeanXmss.lifetime :=
  Nat.mod_lt _ (by norm_num)

/-- **The leanXMSS signature `__loop2`'s iteration checks, off the tables `T`**, from its frame. -/
def xmssSigOfA (T : XmssTabs) (σ : Val) : LeanXmss.Signature :=
  let kw := (List.range 4).map fun w ↦ logGTWith T.lanes (σ (.n (71 + w))) 256
  ⟨⟨lxLeafOf kw, lxLeafOf_lt kw⟩, fun lay ↦ xPartA T kw lay.val σ⟩

/-- **The leanXMSS signature `__loop2`'s iteration checks**, off the tables built. -/
def xmssSigOfN (σ : Val) : LeanXmss.Signature := xmssSigOfA xmssTabs σ

theorem xmssSigOfA_tabs (σ : Val) : xmssSigOfA xmssTabs σ = xmssSigOfN σ := rfl

/-! ## The reader is `xmssSigOf` -/

theorem walksT_snd (W : WotsT) (slots : ℕ → ℕ → ℕ) (first k stride : ℕ) :
    ∀ m r b, (walksT W slots first k stride m r b).2 = walkBase stride k r m b
  | 0, _, _ => rfl
  | m + 1, r, b => by
      simp only [walksT, walkBase]
      exact walksT_snd W slots first k stride m (r + 1) _

theorem walkBase_add (stride k : ℕ) :
    ∀ r j b c, walkBase stride k r j (b + c) = walkBase stride k r j b + c
  | _, 0, _, _ => rfl
  | r, j + 1, b, c => by
      simp only [walkBase]
      rw [show b + c + walkSize stride (k / 4 ^ r % 4) = b + walkSize stride (k / 4 ^ r % 4) + c by
        omega]
      exact walkBase_add stride k (r + 1) j _ c

theorem lxArmNext_add (s n : ℕ) (fold : Bool) (k b c : ℕ) :
    lxArmNext s n fold k (b + c) = lxArmNext s n fold k b + c := by
  have e : (if fold = true then b + c + 1 else b + c) = (if fold = true then b + 1 else b) + c := by
    split <;> omega
  simp only [lxArmNext, e, walkBase_add]
  split_ifs <;> omega

theorem lxArmOff_add (s n : ℕ) (fold : Bool) :
    ∀ k j b c, lxArmOff s n fold k j (b + c) = lxArmOff s n fold k j b + c
  | _, 0, _, _ => rfl
  | k, j + 1, b, c => by
      simp only [lxArmOff, lxArmNext_add]
      exact lxArmOff_add s n fold (k + 1) j _ c

theorem armM_next (W : WotsT) (slots : ℕ → ℕ → ℕ) (first n : ℕ) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : ℕ) :
    (if k = 0 then (armM W slots first n fold prodIn encIn prodOut encOut k b).2 + 2
      else (armM W slots first n fold prodIn encIn prodOut encOut k b).2) =
      lxArmNext W.size n fold k b := by
  unfold armM lxArmNext
  dsimp only
  split_ifs <;> simp [walksT_snd]

theorem armBaseM_eq (W : WotsT) (slots : ℕ → ℕ → ℕ) (first n : ℕ) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ k j b, armBaseM W slots first n fold prodIn encIn prodOut encOut k j b =
      lxArmOff W.size n fold k j b
  | _, 0, _ => rfl
  | k, j + 1, b => by
      rw [armBaseM, lxArmOff, armM_next]
      exact armBaseM_eq W slots first n fold prodIn encIn prodOut encOut (k + 1) j _

theorem armsM_snd (W : WotsT) (slots : ℕ → ℕ → ℕ) (first n : ℕ) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ m k b, (armsM W slots first n fold prodIn encIn prodOut encOut m k b).2 =
      armBaseM W slots first n fold prodIn encIn prodOut encOut k m b
  | 0, _, _ => rfl
  | m + 1, k, b => by
      simp only [armsM, armBaseM]
      exact armsM_snd W slots first n fold prodIn encIn prodOut encOut m (k + 1) _

/-- **The groups' bases**: group `0` takes `2829` values, the others `2573`. -/
theorem sSt_vb {W : WotsT} (hW : W.size = 1) (vb0 : ℕ) :
    ∀ p ≤ 14, (sSt W vb0 p).2.2 = lxGroupBase vb0 p
  | 0, _ => by simp [sSt, lxGroupBase]
  | p + 1, hp => by
      have ih := sSt_vb hW vb0 p (by omega)
      simp only [sSt, sGroupArms, armsM_snd, armBaseM_eq, hW, ih]
      rw [show lxGroupBase vb0 p + 6 = 6 + lxGroupBase vb0 p by omega, lxArmOff_add]
      rcases p with _ | p
      · rw [show lxN 0 = 4 from rfl, show ((0 : ℕ) == 0) = true from rfl, lxGroup0_size]
        simp [lxGroupBase]
        omega
      · have hn : lxN (p + 1) = 4 := by simp only [lxN]; split <;> omega
        have hb : (p + 1 == 0) = false := rfl
        rw [hn, hb, lxGroup_size]
        simp [lxGroupBase]
        omega

/-- Group `p`'s table of chain starts. -/
def lxTabOf (p : ℕ) : List (List ℕ) := if p = 0 then lxFold else if p < 14 then lxRest else lxTail

theorem lxTabOf_eq {p : ℕ} (hp : p ≤ 14) : lxTabOf p = lxRows (lxN p) (p == 0) := by
  rcases p with _ | p
  · exact lxFold_eq
  · have hb : (p + 1 == 0) = false := rfl
    by_cases h : p + 1 < 14
    · simp only [lxTabOf, lxN, h, hb, Nat.add_one_ne_zero, ↓reduceIte]
      exact lxRest_eq
    · simp only [lxTabOf, lxN, h, hb, Nat.add_one_ne_zero, ↓reduceIte]
      exact lxTail_eq

theorem lxRowAux_getD (s n : ℕ) (fold : Bool) (r : ℕ) :
    ∀ m k a j, j < m →
      (lxRowAux s n fold r m k a).getD j 0 = lxStartRel s fold (k + j) (lxArmOff s n fold k j a) r
  | 0, _, _, _, h => absurd h (by omega)
  | m + 1, k, a, 0, _ => by simp [lxRowAux, lxArmOff]
  | m + 1, k, a, j + 1, h => by
      simp only [lxRowAux, List.getD_cons_succ, lxArmOff]
      rw [lxRowAux_getD s n fold r m (k + 1) _ j (by omega), show k + 1 + j = k + (j + 1) by omega]

theorem offAt_lxRows {n : ℕ} {fold : Bool} {r k : ℕ} (hr : r < n) (hk : k < 256) :
    offAt (lxRows n fold) r k = lxStartRel 1 fold k (lxArmOff 1 n fold 0 k 6) r := by
  unfold offAt lxRows
  have h1 : ((List.range n).map fun r ↦ lxRowAux 1 n fold r 256 0 6).getD r [] =
      lxRowAux 1 n fold r 256 0 6 := by
    simp [List.getD_eq_getElem?_getD, hr]
  rw [h1, lxRowAux_getD 1 n fold r 256 0 6 k hk, Nat.zero_add]

theorem armStart_cell {W : WotsT} (hW : W.size = 1) (vb0 p r k : ℕ) (hp : p ≤ 14) :
    armStart W (slotsT W (p == 0) (sSt W vb0 p).2.2) (p == 0) k
      (armBaseM W (slotsT W (p == 0) (sSt W vb0 p).2.2) (4 * p) (lxN p) (p == 0) (sSt W vb0 p).1
        (sSt W vb0 p).2.1 (prodT W (p == 0) (lxN p) (sSt W vb0 p).2.2)
        (encT W (p == 0) (lxN p) (sSt W vb0 p).2.2) 0 k ((sSt W vb0 p).2.2 + 6)) r =
      .n (lxGroupBase vb0 p + lxStartRel 1 (p == 0) k (lxArmOff 1 (lxN p) (p == 0) 0 k 6) r) := by
  rw [armBaseM_eq, sSt_vb hW vb0 p hp, hW,
    show lxGroupBase vb0 p + 6 = 6 + lxGroupBase vb0 p by omega, lxArmOff_add]
  unfold armStart walkStartV lxStartRel slotsT groupStart chainStride
  rw [hW]
  generalize lxArmOff 1 (lxN p) (p == 0) 0 k 6 = A
  generalize lxGroupBase vb0 p = G
  generalize (p == 0) = fold
  split_ifs <;> congr 1 <;> (try rw [show A + G + 1 = (A + 1) + G by omega]) <;>
    (try rw [walkBase_add]) <;> omega

/-- **Chain `i`'s start cell** is its group's base plus the table's offset. -/
theorem sStart_eq {W : WotsT} (hW : W.size = 1) (σ : Val) (dg vb0 i : ℕ) (hi : i < 58) :
    sStart W σ dg vb0 i =
      .n (lxGroupBase vb0 (i / 4) + offAt (lxTabOf (i / 4)) (i % 4) (sK σ dg (i / 4))) := by
  have hp : i / 4 ≤ 14 := by omega
  have hr : i % 4 < lxN (i / 4) := by unfold lxN; split <;> omega
  have hk : sK σ dg (i / 4) < 256 := logG_lt _ (by norm_num)
  rw [lxTabOf_eq hp, offAt_lxRows hr hk]
  exact armStart_cell hW vb0 (i / 4) (i % 4) _ hp

theorem lxArmSize_pos (w k : ℕ) (hk : k ≠ 0) : lxArmSize w k = lxArmSize w 1 := by
  simp [lxArmSize, hk]

theorem lxArmB_succ (w : ℕ) : ∀ j k b, k ≠ 0 → lxArmB w k j b = b + lxArmSize w 1 * j
  | 0, _, b, _ => by simp [lxArmB]
  | j + 1, k, b, hk => by
      rw [lxArmB, lxArmB_succ w j (k + 1) _ (by omega), lxArmSize_pos w k hk]
      ring

/-- **Arm `k`'s base in window `w`** (`lxArmB`'s, from the window's base). -/
theorem lxArmB_zero {w : ℕ} (hw : w < 4) (k : ℕ) :
    lxArmB w 0 k (lxWinBase w + 5) = lxArmBase w k := by
  rcases k with _ | j
  · simp [lxArmB, lxArmBase]
  · rw [lxArmB, lxArmB_succ w j 1 _ one_ne_zero]
    unfold lxArmBase lxArmSize lxStride lxLastNext
    interval_cases w <;> simp <;> ring

theorem lxSibF_eq (σ : Val) {w : ℕ} (hw : w < 4) (k r : ℕ) {b : ℕ} (hb : b = lxWinBase w) :
    lxSibF σ w (lxArmB w 0 k (b + 5)) r = σ (.n (lxSibAt w k r)) := by
  subst hb
  rw [lxArmB_zero hw]
  unfold lxSibF lxSibCell lxStride lxSibAt
  congr 2
  split_ifs <;> omega

/-- Level `l`'s sibling cell. -/
theorem sSibAt_eq (σ : Val) {layer b l : ℕ} (hL : layer < 2) (hl : l < 16)
    (h0 : (sLeafK layer b).2.1 = lxWinBase (2 * layer))
    (h1 : (sWin0 layer b).2.1 = lxWinBase (2 * layer + 1)) :
    sSibAt σ layer b l = σ (.n (lxSibAt (2 * layer + l / 8) (sKw σ (2 * layer + l / 8)) (l % 8))) := by
  unfold sSibAt
  split_ifs with h
  · rw [show l / 8 = 0 by omega, show l % 8 = l by omega, Nat.add_zero]
    exact lxSibF_eq σ (by omega) _ _ h0
  · rw [show l / 8 = 1 by omega, show l % 8 = l - 8 by omega]
    exact lxSibF_eq σ (by omega) _ _ h1

theorem kw_getD (σ : Val) {w : ℕ} (hw : w < 4) :
    ((List.range 4).map fun w ↦ logGTWith gLanes (σ (.n (71 + w))) 256).getD w 0 = sKw σ w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
  simp only [Option.map_some, Option.getD_some]
  rw [logGTWith_gLanes, ← logG_eq_logGT _ (le_refl _)]
  rfl

theorem lxArmsTaken_getD (σ : Val) (dg : ℕ) {p : ℕ} (hp : p < 15) :
    (lxArmsTaken gLanes σ dg).getD p 0 = sK σ dg p := by
  unfold lxArmsTaken
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp]
  simp only [Option.map_some, Option.getD_some]
  rw [logGTWith_gLanes, ← logG_eq_logGT _ (le_refl _)]
  rfl

theorem lxGroupTab_eq (p : ℕ) : lxGroupTab xmssTabs p = tabA (lxTabOf p) := by
  unfold lxGroupTab lxTabOf xmssTabs
  split_ifs <;> rfl

/-- **A layer's signature**, off the tables, is `sPart`'s. -/
theorem xPartA_eq (σ : Val) {layer b : ℕ} (hL : layer < 2) (hρ : sRho layer b = .n (lxRhoCell layer))
    (hA : sA layer b + 6 = lxDigitBase layer)
    (h0 : (sLeafK layer b).2.1 = lxWinBase (2 * layer))
    (h1 : (sWin0 layer b).2.1 = lxWinBase (2 * layer + 1)) :
    xPartA xmssTabs ((List.range 4).map fun w ↦ logGTWith gLanes (σ (.n (71 + w))) 256) layer σ =
      sPart layer b σ := by
  unfold xPartA sPart
  dsimp only
  rw [LeanXmss.LayerSignature.mk.injEq]
  refine ⟨by rw [hρ], funext fun i ↦ ?_, funext fun l ↦ ?_⟩
  · rw [sStart_eq (W := sW layer b) rfl σ _ _ i.val i.2, hA]
    unfold lxChainCell
    rw [lxGroupTab_eq, offAtA_tabA]
    simp only [xmssTabs]
    rw [lxArmsTaken_getD σ _ (by have := i.2; simp only [LeanXmss.chainCount] at this; omega)]
  · have hl : l.val < 16 := l.2
    rw [sSibAt_eq σ hL hl h0 h1, kw_getD σ (by omega)]

/-- **The reader is `xmssSigOf`**: off the tables built, the leanXMSS signature `__loop2`'s
iteration checks is the one its soundness reads (`B1/Sig/XmssSegSound.lean`). -/
theorem xmssSigOfN_eq (σ : Val) : xmssSigOfN σ = xmssSigOf σ := by
  unfold xmssSigOfN xmssSigOfA xmssSigOf
  dsimp only
  rw [LeanXmss.Signature.mk.injEq]
  refine ⟨Fin.ext ?_, funext fun lay ↦ ?_⟩
  · show lxLeafOf _ = lxIndex (sKw σ)
    have hlt := lxIndex_lt (k := sKw σ) (fun w _ ↦ sKw_lt σ w)
    unfold lxIndex at hlt ⊢
    unfold lxLeafOf
    simp only [xmssTabs]
    rw [kw_getD σ (by norm_num : 0 < 4), kw_getD σ (by norm_num : 1 < 4),
      kw_getD σ (by norm_num : 2 < 4), kw_getD σ (by norm_num : 3 < 4)]
    exact Nat.mod_eq_of_lt hlt
  · obtain ⟨v, hv⟩ := lay
    have hv2 : v < 2 := hv
    simp only [xmssTabs]
    interval_cases v
    · simp only [show (⟨0, hv⟩ : LeanXmss.Layer) = LeanXmss.bottomLayer from rfl, ↓reduceIte]
      exact xPartA_eq σ (by norm_num) rfl rfl (by rw [lxLeafK0]; rfl) (by rw [lxWin00]; rfl)
    · have hne : (⟨1, hv⟩ : LeanXmss.Layer) ≠ LeanXmss.bottomLayer :=
        fun h ↦ absurd (congrArg Fin.val h) (by simp [LeanXmss.bottomLayer])
      simp only [hne, ↓reduceIte, lxLayer0_end]
      exact xPartA_eq σ (by norm_num) rfl rfl (by rw [lxLeafK1]; rfl) (by rw [lxWin01]; rfl)

end
end LeanVM.Guest.Fast
