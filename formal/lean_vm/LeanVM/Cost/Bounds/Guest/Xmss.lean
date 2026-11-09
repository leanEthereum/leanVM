module

public import LeanVM.Cost.Bounds.Guest.Signatures
public import LeanVM.Cost.Decoder.Xmss

/-!
# Bounds on the guest decoder's prices: a leanXMSS signature

The reader of a leanXMSS signature off `__loop2`'s iteration frame, off its tables as arrays
(`Cost/Decoder/Xmss.lean`: `xmssSigOfNC` is `xmssSigOfA`, `Guest/Fast/Xmss.lean`), in the price
`S` of an application of the frame:

* the tables' facts (`lxTabs_ok`, by kernel evaluation of the literals), the arrays built from
  them (`XmssTabsOK`, `xmssTabs_ok`, `xmssTabs_cost`);
* the cells' numbers (`lxGroupBase_cost`, `lxGroupTab_cost`, `lxChainCell_cost`, `lxWinBase_cost`,
  `lxArmBase_cost`, `lxSibAt_cost`), a layer's dispatches' exponents (`lxArmsTaken_cost`: `15` of
  them off the lanes, each `23·256 + 25`);
* `xPartA_cost`, **`xmssSigOfN_cost`**: `xmssPrice S`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram)

/-! ## The tables -/

theorem lxTabs_ok : RowsOK 256 lxFold ∧ RowsOK 256 lxRest ∧ RowsOK 256 lxTail ∧
    lxFold.length ≤ 4 ∧ lxRest.length ≤ 4 ∧ lxTail.length ≤ 2 := by decide +kernel

/-- leanXMSS's tables as arrays, their entries small (`xmssTabs_ok`). -/
structure XmssTabsOK (T : XmssTabs) : Prop where
  lanes : ∀ x ∈ T.lanes, x < 2 ^ 64
  fold : ∀ r k, offAtA T.fold r k < 2 ^ 20
  rest : ∀ r k, offAtA T.rest r k < 2 ^ 20
  tail : ∀ r k, offAtA T.tail r k < 2 ^ 20

theorem xmssTabs_ok : XmssTabsOK xmssTabs := by
  obtain ⟨h1, h2, h3, -⟩ := lxTabs_ok
  exact ⟨gLanes_ok.2, offAtA_tabA_lt h1, offAtA_tabA_lt h2, offAtA_tabA_lt h3⟩

/-- **leanXMSS's tables, built** (`xmssTabsC`). -/
theorem xmssTabs_cost (hP : Includes P Decoder.xmssTabsC.costDeps) :
    machineCost P Decoder.xmssTabsC.costIdx [] ≤ 15447 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lxTabs_ok
  have t1 := tabA_cost P (by includes) lxFold 256 fun r hr ↦ (h1 r hr).1
  have t2 := tabA_cost P (by includes) lxRest 256 fun r hr ↦ (h2 r hr).1
  have t3 := tabA_cost P (by includes) lxTail 256 fun r hr ↦ (h3 r hr).1
  have := Nat.mul_le_mul_left (256 + 15) h4
  have := Nat.mul_le_mul_left (256 + 15) h5
  have := Nat.mul_le_mul_left (256 + 15) h6
  rw [Decoder.xmssTabsC.costEq P hP, Decoder.gLanesC.costEq P (by includes),
    Decoder.lxFoldC.costEq P (by includes), Decoder.lxRestC.costEq P (by includes),
    Decoder.lxTailC.costEq P (by includes)]
  omega

/-! ## The cells -/

theorem lxGroupBase_lt (vb0 p : ℕ) (hvb : vb0 < 2 ^ 20) (hp : p < 15) :
    lxGroupBase vb0 p < 2 ^ 21 := by
  unfold lxGroupBase; split_ifs <;> omega

theorem lxGroupBase_cost (hP : Includes P Decoder.lxGroupBaseC.costDeps) (vb0 p : ℕ)
    (hvb : vb0 < 2 ^ 20) (hp : p < 15) :
    machineCost P Decoder.lxGroupBaseC.costIdx [encodeValue vb0, encodeValue p] ≤ 20 := by
  rw [Decoder.lxGroupBaseC.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem lxGroupTab_cost (hP : Includes P Decoder.lxGroupTabC.costDeps) (T : XmssTabs) (p : ℕ)
    (hp : p < 15) :
    machineCost P Decoder.lxGroupTabC.costIdx [encodeValue T, encodeValue p] ≤ 12 := by
  rw [Decoder.lxGroupTabC.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem lxGroupTab_lt {T : XmssTabs} (hT : XmssTabsOK T) (p r k : ℕ) :
    offAtA (lxGroupTab T p) r k < 2 ^ 20 := by
  unfold lxGroupTab; split_ifs
  · exact hT.fold r k
  · exact hT.rest r k
  · exact hT.tail r k

/-- Chain `i`'s start cell (`lxChainCellC`), the arms taken `ks` at most `15`. -/
theorem lxChainCell_cost (hP : Includes P Decoder.lxChainCellC.costDeps) (T : XmssTabs)
    (hT : XmssTabsOK T) (ks : List ℕ) (hks : ks.length ≤ 15) (hk : ∀ x ∈ ks, x ≤ 256)
    (vb0 : ℕ) (hvb : vb0 < 2 ^ 20) (i : ℕ) (hi : i < 58) :
    machineCost P Decoder.lxChainCellC.costIdx
      [encodeValue T, encodeValue ks, encodeValue vb0, encodeValue i] ≤ 300 := by
  rw [Decoder.lxChainCellC.costEq P hP]
  have hb := lxGroupBase_cost P (by includes) vb0 (i / 4) hvb (by omega)
  have hb' := lxGroupBase_lt vb0 (i / 4) hvb (by omega)
  have ht := lxGroupTab_cost P (by includes) T (i / 4) (by omega)
  have hg := getD_cost P (by includes) ks (i / 4) 0 (by omega)
  have hkd : ks.getD (i / 4) 0 ≤ 256 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : ks[i / 4]? with
    | none => simp
    | some x => exact hk x (List.mem_of_getElem? h)
  have ho := lxGroupTab_lt hT (i / 4) (i % 4) (ks.getD (i / 4) 0)
  rw [Decoder.offAtAC.costEq P (by includes)]
  have := Nat.mul_le_mul_left 15 hks
  limbs_one
  omega

theorem lxWinBase_cost (hP : Includes P Decoder.lxWinBaseC.costDeps) (w : ℕ) (hw : w < 4) :
    machineCost P Decoder.lxWinBaseC.costIdx [encodeValue w] ≤ 20 := by
  rw [Decoder.lxWinBaseC.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem lxWinBase_lt (w : ℕ) : lxWinBase w < 2 ^ 18 := by
  unfold lxWinBase; split_ifs <;> omega

theorem lxArmBase_lt (w k : ℕ) (hk : k ≤ 256) : lxArmBase w k < 2 ^ 19 := by
  have := lxWinBase_lt w
  unfold lxArmBase; split_ifs <;> omega

theorem lxArmBase_cost (hP : Includes P Decoder.lxArmBaseC.costDeps) (w k : ℕ) (hw : w < 4)
    (hk : k ≤ 256) :
    machineCost P Decoder.lxArmBaseC.costIdx [encodeValue w, encodeValue k] ≤ 50 := by
  have := lxWinBase_cost P (by includes) w hw
  have := lxWinBase_lt w
  rw [Decoder.lxArmBaseC.costEq P hP]
  limbs_one; split_ifs <;> first | omega | (limbs_one; omega)

theorem lxSibAt_lt (w k r : ℕ) (hk : k ≤ 256) (hr : r < 8) : lxSibAt w k r < 2 ^ 20 := by
  have := lxArmBase_lt w k hk
  unfold lxSibAt; split_ifs <;> omega

theorem lxSibAt_cost (hP : Includes P Decoder.lxSibAtC.costDeps) (w k r : ℕ) (hw : w < 4)
    (hk : k ≤ 256) (hr : r < 8) :
    machineCost P Decoder.lxSibAtC.costIdx [encodeValue w, encodeValue k, encodeValue r] ≤ 80 := by
  have := lxArmBase_cost P (by includes) w k hw hk
  have := lxArmBase_lt w k hk
  rw [Decoder.lxSibAtC.costEq P hP]
  limbs_one; split_ifs <;> omega

/-- The leaf index (`lxLeafOfC`), the windows' arms at most `256`. -/
theorem lxLeafOf_cost (hP : Includes P Decoder.lxLeafOfC.costDeps) (kw : List ℕ)
    (hkw : kw.length ≤ 4) (hk : ∀ x ∈ kw, x ≤ 256) :
    machineCost P Decoder.lxLeafOfC.costIdx [encodeValue kw] ≤ 400 := by
  have hg (w : ℕ) (hw : w < 4) : kw.getD w 0 ≤ 256 ∧
      machineCost P Auto.List.getD.c225.costIdx [encodeValue kw, encodeValue w, encodeValue 0] ≤ 69 := by
    refine ⟨?_, ?_⟩
    · rw [List.getD_eq_getElem?_getD]
      cases h : kw[w]? with
      | none => simp
      | some x => exact hk x (List.mem_of_getElem? h)
    · have := getD_cost P (by includes) kw w 0 (by omega)
      omega
  obtain ⟨a0, c0⟩ := hg 0 (by omega)
  obtain ⟨a1, c1⟩ := hg 1 (by omega)
  obtain ⟨a2, c2⟩ := hg 2 (by omega)
  obtain ⟨a3, c3⟩ := hg 3 (by omega)
  rw [Decoder.lxLeafOfC.costEq P hP]
  limbs_one
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hσ hS in
theorem lxArmsTaken_le (lanes : List ℕ) (dg : ℕ) :
    (lxArmsTaken lanes σ dg).length ≤ 15 ∧ ∀ x ∈ lxArmsTaken lanes σ dg, x ≤ 256 := by
  unfold lxArmsTaken
  refine ⟨by simp, fun x hx ↦ ?_⟩
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact logGTWith_le _ _ _

/-- A layer's dispatches' exponents (`lxArmsTakenC`), its digit words from `dg < 2^20`. -/
theorem lxArmsTaken_cost (hP : Includes P Decoder.lxArmsTakenC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (dg : ℕ) (hdg : dg < 2 ^ 20) :
    machineCost P Decoder.lxArmsTakenC.costIdx [encodeValue lanes, σV, encodeValue dg] ≤
      (S + 5960) * 15 + 30 := by
  rw [Decoder.lxArmsTakenC.costEq P hP lanes σ σV hσ dg]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.lxArmsTakenC.lam0.costIdx [encodeValue lanes, σV, encodeValue dg])
    (fun p ↦ RunsApp.of_spec (Decoder.lxArmsTakenC.lam0.costSpec P (by includes) lanes σ σV hσ dg p))
    (S + 5932) 15 15 le_rfl (by norm_num) (fun p hp ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.lxArmsTakenC.lam0.costEq P (by includes) lanes σ σV hσ dg p, List.length_cons,
        List.length_cons, List.length_cons, List.length_nil]
      have := hS (.n (dg + p))
      have := logGTWith_cost P (by includes) lanes hl (σ (.n (dg + p))) 256 (by norm_num)
      limbs_one
      omega)
  omega

/-- A layer's price. -/
@[expose] def xPartPrice (S : ℕ) : ℕ := 90 * S + 120000

/-- **A layer's signature, off the tables `T`** (`xPartNC`, `xPartA`), the windows' arms `kw`
(at most `4`, each at most `256`) given: at most `xPartPrice S`. -/
theorem xPartA_cost (hP : Includes P Decoder.xPartNC.costDeps) (T : XmssTabs) (hT : XmssTabsOK T)
    (kw : List ℕ) (hkw : kw.length ≤ 4) (hk : ∀ x ∈ kw, x ≤ 256) (layer : ℕ) (hlay : layer ≤ 1) :
    machineCost P Decoder.xPartNC.costIdx [encodeValue T, encodeValue kw, encodeValue layer, σV] ≤
      xPartPrice S := by
  rw [Decoder.xPartNC.costEq P hP T kw layer σ σV hσ, ofFnFrom_length, ofFnFrom_length]
  have hdg : lxDigitBase layer ≤ 107774 := by unfold lxDigitBase; split_ifs <;> omega
  have hd := Decoder.lxDigitBaseC.costEq P (by includes) layer
  have hr := Decoder.lxRhoCellC.costEq P (by includes) layer
  simp only [ite_self, limbs_of_lt (by omega : layer < 2 ^ 64)] at hd hr
  have ha := lxArmsTaken_cost P hσ hS (by includes) T.lanes hT.lanes (lxDigitBase layer) (by omega)
  have hks := lxArmsTaken_le (σ := σ) T.lanes (lxDigitBase layer)
  have hc := cellNat_cost P (by includes) (σ (.n (lxRhoCell layer)))
  have := hS (.n (lxRhoCell layer))
  have m0 := ofFnFrom_cost P (by includes) (n := LeanXmss.chainCount) (by decide) _
    (.closure Decoder.xPartNC.lam0.costIdx [encodeValue T, encodeValue layer, σV,
      encodeValue (lxArmsTaken T.lanes σ (lxDigitBase layer))])
    (fun i ↦ RunsApp.of_spec (Decoder.xPartNC.lam0.costSpec P (by includes) T layer σ σV hσ _ i))
    (S + 360) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.xPartNC.lam0.costEq P (by includes) T layer σ σV hσ,
        List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have hi := i.isLt
      simp only [LeanXmss.chainCount] at hi
      have := lxChainCell_cost P (by includes) T hT _ hks.1 hks.2 (lxDigitBase layer + 70)
        (by omega) i.val hi
      have := cellNat_cost P (by includes)
        (σ (.n (lxChainCell T (lxArmsTaken T.lanes σ (lxDigitBase layer)) (lxDigitBase layer + 70)
          i.val)))
      have := hS (.n (lxChainCell T (lxArmsTaken T.lanes σ (lxDigitBase layer))
        (lxDigitBase layer + 70) i.val))
      limbs_one
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := LeanXmss.layerHeight) (by decide) _
    (.closure Decoder.xPartNC.lam1.costIdx [encodeValue kw, encodeValue layer, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.xPartNC.lam1.costSpec P (by includes) kw layer σ σV hσ l))
    (S + 200) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xPartNC.lam1.costEq P (by includes) kw layer σ σV hσ, List.length_cons,
        List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [LeanXmss.layerHeight] at hl
      have hkd : kw.getD (2 * layer + l.val / 8) 0 ≤ 256 := by
        rw [List.getD_eq_getElem?_getD]
        cases h : kw[2 * layer + l.val / 8]? with
        | none => simp
        | some x => exact hk x (List.mem_of_getElem? h)
      have hg := getD_cost P (by includes) kw (2 * layer + l.val / 8) 0 (by omega)
      have := lxSibAt_cost P (by includes) (2 * layer + l.val / 8)
        (kw.getD (2 * layer + l.val / 8) 0) (l.val % 8) (by omega) hkd (by omega)
      have := cellNat_cost P (by includes) (σ (.n (lxSibAt (2 * layer + l.val / 8)
        (kw.getD (2 * layer + l.val / 8) 0) (l.val % 8))))
      have := hS (.n (lxSibAt (2 * layer + l.val / 8) (kw.getD (2 * layer + l.val / 8) 0)
        (l.val % 8)))
      have := Nat.mul_le_mul_left 15 hkw
      limbs_one
      omega) 0 (Nat.zero_le _)
  simp only [LeanXmss.chainCount, LeanXmss.layerHeight, Nat.sub_zero] at m0 m1 ⊢
  unfold xPartPrice
  omega

/-- A signature's price. -/
@[expose] def xmssPrice (S : ℕ) : ℕ := 2 * xPartPrice S + 4 * S + 25050

/-- **A leanXMSS signature, off the tables `T`** (`xmssSigOfNC`, `xmssSigOfA`): at most
`xmssPrice S`. -/
theorem xmssSigOfN_cost (hP : Includes P Decoder.xmssSigOfNC.costDeps) (T : XmssTabs)
    (hT : XmssTabsOK T) :
    machineCost P Decoder.xmssSigOfNC.costIdx [encodeValue T, σV] ≤ xmssPrice S := by
  rw [Decoder.xmssSigOfNC.costEq P hP T σ σV hσ, ofFnFrom_length]
  have hw := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.xmssSigOfNC.lam0.costIdx [encodeValue T, σV])
    (fun w ↦ RunsApp.of_spec (Decoder.xmssSigOfNC.lam0.costSpec P (by includes) T σ σV hσ w))
    (S + 5933) 4 4 le_rfl (by norm_num) (fun w hw ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xmssSigOfNC.lam0.costEq P (by includes) T σ σV hσ w, List.length_cons,
        List.length_cons, List.length_nil]
      have := hS (.n (71 + w))
      have := logGTWith_cost P (by includes) T.lanes hT.lanes (σ (.n (71 + w))) 256 (by norm_num)
      limbs_one
      omega)
  have hkw : ((List.range 4).map fun w ↦ logGTWith T.lanes (σ (.n (71 + w))) 256).length ≤ 4 ∧
      ∀ x ∈ (List.range 4).map (fun w ↦ logGTWith T.lanes (σ (.n (71 + w))) 256), x ≤ 256 := by
    refine ⟨by simp, fun x hx ↦ ?_⟩
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact logGTWith_le _ _ _
  have hleaf := lxLeafOf_cost P (by includes) _ hkw.1 hkw.2
  have m := ofFnFrom_cost P (by includes) (n := LeanXmss.layerCount) (by decide) _
    (.closure Decoder.xmssSigOfNC.lam1.costIdx [encodeValue T, σV,
      encodeValue ((List.range 4).map fun w ↦ logGTWith T.lanes (σ (.n (71 + w))) 256)])
    (fun l ↦ RunsApp.of_spec (Decoder.xmssSigOfNC.lam1.costSpec P (by includes) T σ σV hσ _ l))
    (xPartPrice S + 10) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xmssSigOfNC.lam1.costEq P (by includes) T σ σV hσ, List.length_cons,
        List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [LeanXmss.layerCount] at hl
      have := xPartA_cost P hσ hS (by includes) T hT _ hkw.1 hkw.2 l.val (by omega)
      omega) 0 (Nat.zero_le _)
  simp only [LeanXmss.layerCount, Nat.sub_zero] at m ⊢
  unfold xmssPrice
  omega

end Val

end

end LeanVM.Cost.Bounds.Guest
