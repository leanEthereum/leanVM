module

public import LeanVM.Cost.Bounds.Guest.Readers
public import LeanVM.Cost.Decoder.Signatures

/-!
# Bounds on the guest decoder's prices: the signatures

The readers of a leanSPHINCS signature off its check's valuations, off the readers' tables as
arrays (`Cost/Decoder/Signatures.lean`: `sphincsSigOfNC` is `sphincsSigOfA`,
`Guest/Fast/Sphincs.lean`; leanXMSS's in `Xmss.lean`), in the price `S` of an application of a
valuation: a signature has a fixed shape, so its price is `a·S + b`:

* the tables' facts (`gLanes_ok`, `spTabs_lits_ok`, … by kernel evaluation of the literals), and
  of the arrays built from them (`SpTabsOK`: `spTabs_ok`), an entry read in constant time
  (`offAtA`: `8`);
* an exponent off the lanes of `g^k` given (`idxBelow_cost`, `logGTWith_cost`: `23·bound + 25`),
  a sibling (`sibN_cost`), a chain's start cell (`cwCellA_cost`: `S + 1543`);
* leanSPHINCS, its four valuations (`verify_sig_lean_sphincs`' and the three `sp_wots` frames)
  each of price at most `S`, its positions off the tables (`offAtA`), the counter big-endian
  (`beWordAt_cost`): `forsOpeningA_cost` (`41·S + 1500`), `layerA_cost` (`169·S + 104600`),
  **`sphincsSigOfA_cost`**: `1492·S + 350800`; the words of a layer's call of `sp_wots`
  (`spWotsArgs_cost`, `spWotsRets_cost`), by which the decoder finds its frame.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram)

/-! ## Tables -/

/-- A table's rows: at most `M` entries, each below `2^20`. -/
@[expose] def RowsOK (M : ℕ) (tab : List (List ℕ)) : Prop :=
  ∀ r ∈ tab, r.length ≤ M ∧ ∀ x ∈ r, x < 2 ^ 20

instance (M : ℕ) (tab : List (List ℕ)) : Decidable (RowsOK M tab) := by
  unfold RowsOK; infer_instance

/-- A list of at most `M` entries, each below `2^20`. -/
@[expose] def ListOK (M : ℕ) (l : List ℕ) : Prop := l.length ≤ M ∧ ∀ x ∈ l, x < 2 ^ 20

instance (M : ℕ) (l : List ℕ) : Decidable (ListOK M l) := by
  unfold ListOK; infer_instance

theorem gLanes_ok : gLanes.length = 256 ∧ ∀ x ∈ gLanes, x < 2 ^ 64 := by decide +kernel

theorem spTabs_lits_ok : RowsOK 64 spFirst ∧ RowsOK 64 spRest ∧ RowsOK 64 spLast ∧
    spFirst.length ≤ 3 ∧ spRest.length ≤ 3 ∧ spLast.length ≤ 1 ∧ ListOK 22 spSel := by
  decide +kernel

theorem spPos_lits_ok : RowsOK 10 spForsKids ∧ RowsOK 10 spForsBits ∧ RowsOK 10 spPathKids ∧
    RowsOK 10 spPathBits ∧ spForsKids.length ≤ 24 ∧ spForsBits.length ≤ 24 ∧
    spPathKids.length ≤ 3 ∧ spPathBits.length ≤ 3 := by
  decide +kernel

theorem getD_lt_of {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x < B) (hB : 0 < B) (k : ℕ) :
    l.getD k 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simpa using hB
  | some x => exact h x (List.mem_of_getElem? hk)

theorem getD_row {tab : List (List ℕ)} {M : ℕ} (h : RowsOK M tab) (r : ℕ) :
    (tab.getD r []).length ≤ M ∧ ∀ x ∈ tab.getD r [], x < 2 ^ 20 := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : tab[r]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hk)

theorem offAt_lt {tab : List (List ℕ)} {M : ℕ} (h : RowsOK M tab) (r k : ℕ) :
    offAt tab r k < 2 ^ 20 :=
  getD_lt_of (getD_row h r).2 (by norm_num) k

/-! ## The tables as arrays -/

theorem offAtA_tabA_lt {tab : List (List ℕ)} {M : ℕ} (h : RowsOK M tab) (r k : ℕ) :
    offAtA (tabA tab) r k < 2 ^ 20 := by
  rw [offAtA_tabA]; exact offAt_lt h r k

theorem getD_toArray_lt {l : List ℕ} {M : ℕ} (h : ListOK M l) (k : ℕ) :
    l.toArray.getD k 0 < 2 ^ 20 := by
  rw [getD_toArray]; exact getD_lt_of h.2 (by norm_num) k

/-- `sp_wots`' tables as arrays, their entries small (`spTabs_ok`). -/
structure SpTabsOK (T : SpTabs) : Prop where
  lanes : ∀ x ∈ T.lanes, x < 2 ^ 64
  sel : ∀ k, T.sel.getD k 0 < 2 ^ 20
  first : ∀ r k, offAtA T.first r k < 2 ^ 20
  rest : ∀ r k, offAtA T.rest r k < 2 ^ 20
  last : ∀ r k, offAtA T.last r k < 2 ^ 20
  forsKid : ∀ r k, offAtA T.forsKid r k < 2 ^ 20
  forsBit : ∀ r k, offAtA T.forsBit r k < 2 ^ 20
  pathKid : ∀ r k, offAtA T.pathKid r k < 2 ^ 20
  pathBit : ∀ r k, offAtA T.pathBit r k < 2 ^ 20

theorem spTabs_ok : SpTabsOK spTabs := by
  obtain ⟨h1, h2, h3, -, -, -, hsel⟩ := spTabs_lits_ok
  obtain ⟨p1, p2, p3, p4, -⟩ := spPos_lits_ok
  exact ⟨gLanes_ok.2, getD_toArray_lt hsel, offAtA_tabA_lt h1, offAtA_tabA_lt h2,
    offAtA_tabA_lt h3, offAtA_tabA_lt p1, offAtA_tabA_lt p2, offAtA_tabA_lt p3,
    offAtA_tabA_lt p4⟩

/-- A table of rows as arrays (`tabAC`), its rows at most `M` entries: at most
`(M + 15)·rows + rows + 7`. -/
theorem tabA_cost (hP : Includes P Decoder.tabAC.costDeps) (t : List (List ℕ)) (M : ℕ)
    (hM : ∀ r ∈ t, r.length ≤ M) :
    machineCost P Decoder.tabAC.costIdx [encodeValue t] ≤ (M + 15) * t.length + t.length + 7 := by
  rw [Decoder.tabAC.costEq P hP, List.length_map]
  have := map_cost P (by includes) List.toArray (.closure Decoder.tabAC.lam0.costIdx [])
    (fun xs ↦ RunsApp.of_spec (Decoder.tabAC.lam0.costSpec P (by includes) xs)) (M + 2) t
    (fun r hr ↦ by
      rw [appCost_fn, List.nil_append, Decoder.tabAC.lam0.costEq P (by includes), List.length_nil]
      have := hM r hr; omega)
  rw [show M + 2 + 13 = M + 15 by omega] at this
  omega

/-- **`verify_sig_lean_sphincs`' and `sp_wots`' tables, built** (`spTabsC`): at most `7800`. -/
theorem spTabs_cost (hP : Includes P Decoder.spTabsC.costDeps) :
    machineCost P Decoder.spTabsC.costIdx [] ≤ 7800 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := spTabs_lits_ok
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := spPos_lits_ok
  have t1 := tabA_cost P (by includes) spFirst 64 fun r hr ↦ (h1 r hr).1
  have t2 := tabA_cost P (by includes) spRest 64 fun r hr ↦ (h2 r hr).1
  have t3 := tabA_cost P (by includes) spLast 64 fun r hr ↦ (h3 r hr).1
  have t4 := tabA_cost P (by includes) spForsKids 10 fun r hr ↦ (p1 r hr).1
  have t5 := tabA_cost P (by includes) spForsBits 10 fun r hr ↦ (p2 r hr).1
  have t6 := tabA_cost P (by includes) spPathKids 10 fun r hr ↦ (p3 r hr).1
  have t7 := tabA_cost P (by includes) spPathBits 10 fun r hr ↦ (p4 r hr).1
  have := Nat.mul_le_mul_left (64 + 15) h4
  have := Nat.mul_le_mul_left (64 + 15) h5
  have := Nat.mul_le_mul_left (64 + 15) h6
  have := Nat.mul_le_mul_left (10 + 15) p5
  have := Nat.mul_le_mul_left (10 + 15) p6
  have := Nat.mul_le_mul_left (10 + 15) p7
  have := Nat.mul_le_mul_left (10 + 15) p8
  rw [Decoder.spTabsC.costEq P hP, Decoder.gLanesC.costEq P (by includes),
    Decoder.spSelC.costEq P (by includes), Decoder.spFirstC.costEq P (by includes),
    Decoder.spRestC.costEq P (by includes), Decoder.spLastC.costEq P (by includes),
    Decoder.spForsKidsC.costEq P (by includes), Decoder.spForsBitsC.costEq P (by includes),
    Decoder.spPathKidsC.costEq P (by includes), Decoder.spPathBitsC.costEq P (by includes),
    show spSel.length = 22 from rfl]
  omega

/-! ## The exponent off the lanes -/

theorem idxBelow_le (w : ℕ) : ∀ (l : List ℕ) (i m : ℕ), idxBelow w l i m ≤ i + m
  | [], _, _ => by simp [idxBelow]
  | _ :: _, _, 0 => by simp [idxBelow]
  | t :: ts, i, m + 1 => by
    rw [idxBelow]
    split_ifs
    · omega
    · have := idxBelow_le w ts (i + 1) m; omega

theorem logGTWith_le (lanes : List ℕ) (x : E) (b : ℕ) : logGTWith lanes x b ≤ b := by
  unfold logGTWith; split_ifs
  · have := idxBelow_le (x.limb 0).lane.toNat lanes 0 b; omega
  · omega

/-- The search among the lanes (`idxBelowC`), `m` entries: at most `23·m + 9`. -/
theorem idxBelow_cost (hP : Includes P Decoder.idxBelowC.costDeps) (w : ℕ)
    (hw : w < 2 ^ 64) : ∀ (l : List ℕ) (i m : ℕ), (∀ x ∈ l, x < 2 ^ 64) → i + m < 2 ^ 64 →
      machineCost P Decoder.idxBelowC.costIdx
        [encodeValue w, encodeValue l, encodeValue i, encodeValue m] ≤ 23 * m + 9
  | [], i, m, _, _ => by rw [Decoder.idxBelowC.costEq_nil P hP]; omega
  | t :: ts, i, m, hl, him => by
    rw [Decoder.idxBelowC.costEq_cons P hP, limbs_of_lt (by omega : m < 2 ^ 64)]
    cases m with
    | zero => simp
    | succ k =>
      have ht := hl t (by simp)
      have := idxBelow_cost hP w hw ts (i + 1) k (fun x hx ↦ hl x (by simp [hx])) (by omega)
      dsimp only
      rw [limbs_of_lt hw, limbs_of_lt ht, limbs_of_lt (by omega : i < 2 ^ 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64)]
      split_ifs <;> omega

/-- **An exponent off the lanes given** (`logGTWithC`), `bound < 2^32`: at most
`23·bound + 25`. -/
theorem logGTWith_cost (hP : Includes P Decoder.logGTWithC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (x : E) (b : ℕ) (hb : b < 2 ^ 32) :
    machineCost P Decoder.logGTWithC.costIdx [encodeValue lanes, encodeValue x, encodeValue b] ≤
      23 * b + 25 := by
  rw [Decoder.logGTWithC.costEq P hP]
  have := idxBelow_cost P (by includes) (x.limb 0).lane.toNat (UInt64.toNat_lt _) lanes 0 b hl
    (by omega)
  split_ifs <;> omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A path level's sibling (`sibNC`): at most `4·S + 71`. -/
theorem sibN_cost (hP : Includes P Decoder.sibNC.costDeps) (bit b : ℕ)
    (hb : b + 1 < 2 ^ 64) :
    machineCost P Decoder.sibNC.costIdx [σV, encodeValue bit, encodeValue b] ≤
      4 * S + 71 := by
  rw [Decoder.sibNC.costEq P hP σ σV hσ, limbs_of_lt hb, limbs_of_lt (by omega : b < 2 ^ 64)]
  have := hS (.n bit); have := hS (.n b); have := hS (.n (b + 1))
  split_ifs <;> omega

/-- **A chain's start cell, off arrays** (`cwCellC`, `cwCellA`): the lanes below `2^64`, the
selectors and the tables' entries below `2^20`: at most `S + 1543`. -/
theorem cwCellA_cost (hP : Includes P Decoder.cwCellC.costDeps) (lanes : List ℕ)
    (hlanes : ∀ x ∈ lanes, x < 2 ^ 64) (G : ℕ) (sel : Array ℕ) (first rest last : Array (Array ℕ))
    (hsel : ∀ k, sel.getD k 0 < 2 ^ 20) (hf : ∀ r k, offAtA first r k < 2 ^ 20)
    (hr : ∀ r k, offAtA rest r k < 2 ^ 20) (hl : ∀ r k, offAtA last r k < 2 ^ 20)
    (hG : G < 2 ^ 20) (i : ℕ) (hi : i < 2 ^ 20) :
    machineCost P Decoder.cwCellC.costIdx [encodeValue lanes, encodeValue G, encodeValue sel,
      encodeValue first, encodeValue rest, encodeValue last, σV, encodeValue i] ≤ S + 1543 := by
  rw [Decoder.cwCellC.costEq P hP _ _ _ _ _ _ σ σV hσ]
  have hsl := hsel (i / 3)
  rw [limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : i / 3 < 2 ^ 64),
    limbs_of_lt (by omega : G < 2 ^ 64), limbs_of_lt (by omega : sel.getD (i / 3) 0 < 2 ^ 64)]
  have := hS (.n (sel.getD (i / 3) 0))
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n (sel.getD (i / 3) 0))) 64
    (by norm_num)
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n (sel.getD (i / 3) 0))) 4
    (by norm_num)
  rw [Decoder.offAtAC.costEq P (by includes), Decoder.offAtAC.costEq P (by includes)]
  have h1 := hf (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64)
  have h2 := hr (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64)
  have h3 := hl (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4)
  split_ifs with c1 c2
  · rw [limbs_of_lt (by omega : offAtA first (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA first (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64)]
    omega
  · rw [limbs_of_lt (by omega : offAtA rest (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA rest (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64)]
    omega
  · rw [limbs_of_lt (by omega : offAtA last (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA last (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4) < 2 ^ 64)]
    omega

/-! ## leanSPHINCS -/

omit hσ hS in
/-- `beWordAt 0 w`, `w` a cell's number (below `2^128`): at most `90`. -/
theorem beWordAt_cost (hP : Includes P Decoder.beWordAtC.costDeps) (w : ℕ) (hw : w < 2 ^ 128) :
    machineCost P Decoder.beWordAtC.costIdx [encodeValue 0, encodeValue w] ≤ 90 := by
  rw [Decoder.beWordAtC.costEq P hP]
  have h1 := limbs_le_of_lt (x := w) (k := 2) (by norm_num) hw
  have h2 := limbs_le_of_lt (x := w / 2 ^ 24) (k := 2) (by norm_num) (by omega)
  have h3 := limbs_le_of_lt (x := w / 2 ^ 16) (k := 2) (by norm_num) (by omega)
  have h4 := limbs_le_of_lt (x := w / 2 ^ 8) (k := 2) (by norm_num) (by omega)
  simp only [Nat.mul_zero, Nat.shiftLeft_eq, Nat.one_mul, pow_zero]
  limbs_one
  omega

omit hσ hS in
theorem beWordAt_lt (w : ℕ) : LeanVM.Guest.B1.Sig.beWordAt 0 w < 2 ^ 32 := by
  unfold LeanVM.Guest.B1.Sig.beWordAt; omega

omit hσ hS in
theorem spForsBase_cost (hP : Includes P Decoder.spForsBaseC.costDeps) (c : ℕ) (hc : c < 24) :
    machineCost P Decoder.spForsBaseC.costIdx [encodeValue c] ≤ 27 := by
  rw [Decoder.spForsBaseC.costEq P hP]
  limbs_one; split_ifs <;> omega

omit hσ hS in
theorem spLayerBase_cost (hP : Includes P Decoder.spLayerBaseC.costDeps) (l : ℕ) (hl : l < 3) :
    machineCost P Decoder.spLayerBaseC.costIdx [encodeValue l] ≤ 12 := by
  rw [Decoder.spLayerBaseC.costEq P hP]
  limbs_one; split_ifs <;> omega

omit hσ hS in
theorem spLayerBase_lt (l : ℕ) : spLayerBase l < 2 ^ 20 := by
  unfold spLayerBase; split_ifs <;> omega

omit hσ hS in
theorem spCtr_cost (hP : Includes P Decoder.spCtrC.costDeps) (l : ℕ) (hl : l < 3) :
    machineCost P Decoder.spCtrC.costIdx [encodeValue l] ≤ 17 := by
  rw [Decoder.spCtrC.costEq P hP]
  have := spLayerBase_cost P (by includes) l hl
  have := spLayerBase_lt l
  limbs_one; omega

/-- **FORS tree `c`'s opening** (`forsOpeningAC`), `c < 24`, the tables `T` small: its secret and
ten siblings, at most `41·S + 1500`. -/
theorem forsOpeningA_cost (hP : Includes P Decoder.forsOpeningAC.costDeps) (T : SpTabs)
    (hT : SpTabsOK T) (c : ℕ) (hc : c < 24) :
    machineCost P Decoder.forsOpeningAC.costIdx [encodeValue T, σV, encodeValue c] ≤
      41 * S + 1500 := by
  rw [Decoder.forsOpeningAC.costEq P hP T σ σV hσ, ofFnFrom_length]
  have := spForsBase_cost P (by includes) c hc
  have := hS (.n (spForsBase c))
  have := cellNat_cost P (by includes) (σ (.n (spForsBase c)))
  have m := ofFnFrom_cost P (by includes) (n := Sphincs.forsTreeHeight) (by decide) _
    (.closure Decoder.forsOpeningAC.lam0.costIdx [encodeValue T, σV, encodeValue c])
    (fun z ↦ RunsApp.of_spec (Decoder.forsOpeningAC.lam0.costSpec P (by includes) T σ σV hσ c z))
    (4 * S + 120) (fun z ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.forsOpeningAC.lam0.costEq P (by includes) T σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have hb := hT.forsBit c z.val
      have hk := hT.forsKid c z.val
      have := sibN_cost P hσ hS (by includes) (offAtA T.forsBit c z.val) (offAtA T.forsKid c z.val)
        (by omega)
      have := cellNat_cost P (by includes)
        (sibN σ (offAtA T.forsBit c z.val) (offAtA T.forsKid c z.val))
      rw [Decoder.offAtAC.costEq P (by includes), Decoder.offAtAC.costEq P (by includes)]
      omega) 0 (Nat.zero_le _)
  simp only [Sphincs.forsTreeHeight, Nat.sub_zero] at m ⊢
  omega

/-- **A layer's signature** (`layerAC`), row `l < 3` of the tables `T`, its chains off the
`sp_wots` frame `w` (a valuation of price at most `S`, like `σ`): at most `169·S + 104600`. -/
theorem layerA_cost (hP : Includes P Decoder.layerAC.costDeps) (T : SpTabs) (hT : SpTabsOK T)
    {w : Val} {wV : MachineValue} (hw : ∀ v : V, RunsApp P wV [encodeValue v] (encodeValue (w v)))
    (hW : ∀ v : V, appCost P wV [encodeValue v] ≤ S) (l : ℕ) (hl : l < 3)
    (layer : Sphincs.Layer) :
    machineCost P Decoder.layerAC.costIdx [encodeValue T, σV, wV, encodeValue l,
      encodeValue layer] ≤ 169 * S + 104600 := by
  rw [Decoder.layerAC.costEq P hP T σ σV hσ w wV hw, ofFnFrom_length, ofFnFrom_length,
    Auto.Sphincs.layerHeight.c844.costEq P (by includes)]
  have := spCtr_cost P (by includes) l hl
  have := hS (.n (spCtr l))
  have := cellNat_cost P (by includes) (σ (.n (spCtr l)))
  have := beWordAt_cost P (by includes) _ (Decoder.cellNat_lt (σ (.n (spCtr l))))
  have hbe := limbs_of_lt (lt_trans (beWordAt_lt (Sig.cellNat (σ (.n (spCtr l))))) (by norm_num))
  rw [limbs_of_lt (by norm_num : 2 ^ 32 - 1 < 2 ^ 64), hbe]
  have hlay := layer.isLt
  simp only [Sphincs.layerCount] at hlay
  rw [limbs_of_lt (by omega : layer.val < 2 ^ 64)]
  have hh : Sphincs.layerHeight layer ≤ 10 := by unfold Sphincs.layerHeight; split <;> omega
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.chainCount) (by decide) _
    (.closure Decoder.layerAC.lam0.costIdx [encodeValue T, wV])
    (fun i ↦ RunsApp.of_spec (Decoder.layerAC.lam0.costSpec P (by includes) T w wV hw i))
    (2 * S + 1580) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.layerAC.lam0.costEq P (by includes) T w wV hw]
      simp only [List.length_cons, List.length_nil]
      have := cwCellA_cost P hw hW (by includes) T.lanes hT.lanes 21 T.sel T.first T.rest T.last
        hT.sel hT.first hT.rest hT.last (by norm_num) i.val
        (by have := i.isLt; simp only [Sphincs.chainCount] at this; omega)
      have := cellNat_cost P (by includes)
        (w (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val)))
      have := hW (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val))
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.layerHeight layer) (by omega) _
    (.closure Decoder.layerAC.lam1.costIdx [encodeValue T, σV, encodeValue l, encodeValue layer])
    (fun j ↦ RunsApp.of_spec (Decoder.layerAC.lam1.costSpec P (by includes) T σ σV hσ l layer j))
    (4 * S + 120) (fun j ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.layerAC.lam1.costEq P (by includes) T σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have hb := hT.pathBit l j.val
      have hk := hT.pathKid l j.val
      have := sibN_cost P hσ hS (by includes) (offAtA T.pathBit l j.val) (offAtA T.pathKid l j.val)
        (by omega)
      have := cellNat_cost P (by includes)
        (sibN σ (offAtA T.pathBit l j.val) (offAtA T.pathKid l j.val))
      rw [Decoder.offAtAC.costEq P (by includes), Decoder.offAtAC.costEq P (by includes)]
      omega) 0 (Nat.zero_le _)
  have hm1 : (4 * S + 120 + 16) * (Sphincs.layerHeight layer - 0) ≤ (4 * S + 136) * 10 := by
    rw [Nat.sub_zero]; exact Nat.mul_le_mul_left _ hh
  simp only [Sphincs.chainCount, Nat.sub_zero, ite_self] at m0 ⊢
  omega

/-- **A leanSPHINCS signature, off the tables `T`** (`sphincsSigOfNC`, `sphincsSigOfA`):
`verify_sig_lean_sphincs`' valuation `σ` and the three `sp_wots` frames `w0`, `w1`, `w2`, each a
valuation of price at most `S`: at most `1492·S + 350800`. -/
theorem sphincsSigOfA_cost (hP : Includes P Decoder.sphincsSigOfNC.costDeps) (T : SpTabs)
    (hT : SpTabsOK T) {w0 w1 w2 : Val} {w0V w1V w2V : MachineValue}
    (hw0 : ∀ v : V, RunsApp P w0V [encodeValue v] (encodeValue (w0 v)))
    (hW0 : ∀ v : V, appCost P w0V [encodeValue v] ≤ S)
    (hw1 : ∀ v : V, RunsApp P w1V [encodeValue v] (encodeValue (w1 v)))
    (hW1 : ∀ v : V, appCost P w1V [encodeValue v] ≤ S)
    (hw2 : ∀ v : V, RunsApp P w2V [encodeValue v] (encodeValue (w2 v)))
    (hW2 : ∀ v : V, appCost P w2V [encodeValue v] ≤ S) :
    machineCost P Decoder.sphincsSigOfNC.costIdx [encodeValue T, σV, w0V, w1V, w2V] ≤
      1492 * S + 350800 := by
  rw [Decoder.sphincsSigOfNC.costEq P hP T σ σV hσ w0 w0V hw0 w1 w1V hw1 w2 w2V hw2,
    ofFnFrom_length]
  have := hS (.n 6)
  have := cellNat_cost P (by includes) (σ (.n 6))
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.forsTreeCount) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam0.costIdx [encodeValue T, σV])
    (fun c ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam0.costSpec P (by includes) T σ σV hσ c))
    (41 * S + 1520) (fun c ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam0.costEq P (by includes) T σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have := forsOpeningA_cost P hσ hS (by includes) T hT c.val
        (by have := c.isLt; simp only [Sphincs.forsTreeCount] at this; omega)
      omega) 0 (Nat.zero_le _)
  have l0 := layerA_cost P hσ hS (by includes) T hT hw0 hW0 0 (by norm_num) 0
  have l1 := layerA_cost P hσ hS (by includes) T hT hw1 hW1 1 (by norm_num) 1
  have l2 := layerA_cost P hσ hS (by includes) T hT hw2 hW2 2 (by norm_num) 2
  rw [Auto.Fin.ofNat.c847.costEq P (by includes), Auto.Fin.ofNat.c847.costEq P (by includes),
    Auto.Fin.ofNat.c847.costEq P (by includes)]
  simp only [Sphincs.forsTreeCount, Sphincs.layerCount, Nat.sub_zero] at m0 ⊢
  limbs_one
  omega

/-- **A layer's call of `sp_wots`, its arguments** (`spWotsArgsC`), `l < 3`: four words, at most
`4·S + 90`. -/
theorem spWotsArgs_cost (hP : Includes P Decoder.spWotsArgsC.costDeps) (l : ℕ) (hl : l < 3) :
    machineCost P Decoder.spWotsArgsC.costIdx [σV, encodeValue l] ≤ 4 * S + 90 := by
  rw [Decoder.spWotsArgsC.costEq P hP σ σV hσ, Decoder.spA0C.costEq P (by includes),
    Decoder.spA1C.costEq P (by includes), Decoder.spEncC.costEq P (by includes)]
  have := spLayerBase_cost P (by includes) l hl
  have := spLayerBase_lt l
  have := hS (.n 2); have := hS (.n (spA0 l)); have := hS (.n (spA1 l)); have := hS (.n (spEnc l))
  limbs_one
  split_ifs <;> omega

/-- **A layer's call of `sp_wots`, its return** (`spWotsRetsC`), `l < 3`: at most `S + 40`. -/
theorem spWotsRets_cost (hP : Includes P Decoder.spWotsRetsC.costDeps) (l : ℕ) (hl : l < 3) :
    machineCost P Decoder.spWotsRetsC.costIdx [σV, encodeValue l] ≤ S + 40 := by
  rw [Decoder.spWotsRetsC.costEq P hP σ σV hσ, Decoder.spLeafC.costEq P (by includes)]
  have := spLayerBase_cost P (by includes) l hl
  have := spLayerBase_lt l
  have := hS (.n (spLeaf l))
  limbs_one
  omega

end Val

end

end LeanVM.Cost.Bounds.Guest
