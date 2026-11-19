module

public import NativeVm.Model.Whir
public import NativeVm.Equiv.Folds
public import NativeVm.Equiv.LayoutSpec
public import NativeVm.Equiv.Transcript

/-!
# Phase 7b's pure steps, the model against the statement

* A query position is a word: `queryBits_toNat` reads `queryBits` as the statement's
  `(eToNat c >>> shift) % 2^depth` for `depth ≤ 64`, and a position `q` is the statement's
  `K.ofBits q.toNat = K.ofLane q` (`ofBits_toNat`).
* The rows and folds: `toList_map_extRow`, `toList_map_foldLanes`, `toE_foldRow`.
* The subspace polynomials: `toList_map_subspaceRoots`; `subspaceTable μ` is the statement's
  `(subspaceRoots μ).map fun r ↦ (r, r⁻¹)` (`toList_map_subspaceTable`), so `subspaceAtTable` on
  it, computed once per level, is `subspaceAt μ` at every position (`toList_map_subspaceAtTable`,
  `toList_map_subspaceAt`); `toList_map_novelBasis`, `toE_novelEval`, `toE_inducedWeight`.
* The weights as data: `GluedWeight.Rel`, `GluedClaimW.Rel`, `BasisW.Rel` say the data evaluate as
  the statement's functions at every point; `GluedWeight.rel_eq`, `GluedWeight.rel_induced`,
  `BasisW.rel_mk` prove it of what the model builds. `WhirStateW.Rel` relates the level loop's
  states.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## Words as numbers and lanes -/

theorem testBit_word (w : UInt64) {i : ℕ} (hi : 64 ≤ i) : w.toNat.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le w.toNat_lt (Nat.pow_le_pow_right (by omega) hi))

/-- The shifted 64-bit window of a challenge's 128-bit integer, before the mask. -/
theorem queryWindow_toNat (c : EW) (shift : ℕ) :
    (if shift = 0 then c.c0
      else if shift < 64 then (c.c0 >>> shift.toUInt64) ||| (c.c1 <<< (64 - shift).toUInt64)
      else if shift < 128 then c.c1 >>> (shift - 64).toUInt64
      else 0).toNat = ((2 ^ 64 * c.c1.toNat + c.c0.toNat) >>> shift) % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_mul_add _ c.c0.toNat_lt]
  by_cases h0 : shift = 0
  · subst h0
    by_cases hi : i < 64
    · simp [hi]
    · simp [hi, testBit_word c.c0 (by omega : 64 ≤ i)]
  by_cases h1 : shift < 64
  · simp only [h0, h1, ite_false, ite_true, UInt64.toNat_or, Nat.testBit_or,
      UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    have e1 : shift.toUInt64.toNat % 64 = shift := by simp; omega
    have e2 : (64 - shift).toUInt64.toNat % 64 = 64 - shift := by simp; omega
    rw [e1, e2]
    by_cases hi : i < 64
    · by_cases h3 : shift + i < 64
      · have : ¬ (i ≥ 64 - shift) := by omega
        simp [hi, h3, this]
      · have : (i ≥ 64 - shift) := by omega
        simp [hi, h3, this, testBit_word c.c0 (by omega : 64 ≤ shift + i)]
        congr 1; omega
    · simp [hi, testBit_word c.c0 (by omega : 64 ≤ shift + i)]
  by_cases h2 : shift < 128
  · simp only [h0, h1, h2, ite_false, ite_true, UInt64.toNat_shiftRight, Nat.testBit_shiftRight]
    have e1 : (shift - 64).toUInt64.toNat % 64 = shift - 64 := by simp; omega
    rw [e1]
    by_cases hi : i < 64
    · have : ¬ shift + i < 64 := by omega
      simp [hi, this]; congr 1; omega
    · simp [hi]
      exact testBit_word c.c1 (by omega)
  · simp only [h0, h1, h2, ite_false]
    have : ¬ shift + i < 64 := by omega
    simp [this, testBit_word c.c1 (by omega : 64 ≤ shift + i - 64)]

/-- **`queryBits`** is the statement's position, `depth ≤ 64`. -/
theorem queryBits_toNat (c : EW) (shift : ℕ) {depth : ℕ} (hd : depth ≤ 64) :
    (queryBits c shift depth).toNat = (Verifier.eToNat c.toE >>> shift) % 2 ^ depth := by
  have hX : Verifier.eToNat c.toE = 2 ^ 64 * c.c1.toNat + c.c0.toNat := by
    show c.c0.toNat + 2 ^ 64 * c.c1.toNat = _
    omega
  rw [hX]
  unfold queryBits
  by_cases h : 64 ≤ depth
  · simp only [h, ite_true]
    rw [queryWindow_toNat]
    have : depth = 64 := by omega
    subst this; rfl
  · simp only [h, ite_false]
    rw [UInt64.toNat_and, queryWindow_toNat]
    have hm : ((1 : UInt64) <<< depth.toUInt64 - 1).toNat = 2 ^ depth - 1 := by
      have h1 : ((1 : UInt64) <<< depth.toUInt64).toNat = 2 ^ depth := by
        rw [UInt64.toNat_shiftLeft, UInt64.toNat_one,
          show depth.toUInt64.toNat % 64 = depth by simp; omega, Nat.one_shiftLeft]
        exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
      rw [UInt64.toNat_sub_of_le _ _
        (UInt64.le_iff_toNat_le.mpr (by rw [h1]; exact Nat.one_le_two_pow)), h1]
      rfl
    rw [hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd]
    exact Nat.pow_dvd_pow 2 (by omega)

theorem ofBits_toNat (q : UInt64) : K.ofBits q.toNat = K.ofLane q := by
  simp [K.ofBits, K.ofLane]

theorem Array.getD_eq_toList_getD {α : Type} (a : Array α) (i : ℕ) (d : α) :
    a.getD i d = a.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem toList_extract_end {α : Type} (a : Array α) (k : ℕ) :
    (a.extract k a.size).toList = a.toList.drop k := by
  rw [Array.toList_extract, List.extract_eq_take_drop,
    List.take_of_length_le (l := List.drop _ _) (by simp)]

theorem toList_extract_zero {α : Type} (a : Array α) (k : ℕ) :
    (a.extract 0 k).toList = a.toList.take k := by
  rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]

/-! ## Rows and folds -/

theorem extRow_aux : ∀ l : List UInt64,
    (List.range (l.length / 2)).map (fun i ↦ (⟨l.getD (2 * i) 0, l.getD (2 * i + 1) 0⟩ : EW).toE) =
      Verifier.extRow (l.map K.ofLane)
  | [] => rfl
  | [_] => by simp [Verifier.extRow]
  | a :: b :: l => by
    rw [show (a :: b :: l).length / 2 = l.length / 2 + 1 by simp; omega, List.range_succ_eq_map,
      List.map_cons, List.map_map, List.map_cons, List.map_cons, Verifier.extRow, ← extRow_aux l]
    refine congrArg₂ _ rfl (List.map_congr_left fun i _ ↦ ?_)
    simp only [Function.comp_apply, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getD_cons_succ]

theorem toList_map_extRow (row : Array UInt64) :
    (Model.extRow row).toList.map EW.toE = Verifier.extRow (row.toList.map K.ofLane) := by
  rw [← extRow_aux, Model.extRow, Array.toList_map, Array.toList_range, List.map_map,
    ← Array.length_toList]
  simp only [Function.comp_def, Array.getD_eq_toList_getD]

/-- A fold round's challenges. -/
def _root_.NativeVm.Model.FoldRoundW.toSpec (r : FoldRoundW) : Verifier.FoldRound := ⟨r.alpha.toE, r.beta.toE⟩

theorem foldLanes_aux (x : UInt64) (round : FoldRoundW) : ∀ l : List EW,
    (List.range (l.length / 2)).map (fun i ↦
      (l.getD (2 * i + 1) 0 + (round.alpha + EW.scale x round.beta) * l.getD (2 * i) 0).toE) =
      Verifier.foldLanes (K.ofLane x) round.toSpec (l.map EW.toE)
  | [] => rfl
  | [_] => by simp [Verifier.foldLanes]
  | a :: b :: l => by
    rw [show (a :: b :: l).length / 2 = l.length / 2 + 1 by simp; omega, List.range_succ_eq_map,
      List.map_cons, List.map_map, List.map_cons, List.map_cons, Verifier.foldLanes,
      ← foldLanes_aux x round l]
    refine congrArg₂ _ ?_ (List.map_congr_left fun i _ ↦ ?_)
    · simp only [FoldRoundW.toSpec, EW.toE_add, EW.toE_mul, EW.toE_scale,
        List.getD_cons_succ, mul_comm (ofK _)]
      rfl
    · simp only [Function.comp_apply, show 2 * (i + 1) = 2 * i + 1 + 1 by omega,
        List.getD_cons_succ]

theorem toList_map_foldLanes (x : UInt64) (round : FoldRoundW) (values : Array EW) :
    (Model.foldLanes x round values).toList.map EW.toE =
      Verifier.foldLanes (K.ofLane x) round.toSpec (values.toList.map EW.toE) := by
  rw [← foldLanes_aux, Model.foldLanes, Array.toList_map, Array.toList_range, List.map_map,
    ← Array.length_toList]
  simp only [Function.comp_def, Array.getD_eq_toList_getD]

theorem toE_foldRow (values : Array EW) (x : UInt64) (rounds : Array FoldRoundW) :
    (Model.foldRow values x rounds).toE =
      Verifier.foldRow (values.toList.map EW.toE) (K.ofLane x) (rounds.toList.map FoldRoundW.toSpec) := by
  unfold Model.foldRow Verifier.foldRow
  rw [← Array.foldl_toList, getD_map EW.toE, EW.toE_zero,
    foldl_hom (fun v : Array EW ↦ v.toList.map EW.toE) FoldRoundW.toSpec
      (g := fun values round ↦ Verifier.foldLanes (K.ofLane x) round values)
      (fun a b ↦ toList_map_foldLanes x b a)]
  generalize List.foldl _ _ _ = l
  cases l <;> rfl

/-! ## The subspace polynomials -/

theorem subspaceRootsAux_nil : ∀ (n : ℕ) (last : K), Verifier.subspaceRootsAux n last [] = []
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem subspaceRoots_fold
    {step : Array UInt64 × UInt64 × Array UInt64 → ℕ → Array UInt64 × UInt64 × Array UInt64}
    (hnil : ∀ roots last layer x, (layer.map fun v ↦ kmul v v ^^^ kmul last v).toList = [] →
      step (roots, last, layer) x = (roots, last, #[]))
    (hcons : ∀ roots last layer x root rest,
      (layer.map fun v ↦ kmul v v ^^^ kmul last v).toList = root :: rest →
      step (roots, last, layer) x = (roots.push root, root, rest.toArray)) :
    ∀ (l : List ℕ) (roots : Array UInt64) (last : UInt64) (layer : Array UInt64),
    (l.foldl step (roots, last, layer)).1.toList.map K.ofLane =
      roots.toList.map K.ofLane ++
        Verifier.subspaceRootsAux l.length (K.ofLane last) (layer.toList.map K.ofLane)
  | [], roots, _, _ => by simp [Verifier.subspaceRootsAux]
  | x :: l, roots, last, layer => by
    rw [List.foldl_cons, List.length_cons, Verifier.subspaceRootsAux]
    have hmap : (layer.toList.map K.ofLane).map (fun v ↦ v * v + K.ofLane last * v) =
        (layer.map fun v ↦ kmul v v ^^^ kmul last v).toList.map K.ofLane := by
      simp [Function.comp_def, K_ofLane_xor, K_ofLane_kmul]
    rw [hmap]
    cases h : (layer.map fun v ↦ kmul v v ^^^ kmul last v).toList with
    | nil =>
      rw [hnil roots last layer x h, subspaceRoots_fold hnil hcons l roots last #[]]
      simp [subspaceRootsAux_nil]
    | cons root rest =>
      rw [hcons roots last layer x root rest h, subspaceRoots_fold hnil hcons l]
      simp

theorem toList_map_subspaceRoots (logN : ℕ) :
    (Model.subspaceRoots logN).toList.map K.ofLane = Verifier.subspaceRoots logN := by
  unfold Model.subspaceRoots Verifier.subspaceRoots
  dsimp only
  rw [subspaceRoots_fold (fun _ _ _ _ h ↦ by simp only [h]) (fun _ _ _ _ _ _ h ↦ by simp only [h]),
    List.length_range]
  simp only [Array.toList_map, Array.toList_range, List.map_map, Function.comp_def]
  exact congrArg₂ _ rfl rfl

theorem toList_map_subspaceTable (mu : ℕ) :
    (Model.subspaceTable mu).toList.map (fun p ↦ (K.ofLane p.1, K.ofLane p.2)) =
      (Verifier.subspaceRoots mu).map fun root ↦ (root, root⁻¹) := by
  rw [← toList_map_subspaceRoots, Model.subspaceTable, Array.toList_map, List.map_map,
    List.map_map]
  simp [Function.comp_def, K_ofLane_kinv]

theorem subspaceAt_fold : ∀ (l : List (UInt64 × UInt64)) (out : Array UInt64) (w : UInt64),
    (l.foldl (fun (acc : Array UInt64 × UInt64) (root, inverse) ↦
      (acc.1.push (kmul acc.2 inverse), kmul acc.2 acc.2 ^^^ kmul root acc.2)) (out, w)).1.toList.map
        K.ofLane =
      out.toList.map K.ofLane ++
        Verifier.subspaceAtAux (l.map fun p ↦ (K.ofLane p.1, K.ofLane p.2)) (K.ofLane w)
  | [], out, _ => by simp [Verifier.subspaceAtAux]
  | (root, inverse) :: l, out, w => by
    rw [List.foldl_cons, List.map_cons, Verifier.subspaceAtAux, subspaceAt_fold l]
    simp [K_ofLane_xor, K_ofLane_kmul]

theorem toList_map_subspaceAtTable (table : Array (UInt64 × UInt64)) (x : UInt64) :
    (Model.subspaceAtTable table x).toList.map K.ofLane =
      Verifier.subspaceAtAux (table.toList.map fun p ↦ (K.ofLane p.1, K.ofLane p.2)) (K.ofLane x) := by
  unfold Model.subspaceAtTable
  rw [← Array.foldl_toList, subspaceAt_fold]
  rfl

/-- **`subspaceAt` from the level's table** is the statement's, rebuilt per call. -/
theorem toList_map_subspaceAt (mu : ℕ) (x : UInt64) :
    (Model.subspaceAt mu x).toList.map K.ofLane = Verifier.subspaceAt mu (K.ofLane x) := by
  rw [Model.subspaceAt, toList_map_subspaceAtTable, toList_map_subspaceTable]
  rfl

theorem toList_map_novelBasis (what : Array UInt64) (count : ℕ) :
    (Model.novelBasis what count).toList.map K.ofLane =
      Verifier.novelBasis (what.toList.map K.ofLane) count := by
  unfold Model.novelBasis Verifier.novelBasis
  rw [toList_extract_zero, List.map_take, ← Array.foldl_toList,
    foldl_hom (fun v : Array UInt64 ↦ v.toList.map K.ofLane) K.ofLane
      (g := fun basis value ↦ if count ≤ basis.length then basis else basis ++ basis.map (· * value))
      (fun a b ↦ by split <;> simp_all [Function.comp_def, K_ofLane_kmul])]
  rfl

theorem toE_novelEval (coefficients : Array EW) (what : Array UInt64) :
    (Model.novelEval coefficients what).toE =
      Verifier.novelEval (coefficients.toList.map EW.toE) (what.toList.map K.ofLane) := by
  unfold Model.novelEval Verifier.novelEval
  rw [toE_sumE, Array.toList_zipWith, List.map_zipWith, List.length_map, Array.length_toList,
    ← toList_map_novelBasis, List.zipWith_map]
  simp [EW.toE_scale, mul_comm]

theorem toE_inducedWeight (mu : ℕ) (queries : Array UInt64) (weights point : Array EW) :
    (Model.inducedWeight mu queries weights point).toE =
      Verifier.inducedWeight mu (queries.toList.map UInt64.toNat) (weights.toList.map EW.toE)
        (point.toList.map EW.toE) := by
  unfold Model.inducedWeight Verifier.inducedWeight
  rw [← Array.foldl_toList, Array.toList_zip, List.zip_map,
    foldl_hom EW.toE (Prod.map EW.toE UInt64.toNat)
      (g := fun total (weight, query) ↦
        total + (List.zip (point.toList.map EW.toE) (Verifier.subspaceAt mu (K.ofBits query))).foldl
          (fun product (challenge, value) ↦ product * (1 + challenge * ofK (1 + value))) weight)]
  · rfl
  intro total ⟨weight, query⟩
  simp only [Prod.map, EW.toE_add, ofBits_toNat]
  rw [← toList_map_subspaceAt, ← Array.foldl_toList, Array.toList_zip, List.zip_map,
    foldl_hom EW.toE (Prod.map EW.toE K.ofLane)
      (g := fun product (challenge, value) ↦ product * (1 + challenge * ofK (1 + value)))]
  intro product ⟨challenge, value⟩
  simp [EW.toE_scale, K_ofLane_xor, K_ofLane_one, mul_comm]

/-! ## The weights as data -/

/-- A glued claim's weight evaluates as the statement's function at every point of words. -/
def _root_.NativeVm.Model.GluedWeight.Rel (w : GluedWeight) (f : List E → E) : Prop :=
  ∀ x : Array EW, (w.eval x).toE = f (x.toList.map EW.toE)

/-- A glued claim is the statement's. -/
structure _root_.NativeVm.Model.GluedClaimW.Rel (g : GluedClaimW) (g' : Verifier.GluedClaim) : Prop where
  scalar : g.scalar.toE = g'.scalar
  foldStart : g.foldStart = g'.foldStart
  weight : g.weight.Rel g'.weightAt

/-- `evaluateBasis` as data evaluates as the statement's function at every point of words. -/
def _root_.NativeVm.Model.BasisW.Rel (b : BasisW) (f : List E → E) : Prop :=
  ∀ x : Array EW, (b.eval x).toE = f (x.toList.map EW.toE)

theorem _root_.NativeVm.Model.GluedWeight.rel_eq (p : Array EW) :
    (GluedWeight.eq p).Rel fun x ↦ Verifier.eqEval (p.toList.map EW.toE) x :=
  fun x ↦ toE_eqEval p x

theorem _root_.NativeVm.Model.GluedWeight.rel_induced (mu : ℕ) (queries : Array UInt64) (weights : Array EW) :
    (GluedWeight.induced mu queries weights).Rel
      (Verifier.inducedWeight mu (queries.toList.map UInt64.toNat) (weights.toList.map EW.toE)) :=
  fun x ↦ toE_inducedWeight mu queries weights x

theorem _root_.NativeVm.Model.BasisW.rel_mk {scales : Array EW} {claims : Array StackClaimW} {scales' : List E}
    {claims' : List Verifier.StackClaim} (hs : scales.toList.map EW.toE = scales')
    (hc : List.Forall₂ StackClaimW.Rel claims.toList claims') :
    BasisW.Rel ⟨scales, claims⟩ fun point ↦ Verifier.dot scales' (claims'.map fun c ↦ c.1 point) := by
  intro x
  rw [BasisW.eval, toE_dot, hs, Array.toList_map, List.map_map]
  congr 1
  generalize claims.toList = l at hc ⊢
  induction hc with
  | nil => rfl
  | cons h _ ih => exact congrArg₂ _ (h.1 x) ih

/-- The level loop's state is the statement's. -/
structure _root_.NativeVm.Model.WhirStateW.Rel (s : WhirStateW) (s' : Verifier.WhirState) : Prop where
  claim : s.claim.toE = s'.claim
  alphas : s.alphas.toList.map EW.toE = s'.alphas
  glued : List.Forall₂ GluedClaimW.Rel s.glued.toList s'.glued

end NativeVm.Equiv
