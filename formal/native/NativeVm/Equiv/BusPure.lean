module

public import NativeVm.Equiv.FormFacts
public import NativeVm.Equiv.LayoutSpec
public import NativeVm.Equiv.StackOffsets
public import NativeVm.Model.Bus

/-!
# The bus phase's pure steps are the statement's

The leaf decomposition of `verifyBusBalance` (`NativeVm/Model/Bus.lean`) through the maps of words
to values: `busLayout` is the statement's (`busLayout_toSpec`, by `stackOffsets_toSpec`),
`blockForm` (`blockForm_toSpec`), the side's fold `accumulateSide` with the forms per table and side
(`formsToSpec`) and the side's total (`accumulateSide_toSpec`, and `accumulateSide_eq` to rewrite
the statement's call), and the framework `fingerprints` (`fingerprints_toSpec`). A table's padding
row in the model is the statement's (`tablesW_padding`): `tablesW` holds each table's `padding` as
lanes, and the default table has no column.
-/

@[expose] public section

namespace NativeVm.Model

open NativeVm.Equiv LeanVM.Parameters LeanVM.Protocol

/-- A side's placements as the statement's `BusLayout`. -/
def BusLayoutW.toSpec (l : BusLayoutW) : Verifier.BusLayout :=
  ⟨l.depth, l.framework.toList, l.tables.toList⟩

/-- The forms per table and side as the statement's. -/
def formsToSpec (forms : Array (Array FormW)) : List (List Verifier.Form) :=
  forms.toList.map fun row ↦ row.toList.map FormW.toForm

/-- The bus phase's result as the statement's. -/
def BusResultW.toSpec (r : BusResultW) : Verifier.BusResult :=
  ⟨r.claims.toList.map ColumnClaimW.toSpec, r.bytecodePoint.toList.map EW.toE,
    r.point.toList.map EW.toE, formsToSpec r.forms, r.totals.toList.map EW.toE⟩

/-- An entry read through `EW.toE`, a missing one `0`. -/
theorem getD_toE (xs : Array EW) (i : ℕ) :
    (xs.toList.map EW.toE).getD i 0 = (xs.getD i 0).toE := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  rcases xs[i]? <;> simp

private theorem map_modify_of_comm {α β : Type} (g : α → β) (f : α → α) (f' : β → β)
    (h : ∀ a, g (f a) = f' (g a)) :
    ∀ (l : List α) (i : ℕ), (l.modify i f).map g = (l.map g).modify i f'
  | [], _ => by simp
  | a :: l, 0 => by simp [List.modify_zero_cons, h]
  | a :: l, i + 1 => by simp [List.modify_succ_cons, map_modify_of_comm g f f' h l i]

theorem busLayout_toSpec (fr : Array ℕ) (blocks : Array BusBlockW) :
    (busLayout fr blocks).toSpec =
      Verifier.busLayout fr.toList (blocks.toList.map BusBlockW.toSpec) := by
  have hs : (fr ++ blocks.map (·.logRows)).toList =
      fr.toList ++ (blocks.toList.map BusBlockW.toSpec).map (·.logRows) := by
    simp [BusBlockW.toSpec]
  obtain ⟨h1, h2⟩ := stackOffsets_toSpec (fr ++ blocks.map (·.logRows))
  rw [hs] at h1 h2
  unfold busLayout Verifier.busLayout BusLayoutW.toSpec
  simp only [Array.toList_extract, List.extract_eq_take_drop, Array.toList_zipWith, hs, h1, h2,
    Nat.sub_zero, List.drop_zero, Array.size_eq_length_toList, List.length_zipWith]
  congr 1
  exact List.take_of_length_le (by simp)

/-- `Placement::eq_above` (the same lemma as `RingSwitch`'s, kept here so the bus's pure steps do
not import the ring switch). -/
private theorem toE_eqAbove' (p : Verifier.Placement) (pt : Array EW) :
    (eqAbove p pt).toE = p.eqAbove (pt.toList.map EW.toE) := by
  unfold eqAbove Verifier.Placement.eqAbove
  rw [toE_eqEval, toList_map_selectorPoint, Array.toList_extract, List.extract_eq_take_drop,
    List.map_take, List.map_drop, List.take_of_length_le (by simp)]
  simp

theorem blockForm_toSpec (b : BusBlockW) (ws : Array EW) (β : EW) :
    (blockForm b ws β).toForm = Verifier.blockForm b.toSpec (ws.toList.map EW.toE) β.toE := by
  unfold blockForm Verifier.blockForm
  rw [← Array.foldl_toList, Array.toList_zipIdx, ← FormW.toForm_const]
  simp only [BusBlockW.toSpec, List.zipIdx_map, List.foldl_map]
  refine (List.foldl_hom FormW.toForm ?_).symm
  rintro g ⟨c, k⟩
  simp only [Prod.map, id, FormW.toForm_addScaled]
  congr 1
  exact getD_toE ws k

/-- A table's padding row: the default table has no column. -/
theorem tablesW_padding (o : ℕ) :
    (tablesW.getD o default).padding.toList.map EW.toE =
      (Verifier.tables.getD o default).padding := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  unfold tablesW
  rw [Array.getElem?_map, List.getElem?_toArray]
  rcases Verifier.tables[o]? with _ | t
  · simp only [Option.map_none, Option.getD_none]
    simp [Verifier.Table.padding, Verifier.Table.width]
    rfl
  · simp [TableW.ofTable, Function.comp_def]

theorem accumulateSide_toSpec (forms : Array (Array FormW)) (side : ℕ) (blocks : Array BusBlockW)
    (L : BusLayoutW) (ffp ws : Array EW) (β : EW) (point : Array EW) (tv : EW) :
    (formsToSpec (accumulateSide forms side blocks L ffp ws β point tv).1,
      (accumulateSide forms side blocks L ffp ws β point tv).2.toE) =
    Verifier.accumulateSide (formsToSpec forms) side (blocks.toList.map BusBlockW.toSpec) L.toSpec
      (ffp.toList.map EW.toE) (ws.toList.map EW.toE) β.toE (point.toList.map EW.toE) tv.toE := by
  have hsel : ∀ ps : Array Verifier.Placement,
      ps.toList.map (·.eqAbove (point.toList.map EW.toE)) =
        (ps.map (eqAbove · point)).toList.map EW.toE := by
    intro ps; simp [toE_eqAbove']
  unfold accumulateSide Verifier.accumulateSide
  simp only [BusLayoutW.toSpec, hsel, List.zip_map, List.foldl_map]
  rw [← Array.foldl_toList, Array.toList_zip, show ((formsToSpec forms, (0 : E))) =
    (fun x : Array (Array FormW) × EW ↦ (formsToSpec x.1, x.2.toE)) (forms, 0) by simp]
  rw [List.foldl_hom (fun x : Array (Array FormW) × EW ↦ (formsToSpec x.1, x.2.toE))
    (g₁ := fun (acc : Array (Array FormW) × EW) (x : EW × BusBlockW) ↦
      (acc.1.modify x.2.owner fun row ↦
          row.modify side fun f ↦ f.addScaled (blockForm x.2 ws β) x.1,
        acc.2 + x.1 * paddingWeight (point.extract 0 x.2.logRows) x.2.rows *
          ((blockForm x.2 ws β).evaluate (tablesW[x.2.owner]?.getD default).padding + 1)))]
  · simp [toE_dot, toE_sumE, Function.comp_def]
  · rintro ⟨fs, pr⟩ ⟨sel, b⟩
    simp only [Prod.map]
    refine Prod.ext ?_ ?_
    · simp only [formsToSpec, Array.toList_modify]
      refine (map_modify_of_comm _ _ _ (fun row ↦ ?_) _ _).symm
      simp only [Array.toList_modify]
      refine map_modify_of_comm _ _ _ (fun f ↦ ?_) _ _
      rw [FormW.toForm_addScaled, blockForm_toSpec]
    · have hp := tablesW_padding b.owner
      rw [Array.getD_eq_getD_getElem?] at hp
      simp only [EW.toE_add, EW.toE_mul, EW.toE_one, toE_paddingWeight, FormW.toE_evaluate,
        blockForm_toSpec, hp, Array.toList_extract, List.extract_eq_take_drop, List.drop_zero,
        Nat.sub_zero, List.map_take]
      rfl

/-- `accumulateSide_toSpec`, to rewrite the statement's call on arguments related to the model's. -/
theorem accumulateSide_eq {forms : Array (Array FormW)} {side : ℕ} {blocks : Array BusBlockW}
    {L : BusLayoutW} {ffp ws : Array EW} {β : EW} {point : Array EW} {tv : EW}
    {forms' : List (List Verifier.Form)} {blocks' : List Verifier.BusBlock}
    {L' : Verifier.BusLayout} {ffp' ws' : List E} {β' : E} {point' : List E} {tv' : E}
    (h1 : formsToSpec forms = forms') (h2 : blocks.toList.map BusBlockW.toSpec = blocks')
    (h3 : L.toSpec = L') (h4 : ffp.toList.map EW.toE = ffp') (h5 : ws.toList.map EW.toE = ws')
    (h6 : β.toE = β') (h7 : point.toList.map EW.toE = point') (h8 : tv.toE = tv') :
    Verifier.accumulateSide forms' side blocks' L' ffp' ws' β' point' tv' =
      (formsToSpec (accumulateSide forms side blocks L ffp ws β point tv).1,
        (accumulateSide forms side blocks L ffp ws β point tv).2.toE) := by
  subst h1 h2 h3 h4 h5 h6 h7 h8
  exact (accumulateSide_toSpec ..).symm

theorem fingerprints_toSpec (w m ml bl : Array EW) (s pc mc bc : EW) :
    (fingerprints w m ml bl s pc mc bc).toList.map EW.toE =
      Verifier.fingerprints (w.toList.map EW.toE) (m.toList.map EW.toE) (ml.toList.map EW.toE)
        (bl.toList.map EW.toE) s.toE pc.toE mc.toE bc.toE := by
  simp [fingerprints, Verifier.fingerprints, toE_dot, toE_indexMle, Array.toList_extract,
    List.extract_eq_take_drop, sepStateW, sepMemW, sepBytecodeW, Verifier.sepState,
    Verifier.sepMem, Verifier.sepBytecode, toE_gen, toE_gpow, Verifier.gpow]

end NativeVm.Model
