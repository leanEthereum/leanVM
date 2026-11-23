module

public import NativeVm.Equiv.TablesPure
public import NativeVm.Equiv.Transcript

/-!
# Phase 4: the table sumcheck

`Sim.tablePhase`: the model's `tablePhase` simulates the statement's on the layout and the bus
result read as the statement's (`LayoutW.toSpec`, `BusResultW.toSpec`), each table's point and
evaluations related by `convEval`. The tables' loop (`Sim.tableTerms_loop`) runs over one list
of the statement's tables, heights, forms and weights, read by `TableW.ofTable` on the model's side
and through `FormW.toForm` and `EW.toE` on the statement's; the claims are then
`tableColumnClaims_toSpec` (`NativeVm/Equiv/TablesPure.lean`).
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- The tables' loop from a cursor, a running sum and the rows collected so far. -/
theorem Sim.tableTerms_loop (cp fp pt : Array EW) :
    ∀ (L : List (Verifier.Table × ℕ × Array FormW × EW)), (∀ x ∈ L, x.1 ∈ Verifier.tables) →
    ∀ (cursor : ℕ) (final : EW) (out : Array (Array EW × Array EW)),
    Sim ((L.map fun x ↦ (TableW.ofTable x.1, x.2.1, x.2.2.1, x.2.2.2)).foldlM
        (tableTermsStep cp fp pt) (cursor, final, out))
      (Verifier.tableTerms (cp.toList.map EW.toE) (fp.toList.map EW.toE) (pt.toList.map EW.toE)
        (L.map fun x ↦ (x.1, x.2.1, x.2.2.1.toList.map FormW.toForm, x.2.2.2.toE)) cursor final.toE)
      (fun a b ↦ a.2.1.toE = b.1 ∧ a.2.2.toList.map convEval = out.toList.map convEval ++ b.2)
  | [], _, cursor, final, out => Sim.pure ⟨rfl, by simp⟩
  | ⟨t, h, forms, w⟩ :: L, hL, cursor, final, out => by
    simp only [List.map_cons, List.foldlM_cons, tableTermsStep, Verifier.tableTerms, bind_assoc,
      pure_bind]
    have ht : t ∈ Verifier.tables := hL _ (List.mem_cons_self ..)
    refine Sim.bind (Sim.readScalars _) fun ev ev' ⟨hev, _⟩ ↦ ?_
    subst hev
    have hfin : (final + w * (dot (cp.extract cursor (cursor + (TableW.ofTable t).nConstraints))
        (constraintsW (TableW.ofTable t).opcode ev) +
          dot fp (Array.map (fun x ↦ x.evaluate ev) forms))).toE =
        final.toE + w.toE * (Verifier.dot (List.take t.nConstraints
            (List.drop cursor (List.map EW.toE cp.toList))) (t.constraints (ev.toList.map EW.toE)) +
          Verifier.dot (List.map EW.toE fp.toList)
            (List.map (fun x ↦ x.evaluate fun x ↦ (ev.toList.map EW.toE).getD x 0)
              (List.map FormW.toForm forms.toList))) := by
      simp only [EW.toE_add, EW.toE_mul, toE_dot, toList_extract', Nat.add_sub_cancel_left,
        List.map_take, List.map_drop, TableW.ofTable]
      rw [constraintsW_toSpec ht]
      simp [Function.comp_def, FormW.toE_evaluate]
    rw [← hfin, ← bind_pure (List.foldlM _ _ _)]
    refine Sim.bind (Sim.tableTerms_loop cp fp pt L (fun x hx ↦ hL x (List.mem_cons_of_mem _ hx))
      _ _ _) fun a b hab ↦ Sim.pure ⟨hab.1, ?_⟩
    rw [hab.2]
    simp [convEval]

/-- `tableSumcheck`. -/
theorem Sim.tableSumcheck (heights : Array ℕ) (busForms : Array (Array FormW))
    (cp fp ep : Array EW) (target : EW) :
    Sim (Model.tableSumcheck heights busForms cp fp ep target)
      (Verifier.tableSumcheck heights.toList (formsToSpec busForms) (cp.toList.map EW.toE)
        (fp.toList.map EW.toE) (ep.toList.map EW.toE) target.toE)
      (fun a b ↦ a.toList.map convEval = b) := by
  unfold Model.tableSumcheck Verifier.tableSumcheck
  rw [← Array.foldl_toList]
  refine Sim.bind (Sim.sumcheckPlain rfl 4 _) fun ⟨chs, cl⟩ ⟨chs', cl'⟩ ⟨hch, hcl⟩ ↦ ?_
  simp only at hch hcl ⊢
  subst hch hcl
  have hw := tableWeights_toSpec heights ep chs.reverse
  rw [Array.toList_reverse, List.map_reverse] at hw
  rw [← hw]
  generalize tableWeights heights ep chs.reverse = W
  have hrowsW : (tablesW.zip (heights.zip (busForms.zip W))).toList =
      (Verifier.tables.zip (heights.toList.zip (busForms.toList.zip W.toList))).map
        fun x ↦ (TableW.ofTable x.1, x.2.1, x.2.2.1, x.2.2.2) := by
    simp [Array.toList_zip, tablesW_toList, List.zip_map_left]
  have hrowsS : Verifier.tables.zip (heights.toList.zip ((formsToSpec busForms).zip
      (W.toList.map EW.toE))) =
      (Verifier.tables.zip (heights.toList.zip (busForms.toList.zip W.toList))).map
        fun x ↦ (x.1, x.2.1, x.2.2.1.toList.map FormW.toForm, x.2.2.2.toE) := by
    simp [formsToSpec, List.zip_map_left, List.zip_map_right, List.map_map]
  have hmem : ∀ x ∈ Verifier.tables.zip (heights.toList.zip (busForms.toList.zip W.toList)),
      x.1 ∈ Verifier.tables := fun x hx ↦ (List.of_mem_zip hx).1
  unfold Model.tableTerms
  rw [← Array.foldlM_toList, hrowsW, hrowsS, ← EW.toE_zero]
  simp only [bind_assoc, pure_bind]
  rw [show (chs.toList.map EW.toE).reverse = chs.reverse.toList.map EW.toE by
    simp [Array.toList_reverse, List.map_reverse]]
  refine Sim.bind (Sim.tableTerms_loop cp fp chs.reverse _ hmem 0 0 #[])
    fun ⟨_, f, o⟩ ⟨f', rows⟩ hab ↦ ?_
  simp only at hab ⊢
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ Sim.pure ?_
  · rw [EW.beq_iff_toE, hab.1]
  · simpa [Array.toList_reverse, List.map_reverse] using hab.2

/-- **Phase 4** (`tablePhase`): each table's point and evaluations. -/
theorem Sim.tablePhase (layout : LayoutW) (bus : BusResultW) :
    Sim (Model.tablePhase layout bus) (Verifier.tablePhase layout.toSpec bus.toSpec)
      (fun a b ↦ a.toList.map convEval = b) := by
  unfold Model.tablePhase Verifier.tablePhase
  rw [nConstraints_eq]
  generalize (Verifier.tables.map Verifier.Table.nConstraints).sum = nC
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ Sim.bind Sim.sampleChallenge fun xi xi' hxi ↦ ?_
  subst hxi
  have hp := toList_map_powers xi (nC + Verifier.nTrees)
  have h1 : ((powers xi (nC + Verifier.nTrees)).extract 0 nC).toList.map EW.toE =
      (Verifier.powers xi.toE (nC + Verifier.nTrees)).take nC := by
    rw [← hp, toList_extract']; simp [List.map_take]
  have h2 : ((powers xi (nC + Verifier.nTrees)).extract nC
      (powers xi (nC + Verifier.nTrees)).size).toList.map EW.toE =
      (Verifier.powers xi.toE (nC + Verifier.nTrees)).drop nC := by
    rw [← hp, toList_extract']; simp [List.map_drop]
  have h3 : (dot ((powers xi (nC + Verifier.nTrees)).extract nC
      (powers xi (nC + Verifier.nTrees)).size) bus.totals).toE =
      Verifier.dot ((Verifier.powers xi.toE (nC + Verifier.nTrees)).drop nC) bus.toSpec.totals := by
    rw [toE_dot, h2]; rfl
  simp only []
  rw [← h3, ← h1, ← h2]
  exact Sim.tableSumcheck _ _ _ _ _ _

end NativeVm.Equiv
