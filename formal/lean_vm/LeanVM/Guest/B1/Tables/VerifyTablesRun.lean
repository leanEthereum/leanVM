/-
  LeanVM.Guest.B1.Tables.VerifyTablesRun

  The specification's run of `tablesSeg`, piece by piece: the bus after GKR, the table
  sumcheck's terms, the public input's binding.
-/

module

public import LeanVM.Guest.B1.Tables.GkrBase

/-!
# The run of `tablesSeg`

`busRest` reads five words and asks `ev` for the bytecode's value: its run gives `busVal`
(`runsTo_busRest`). `tableTerms` reads each table's evaluations: its run gives `ttVal`
(`runsTo_tableTerms`). `publicInputPhase` reads nothing.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `busRest`'s result from the words it reads and the bytecode's value. -/
def busVal (layout : Layout) (alphas : List E) (beta : E) (point treeValues : List E)
    (memory : List E) (memoryFinal bytecodeFinal bytecodeValue : E) : BusResult :=
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let weights := eqKernel alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let finalPc := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp finalPc memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  ⟨claims, point, forms3, [total0, total1, total2]⟩

theorem runsTo_bytecodeAt {ev : Evaluations} {words : List K} {point : List E} {value : E}
    (h : BytecodeAt ev words point value) (cv : Digest) :
    RunsTo (ev.bytecode words point) cv [] value cv := fun _ _ _ => h _

/-- **`busRest`'s run**: the three memory limbs and the two final counters read, the bytecode's
value from `ev`. -/
theorem runsTo_busRest {ev : Evaluations} {layout : Layout} {alphas : List E} {beta : E}
    {point treeValues : List E} {cv : Digest} {memory : List E} (hm : memory.length = 3)
    {memoryFinal bytecodeFinal bytecodeValue : E}
    (hbv : BytecodeAt ev layout.bytecode (point.take layout.logBytecode ++ alphas) bytecodeValue) :
    RunsTo (busRest ev layout alphas beta point treeValues) cv (memory ++ [memoryFinal, bytecodeFinal])
      (busVal layout alphas beta point treeValues memory memoryFinal bytecodeFinal bytecodeValue)
      (obsAll cv (memory ++ [memoryFinal, bytecodeFinal])) := by
  have h : RunsTo (busRest ev layout alphas beta point treeValues) cv
      (memory ++ ([memoryFinal] ++ ([bytecodeFinal] ++ ([] ++ []))))
      (busVal layout alphas beta point treeValues memory memoryFinal bytecodeFinal bytecodeValue)
      (obsCv (obsCv (obsAll cv memory) memoryFinal) bytecodeFinal) := by
    unfold busRest
    refine (runsTo_readN_of_length _ hm).bind ?_
    refine (runsTo_readE _ _).bind ?_
    refine (runsTo_readE _ _).bind ?_
    refine (runsTo_bytecodeAt hbv _).bind ?_
    exact runsTo_ret _ _
  exact h.of_eq (by simp) rfl (by simp [obsAll, List.foldl_append])

/-- `tableTerms`' result from the evaluations it reads, table by table. -/
def ttVal (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → List (List E) → ℕ → E → List ColumnClaim →
      E × List ColumnClaim
  | [], _, _, final, claims => (final, claims)
  | (table, height, forms, weight) :: rest, evs :: evss, cursor, final, claims =>
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evs)
    ttVal constraintPowers formPowers point rest evss (cursor + table.nConstraints)
      (final + weight * (summand + dot formPowers (forms.map (·.evaluate (evs.getD · 0)))))
      (claims ++ evs.zipIdx.map fun (value, column) ↦
        ⟨globalColumnBases.getD table.opcode 0 + column, point.take height, value⟩)
  | _ :: _, [], _, final, claims => (final, claims)

/-- **`tableTerms`' run**: table `i` reads its `width` evaluations `evss[i]`. -/
theorem runsTo_tableTerms (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evss : List (List E)), evss.length = rows.length →
      (∀ i (hi : i < rows.length) (he : i < evss.length), evss[i].length = rows[i].1.width) →
      ∀ (cursor : ℕ) (final : E) (claims : List ColumnClaim) (cv : Digest),
      RunsTo (tableTerms constraintPowers formPowers point rows cursor final claims) cv evss.flatten
        (ttVal constraintPowers formPowers point rows evss cursor final claims)
        (obsAll cv evss.flatten)
  | [], [], _, _, cursor, final, claims, cv => runsTo_ret _ _
  | (table, height, forms, weight) :: rest, evs :: evss, hl, hw, cursor, final, claims, cv => by
    have hw0 := hw 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at hw0
    have ih := runsTo_tableTerms constraintPowers formPowers point rest evss (by simpa using hl)
      (fun i hi he => by have := hw (i + 1) (by simp; omega) (by simp; omega); simpa using this)
    unfold tableTerms
    refine ((runsTo_readN_of_length cv hw0).bind (ih _ _ _ _)).of_eq (by simp) rfl ?_
    simp [obsAll, List.foldl_append]

/-- **`tableSumcheck`'s run**: its rounds, then each table's evaluations, the terms' sum the
rounds' final claim. -/
theorem runsTo_tableSumcheck {heights : List ℕ} {busForms : List (List Form)}
    {constraintPowers formPowers equalityPoint : List E} {target : E} {cv cv1 : Digest}
    {ws rs : List E} {cl : E}
    (hsc : RunsTo (sumcheck target 4 (List.replicate (heights.foldl max 0) none)) cv ws (rs, cl) cv1)
    {evss : List (List E)}
    (hl : evss.length = (List.zip tables (List.zip heights (List.zip busForms
      (tableWeights heights equalityPoint rs.reverse)))).length)
    (hw : ∀ i (hi : i < (List.zip tables (List.zip heights (List.zip busForms
      (tableWeights heights equalityPoint rs.reverse)))).length) (he : i < evss.length),
      evss[i].length = (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint rs.reverse))))[i].1.width)
    (hfin : (ttVal constraintPowers formPowers rs.reverse (List.zip tables (List.zip heights
      (List.zip busForms (tableWeights heights equalityPoint rs.reverse)))) evss 0 0 []).1 = cl) :
    RunsTo (tableSumcheck heights busForms constraintPowers formPowers equalityPoint target) cv
      (ws ++ evss.flatten)
      (ttVal constraintPowers formPowers rs.reverse (List.zip tables (List.zip heights
        (List.zip busForms (tableWeights heights equalityPoint rs.reverse)))) evss 0 0 []).2
      (obsAll cv1 evss.flatten) := by
  refine RunsTo.of_eq (xs := ws ++ (evss.flatten ++ ([] ++ []))) ?_ (by simp) rfl rfl
  unfold tableSumcheck
  refine hsc.bind ?_
  refine (runsTo_tableTerms constraintPowers formPowers rs.reverse _ evss hl hw 0 0 [] cv1).bind ?_
  refine (runsTo_require hfin _).bind ?_
  exact runsTo_ret _ _

/-- **`tablePhase`'s run**: `ξ` squeezed, then the table sumcheck from the bus's target. -/
theorem runsTo_tablePhase {layout : Layout} {bus : BusResult} {cv cv' : Digest} {xs : List E}
    {tc : List ColumnClaim}
    (h : RunsTo (tableSumcheck layout.tableLogHeights bus.forms
      ((powers (challengeOf (sqCv cv)) ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers (challengeOf (sqCv cv)) ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) bus.point
      (dot ((powers (challengeOf (sqCv cv)) ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) bus.totals)) (sqCv cv) xs tc cv') :
    RunsTo (tablePhase layout bus) cv xs (bus.claims ++ tc) cv' := by
  refine RunsTo.of_eq (xs := [] ++ (xs ++ [])) ?_ (by simp) rfl rfl
  unfold tablePhase
  refine (runsTo_sampleE cv).bind ?_
  refine h.bind ?_
  exact runsTo_ret _ _

/-- `publicInputPhase`'s claims at the challenge `rm`. -/
def piClaims (layout : Layout) (publicInput : Digest) (rm : E) : List ColumnClaim :=
  let halves := digestScalars publicInput
  let publicLimbs := ([0, 1, 2] : List (Fin 3)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [rm]
  let publicPoint := rm :: List.replicate ((layout.placements.getD memory0 default).vars - 1) 0
  List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩) [memory0, memory1, memory2]
    publicLimbs

theorem runsTo_publicInputPhase (layout : Layout) (publicInput : Digest) (cv : Digest) :
    RunsTo (publicInputPhase layout publicInput) cv []
      (piClaims layout publicInput (challengeOf (sqCv cv))) (sqCv cv) := by
  refine RunsTo.of_eq (xs := [] ++ []) ?_ rfl rfl rfl
  unfold publicInputPhase
  refine (runsTo_sampleE cv).bind ?_
  exact runsTo_ret _ _

/-- **`tablesSeg`'s run**, from its three phases'. -/
theorem runsTo_tablesSeg {ev : Evaluations} {layout : Layout} {publicInput : Digest}
    {alphas : List E} {beta : E} {point treeValues : List E} {cv cv1 cv2 : Digest}
    {xs ys : List E} {bus : BusResult} {tc : List ColumnClaim}
    (h1 : RunsTo (busRest ev layout alphas beta point treeValues) cv xs bus cv1)
    (h2 : RunsTo (tablePhase layout bus) cv1 ys tc cv2) :
    RunsTo (tablesSeg ev layout publicInput alphas beta point treeValues) cv (xs ++ ys)
      (bus, tc ++ piClaims layout publicInput (challengeOf (sqCv cv2))) (sqCv cv2) := by
  refine RunsTo.of_eq (xs := xs ++ (ys ++ ([] ++ []))) ?_ (by simp) rfl rfl
  unfold tablesSeg
  refine h1.bind ?_
  refine h2.bind ?_
  refine (runsTo_publicInputPhase layout publicInput cv2).bind ?_
  exact runsTo_ret _ _

end
end LeanVM.Guest.B1.VerifySub
