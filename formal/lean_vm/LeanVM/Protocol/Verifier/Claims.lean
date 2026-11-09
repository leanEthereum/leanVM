/-
  LeanVM.Protocol.Verifier.Claims

  `verify_execution` with the column claims as one list that the Keccak phase filters, the form
  the proofs reason on, and its equality with the statement's `verifyExecution`.
-/

module

public import LeanVM.Protocol.Compile.Prog

/-!
# The claim-list form of `verify_execution`

`Statement/LeanVmVerifier.lean` transcribes steps 4 to 7 of `verify_execution` as the Rust
writes them (`crates/verifier/src/lib.rs:242-320`): `tableSumcheck` returns each table's point and
evaluations, step 6 reads the `KECCAK` row's output lanes off them, and the opening drops the
claims `ColumnClaim.onStack` finds no placement for, the output lanes'. The proofs reason on the
claim-list form `verifyExecutionClaims`: the table sumcheck returns the tables' column claims, the
Keccak phase takes the output lanes' claims out of the list after checking there is one per lane,
in lane order, at one point, and every claim left reaches the stack (`ColumnClaim.stackClaim`).

`verifyExecution_claims` proves the two are one program: on every run the check holds, the lanes it
takes out are the `KECCAK` row's, and the claims it keeps are those with a placement.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.Compile

@[expose] public section

/-! ## The claim-list form -/

/-- A column claim as a claim on the stack, at its column's placement. -/
def ColumnClaim.stackClaim (c : ColumnClaim) (layout : Layout) : StackClaim :=
  let point := (layout.placement c.column).stackPoint c.point layout.stackLog
  (fun x ↦ eqEval point x, c.value)

/-- `tableTerms`, collecting the column claims of the evaluations. -/
def tableTermsClaims (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → ℕ → E → List ColumnClaim → VerifierProgram (E × List
        ColumnClaim)
  | [], _, final, claims => return (final, claims)
  | (table, height, forms, weight) :: rest, cursor, final, claims => do
    let evaluations ← VerifierProgram.readScalars table.width
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let claims := claims ++ evaluations.zipIdx.map fun (value, column) ↦
      ⟨globalColumnBases.getD table.opcode 0 + column, point.take height, value⟩
    tableTermsClaims constraintPowers formPowers point rest (cursor + table.nConstraints) final
      claims

/-- `tableSumcheck`, returning the tables' column claims. -/
def tableSumcheckClaims (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    VerifierProgram (List ColumnClaim) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheck target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := List.zip tables (List.zip heights (List.zip busForms weights))
  let (final, claims) ← tableTermsClaims constraintPowers formPowers point rows 0 0 []
  VerifierProgram.require (final = claim)
  return claims

/-- `tablePhase`, returning the bus's and the tables' column claims. -/
def tablePhaseClaims (layout : Layout) (bus : BusResult) : VerifierProgram (List ColumnClaim) := do
  let nConstraints := (tables.map Table.nConstraints).sum
  let nPowers := nConstraints + nTrees
  VerifierProgram.grindProofOfWork (grindingBits (nPowers - 1))
  let xi ← VerifierProgram.sampleChallenge
  let xiPowers := powers xi nPowers
  let constraintPowers := xiPowers.take nConstraints
  let formPowers := xiPowers.drop nConstraints
  let target := dot formPowers bus.totals
  let tableClaims ← tableSumcheckClaims layout.tableLogHeights bus.forms constraintPowers
    formPowers bus.point target
  return bus.claims ++ tableClaims

/-- `keccakPhase` on the claim list: take the output lanes' claims out, check there is one per
lane, in lane order, all at one point, and hand them to the Keccak reduction. -/
def keccakPhaseClaims (layout : Layout) (claims : List ColumnClaim) :
    VerifierProgram (List ColumnClaim × List E × List E) := do
  let lanes := claims.filter fun c ↦ c.column ∈ keccakOutputColumns
  VerifierProgram.require (lanes.map (·.column) = keccakOutputColumns ∧
    ∀ c ∈ lanes, c.point = (lanes.headD default).point)
  let claims := claims.filter fun c ↦ c.column ∉ keccakOutputColumns
  let (outputs, point, slices) ← verifyKeccak (layout.tableLogHeights.getD opKeccak 0)
    (lanes.headD default).point (lanes.map (·.value))
  return (claims ++ outputs, point, slices)

/-- **`verify_execution` on the claim list.** -/
def verifyExecutionClaims (ev : List K → List E → E → VerifierProgram Unit) (bytecode : List K)
    (publicInput : Digest) : VerifierProgram Unit := do
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog logInverseRate
  let ood ← readOod layout.stackLog
  let bus ← verifyBusBalance ev layout
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (claims, keccakPoint, keccakSlices) ← keccakPhaseClaims layout claims
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout) ++ [ood])

/-! ## Every value a program returns -/

namespace Claims

/-- Every value a program can return satisfies `P`, whatever it reads and samples: an inductive
predicate, so that elaboration does not unfold it along a program. -/
inductive AllRetI {α : Type} (P : α → Prop) : VerifierProgram α → Prop
  | ret {a : α} : P a → AllRetI P (.ret a)
  | fail : AllRetI P .fail
  | read {k : E → VerifierProgram α} : (∀ x, AllRetI P (k x)) → AllRetI P (.read k)
  | sample {k : E → VerifierProgram α} : (∀ c, AllRetI P (k c)) → AllRetI P (.sample k)
  | grind {b : ℕ} {k : VerifierProgram α} : AllRetI P k → AllRetI P (.grind b k)
  | commit {h w : ℕ} {k : VerifierProgram α} : AllRetI P k → AllRetI P (.commit h w k)
  | query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} :
      (∀ r, AllRetI P (k r)) → AllRetI P (.query i ps k)

/-- Every value `p` can return satisfies `P`. -/
abbrev AllRet {α : Type} (p : VerifierProgram α) (P : α → Prop) : Prop := AllRetI P p

theorem allRet_of_forall {α : Type} {P : α → Prop} (h : ∀ a, P a) : ∀ p : VerifierProgram α,
    AllRet p P
  | .ret a => .ret (h a)
  | .fail => .fail
  | .read k => .read fun x ↦ allRet_of_forall h (k x)
  | .sample k => .sample fun c ↦ allRet_of_forall h (k c)
  | .grind _ k => .grind (allRet_of_forall h k)
  | .commit _ _ k => .commit (allRet_of_forall h k)
  | .query _ _ k => .query fun r ↦ allRet_of_forall h (k r)

theorem allRet_true {α : Type} (p : VerifierProgram α) : AllRet p fun _ ↦ True :=
  allRet_of_forall (fun _ ↦ trivial) p

theorem AllRet.mono {α : Type} {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) {p : VerifierProgram α}
    (hp : AllRet p P) : AllRet p Q := by
  induction hp with
  | ret h => exact .ret (hPQ _ h)
  | fail => exact .fail
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

theorem AllRet.bind {α β : Type} {Q : α → Prop} {P : β → Prop} {f : α → VerifierProgram β}
    (hf : ∀ a, Q a → AllRet (f a) P) (p : VerifierProgram α) (hp : AllRet p Q) : AllRet (p.bind f)
        P := by
  induction hp with
  | ret h => exact hf _ h
  | fail => exact .fail
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

/-- Two continuations that agree on every value a program returns make one program. -/
theorem bind_congr {α β : Type} {Q : α → Prop} {f g : α → VerifierProgram β} (h : ∀ a, Q a → f
    a = g a)
    (p : VerifierProgram α) (hp : AllRet p Q) : p.bind f = p.bind g := by
  induction hp with
  | ret hq => exact h _ hq
  | fail => rfl
  | read _ ih => exact congrArg VerifierProgram.read (funext ih)
  | sample _ ih => exact congrArg VerifierProgram.sample (funext ih)
  | grind _ ih => exact congrArg (VerifierProgram.grind _) ih
  | commit _ ih => exact congrArg (VerifierProgram.commit _ _) ih
  | query _ ih => exact congrArg (VerifierProgram.query _ _) (funext ih)

theorem allRet_readN : ∀ n : ℕ, AllRet (VerifierProgram.readScalars n) fun xs ↦ xs.length = n
  | 0 => .ret rfl
  | n + 1 => .read fun x ↦
    AllRet.bind (fun xs hxs ↦ .ret (by show (x :: xs).length = n + 1; simp [hxs])) _
      (allRet_readN n)

theorem allRet_liftOption {α : Type} (o : Option α) : AllRet (liftOption o) fun a ↦ o = some a := by
  cases o with
  | none => exact .fail
  | some a => exact .ret rfl

/-! ## The layout -/

/-- What the equality uses of a layout: six tables, and a placement for every column but the
`KECCAK` output lanes. -/
def LayoutOk (layout : Layout) : Prop :=
  layout.tableLogHeights.length = tables.length ∧
    ∀ c < 158, (layout.placements.getD c none).isSome = decide (c ∉ keccakOutputColumns)

theorem columnKappas_length (logMemory logBytecode : ℕ) (heights : List ℕ) :
    (columnKappas logMemory logBytecode heights).length = 158 := by
  simp only [columnKappas, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap, List.length_replicate]
  rfl

theorem slotted_not_lane_all :
    (List.range 158).all (fun c ↦ !(keccakSlot c).isSome || decide (c ∉ keccakOutputColumns)) =
      true := by
  decide +kernel

theorem placementsOf_isSome {kappas : List ℕ} (hl : kappas.length = 158) {c : ℕ} (hc : c < 158) :
    ((placementsOf kappas).1.getD c none).isSome = decide (c ∉ keccakOutputColumns) := by
  have hs := List.all_eq_true.mp slotted_not_lane_all c (List.mem_range.mpr hc)
  unfold placementsOf
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_eq_getElem (hl ▸ hc : c < kappas.length), Option.map_some, Option.getD_some,
    zero_add]
  cases h : keccakSlot c with
  | some slot => simp only [h, Option.isSome_some, Bool.not_true, Bool.false_or] at hs ⊢; exact hs.symm
  | none =>
    by_cases hm : c ∈ keccakOutputColumns <;> simp [hm]

theorem buildLayout_ok {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode logMemory tableRows = some layout) : LayoutOk layout := by
  unfold buildLayout at h
  split at h
  · cases h
  · split_ifs at h with hc
    · obtain ⟨-, -, -, -, -, hrows⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, fun c hc ↦ placementsOf_isSome (columnKappas_length _ _ _) hc⟩
      simp only [List.length_zipWith, hrows]
      rfl

theorem allRet_readSizes (bytecode : List K) :
    AllRet (readAnnouncedSizes bytecode) fun x ↦ LayoutOk x.1 := by
  unfold readAnnouncedSizes
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun layout hlayout ↦ ?_) _ (allRet_liftOption _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  exact .ret (buildLayout_ok hlayout)

/-! ## The bus -/

/-- The framework columns. -/
abbrev framework : List ℕ := [memory0, memory1, memoryFinalCounters, bytecodeFinalCounters]

/-- What the equality uses of the bus: a form per table, claims on the framework columns. -/
def BusOk (bus : BusResult) : Prop :=
  bus.forms.length = tables.length ∧ ∀ c ∈ bus.claims, c.column ∈ framework

theorem accumulateSide_length (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sideLayout : BusLayout) (fps sideWeights : List E) (sideBeta : E) (point : List E)
    (treeValue : E) :
    (accumulateSide forms side blocks sideLayout fps sideWeights sideBeta point treeValue).1.length =
      forms.length := by
  unfold accumulateSide
  dsimp only
  generalize (List.zip _ blocks) = pairs
  suffices ∀ (acc : List (List Form) × E), acc.1.length = forms.length →
      (pairs.foldl (fun (x : List (List Form) × E) (y : E × BusBlock) ↦
        (x.1.modify y.2.owner fun row ↦ row.modify side fun f ↦
            f.addScaled (blockForm y.2 sideWeights sideBeta) y.1,
          x.2 + y.1 * paddingWeight (point.take y.2.logRows) y.2.rows *
            ((blockForm y.2 sideWeights sideBeta).evaluate
              ((tables.getD y.2.owner default).padding.getD · 0) + 1))) acc).1.length =
        forms.length from this _ rfl
  induction pairs with
  | nil => exact fun _ h ↦ h
  | cons p ps ih => exact fun acc h ↦ ih _ (by simp [List.length_modify, h])

theorem zipWith_columns {β : Type} (pt : List E) :
    ∀ (cols : List ℕ) (vals : List β) (g : β → E) (c : ColumnClaim),
      c ∈ List.zipWith (fun column value ↦ (⟨column, pt, g value⟩ : ColumnClaim)) cols vals →
        c.column ∈ cols
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | col :: cols, v :: vals, g, c, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (zipWith_columns pt cols vals g c h)

theorem allRet_verifyBusBalance (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout) :
    AllRet (verifyBusBalance ev layout) BusOk := by
  unfold verifyBusBalance
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun r _ ↦ ?_) _ (allRet_true _)
  obtain ⟨countRoot, point, treeValues⟩ := r
  dsimp only
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun memory _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine .ret ⟨?_, fun c hc ↦ ?_⟩
  · simp only [accumulateSide_length, List.length_map]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with hc | rfl | rfl
    · have := zipWith_columns _ _ _ id c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      tauto
    · tauto
    · tauto

/-! ## The table sumcheck -/

theorem tableWeights_length (heights : List ℕ) (equalityPoint point : List E) :
    (tableWeights heights equalityPoint point).length = heights.length := by
  unfold tableWeights
  generalize point.zipIdx = cs
  suffices ∀ ws : List E, ws.length = heights.length →
      (cs.foldl (fun weights (challenge, coord) ↦
        List.zipWith (fun weight height ↦ weight *
          if coord < height then 1 + equalityPoint.getD coord 0 + challenge else challenge)
          weights heights) ws).length = heights.length from this _ (by simp)
  induction cs with
  | nil => exact fun _ h ↦ h
  | cons c cs ih => exact fun ws h ↦ ih _ (by simp [List.length_zipWith, h])

/-- Each table's evaluations: one per column. -/
def RowsOk (rows : List (List E × List E)) : Prop :=
  List.Forall₂ (fun (t : Table) (row : List E × List E) ↦ row.2.length = t.width) tables rows

theorem allRet_tableTerms (cP fP point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E),
      AllRet (tableTerms cP fP point rows cursor final)
        fun r ↦ List.Forall₂ (fun x (row : List E × List E) ↦ row.2.length = x.1.width) rows r.2
  | [], _, _ => .ret List.Forall₂.nil
  | (table, height, forms, weight) :: rest, cursor, final => by
    unfold tableTerms
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine AllRet.bind (fun evs hevs ↦ ?_) _ (allRet_readN table.width)
    refine AllRet.bind (fun r hr ↦ ?_) _ (allRet_tableTerms cP fP point rest _ _)
    obtain ⟨fin, rs⟩ := r
    exact .ret (List.Forall₂.cons hevs hr)

theorem allRet_tableSumcheck {heights : List ℕ} {busForms : List (List Form)}
    (hh : heights.length = tables.length) (hf : busForms.length = tables.length)
    (cP fP eqPt : List E) (target : E) :
    AllRet (tableSumcheck heights busForms cP fP eqPt target) RowsOk := by
  unfold tableSumcheck
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine AllRet.bind (fun r _ ↦ ?_) _ (allRet_true _)
  obtain ⟨chs, cl⟩ := r
  dsimp only
  refine AllRet.bind (fun r hr ↦ ?_) _ (allRet_tableTerms cP fP _ _ 0 0)
  obtain ⟨fin, rows⟩ := r
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  have hlen : (List.zip heights (List.zip busForms (tableWeights heights eqPt chs.reverse))).length =
      tables.length := by
    simp [List.length_zip, tableWeights_length, hh, hf]
  have hfst : (List.zip tables
      (List.zip heights (List.zip busForms (tableWeights heights eqPt chs.reverse)))).map
        Prod.fst = tables := List.map_fst_zip (by rw [hlen])
  refine .ret ?_
  show List.Forall₂ (fun (t : Table) (row : List E × List E) ↦ row.2.length = t.width) tables rows
  rw [← hfst, List.forall₂_map_left_iff]
  exact hr

theorem allRet_tablePhase {layout : Layout} {bus : BusResult} (hl : LayoutOk layout)
    (hb : BusOk bus) : AllRet (tablePhase layout bus) RowsOk := by
  unfold tablePhase
  simp only [VerifierProgram.bind_eq]
  exact AllRet.bind (fun _ _ ↦ allRet_tableSumcheck hl.1 hb.1 _ _ _ _) _ (allRet_true _)

/-- The claims of one table's evaluations. -/
abbrev rowClaims (base : ℕ) (row : List E × List E) : List ColumnClaim :=
  row.2.zipIdx.map fun (value, column) ↦ ⟨base + column, row.1, value⟩

theorem tableTermsClaims_eq (cP fP point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (bases : List ℕ), rows.length ≤ bases.length →
      (∀ i < rows.length, bases.getD i 0 = globalColumnBases.getD (rows.getD i default).1.opcode 0) →
      ∀ (cursor : ℕ) (final : E) (acc : List ColumnClaim),
      tableTermsClaims cP fP point rows cursor final acc =
        (tableTerms cP fP point rows cursor final).bind fun r ↦
          VerifierProgram.ret (r.1, acc ++ (bases.zip r.2).flatMap fun (base, row) ↦ rowClaims
              base row)
  | [], _, _, _, _, _, acc => by simp [tableTermsClaims, tableTerms]
  | (table, height, forms, weight) :: rest, b :: bases, hlen, hb, cursor, final, acc => by
    have hb0 := hb 0 (by simp)
    simp only [List.getD_cons_zero] at hb0
    have ih := tableTermsClaims_eq cP fP point rest bases (by simpa using hlen)
      (fun i hi ↦ by simpa using hb (i + 1) (by simpa using hi))
    unfold tableTermsClaims tableTerms
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
        VerifierProgram.ret_bind]
    congr 1
    funext evs
    rw [ih]
    congr 1
    funext r
    obtain ⟨fin, rs⟩ := r
    simp only [List.zip_cons_cons, List.flatMap_cons, List.append_assoc, hb0]
  | _ :: _, [], hlen, _, _, _, _ => by simp at hlen

theorem bases_opcode : ∀ i < tables.length,
    globalColumnBases.getD i 0 = globalColumnBases.getD (tables.getD i default).opcode 0 := by
  decide +kernel

theorem tableSumcheckClaims_eq (heights : List ℕ) (busForms : List (List Form))
    (cP fP eqPt : List E) (target : E) :
    tableSumcheckClaims heights busForms cP fP eqPt target =
      (tableSumcheck heights busForms cP fP eqPt target).bind fun rows ↦
        VerifierProgram.ret (tableColumnClaims rows) := by
  unfold tableSumcheckClaims tableSumcheck
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc]
  congr 1
  funext r
  obtain ⟨chs, cl⟩ := r
  dsimp only
  rw [tableTermsClaims_eq cP fP chs.reverse _ globalColumnBases ?_ ?_ 0 0 [],
      VerifierProgram.bind_assoc]
  · rfl
  · simp [globalColumnBases]
  · intro i hi
    simp only [List.length_zip, lt_min_iff] at hi
    have h1 : ((tables.zip (heights.zip (busForms.zip (tableWeights heights eqPt chs.reverse)))).getD
        i default).1 = tables.getD i default := by
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_zip, lt_min_iff]; exact hi),
        List.getElem_zip, List.getD_eq_getElem _ _ hi.1]
    rw [h1]
    exact bases_opcode i hi.1

theorem tablePhaseClaims_eq (layout : Layout) (bus : BusResult) :
    tablePhaseClaims layout bus =
      (tablePhase layout bus).bind fun rows ↦ VerifierProgram.ret (bus.claims ++ tableColumnClaims
          rows) := by
  unfold tablePhaseClaims tablePhase
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
      tableSumcheckClaims_eq, VerifierProgram.ret_bind]

/-! ## The public input and the Keccak reduction -/

theorem allRet_publicInputPhase (layout : Layout) (publicInput : Digest) :
    AllRet (publicInputPhase layout publicInput)
      fun claims ↦ ∀ c ∈ claims, c.column ∈ [memory0, memory1] := by
  unfold publicInputPhase
  simp only [VerifierProgram.bind_eq]
  exact AllRet.bind (fun _ _ ↦ .ret fun c hc ↦ zipWith_columns _ _ _ id c hc) _ (allRet_true _)

theorem allRet_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    AllRet (verifyKeccak logSteps inst output) fun r ↦ ∀ c ∈ r.1, c.column = qkeccak := by
  have h1 : 1 < keccakSegments := by decide
  unfold verifyKeccak
  simp only [h1, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.ret_bind]
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine .ret ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  rw [hc]

theorem allRet_keccakPhase (layout : Layout) (rows : List (List E × List E)) :
    AllRet (keccakPhase layout rows) fun r ↦ ∀ c ∈ r.1, c.column = qkeccak := by
  unfold keccakPhase
  split
  exact allRet_verifyKeccak _ _ _

/-! ## The output lanes -/

theorem zipIdx_map_eq {β : Type} (base : ℕ) (pt : List E) (vals : List E)
    (f : ℕ → List E → E → β) :
    vals.zipIdx.map (fun (value, column) ↦ f (base + column) pt value) =
      (List.range vals.length).map fun j ↦ f (base + j) pt (vals.getD j 0) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, zero_add]
  simp only [List.length_map, List.length_zipIdx] at h1
  rw [List.getD_eq_getElem _ _ h1]

theorem lanes_filter : ∀ i < tables.length,
    (List.range (tables.getD i default).width).filter
        (fun j ↦ decide (globalColumnBases.getD i 0 + j ∈ keccakOutputColumns)) =
      if i = opKeccak then (List.range 25).map (keccakOut + ·) else [] := by
  decide +kernel

theorem columns_lt : ∀ i < tables.length,
    globalColumnBases.getD i 0 + (tables.getD i default).width ≤ 158 := by
  decide +kernel

theorem rowsOk_iff {rows : List (List E × List E)} (hr : RowsOk rows) :
    rows.length = tables.length ∧
      ∀ i < tables.length, (rows.getD i ([], [])).2.length = (tables.getD i default).width := by
  refine ⟨hr.length_eq.symm, fun i hi ↦ ?_⟩
  have hi' : i < rows.length := hr.length_eq ▸ hi
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
  exact hr.get hi hi'

theorem tableClaims_range {rows : List (List E × List E)} (hlen : rows.length = tables.length) :
    tableColumnClaims rows = (List.range tables.length).flatMap fun i ↦
      rowClaims (globalColumnBases.getD i 0) (rows.getD i ([], [])) := by
  match rows, hlen with
  | [r0, r1, r2, r3, r4, r5], _ => rfl

/-- The output lanes' claims of the `KECCAK` row, by lane. -/
abbrev laneClaims (row : List E × List E) : List ColumnClaim :=
  (List.range 25).map fun lane ↦
    ⟨globalColumnBases.getD opKeccak 0 + (keccakOut + lane), row.1, row.2.getD (keccakOut + lane) 0⟩

theorem rowClaims_filter {i : ℕ} (hi : i < tables.length) {row : List E × List E}
    (hrow : row.2.length = (tables.getD i default).width) :
    (rowClaims (globalColumnBases.getD i 0) row).filter (fun c ↦ decide (c.column ∈ keccakOutputColumns)) =
      if i = opKeccak then laneClaims row else [] := by
  obtain ⟨pt, vals⟩ := row
  simp only at hrow
  have := zipIdx_map_eq (globalColumnBases.getD i 0) pt vals
    (fun col p v ↦ (⟨col, p, v⟩ : ColumnClaim))
  simp only [rowClaims] at this ⊢
  rw [this, List.filter_map, hrow]
  have hf := lanes_filter i hi
  simp only [Function.comp_def] at hf ⊢
  rw [hf]
  split
  · subst_vars
    simp only [List.map_map, laneClaims]
    rfl
  · rfl

theorem lanes_eq {busClaims publicClaims : List ColumnClaim} {rows : List (List E × List E)}
    (hb : ∀ c ∈ busClaims, c.column ∈ framework)
    (hp : ∀ c ∈ publicClaims, c.column ∈ [memory0, memory1]) (hr : RowsOk rows) :
    (busClaims ++ tableColumnClaims rows ++ publicClaims).filter
        (fun c ↦ decide (c.column ∈ keccakOutputColumns)) =
      laneClaims (rows.getD opKeccak ([], [])) := by
  obtain ⟨hlen, hrow⟩ := rowsOk_iff hr
  have hfw : ∀ x ∈ framework, x ∉ keccakOutputColumns := by decide +kernel
  have h1 : busClaims.filter (fun c ↦ decide (c.column ∈ keccakOutputColumns)) = [] :=
    List.filter_eq_nil_iff.mpr fun c hc ↦ by simpa using hfw _ (hb c hc)
  have h2 : publicClaims.filter (fun c ↦ decide (c.column ∈ keccakOutputColumns)) = [] :=
    List.filter_eq_nil_iff.mpr fun c hc ↦ by
      have hm : c.column ∈ framework := by
        have := hp c hc
        simp only [framework, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
        tauto
      simpa using hfw _ hm
  rw [List.filter_append, List.filter_append, h1, h2, List.nil_append, List.append_nil,
    tableClaims_range hlen, List.filter_flatMap, show tables.length = 6 from rfl]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [rowClaims_filter (by decide) (hrow 0 (by decide)), rowClaims_filter (by decide) (hrow 1 (by decide)),
    rowClaims_filter (by decide) (hrow 2 (by decide)), rowClaims_filter (by decide) (hrow 3 (by decide)),
    rowClaims_filter (by decide) (hrow 4 (by decide)), rowClaims_filter (by decide) (hrow 5 (by decide))]
  rfl

theorem keccakPhaseClaims_eq {layout : Layout} {busClaims publicClaims : List ColumnClaim}
    {rows : List (List E × List E)} (hb : ∀ c ∈ busClaims, c.column ∈ framework)
    (hp : ∀ c ∈ publicClaims, c.column ∈ [memory0, memory1]) (hr : RowsOk rows) :
    keccakPhaseClaims layout (busClaims ++ tableColumnClaims rows ++ publicClaims) =
      (keccakPhase layout rows).bind fun r ↦
        VerifierProgram.ret ((busClaims ++ tableColumnClaims rows ++ publicClaims).filter
          (fun c ↦ c.column ∉ keccakOutputColumns) ++ r.1, r.2.1, r.2.2) := by
  unfold keccakPhaseClaims keccakPhase
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  rw [lanes_eq hb hp hr]
  have hok : ((laneClaims (rows.getD opKeccak ([], []))).map (·.column) = keccakOutputColumns ∧
      ∀ c ∈ laneClaims (rows.getD opKeccak ([], [])),
        c.point = ((laneClaims (rows.getD opKeccak ([], []))).headD default).point) := by
    refine ⟨by simp only [laneClaims, List.map_map]; rfl, fun c hc ↦ ?_⟩
    obtain ⟨lane, -, rfl⟩ := List.mem_map.mp hc
    rfl
  unfold VerifierProgram.require
  split
  · simp only [VerifierProgram.ret_bind, List.map_map]
    rfl
  · contradiction

/-! ## The opening -/

theorem onStack_eq {layout : Layout} (hl : LayoutOk layout) {c : ColumnClaim} (hc : c.column < 158) :
    c.onStack layout =
      if c.column ∈ keccakOutputColumns then none else some (c.stackClaim layout) := by
  have h := hl.2 c.column hc
  unfold ColumnClaim.onStack ColumnClaim.stackClaim Layout.placement
  cases hp : layout.placements.getD c.column none with
  | none =>
    rw [hp] at h
    simp only [Option.isSome_none, Bool.false_eq, decide_eq_false_iff_not, not_not] at h
    simp [h]
  | some p =>
    rw [hp] at h
    have hn : c.column ∉ keccakOutputColumns := of_decide_eq_true (by simpa using h.symm)
    simp [hn]

theorem filterMap_onStack {layout : Layout} (hl : LayoutOk layout) :
    ∀ claims : List ColumnClaim, (∀ c ∈ claims, c.column < 158) →
      claims.filterMap (·.onStack layout) =
        (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.stackClaim layout)
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.filterMap_cons, onStack_eq hl (h c (List.mem_cons_self ..)),
      filterMap_onStack hl cs fun c hc ↦ h c (List.mem_cons_of_mem _ hc)]
    by_cases hm : c.column ∈ keccakOutputColumns <;> simp [hm]

theorem tableClaims_lt {rows : List (List E × List E)} (hr : RowsOk rows) :
    ∀ c ∈ tableColumnClaims rows, c.column < 158 := by
  obtain ⟨hlen, hrow⟩ := rowsOk_iff hr
  intro c hc
  rw [tableClaims_range hlen, List.mem_flatMap] at hc
  obtain ⟨i, hi, hc⟩ := hc
  rw [List.mem_range] at hi
  obtain ⟨⟨v, j⟩, hvj, rfl⟩ := List.mem_map.mp hc
  have hj := List.snd_lt_of_mem_zipIdx hvj
  rw [hrow i hi] at hj
  have := columns_lt i hi
  simp only
  omega

end Claims

open Claims in
/-- **The two forms are one program.** -/
theorem verifyExecution_claims (ev : List K → List E → E → VerifierProgram Unit) (bytecode : List K)
    (publicInput : Digest) :
    verifyExecution ev bytecode publicInput = verifyExecutionClaims ev bytecode publicInput := by
  unfold verifyExecution verifyExecutionClaims
  simp only [VerifierProgram.bind_eq]
  refine bind_congr (Q := fun x ↦ LayoutOk x.1) (fun x hl ↦ ?_) _ (allRet_readSizes bytecode)
  refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
  refine bind_congr (fun bus hb ↦ ?_) _ (allRet_verifyBusBalance ev x.1)
  rw [tablePhaseClaims_eq, VerifierProgram.bind_assoc]
  refine bind_congr (fun rows hr ↦ ?_) _ (allRet_tablePhase hl hb)
  rw [VerifierProgram.ret_bind]
  refine bind_congr (fun pc hpc ↦ ?_) _ (allRet_publicInputPhase x.1 publicInput)
  rw [keccakPhaseClaims_eq hb.2 hpc hr, VerifierProgram.bind_assoc]
  refine bind_congr (fun r hout ↦ ?_) _ (allRet_keccakPhase x.1 rows)
  rw [VerifierProgram.ret_bind]
  refine bind_congr (Q := fun _ ↦ True) (fun rs _ ↦ ?_) _ (allRet_true _)
  have hlt : ∀ c ∈ bus.claims ++ tableColumnClaims rows ++ pc ++ r.1, c.column < 158 := by
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · have := hb.2 c hc
      simp only [framework, memory0, memory1, memoryFinalCounters, bytecodeFinalCounters,
        List.mem_cons, List.not_mem_nil, or_false] at this
      omega
    · exact tableClaims_lt hr c hc
    · have := hpc c hc
      simp only [memory0, memory1, List.mem_cons, List.not_mem_nil, or_false] at this
      omega
    · rw [hout c hc]; decide
  have hfm := filterMap_onStack hl _ hlt
  rw [List.filter_append,
    (List.filter_eq_self (l := r.1)).mpr fun c hc ↦ by rw [hout c hc]; decide] at hfm
  exact congrArg (fun l ↦ verifyStackedOpening x.1.stackLog x.2 (_ :: l)) hfm


/-- The verifier program on the claim-list form. -/
theorem leanVmProgram_eq (bytecode : List K) (publicInput : Digest) :
    leanVmVerifierProgram bytecode publicInput =
      (verifyExecutionClaims computedBytecodeValue bytecode publicInput).bind fun _ ↦
          VerifierProgram.ret true := by
  unfold leanVmVerifierProgram
  rw [verifyExecution_claims]
  rfl

/-- The deferring verifier program on the claim-list form. -/
theorem deferredProgram_eq (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    deferringVerifierProgram c bytecode publicInput =
      (verifyExecutionClaims (claimedBytecodeValue c) bytecode publicInput).bind fun _ ↦
          VerifierProgram.ret true := by
  unfold deferringVerifierProgram
  rw [verifyExecution_claims]
  rfl

end

end LeanVM.Protocol.Verifier
