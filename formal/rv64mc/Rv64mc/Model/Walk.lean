module

public import Rv64mc.Model.Bus
public import Rv64mc.Model.Whir

/-!
# `walk`, as the Rust runs it

`crates/verifier/src/lib.rs`'s `walk` in checked mode (`verify_execution`, as the guest calls it,
`formal/rv64mc/guest/src/main.rs`), mirrored in `TM` from the other files' mirrors step by step in
the Rust's order, and `walkRust_sound`: where the mirror returns `Ok` from the transcript
`Transcript::new` starts, the statement's `verifyWith keccakF1600 bytecode publicInput proof` is
`true`. A mirror fails exactly where the Rust returns `Err`; where the Rust panics it may return
anything.

The stack's root is read in step 2 and opened in step 7; every step between them mirrors a program
that reads no commitment (`NoCommit`, `Model.Transcript`), so it keeps the roots and the opening
runs from the stack's root alone (`SimRoots`, `StackRoots`, `Model.Whir`).
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/- `NoCommit` of a statement program unfolds the program to its constructors, which is costly for
the Keccak reduction's: it is closed by the lemmas below, never by unfolding. -/
attribute [local irreducible] NoCommit

/-! ## Step 1: the announced sizes and the layout -/

/-- `walk`'s step 1: the announced sizes read and checked, and `build_layout`. -/
def announcedRust (bc : BytecodeRust) : TM (LayoutRust × List (BitVec 64) × BitVec 64) := do
  let announced ← TM.nextScalars (2 + 6)
  TM.require (announced.all fun value ↦ (limbs value).2 = 0#64)
  let logMemory := (limbs (announced.getD 0 0)).1
  let tableRows := ((announced.drop 1).take 6).map fun value ↦ (limbs value).1
  let logInverseRate := (limbs (announced.getD (1 + 6) 0)).1
  TM.require (1#64 ≤ logInverseRate ∧ logInverseRate ≤ 4#64)
  let layout ← TM.ofOption (buildLayoutRust bc.len logMemory tableRows)
  TM.require (16 ≤ layout.stackLog ∧ layout.stackLog ≤ 30)
  Pure.pure (layout, tableRows, logInverseRate)

theorem limb1_eq_zero_iff (value : E) : (limbs value).2 = 0#64 ↔ value.limb 1 = 0 := by
  constructor
  · intro h
    have : BF64.ofBitVec (value.limb 1).toBitVec = BF64.ofBitVec 0#64 := by
      rw [show (limbs value).2 = (value.limb 1).toBitVec from rfl] at h
      rw [h]
    exact (by simpa using this : value.limb 1 = BF64.ofBitVec 0#64).trans rfl
  · intro h
    show (value.limb 1).toBitVec = 0#64
    rw [h]
    rfl

theorem kToNat_limb0 (value : E) : (limbs value).1.toNat = kToNat (value.limb 0) := rfl

/-- What step 1 leaves: the layout the statement's, its bounds, the rate. -/
structure AnnouncedOk (words : List K) (a : LayoutRust × List (BitVec 64) × BitVec 64)
    (b : Layout × ℕ) : Prop where
  rel : a.1.Rel b.1
  bytecode : b.1.bytecode = words
  rate : b.2 = a.2.2.toNat
  rate1 : 1 ≤ b.2
  rate4 : b.2 ≤ 4
  stack16 : 16 ≤ a.1.stackLog
  stack30 : a.1.stackLog ≤ 30
  rows : a.2.1.length = 6
  built : ∃ lm, buildLayoutRust words.length lm a.2.1 = some a.1

theorem SimR.announced (words : List K) (bc : BytecodeRust) (hbc : BytecodeOk words bc)
    (hlen : words.length < 2 ^ 64) :
    SimR (announcedRust bc) (readAnnouncedSizes words) (AnnouncedOk words) := by
  unfold announcedRust readAnnouncedSizes
  rw [show tables.length = 6 from rfl]
  refine SimR.bindPost (Sim.nextScalars _) (Returns.nextScalars _) fun announced h8 ↦ ?_
  refine SimR.bindEq (Sim.require_iff (by simp [limb1_eq_zero_iff])) fun _ ↦ ?_
  have hlast : announced.getLastD 0 = announced.getD (1 + 6) 0 := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, h8, List.getD_eq_getElem?_getD]
  have hhead : announced.headD 0 = announced.getD 0 0 := by cases announced <;> rfl
  refine SimR.bindPost (Sim.require_iff (c' := 1 ≤ kToNat ((announced.getLastD 0).limb 0) ∧
      kToNat ((announced.getLastD 0).limb 0) ≤ 4) (by
    rw [hlast, BitVec.le_def, BitVec.le_def, kToNat_limb0]
    simp)) (Returns.require _) fun _ hrate ↦ ?_
  refine SimR.ofOption_bind fun l hl ↦ ?_
  have hrows : (((announced.drop 1).take 6).map fun value ↦ (limbs value).1).length = 6 := by
    simp [h8]
  have hspec := buildLayoutRust_spec words ((limbs (announced.getD 0 0)).1)
    (((announced.drop 1).take 6).map fun value ↦ (limbs value).1) hlen hrows
  rw [← hbc.len] at hspec
  have hstmt : buildLayout words (kToNat ((announced.headD 0).limb 0))
      (((announced.drop 1).take 6).map fun value ↦ kToNat (value.limb 0)) =
      buildLayout words (limbs (announced.getD 0 0)).1.toNat
        ((((announced.drop 1).take 6).map fun value ↦ (limbs value).1).map BitVec.toNat) := by
    rw [hhead, List.map_map]
    rfl
  rw [hstmt]
  revert hspec
  cases hb : buildLayout words (limbs (announced.getD 0 0)).1.toNat
      ((((announced.drop 1).take 6).map fun value ↦ (limbs value).1).map BitVec.toNat) with
  | none => intro hspec; rw [hspec] at hl; cases hl
  | some L =>
    intro hspec
    obtain ⟨l', hl', hrel⟩ := hspec
    rw [hl'] at hl
    cases hl
    refine SimR.bindPost (Sim.require_iff (c' := Whir.minLogStack ≤ L.stackLog ∧
      L.stackLog ≤ Whir.maxLogStack) (by rw [← hrel.stackLog]; rfl)) (Returns.require _)
      fun _ hs ↦ SimR.pure ⟨hrel, ?_, by rw [hlast]; rfl, ?_, ?_, hs.1, hs.2, hrows,
        ⟨_, hbc.len ▸ hl'⟩⟩
    rotate_left
    · show 1 ≤ kToNat ((announced.getLastD 0).limb 0)
      rw [hlast, ← kToNat_limb0]
      have := BitVec.le_def.mp hrate.1
      simpa using this
    · show kToNat ((announced.getLastD 0).limb 0) ≤ 4
      rw [hlast, ← kToNat_limb0]
      have := BitVec.le_def.mp hrate.2
      simpa using this
    unfold buildLayout at hb
    split at hb
    · cases hb
    · split_ifs at hb
      cases hb
      rfl

/-! ## The layout's bounds -/

private theorem mem_busBlocks {heights : List ℕ} {rows : List (BitVec 64)} {b : BusBlock}
    (hb : b ∈ (busBlocksRust tablesRust heights rows).1 ++
      (busBlocksRust tablesRust heights rows).2.1 ++
      (busBlocksRust tablesRust heights rows).2.2) :
    b.logRows ∈ heights ∧ b.rows < 2 ^ 64 := by
  unfold busBlocksRust at hb
  rw [foldl_blocks] at hb
  simp only [List.nil_append, List.mem_append, List.mem_flatMap, List.mem_map] at hb
  rcases hb with (⟨⟨⟨t, h⟩, r⟩, hx, c, -, rfl⟩ | ⟨⟨⟨t, h⟩, r⟩, hx, c, -, rfl⟩) |
    ⟨⟨⟨t, h⟩, r⟩, hx, c, -, rfl⟩ <;>
    exact ⟨(List.of_mem_zip (List.of_mem_zip hx).1).2, r.isLt⟩

private theorem length_busBlocks (heights : List ℕ) (rows : List (BitVec 64)) :
    (busBlocksRust tablesRust heights rows).1.length ≤ 1024 ∧
      (busBlocksRust tablesRust heights rows).2.1.length ≤ 1024 ∧
      (busBlocksRust tablesRust heights rows).2.2.length ≤ 1024 := by
  have hb : ∀ t ∈ tablesRust, t.flushes.push.length ≤ 28 ∧ t.flushes.pull.length ≤ 28 ∧
      t.countColumns.length ≤ 28 := by decide +kernel
  unfold busBlocksRust
  rw [foldl_blocks]
  simp only [List.nil_append, List.length_flatMap, List.length_map]
  have hz : ∀ (f : (TableRust × ℕ) × BitVec 64 → ℕ),
      (∀ x ∈ (tablesRust.zip heights).zip rows, f x ≤ 28) →
      (((tablesRust.zip heights).zip rows).map f).sum ≤ 1024 := by
    intro f hf
    have hlen : ((tablesRust.zip heights).zip rows).length ≤ 6 := by
      simp only [List.length_zip]
      have : tablesRust.length = 6 := rfl
      omega
    have h1 := List.sum_le_length_nsmul (((tablesRust.zip heights).zip rows).map f) 28 (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hf y hy)
    rw [List.length_map, smul_eq_mul] at h1
    omega
  refine ⟨hz _ ?_, hz _ ?_, hz _ ?_⟩ <;> rintro ⟨⟨t, h⟩, r⟩ hx <;>
    have := hb t (List.of_mem_zip (List.of_mem_zip hx).1).1 <;> simp only <;> omega

/-- What the walk needs of a layout `build_layout` returned. -/
structure LayoutBounds (l : LayoutRust) : Prop where
  logMemory1 : 1 ≤ l.logMemory
  logMemory : l.logMemory ≤ 30
  logBytecode : l.logBytecode ≤ 30
  blocks : ∀ b ∈ l.push ++ l.pull ++ l.count, b.logRows ≤ 30 ∧ b.rows < 2 ^ 64
  counts : l.push.length ≤ 1024 ∧ l.pull.length ≤ 1024 ∧ l.count.length ≤ 1024
  heights : l.tableLogHeights.length = 6

theorem buildLayoutRust_bounds {len : ℕ} {lm : BitVec 64} {rows : List (BitVec 64)}
    {l : LayoutRust} (h : buildLayoutRust len lm rows = some l) (hrows : rows.length = 6) :
    LayoutBounds l := by
  unfold buildLayoutRust at h
  cases hs : log2StrictRust (BitVec.ofNat 64 len) with
  | none => rw [hs] at h; cases h
  | some logLength =>
    rw [hs] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split_ifs at h with hc
    simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨ps, -, rfl⟩ := h
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hc
      have hrows' : ∀ r ∈ rows.map BitVec.toNat, r ≤ 2 ^ 30 := by
        intro r hr
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
        have := List.all_eq_true.mp h3 x hx
        simp only [decide_eq_true_eq, BitVec.le_def] at this
        simpa using this
      have hH := tableLogHeights_le _ hrows'
      rw [← tableLogHeightsRust_eq] at hH
      refine ⟨by rw [BitVec.le_def] at h1; simpa using h1, by
        rw [BitVec.le_def] at h2; simpa using h2, by show logLength - 4 ≤ 30; omega,
        fun b hb ↦ ?_,
        length_busBlocks _ _, by simp [hrows, tableLogFloorsRust]⟩
      obtain ⟨hb1, hb2⟩ := mem_busBlocks hb
      exact ⟨hH _ hb1, hb2⟩

/-! ## Steps 2 to 7 -/

/-- The shape the stack's opening reads its root at: a ghost (`TState.roots`). -/
def stackShape (stackLog logInvRate : ℕ) : ℕ × ℕ :=
  match Whir.ladder stackLog logInvRate with
  | some (level :: _) => levelShape stackLog level (2 ^ level.fold)
  | _ => (0, 0)

/-- `walk`'s step 4: the grind, `xi`, its powers split at the constraints' count, the target,
and `table_sumcheck`. -/
def tablePhaseRust (layout : LayoutRust) (bus : BusResultRust) : TM (List (List E × List E)) := do
  let nConstraints := (layout.tables.map TableRust.nConstraints).sum
  let nPowers := nConstraints + 3
  TM.grindCheck (grindingBitsRust (BitVec.ofNat 128 nPowers - 1#128))
  let xi ← TM.sample
  let xiPowers := (powersM (limbs xi) nPowers).map ofLimbsW
  let target ← TM.ofOption (dotRust (xiPowers.drop nConstraints) bus.totals)
  tableSumcheckRust layout.tables layout.tableLogHeights bus.forms (xiPowers.take nConstraints)
    (xiPowers.drop nConstraints) bus.point target

/-- The loop extending the claims with each table's evaluations at its point. -/
def tableClaimsRust (evaluations : List (List E × List E)) : List ColumnClaim :=
  (globalColumnBasesRust.zip evaluations).flatMap fun (base, point, values) ↦
    values.zipIdx.map fun (value, column) ↦ ⟨base + column, point, value⟩

/-- `walk`'s step 5: a challenge, and each memory limb's claim on its public line. -/
def publicInputRust (layout : LayoutRust) (publicInput : List (BitVec 8)) :
    TM (List ColumnClaim) := do
  let publicChallenge ← TM.sample
  let halves := digestHalvesRust publicInput
  let memory0 ← TM.ofOption (layout.committed 0)
  let publicPoint ← TM.ofOption (if 0 < memory0.variableCount then
    some ((List.replicate memory0.variableCount (0 : E)).set 0 publicChallenge) else none)
  let low ← TM.ofOption
    (multilinearEvalRust [eNew halves.1.1, eNew halves.2.1] [publicChallenge])
  let high ← TM.ofOption
    (multilinearEvalRust [eNew halves.1.2, eNew halves.2.2] [publicChallenge])
  Pure.pure [⟨0, publicPoint, low⟩, ⟨1, publicPoint, high⟩]

/-- `walk`'s step 6: the `KECCAK` table's point and output lanes (`&values[KECCAK_OUT..]`),
`verify_keccak` between two reads of the stream's position. -/
def keccakPhaseRust (layout : LayoutRust) (evaluations : List (List E × List E)) :
    TM (KeccakOpenings × ℕ × ℕ) := do
  let pv ← TM.ofOption evaluations[opKeccakRust]?
  let keccakStart ← TM.streamPosition
  let output ← TM.ofOption
    (if keccakOutRust + stateLanesRust ≤ pv.2.length then
      some ((pv.2.drop keccakOutRust).take stateLanesRust) else none)
  let openings ← verifyKeccakRust layout.keccak pv.1 output
  let keccakEnd ← TM.streamPosition
  Pure.pure (openings, keccakStart, keccakEnd)

/-- `ColumnClaim::on_stack`: the column's placement, an `Eq` weight at its stacked point. -/
def onStackRust (layout : LayoutRust) (c : ColumnClaim) : Option (StackWeightRust × E) :=
  (layout.placements.getD c.column none).map fun p ↦
    (.eq (p.stackPoint c.point layout.stackLog), c.value)

/-- `Summary`. -/
structure SummaryRust where
  /-- `log_memory`. -/
  logMemory : ℕ
  /-- `table_rows`. -/
  tableRows : List (BitVec 64)
  /-- `log_inv_rate`. -/
  logInvRate : ℕ
  /-- `bytecode_point`. -/
  bytecodePoint : List E
  /-- `keccak_scalars`. -/
  keccakScalars : ℕ × ℕ

/-- `walk(bytecode, public_input, proof, true)` up to `transcript.finish()`. -/
def walkBodyRust (bc : BytecodeRust) (publicInput : List (BitVec 8)) : TM SummaryRust := do
  let (layout, tableRows, logInverseRate) ← announcedRust bc
  let root ← TM.commit (stackShape layout.stackLog logInverseRate.toNat).1
    (stackShape layout.stackLog logInverseRate.toNat).2
  let (oodPoint, oodValue) ← readOodRust layout.stackLog 15
  let bus ← verifyBusBalanceRust layout bc
  let evaluations ← tablePhaseRust layout bus
  let claims := bus.claims ++ tableClaimsRust evaluations
  let publicClaims ← publicInputRust layout publicInput
  let claims := claims ++ publicClaims
  let (openings, keccakStart, keccakEnd) ← keccakPhaseRust layout evaluations
  let claims := claims ++ openings.outputs.toList.map fun pw ↦ (⟨4, pw.1, pw.2⟩ : ColumnClaim)
  let (ringTarget, ringWeight) ← ringSwitchRust openings.inputs.1 openings.inputs.2
  let qkeccak ← TM.ofOption (layout.committed 4)
  verifyStackedOpeningRust root layout.stackLog logInverseRate.toNat
    ((.placedRing qkeccak ringWeight, ringTarget) :: claims.filterMap (onStackRust layout) ++
      [(.eq oodPoint, oodValue)])
  Pure.pure ⟨layout.logMemory, tableRows, logInverseRate.toNat, bus.bytecodePoint,
    (keccakStart, keccakEnd)⟩

/-- `walk(bytecode, public_input, proof, true)`: the body, then `finish`. -/
def walkRust (bc : BytecodeRust) (publicInput : List (BitVec 8)) : TM SummaryRust := do
  let summary ← walkBodyRust bc publicInput
  TM.finish
  Pure.pure summary

/-- `verify_execution(bytecode, public_input, proof)`, from `Transcript::new(proof,
bytecode.fiat_shamir_iv, public_input, true)`: `Ok(summary)` is `some summary`. -/
def verifyExecutionRust (bc : BytecodeRust) (publicInput : List (BitVec 8)) (proof : Proof) :
    Option SummaryRust :=
  ((walkRust bc publicInput).run
    ⟨proof, SpongeRust.new bc.fiatShamirIv publicInput, 0, 0, true, []⟩).map (·.1)

/-! ## Each step runs the statement's -/

theorem SimR.readOod (stackLog : ℕ) :
    SimR (readOodRust stackLog 15) (readOod stackLog) fun a b ↦
      b = ((fun x ↦ eqEval a.1 x), a.2) ∧ a.1.length = stackLog := by
  unfold readOodRust LeanVM.Protocol.Verifier.readOod
  refine SimR.bindEq (Sim.grindCheck _) fun _ ↦
    SimR.bindPost (Sim.samples _) (Returns.samples _) fun z hz ↦
    SimR.bindEq Sim.nextScalar fun v ↦ SimR.pure ⟨rfl, hz⟩

private theorem nConstraints_sum : (tablesRust.map TableRust.nConstraints).sum = 2 := rfl

theorem Sim.tablePhase (l : LayoutRust) (L : Layout) (hl : l.Rel L) (hb : LayoutBounds l)
    (bus : BusResultRust) (bus' : BusResult) (hbus : bus.Rel bus') :
    Sim (tablePhaseRust l bus) (tablePhase L bus') := by
  unfold tablePhaseRust LeanVM.Protocol.Verifier.tablePhase
  rw [hl.tables, nConstraints_sum, show (tables.map Table.nConstraints).sum = 2 by
    simp [tables, Table.nConstraints, Table.width, jumpConstraints], show nTrees = 3 from rfl]
  dsimp only
  rw [show BitVec.ofNat 128 (2 + 3) - 1#128 = BitVec.ofNat 128 (2 + 3 - 1) from rfl,
    grindingBitsRust_ofNat (by norm_num)]
  refine Sim.bind (Sim.grindCheck _) fun _ ↦ Sim.bind Sim.sample fun xi ↦ ?_
  have hp : (powersM (limbs xi) (2 + 3)).map ofLimbsW = powers xi (2 + 3) := by
    rw [powersM_eq, List.map_map]
    simp [Function.comp_def, ofLimbsW_limbs]
  rw [hp]
  refine SimR.ofOption_bind fun target ht ↦ ?_
  rw [dotRust_some ht, ← hbus.totals, ← hbus.point, ← hl.heights]
  have hf : formsDen bus.forms = formsDen bus'.forms := hbus.forms
  have hf6 : bus'.forms.length = 6 := hbus.formsLength
  have hf6' : bus.forms.length = 6 := by
    have := congrArg List.length hf
    simp only [formsDen, List.length_map] at this
    omega
  exact SimR.tableSumcheck _ hb.heights hf hf6' _ _ _ _

theorem ofK_toBitVec (k : K) : eNew k.toBitVec = ofK k := by
  simp [eNew]

theorem placement_of_committed {l : LayoutRust} {L : Layout} (hl : l.Rel L) {c : ℕ}
    {p : PlacementRust} (h : l.committed c = some p) : L.placement c = p.toSpec := by
  rw [Layout.placement, ← hl.placements]
  unfold LayoutRust.committed at h
  rw [List.getD_eq_getElem?_getD] at h ⊢
  rw [List.getElem?_map]
  cases hc : l.placements[c]? with
  | none => rw [hc] at h; cases h
  | some o => rw [hc] at h; simp at h; subst h; rfl

theorem Sim.publicInput (l : LayoutRust) (L : Layout) (hl : l.Rel L) (d : Digest) :
    Sim (publicInputRust l (digestBits d)) (publicInputPhase L d) := by
  unfold publicInputRust publicInputPhase
  refine Sim.bind Sim.sample fun c ↦ ?_
  rw [digestBits, digestHalvesRust_eq]
  refine SimR.ofOption_bind fun p hp ↦ ?_
  rw [show L.placement memory0 = p.toSpec from placement_of_committed hl hp]
  by_cases hn : 0 < p.variableCount
  · rw [ite_eq_left hn]
    simp only [TM.ofOption, pure_bind]
    have hset : (List.replicate p.variableCount (0 : E)).set 0 c =
        c :: List.replicate (p.toSpec.variableCount - 1) 0 := by
      obtain ⟨n, hn'⟩ : ∃ n, p.variableCount = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hn).symm⟩
      simp [PlacementRust.toSpec, hn', List.replicate_succ]
    rw [hset, multilinearEvalRust_eq _ _ (by simp), multilinearEvalRust_eq _ _ (by simp)]
    simp only [pure_bind, ofK_toBitVec, limbs]
    exact Sim.pure _
  · rw [ite_eq_right hn]
    exact SimR.fail_bind

theorem SimR.keccakPhase (l : LayoutRust) (L : Layout) (hl : l.Rel L)
    (evaluations : List (List E × List E)) :
    SimR (keccakPhaseRust l evaluations) (keccakPhase L evaluations) fun a b ↦ a.1.toSpec = b := by
  unfold keccakPhaseRust LeanVM.Protocol.Verifier.keccakPhase
  refine SimR.ofOption_bind fun pv hpv ↦ ?_
  have hget : evaluations.getD opKeccak ([], []) = pv := by
    rw [List.getD_eq_getElem?_getD]
    exact congrArg (·.getD ([], [])) hpv
  rw [hget]
  obtain ⟨point, values⟩ := pv
  refine SimR.streamPosition_left fun k0 ↦ ?_
  by_cases hlen : keccakOutRust + stateLanesRust ≤ values.length
  · rw [ite_eq_left hlen]
    simp only [TM.ofOption, pure_bind]
    have hout : (values.drop keccakOutRust).take stateLanesRust =
        (List.range 25).map fun lane ↦ values.getD (keccakOut + lane) 0 := by
      have h40 : keccakOut = 40 := by decide +kernel
      have hlen' : 65 ≤ values.length := hlen
      rw [h40, show keccakOutRust = 40 from rfl, show stateLanesRust = 25 from rfl]
      apply List.ext_getElem (by simp; omega)
      intro i h1 h2
      simp only [List.length_map, List.length_range] at h2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hout, hl.keccak, ← hl.heights]
    have h := SimR.bind (SimR.verifyKeccak (l.tableLogHeights.getD opKeccakRust 0) point
      ((List.range 25).map fun lane ↦ values.getD (keccakOut + lane) 0))
      (k := fun o ↦ TM.streamPosition >>= fun k1 ↦ (Pure.pure (o, k0, k1) : TM _))
      (Q := VerifierProgram.ret) (r' := fun a b ↦ a.1.toSpec = b) fun o b hob ↦
        SimR.streamPosition_left fun k1 ↦ SimR.pure hob
    rw [VerifierProgram.bind_ret'] at h
    exact h
  · rw [ite_eq_right hlen]
    exact SimR.fail_bind

/-- The claims' weights on the stack are the statement's. -/
theorem onStack_rel (l : LayoutRust) (L : Layout) (hl : l.Rel L) (hs : l.stackLog ≤ 64) :
    ∀ claims : List ColumnClaim, List.Forall₂ (StackClaimRel l.stackLog)
      (claims.filterMap (onStackRust l)) (claims.filterMap (·.onStack L))
  | [] => .nil
  | c :: cs => by
    have ih := onStack_rel l L hl hs cs
    have key : (onStackRust l c = none ∧ c.onStack L = none) ∨
        ∃ a b, onStackRust l c = some a ∧ c.onStack L = some b ∧ StackClaimRel l.stackLog a b := by
      unfold onStackRust ColumnClaim.onStack
      rw [← hl.placements, ← hl.stackLog, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_map]
      cases h : l.placements[c.column]? with
      | none => left; simp
      | some o =>
        cases o with
        | none => left; simp
        | some p =>
          right
          refine ⟨_, _, rfl, rfl, ?_⟩
          dsimp only
          rw [PlacementRust.stackPoint_eq _ _ _ hs]
          exact stackClaimRel_eq _ _ _
    rcases key with ⟨h1, h2⟩ | ⟨a, b, h1, h2, h3⟩
    · simp only [List.filterMap_cons, h1, h2]
      exact ih
    · simp only [List.filterMap_cons, h1, h2]
      exact .cons h3 ih

/-- A simulation followed by a pure step the statement does not take. -/
theorem SimRoots.bind_pure {α β γ : Type} {pre : Roots → Prop} {m : TM α} {P : VerifierProgram β}
    {r : α → β → Prop} (h : SimRoots pre m P r) (c : γ) :
    SimRoots pre (m >>= fun _ ↦ (Pure.pure c : TM γ)) P fun _ _ ↦ True := by
  intro t a t' hi hp hm
  rw [StateT.run_bind] at hm
  cases hmt : m.run t with
  | none => rw [hmt] at hm; cases hm
  | some p =>
    obtain ⟨a', t₁⟩ := p
    rw [hmt] at hm
    simp only [Option.bind_eq_bind, Option.bind_some, StateT.run_pure, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨-, rfl⟩ := hm
    obtain ⟨hi', b, hb, -⟩ := h t a' t₁ hi hp hmt
    exact ⟨hi', b, hb, trivial⟩

/-- The ladder of every stack and rate the walk opens has a first level. -/
def ladderCons (μ r : ℕ) : Bool :=
  match Whir.ladder μ r with
  | some (_ :: _) => true
  | _ => false

theorem ladderCons_window : ∀ μ < 31, ∀ r < 5, 16 ≤ μ → 1 ≤ r → ladderCons μ r = true := by
  decide +kernel

theorem commitStack_eq {μ r : ℕ} (hμ : 16 ≤ μ ∧ μ ≤ 30) (hr : 1 ≤ r ∧ r ≤ 4) :
    commitStack μ r = VerifierProgram.readCommitment (stackShape μ r).1 (stackShape μ r).2 := by
  have hc := ladderCons_window μ (by omega) r (by omega) hμ.1 hr.1
  unfold ladderCons at hc
  unfold commitStack stackShape
  split at hc
  · rename_i level rest hlad
    rw [hlad]
    rfl
  · cases hc

theorem stackRoots_of {μ r : ℕ} {d : Digest} {roots : Roots}
    (h : ∃ old, old = [] ∧ roots = old ++ [(d, (stackShape μ r).1, (stackShape μ r).2)]) :
    StackRoots μ r d roots := by
  obtain ⟨old, rfl, rfl⟩ := h
  intro ls hls l hl
  unfold stackShape
  rw [hls]
  cases ls with
  | nil => cases hl
  | cons l' rest =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl
    subst hl
    rfl

/-! ## The walk runs `verifyExecution` -/

section NoCommitSteps

/-- `no_commit`, with sumchecks. -/
local macro "no_commit'" : tactic => `(tactic| repeat' (first
  | exact NoCommit.sumcheck _ _ _
  | exact NoCommit.ret _
  | exact NoCommit.readScalar
  | exact NoCommit.sampleChallenge
  | apply NoCommit.bind
  | exact NoCommit.readScalars _
  | exact NoCommit.sampleChallenges _
  | exact NoCommit.grindProofOfWork _
  | exact NoCommit.require _
  | intro _
  | split))

theorem NoCommit.liftOption {α : Type} (o : Option α) : NoCommit (liftOption o) := by
  unfold NoCommit
  cases o <;> trivial

theorem NoCommit.gkrStep (step : ℕ) (last : Bool) (s : GkrState) :
    NoCommit (LeanVM.Protocol.Verifier.gkrStep step last s) := by
  unfold LeanVM.Protocol.Verifier.gkrStep
  no_commit'

theorem NoCommit.gkrLayers : ∀ n s, NoCommit (LeanVM.Protocol.Verifier.gkrLayers n s)
  | 0, _ => NoCommit.ret _
  | 1, _ => NoCommit.bind (NoCommit.gkrStep _ _ _) fun _ ↦ NoCommit.ret _
  | n + 2, s => by
    unfold LeanVM.Protocol.Verifier.gkrLayers
    split
    · exact NoCommit.bind (NoCommit.gkrStep _ _ _) fun _ ↦ NoCommit.gkrLayers _ _
    · exact NoCommit.bind (NoCommit.gkrStep _ _ _) fun _ ↦ NoCommit.gkrLayers _ _

theorem NoCommit.verifyBusBalance (layout : Layout) :
    NoCommit (LeanVM.Protocol.Verifier.verifyBusBalance computedBytecodeValue layout) := by
  unfold LeanVM.Protocol.Verifier.verifyBusBalance verifyGkrGrandProducts bytecodeShare
    computedBytecodeValue
  no_commit'
  exact NoCommit.gkrLayers _ _

theorem NoCommit.tableTerms (cp fp point : List E) :
    ∀ rows cursor final,
      NoCommit (LeanVM.Protocol.Verifier.tableTerms cp fp point rows cursor final)
  | [], _, _ => NoCommit.ret _
  | _ :: rest, _, _ => by
    unfold LeanVM.Protocol.Verifier.tableTerms
    refine NoCommit.bind (NoCommit.readScalars _) fun _ ↦
      NoCommit.bind (NoCommit.tableTerms cp fp point rest _ _) fun _ ↦ ?_
    no_commit'

theorem NoCommit.tablePhase (layout : Layout) (bus : BusResult) :
    NoCommit (LeanVM.Protocol.Verifier.tablePhase layout bus) := by
  unfold LeanVM.Protocol.Verifier.tablePhase LeanVM.Protocol.Verifier.tableSumcheck
  no_commit'
  exact NoCommit.tableTerms _ _ _ _ _ _

theorem NoCommit.readAnnouncedSizes (bytecode : List K) :
    NoCommit (LeanVM.Protocol.Verifier.readAnnouncedSizes bytecode) := by
  unfold LeanVM.Protocol.Verifier.readAnnouncedSizes
  no_commit'
  exact NoCommit.liftOption _

theorem NoCommit.readOod (stackLog : ℕ) :
    NoCommit (LeanVM.Protocol.Verifier.readOod stackLog) := by
  unfold LeanVM.Protocol.Verifier.readOod
  no_commit'

theorem NoCommit.publicInputPhase (layout : Layout) (d : Digest) :
    NoCommit (LeanVM.Protocol.Verifier.publicInputPhase layout d) := by
  unfold LeanVM.Protocol.Verifier.publicInputPhase
  no_commit'

theorem NoCommit.ringSwitch (point s : List E) :
    NoCommit (LeanVM.Protocol.Verifier.ringSwitch point s) := by
  unfold LeanVM.Protocol.Verifier.ringSwitch
  no_commit'

theorem NoCommit.verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    NoCommit (LeanVM.Protocol.Verifier.verifyKeccakLayer logSteps step claim) := by
  unfold LeanVM.Protocol.Verifier.verifyKeccakLayer
  no_commit'

theorem NoCommit.keccakLayers (logSteps : ℕ) :
    ∀ steps claim, NoCommit (LeanVM.Protocol.Verifier.keccakLayers logSteps steps claim)
  | [], _ => NoCommit.ret _
  | _ :: steps, _ => NoCommit.bind (NoCommit.verifyKeccakLayer _ _ _) fun _ ↦
      NoCommit.keccakLayers logSteps steps _

theorem NoCommit.keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    NoCommit (LeanVM.Protocol.Verifier.keccakOpen logSteps claim first count value) := by
  unfold LeanVM.Protocol.Verifier.keccakOpen
  no_commit'

theorem NoCommit.verifyKeccak (logSteps : ℕ) (inst output : List E) :
    NoCommit (LeanVM.Protocol.Verifier.verifyKeccak logSteps inst output) := by
  unfold LeanVM.Protocol.Verifier.verifyKeccak
  refine NoCommit.bind (NoCommit.grindProofOfWork _) fun _ ↦
    NoCommit.bind (NoCommit.sampleChallenges _) fun _ ↦
    NoCommit.bind (NoCommit.sampleChallenges _) fun _ ↦ NoCommit.bind ?_ fun _ ↦
    NoCommit.bind (NoCommit.keccakLayers _ _ _) fun _ ↦ NoCommit.bind ?_ fun _ ↦ ?_
  · exact NoCommit.readScalar
  · exact NoCommit.keccakOpen _ _ _ _ _
  · split
    refine NoCommit.bind NoCommit.readScalar fun _ ↦ NoCommit.bind (NoCommit.require _) fun _ ↦
      NoCommit.bind (NoCommit.ret _) fun _ ↦ NoCommit.bind (NoCommit.sumcheck _ _ _) fun _ ↦ ?_
    split
    refine NoCommit.bind (NoCommit.keccakOpen _ _ _ _ _) fun _ ↦ ?_
    no_commit'

theorem NoCommit.keccakPhase (layout : Layout) (evaluations : List (List E × List E)) :
    NoCommit (LeanVM.Protocol.Verifier.keccakPhase layout evaluations) := by
  unfold LeanVM.Protocol.Verifier.keccakPhase
  split
  exact NoCommit.verifyKeccak _ _ _

end NoCommitSteps

/-- **`walk`'s body runs `verifyExecution`**, the deployed verifier's (`computedBytecodeValue`),
from a transcript that has read no root, on a prepared bytecode of the statement's words. -/
theorem SimRoots.walkBody (words : List K) (bc : BytecodeRust)
    (hbc : BytecodeOk words bc) (hlen : words.length < 2 ^ 64) (d : Digest) :
    SimRoots (fun roots ↦ roots = []) (walkBodyRust bc (digestBits d))
      (verifyExecution computedBytecodeValue words d) fun _ _ ↦ True := by
  unfold walkBodyRust verifyExecution
  refine SimRoots.bindR (SimR.announced words bc hbc hlen) (NoCommit.readAnnouncedSizes _) ?_
  rintro ⟨l, rows, rate⟩ ⟨L, r⟩ hab
  obtain ⟨lm, hbuilt⟩ := hab.built
  have hB := buildLayoutRust_bounds hbuilt hab.rows
  have hrel : l.Rel L := hab.rel
  have hr : r = rate.toNat := hab.rate
  subst hr
  have hs30 : l.stackLog ≤ 30 := hab.stack30
  have hs : l.stackLog ≤ 64 := by omega
  dsimp only
  rw [← hrel.stackLog, commitStack_eq ⟨hab.stack16, hab.stack30⟩ ⟨hab.rate1, hab.rate4⟩]
  refine SimRoots.commit_bind fun dd ↦ ?_
  refine SimRoots.bindR (SimR.readOod _) (NoCommit.readOod _) ?_
  rintro ⟨oz, ov⟩ ood ⟨rfl, hoz⟩
  refine SimRoots.bindR (SimR.verifyBusBalance l L hrel words bc hbc hab.bytecode hB.logMemory
    hB.logBytecode hB.blocks hB.counts) (NoCommit.verifyBusBalance _) fun bus bus' hbus ↦ ?_
  refine SimRoots.bindR (Sim.tablePhase l L hrel hB bus bus' hbus) (NoCommit.tablePhase _ _)
    fun evs evs' hevs ↦ ?_
  subst hevs
  refine SimRoots.bindR (Sim.publicInput l L hrel d) (NoCommit.publicInputPhase _ _)
    fun pcs pcs' hpcs ↦ ?_
  subst hpcs
  refine SimRoots.bindR (SimR.keccakPhase l L hrel evs) (NoCommit.keccakPhase _ _) ?_
  rintro ⟨ko, k0, k1⟩ ko' hko
  simp only at hko
  subst hko
  dsimp only [KeccakOpenings.toSpec]
  refine SimRoots.bindR (SimR.ringSwitch_agree _ _) (NoCommit.ringSwitch _ _) ?_
  rintro ⟨rt, rw⟩ ⟨rt', rw'⟩ ⟨h1, -, h3⟩
  simp only at h1 h3
  subst h1
  refine SimRoots.ofOption_bind fun q hq ↦ ?_
  refine SimRoots.bind_pure (SimRoots.weaken (fun roots h ↦ stackRoots_of h)
    (SimRoots.verifyStackedOpening _ _ dd ?_)) _
  have hclaims : bus.claims ++ tableClaimsRust evs ++ pcs ++
      ko.outputs.toList.map (fun pw ↦ (⟨4, pw.1, pw.2⟩ : ColumnClaim)) =
      bus'.claims ++ tableColumnClaims evs ++ pcs ++
        ko.outputs.toList.map (fun pw ↦ (⟨qkeccak, pw.1, pw.2⟩ : ColumnClaim)) := by
    rw [hbus.claims, tableClaimsRust, tableColumnClaims, globalColumnBasesRust_eq]
    rfl
  rw [hclaims]
  refine .cons (stackClaimRel_placedRing hs L q (placement_of_committed hrel hq).symm rw rw'
    h3 rt) (List.rel_append (onStack_rel l L hrel hs _) (.cons (stackClaimRel_eq _ _ _) .nil))

/-! ## The end theorem -/

/-- **`verify_execution` is sound for the statement**: where the mirror of `verify_execution`
(checked mode, from `Transcript::new` on the bytecode's IV) returns `Ok`, on the bytecode
`Bytecode::new` prepared from the statement's words, the statement's verifier over Keccak-f[1600]
accepts. Every leaf index fits a `u64` (the wire format's). -/
theorem walkRust_sound (words : List K) (bc : BytecodeRust)
    (hbc : newRust (words.map BF64.toBitVec) = some bc) (publicInput : Digest) (proof : Proof)
    (hl : ∀ phase ∈ proof.openings, ∀ o ∈ phase, o.leafIndex < 2 ^ 64) {summary : SummaryRust}
    (h : verifyExecutionRust bc (digestBits publicInput) proof = some summary) :
    verifyWith (m := Id) keccakF1600 words publicInput proof = true := by
  have hlen : words.length < 2 ^ 64 := by
    have := newRust_length hbc
    rw [List.length_map] at this
    omega
  replace hbc := newRust_ok hbc
  have ht0 : (⟨proof, SpongeRust.new bc.fiatShamirIv (digestBits publicInput), 0, 0, true, []⟩ :
      TState) = TState.new proof (fiatShamirIv words) publicInput true := by
    rw [TState.new, hbc.iv]
  unfold verifyExecutionRust at h
  rw [ht0] at h
  obtain ⟨⟨_, _⟩, hrun, -⟩ := Option.map_eq_some_iff.mp h
  exact runProof_of_simRoots (SimRoots.walkBody words bc hbc hlen publicInput) proof _ publicInput
    hl hrun

/-- `main`'s verdict on its decoded input (`formal/rv64mc/guest/src/main.rs`): the bytecode's
words, the public input and the proof as `main` reads them. `REJECT` (`false`) where
`Bytecode::new` fails, else `ACCEPT` exactly where `verify_execution` returns `Ok`. `ABORT` on
malformed input is not here: it is the decoding's (`decodeInput`) and the machine code's. -/
def mainVerdictRust (words : List (BitVec 64)) (publicInput : List (BitVec 8)) (proof : Proof) :
    Bool :=
  match newRust words with
  | none => false
  | some bc => (verifyExecutionRust bc publicInput proof).isSome

/-- **`main` accepts only what the statement accepts.** -/
theorem mainVerdictRust_sound (words : List K) (publicInput : Digest) (proof : Proof)
    (hl : ∀ phase ∈ proof.openings, ∀ o ∈ phase, o.leafIndex < 2 ^ 64)
    (h : mainVerdictRust (words.map BF64.toBitVec) (digestBits publicInput) proof = true) :
    verifyWith (m := Id) keccakF1600 words publicInput proof = true := by
  unfold mainVerdictRust at h
  split at h
  · cases h
  · next bc hbc =>
    obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp h
    exact walkRust_sound words bc hbc publicInput proof hl hs

end

/--
info: 'Rv64mc.Model.mainVerdictRust_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainVerdictRust_sound

end Rv64mc.Model
