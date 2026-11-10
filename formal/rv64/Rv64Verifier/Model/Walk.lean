import Rv64Verifier.Model.Bus
import Rv64Verifier.Model.Whir
import Rv64Verifier.Model.Layout
import Rv64Verifier.Model.KeccakGkr
import Rv64Verifier.Model.Bytecode

/-!
# `walk`, as the Rust runs it

`crates/verifier/src/lib.rs`'s `walk` in checked mode (`verify_execution`), mirrored in `TM` from
the other files' mirrors, step by step in the Rust's order, and `walkRust_sound`: where the mirror
returns `Ok` from the transcript `Transcript::new` starts, the statement's compiled verifier
accepts.

The steps are `announcedRust` (step 1: the announced sizes, their checks and `build_layout`), the
stack's root (step 2), `verifyBusBalanceM` (step 3), `tablePhaseRust` and `tableClaimsRust`
(step 4), `publicInputRust` (step 5), `keccakPhaseRust` (step 6), then ring switching, the stack
claims and `verify_stacked_opening` (step 7), and `finish`. Each is proved to run the statement's
step (`verifyExecution`'s), so the composition runs `verifyExecution computedBytecodeValue`.

The root's tree shape is a ghost (`TState.roots`): the Rust's step 2 reads two scalars and makes a
digest, and `TM.commit` records the shape the opening's level 0 checks, `stackShape`. The Rust's
`build_layout` reads the bytecode's length only, and `verify_bus_balance` its `evaluate`; the
mirror passes them `bc.len` and `evaluateRust bc`, and `layout.toSpec []` (the statement's layout
with no words, which `verifyBusBalanceM` never reads). The public input is the 32 bytes
`verify_execution` takes.

`walkRust_sound` assumes of the inputs only that the bytecode structure is prepared from the
table's words and carries their IV (`Bytecode::new` builds such a one: `walkRust_sound_new`), and
that the table's length fits a `usize`.
-/

namespace Rv64Verifier.Model
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

/-! ## Generic steps -/

/-- `slice[start..stop]`, a panic out of range. -/
def sliceRust {α : Type} (l : List α) (start stop : ℕ) : Option (List α) :=
  if start ≤ stop ∧ stop ≤ l.length then some ((l.drop start).take (stop - start)) else none

/-- `slice[index] = value`, a panic out of range. -/
def setRust {α : Type} (l : List α) (index : ℕ) (value : α) : Option (List α) :=
  if index < l.length then some (l.set index value) else none

theorem sliceRust_some {l : List E} {start stop : ℕ} {out : List E}
    (h : sliceRust l start stop = some out) :
    out = (List.range (stop - start)).map fun i ↦ l.getD (start + i) 0 := by
  unfold sliceRust at h
  split_ifs at h with hc
  cases h
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]
    omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by omega)]

theorem SimR.bind_pure_left {α β γ : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    {f : α → γ} {r' : γ → β → Prop} (h : SimR m P r) (hr : ∀ a b, r a b → r' (f a) b) :
    SimR (m >>= fun a ↦ Pure.pure (f a)) P r' := by
  have := SimR.bind h fun a b hab ↦ (SimR.pure (r := r') (hr a b hab) :
    SimR (Pure.pure (f a) : TM γ) (VerifierProgram.ret b) r')
  rwa [VerifierProgram.bind_ret] at this

/-! ## Step 1: the announced sizes and the layout (`lib.rs:219-233`) -/

/-- `walk`'s step 1: the announced sizes read and checked, and `build_layout`; the layout, the
row counts and the rate exponent. -/
def announcedRust (bc : BytecodeRust) :
    TM (LayoutMirror.LayoutRust × List (BitVec 64) × BitVec 64) := do
  let announced ← TM.nextScalars (2 + LayoutMirror.nTablesRust)
  TM.require (announced.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0)
  let logMemory := ((announced.getD 0 0).limb 0).toBitVec
  let tableRows := ((announced.drop 1).take LayoutMirror.nTablesRust).map fun value ↦
    (value.limb 0).toBitVec
  let logInverseRate := ((announced.getD (1 + LayoutMirror.nTablesRust) 0).limb 0).toBitVec
  TM.require (1#64 ≤ logInverseRate ∧ logInverseRate ≤ 4#64)
  let layout ← TM.ofOption
    (LayoutMirror.buildLayoutRust (BitVec.ofNat 64 bc.len) logMemory tableRows)
  TM.require (Pcs.minStackedLog ≤ layout.stackLog ∧ layout.stackLog ≤ Pcs.maxStackedLog)
  pure (layout, tableRows, logInverseRate)

/-- What step 1 establishes of the layout. -/
structure LayoutOk (table : List K) (l : LayoutMirror.LayoutRust) : Prop where
  build : ∃ logMemory tableRows, tableRows.length = LayoutMirror.nTablesRust ∧
    LayoutMirror.buildLayoutRust (BitVec.ofNat 64 table.length) logMemory tableRows = some l ∧
    buildLayout table logMemory.toNat (tableRows.map BitVec.toNat) = some (l.toSpec table)
  stack : 15 ≤ l.stackLog ∧ l.stackLog ≤ 28

theorem getLastD_eq_getD {l : List E} {n : ℕ} (h : l.length = n + 1) :
    l.getLastD 0 = l.getD n 0 := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, h,
    Nat.add_sub_cancel]

theorem headD_eq_getD (l : List E) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem announcedRust_sim (table : List K) (bc : BytecodeRust) (hbc : bc.len = table.length)
    (hlen : table.length < 2 ^ 64) :
    SimR (announcedRust bc) (readAnnouncedSizes table) fun a b ↦
      b = (a.1.toSpec table, a.2.2.toNat) ∧ LayoutOk table a.1 ∧ 1 ≤ a.2.2.toNat ∧
        a.2.2.toNat ≤ 4 := by
  have ht : tables.length = LayoutMirror.nTablesRust := by decide +kernel
  unfold announcedRust readAnnouncedSizes
  rw [ht]
  refine SimR.bindPost (Sim.nextScalars _) (Returns.nextScalars _) fun announced hlen8 ↦ ?_
  refine SimR.bindEq (Sim.require _) fun _ ↦ ?_
  have hlast : announced.getLastD 0 = announced.getD (1 + LayoutMirror.nTablesRust) 0 :=
    getLastD_eq_getD (by rw [hlen8]; rfl)
  refine SimR.bind (SimR.require_post (c' := 1 ≤ kToNat ((announced.getLastD 0).limb 0) ∧
    kToNat ((announced.getLastD 0).limb 0) ≤ 4) ?_) fun _ _ hrate ↦ ?_
  · rw [hlast, BitVec.le_def, BitVec.le_def]
    rfl
  refine SimR.ofOption_bind fun l hl ↦ ?_
  have hrows : (((announced.drop 1).take LayoutMirror.nTablesRust).map fun value ↦
      (value.limb 0).toBitVec).length = LayoutMirror.nTablesRust := by
    simp only [List.length_map, List.length_take, List.length_drop, hlen8]
    rfl
  have hspec := LayoutMirror.buildLayoutRust_eq table ((announced.getD 0 0).limb 0).toBitVec _ hlen
    hrows
  rw [← hbc, hl, Option.map_some] at hspec
  have hspec' : buildLayout table (kToNat ((announced.headD 0).limb 0))
      (((announced.drop 1).take LayoutMirror.nTablesRust).map fun value ↦ kToNat (value.limb 0)) =
      some (l.toSpec table) := by
    rw [hspec, headD_eq_getD, List.map_map]
    rfl
  rw [hspec',
    show liftOption (some (l.toSpec table)) = VerifierProgram.ret (l.toSpec table) from rfl,
    VerifierProgram.ret_bind]
  refine SimR.bind (SimR.require_post Iff.rfl) fun _ _ hstack ↦ SimR.pure ⟨?_, ⟨?_, hstack⟩, ?_⟩
  · rw [hlast]
    rfl
  · exact ⟨_, _, hrows, hbc ▸ hl, hspec.symm⟩
  · simpa [BitVec.le_def] using hrate

/-! ## Step 2: the stack's root (`lib.rs:235-237`) -/

/-- The tree shape level `0` of the stack's opening reads the root at: a ghost (`TState.roots`). -/
def stackShape (stackLog logInvRate : ℕ) : ℕ × ℕ :=
  match Whir.ladder stackLog logInvRate with
  | some (level :: _) => levelShape stackLog level (2 ^ level.fold)
  | _ => (0, 0)

/-- The ladder has a first level. -/
def ladderConsB (μ r : ℕ) : Bool :=
  match Whir.ladder μ r with
  | some (_ :: _) => true
  | _ => false

theorem ladder_cons_window : ∀ μ < 29, ∀ r < 5, Whir.Admissible μ r → ladderConsB μ r = true := by
  decide +kernel

theorem commitStack_sim {μ r : ℕ} (hμ : 15 ≤ μ ∧ μ ≤ 28) (hr : 1 ≤ r ∧ r ≤ 4) :
    SimUnit (TM.commit (stackShape μ r).1 (stackShape μ r).2) (commitStack μ r) := by
  have hb := ladder_cons_window μ (by omega) r (by omega) ⟨hμ.1, hμ.2, hr.1, hr.2⟩
  unfold ladderConsB at hb
  unfold stackShape commitStack
  split at hb
  · rename_i level rest hl
    rw [hl]
    exact SimUnit.commit _ _
  · cases hb

/-! ## Step 3: the bus (`lib.rs:239-240`) -/

theorem verifyBusBalanceM_toSpec (ev : List E → Option E) (l : LayoutMirror.LayoutRust)
    (b b' : List K) : verifyBusBalanceM ev (l.toSpec b) = verifyBusBalanceM ev (l.toSpec b') :=
  rfl

theorem busBounds {len lm : BitVec 64} {rows : List (BitVec 64)} {l : LayoutMirror.LayoutRust}
    (h : LayoutMirror.buildLayoutRust len lm rows = some l) (table : List K) :
    BusBounds (l.toSpec table) := by
  obtain ⟨h1, h2, h3⟩ := LayoutMirror.buildLayoutRust_busLayout h
  have e : ∀ bs : List LayoutMirror.BusBlockRust,
      (bs.map LayoutMirror.BusBlockRust.toSpec).map (·.logRows) = bs.map (·.logRows) :=
    fun bs ↦ by rw [List.map_map]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [LayoutMirror.LayoutRust.toSpec, e]
    exact h1
  · simp only [LayoutMirror.LayoutRust.toSpec, e]
    exact h2
  · simp only [LayoutMirror.LayoutRust.toSpec, e]
    exact h3
  · intro b hb
    simp only [LayoutMirror.LayoutRust.toSpec, List.mem_append, List.mem_map] at hb
    rcases hb with (⟨b', -, rfl⟩ | ⟨b', -, rfl⟩) | ⟨b', -, rfl⟩ <;> exact b'.rows.isLt

/-- `Bytecode::evaluate` on a prepared table returns the statement's value. -/
theorem evaluateRust_hv (table : List K) (bc : BytecodeRust)
    (h : Prepared (table.map BF64.toBitVec) bc) :
    ∀ pt v, evaluateRust bc pt = some v →
      ∀ σ, runK (computedBytecodeValue table pt) σ = some (v, σ) := by
  intro pt v hv σ
  rw [evaluateRust_eq _ bc h] at hv
  split_ifs at hv
  cases hv
  rw [List.map_map]
  rfl

theorem bus_sim (table : List K) (bc : BytecodeRust) (hprep : Prepared (table.map BF64.toBitVec) bc)
    (l : LayoutMirror.LayoutRust) (hl : LayoutOk table l) :
    SimR (verifyBusBalanceM (evaluateRust bc) (l.toSpec []))
      (verifyBusBalance computedBytecodeValue (l.toSpec table))
      fun a b ↦ a.toSpec = b ∧ a.forms.length = tables.length := by
  obtain ⟨_, _, _, hb, _⟩ := hl.build
  rw [verifyBusBalanceM_toSpec _ l [] table]
  exact SimR.and_returns (SimR.verifyBusBalance _ _ _ (busBounds hb table)
    (evaluateRust_hv table bc hprep)) (Returns.verifyBusBalance _ _)

/-! ## Step 4: the table sumcheck and the tables' claims (`lib.rs:242-266`) -/

/-- `walk`'s step 4: `xi`, its powers split at the constraints' count, the target, and
`table_sumcheck`. -/
def tablePhaseRust (layout : LayoutMirror.LayoutRust) (bus : BusResultRust) :
    TM (List (List E × List E)) := do
  let xi ← TM.sample
  let nConstraints := (layout.tables.map LayoutMirror.TableRust.nConstraints).sum
  let xiPowers := powers xi (nConstraints + 3)
  let constraintPowers := xiPowers.take nConstraints
  let formPowers := xiPowers.drop nConstraints
  let target := dotRust formPowers bus.totals
  tableSumcheckM tables layout.tableLogHeights bus.forms constraintPowers formPowers bus.point
    target

/-- The loop extending `claims` with each table's evaluations at its point. -/
def tableClaimsRust (evaluations : List (List E × List E)) : List ColumnClaim :=
  (LayoutMirror.globalColumnBasesRust.zip evaluations).flatMap fun (base, point, values) ↦
    values.zipIdx.map fun (value, column) ↦ ⟨base + column, point, value⟩

theorem tablePhaseRust_sim (table : List K) (l : LayoutMirror.LayoutRust) (bus : BusResultRust)
    (htab : l.tables = LayoutMirror.tablesRust) (hh : l.tableLogHeights.length = tables.length)
    (hf : bus.forms.length = tables.length) :
    Sim (tablePhaseRust l bus) (tablePhase (l.toSpec table) bus.toSpec) := by
  unfold tablePhaseRust tablePhase
  rw [htab, LayoutMirror.tablesRust_nConstraints]
  refine Sim.bind Sim.sample fun xi ↦ ?_
  simp only [dotRust_eq]
  exact Sim.tableSumcheck _ _ _ _ _ _ hh hf

theorem tableClaimsRust_eq (evaluations : List (List E × List E)) :
    tableClaimsRust evaluations = tableColumnClaims evaluations := by
  rw [tableClaimsRust, tableColumnClaims, LayoutMirror.globalColumnBasesRust_eq]

/-! ## Step 5: the public input (`lib.rs:268-281`) -/

/-- `Digest::halves` of the digest whose words are `w`: `(E::new(w0, w1, 0), E::new(w2, w3, 0))`. -/
def halvesRust (w : List (BitVec 64)) : E × E :=
  (E.ofLimbs (BF64.ofBitVec (w.getD 0 0)) (BF64.ofBitVec (w.getD 1 0)) 0,
    E.ofLimbs (BF64.ofBitVec (w.getD 2 0)) (BF64.ofBitVec (w.getD 3 0)) 0)

theorem halvesRust_eq (d : Digest) :
    halvesRust (digestWordsRust (byteBits (digestBytes d))) = digestHalves d := by
  rw [digestWordsRust_digestBytes]
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => rfl

/-- `walk`'s step 5: a challenge, and each memory limb's claim at `(challenge, 0, …, 0)`; the
public input is its 32 bytes. -/
def publicInputRust (layout : LayoutMirror.LayoutRust) (publicInput : List (BitVec 8)) :
    TM (List ColumnClaim) := do
  let publicChallenge ← TM.sample
  let halves := halvesRust (digestWordsRust publicInput)
  let publicPoint ← TM.ofOption (setRust (List.replicate layout.logMemory 0) 0 publicChallenge)
  let v0 ← TM.ofOption (multilinearEvalRust [ofK (halves.1.limb 0), ofK (halves.2.limb 0)]
    [publicChallenge])
  let v1 ← TM.ofOption (multilinearEvalRust [ofK (halves.1.limb 1), ofK (halves.2.limb 1)]
    [publicChallenge])
  let v2 ← TM.ofOption (multilinearEvalRust [ofK (halves.1.limb 2), ofK (halves.2.limb 2)]
    [publicChallenge])
  pure [⟨memory0, publicPoint, v0⟩, ⟨memory1, publicPoint, v1⟩, ⟨memory2, publicPoint, v2⟩]

theorem publicInputRust_sim (table : List K) (l : LayoutMirror.LayoutRust) (publicInput : Digest)
    (hm : ((l.toSpec table).placement memory0).variableCount = l.logMemory) (h0 : 0 < l.logMemory) :
    Sim (publicInputRust l (byteBits (digestBytes publicInput)))
      (publicInputPhase (l.toSpec table) publicInput) := by
  unfold publicInputRust publicInputPhase
  rw [halvesRust_eq]
  refine Sim.bind Sim.sample fun c ↦ ?_
  have hset : setRust (List.replicate l.logMemory (0 : E)) 0 c =
      some (c :: List.replicate (l.logMemory - 1) 0) := by
    obtain ⟨n, hn⟩ : ∃ n, l.logMemory = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
    simp [setRust, hn, List.replicate_succ]
  have hml : ∀ a b : K, multilinearEvalRust [ofK a, ofK b] [c] =
      some (multilinearEval [ofK a, ofK b] [c]) :=
    fun a b ↦ multilinearEvalRust_eq _ _ (by simp)
  simp only [hset, hml, TM.ofOption, pure_bind, hm]
  exact Sim.pure _

/-! ## Step 6: `KECCAK` (`lib.rs:283-300`) -/

/-- `walk`'s step 6: the `KECCAK` table's point and output lanes, `verify_keccak` between two
reads of the stream's position; the openings and the positions. -/
def keccakPhaseRust (layout : LayoutMirror.LayoutRust) (evaluations : List (List E × List E)) :
    TM (Gkr.KeccakOpenings × ℕ × ℕ) := do
  let pv ← TM.ofOption evaluations[LayoutMirror.opKeccakRust]?
  let keccakStart ← TM.streamPosition
  let output ← TM.ofOption (sliceRust pv.2 LayoutMirror.keccakOutRust
    (LayoutMirror.keccakOutRust + LayoutMirror.stateLanesRust))
  let openings ← Gkr.verifyKeccakRust ⟨layout.keccakLogSteps, LayoutMirror.keccakDepthRust⟩ pv.1
    output
  let keccakEnd ← TM.streamPosition
  pure (openings, keccakStart, keccakEnd)

theorem keccakPhaseRust_sim (table : List K) (l : LayoutMirror.LayoutRust)
    (evaluations : List (List E × List E))
    (hk : l.keccakLogSteps = l.tableLogHeights.getD opKeccak 0) :
    SimR (keccakPhaseRust l evaluations) (keccakPhase (l.toSpec table) evaluations)
      fun a b ↦ a.1.toSpec = b := by
  unfold keccakPhaseRust keccakPhase
  refine SimR.ofOption_bind fun pv hpv ↦ ?_
  rcases pv with ⟨p, v⟩
  have hget : evaluations.getD opKeccak ([], []) = (p, v) := by
    rw [List.getD_eq_getElem?_getD]
    exact congrArg (·.getD ([], [])) hpv
  rw [hget]
  refine SimR.streamPosition_left fun k0 ↦ ?_
  refine SimR.ofOption_bind fun out hout ↦ ?_
  obtain rfl := sliceRust_some hout
  have hko : keccakOut = LayoutMirror.keccakOutRust := by decide +kernel
  have h25 : LayoutMirror.keccakOutRust + LayoutMirror.stateLanesRust -
      LayoutMirror.keccakOutRust = 25 := by decide
  rw [h25, hk]
  dsimp only
  rw [hko, ← VerifierProgram.bind_ret (verifyKeccak _ _ _)]
  exact SimR.bind (SimR.of_map (Gkr.verifyKeccakRust_sim _ _ _)) fun o b hob ↦
    SimR.streamPosition_left fun k1 ↦ SimR.pure hob

/-! ## Step 7, and `walk` -/

/-- `ColumnClaim::on_stack`, its weight `StackWeight::Eq`. -/
def onStackRust (layout : LayoutMirror.LayoutRust) (c : ColumnClaim) : Option Pcs.StackClaimRust :=
  (LayoutMirror.ColumnClaimRust.onStack ⟨c.column, c.point, c.value⟩ layout).map fun pv ↦
    ⟨.eq pv.1, pv.2⟩

theorem onStackRust_cases (l : LayoutMirror.LayoutRust) (table : List K) (hs : l.stackLog ≤ 64)
    (c : ColumnClaim) :
    (onStackRust l c = none ∧ c.onStack (l.toSpec table) = none) ∨
      ∃ pv : List E × E, onStackRust l c = some ⟨.eq pv.1, pv.2⟩ ∧
        c.onStack (l.toSpec table) = some (fun x ↦ eqEval pv.1 x, pv.2) := by
  have h := LayoutMirror.ColumnClaimRust.onStack_eq ⟨c.column, c.point, c.value⟩ l table hs
  unfold onStackRust
  cases hx : LayoutMirror.ColumnClaimRust.onStack ⟨c.column, c.point, c.value⟩ l with
  | none =>
    rw [hx] at h
    exact .inl ⟨rfl, h.symm⟩
  | some pv =>
    rw [hx] at h
    exact .inr ⟨pv, rfl, h.symm⟩

theorem onStack_rel (l : LayoutMirror.LayoutRust) (table : List K) (hs : l.stackLog ≤ 64) :
    ∀ claims : List ColumnClaim, List.Forall₂ (Pcs.StackClaimRel l.stackLog)
      (claims.filterMap (onStackRust l)) (claims.filterMap (·.onStack (l.toSpec table)))
  | [] => .nil
  | c :: cs => by
    rcases onStackRust_cases l table hs c with ⟨h1, h2⟩ | ⟨pv, h1, h2⟩
    · simp only [List.filterMap_cons, h1, h2]
      exact onStack_rel l table hs cs
    · simp only [List.filterMap_cons, h1, h2]
      exact .cons (Pcs.stackClaimRel_eq _ pv.1 pv.2) (onStack_rel l table hs cs)

theorem placementsOf_zero (k : ℕ) (ks : List ℕ) :
    ((placementsOf (k :: ks)).1.getD 0 none).map Placement.variableCount = some k := by
  have h1 : keccakSlot 0 = none := by decide +kernel
  have h2 : 0 ∉ keccakOutputColumns := by decide +kernel
  unfold placementsOf
  simp [List.zipIdx_cons, h1, h2]

theorem variableCount_of_map {o : Option Placement} {k : ℕ}
    (h : o.map Placement.variableCount = some k) : (o.getD default).variableCount = k := by
  cases o <;> simp_all

/-- What the statement's layout gives the public input's step and the table sumcheck. -/
theorem buildLayout_facts {table : List K} {lm : ℕ} {rows : List ℕ} {L : Layout}
    (h : buildLayout table lm rows = some L) :
    (L.placement memory0).variableCount = L.logMemory ∧ 16 ≤ L.logMemory ∧
      L.tableLogHeights.length = tables.length := by
  unfold buildLayout at h
  split at h
  · cases h
  · split_ifs at h with hc
    obtain ⟨-, h16, -, -, -, hrl⟩ := hc
    dsimp only at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, h16, ?_⟩
    · exact variableCount_of_map (placementsOf_zero lm _)
    · simp only [List.length_zipWith, hrl]
      rfl

/-- What `walk` returns. -/
structure SummaryRust where
  logMemory : ℕ
  tableRows : List (BitVec 64)
  logInvRate : ℕ
  bytecodePoint : List E
  keccakScalars : ℕ × ℕ

/-- `walk(bytecode, public_input, proof, true)` up to `transcript.finish()`. -/
def walkBodyRust (bc : BytecodeRust) (publicInput : List (BitVec 8)) : TM SummaryRust := do
  -- 1] memory log-size, table row counts, and log-inv-rate in WHIR
  let (layout, tableRows, logInverseRate) ← announcedRust bc
  -- 2] the WHIR commitment's root
  let _root ← TM.commit (stackShape layout.stackLog logInverseRate.toNat).1
    (stackShape layout.stackLog logInverseRate.toNat).2
  -- 3] the bus
  let bus ← verifyBusBalanceM (evaluateRust bc) (layout.toSpec [])
  -- 4] the table sumcheck
  let evaluations ← tablePhaseRust layout bus
  let claims := bus.claims ++ tableClaimsRust evaluations
  -- 5] the public input
  let publicClaims ← publicInputRust layout publicInput
  let claims := claims ++ publicClaims
  -- 6] KECCAK validity
  let (openings, keccakStart, keccakEnd) ← keccakPhaseRust layout evaluations
  let claims := claims ++
    openings.outputs.toList.map fun pw ↦ (⟨LayoutMirror.qkeccakRust, pw.1, pw.2⟩ : ColumnClaim)
  -- 7] ring switching, and the stacked opening
  let (ringTarget, ringWeight) ← Pcs.ringSwitchRust openings.inputs.1 openings.inputs.2
  Pcs.verifyStackedOpeningRust layout.stackLog logInverseRate.toNat
    (⟨.placedRing layout.qkeccak ringWeight, ringTarget⟩ :: claims.filterMap (onStackRust layout))
  pure ⟨layout.logMemory, tableRows, logInverseRate.toNat, bus.bytecodePoint,
    (keccakStart, keccakEnd)⟩

/-- `walk(bytecode, public_input, proof, true)`, after `Transcript::new`. -/
def walkRust (bc : BytecodeRust) (publicInput : List (BitVec 8)) : TM SummaryRust := do
  let summary ← walkBodyRust bc publicInput
  TM.finish
  pure summary

theorem walkBodyRust_sim (table : List K) (bc : BytecodeRust) (publicInput : Digest)
    (hprep : Prepared (table.map BF64.toBitVec) bc) (hlen : table.length < 2 ^ 64) :
    SimR (walkBodyRust bc (byteBits (digestBytes publicInput)))
      (verifyExecution computedBytecodeValue table publicInput) fun _ _ ↦ True := by
  have hbc : bc.len = table.length := hprep.len.trans (List.length_map _)
  unfold walkBodyRust verifyExecution
  refine SimR.bind (announcedRust_sim table bc hbc hlen) ?_
  rintro ⟨l, rows, lir⟩ _ ⟨rfl, hok, hr1, hr4⟩
  obtain ⟨lm, trows, -, hbuild, hspec⟩ := hok.build
  obtain ⟨hq, htabs, hks, hs64⟩ := LayoutMirror.buildLayoutRust_rest hbuild table
  obtain ⟨hmem, h16, hhl⟩ := buildLayout_facts hspec
  dsimp only
  refine SimR.bind (commitStack_sim hok.stack ⟨hr1, hr4⟩) ?_
  rintro _ ⟨⟩ _
  refine SimR.bind (bus_sim table bc hprep l hok) ?_
  rintro bus _ ⟨rfl, hforms⟩
  refine SimR.bind (tablePhaseRust_sim table l bus htabs hhl hforms) ?_
  rintro evs _ rfl
  refine SimR.bind (publicInputRust_sim table l publicInput hmem (by
    have : 16 ≤ l.logMemory := h16
    omega)) ?_
  rintro pcs _ rfl
  refine SimR.bind (keccakPhaseRust_sim table l evs hks) ?_
  rintro ⟨⟨outs, kp, ks⟩, k0, k1⟩ _ rfl
  dsimp only
  refine SimR.bind (Pcs.ringSwitchRust_sim kp ks) ?_
  rintro ⟨rt, rw⟩ ⟨bt, bw⟩ ⟨h1, h2⟩
  dsimp only at h1 h2 ⊢
  subst h1
  have hC : bus.claims ++ tableClaimsRust evs ++ pcs ++ outs.toList.map
      (fun pw ↦ (⟨LayoutMirror.qkeccakRust, pw.1, pw.2⟩ : ColumnClaim)) =
      bus.toSpec.claims ++ tableColumnClaims evs ++ pcs ++
        (⟨outs, (kp, ks)⟩ : Gkr.KeccakOpenings).toSpec.1 := by
    rw [tableClaimsRust_eq]
    rfl
  rw [hC]
  refine SimR.bind_pure_left (Pcs.verifyStackedOpeningRust_sim _ _ _ _
    (.cons ?_ (onStack_rel l table hs64 _))) fun _ _ _ ↦ trivial
  exact Pcs.stackClaimRel_ringSwitchClaim hs64 _ _ hq _ _ _ h2

/-! ## The transcript `Transcript::new` starts, and the top statement -/

/-- `Sponge::new(fiat_shamir_iv, public_input)`: one permutation of the IV's and the public
input's words, the other lanes zero. -/
def spongeNewRust (iv publicInput : List (BitVec 8)) : Sponge :=
  ⟨keccakF1600 (Vector.ofFn fun i ↦
    if i.val < 4 then UInt64.ofBitVec ((digestWordsRust iv).getD i.val 0)
    else if i.val < 8 then UInt64.ofBitVec ((digestWordsRust publicInput).getD (i.val - 4) 0)
    else 0), []⟩

/-- `Transcript::new(proof, fiat_shamir_iv, public_input, true)`. -/
def TState.init (proof : Proof) (sponge : Sponge) : TState := ⟨proof, sponge, 0, 0, []⟩

/-- `verify_execution(bytecode, public_input, proof)`: `Ok(summary)` is `some summary`. -/
def verifyExecutionRust (bc : BytecodeRust) (publicInput : List (BitVec 8)) (proof : Proof) :
    Option SummaryRust :=
  ((walkRust bc publicInput).run
    (TState.init proof (spongeNewRust bc.fiatShamirIv publicInput))).map (·.1)

theorem spongeNewRust_eq (table : List K) (publicInput : Digest) :
    spongeNewRust (fiatShamirIvRust (table.map BF64.toBitVec))
        (byteBits (digestBytes publicInput)) =
      ⟨Id.run (spongeSeedWith (m := Id) keccakF1600 table publicInput), []⟩ := by
  rw [spongeNewRust, fiatShamirIvRust_words, digestWordsRust_digestBytes]
  simp only [spongeSeedWith, Id.run, bind, seedInput]
  refine congrArg (fun s ↦ (⟨keccakF1600 s, []⟩ : Sponge))
    (congrArg Vector.ofFn (funext fun i ↦ ?_))
  split_ifs with h1 h2
  · rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, Vector.getElem_toList]
  · rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, Vector.getElem_toList]
  · rfl

/-- **`verify_execution` is sound for the statement**: where the mirror of `verify_execution`
returns `Ok`, on a bytecode structure prepared from `table` with the IV of `table` (as
`Bytecode::new` builds it, `walkRust_sound_new`), the statement's compiled verifier over
Keccak-f[1600] accepts. The bytecode's length fits a `usize`. -/
theorem walkRust_sound (table : List K) (bc : BytecodeRust) (publicInput : Digest) (proof : Proof)
    (summary : SummaryRust) (hprep : Prepared (table.map BF64.toBitVec) bc)
    (hiv : bc.fiatShamirIv = fiatShamirIvRust (table.map BF64.toBitVec))
    (hlen : table.length < 2 ^ 64)
    (h : verifyExecutionRust bc (byteBits (digestBytes publicInput)) proof = some summary) :
    verifyWith (m := Id) keccakF1600 table publicInput proof = true := by
  have hbody := walkBodyRust_sim table bc publicInput hprep hlen
  unfold verifyExecutionRust at h
  rw [hiv, spongeNewRust_eq] at h
  unfold verifyWith runProof
  change (match runK (leanVmVerifierProgram table publicInput)
      ⟨⟨Id.run (spongeSeedWith (m := Id) keccakF1600 table publicInput), []⟩, proof.stream,
        proof.openings, []⟩ with
    | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
    | _ => false) = true
  generalize Id.run (spongeSeedWith (m := Id) keccakF1600 table publicInput) = seed at h ⊢
  obtain ⟨⟨s', t'⟩, hrun, -⟩ := Option.map_eq_some_iff.mp h
  unfold walkRust at hrun
  rw [StateT.run_bind] at hrun
  cases hb : (walkBodyRust bc (byteBits (digestBytes publicInput))).run (TState.init proof ⟨seed, []⟩) with
  | none =>
    rw [hb] at hrun
    cases hrun
  | some p =>
    obtain ⟨s1, t1⟩ := p
    rw [hb] at hrun
    have hfin : t1.streamOffset = t1.proof.stream.length ∧
        t1.openingOffset = t1.proof.openings.length := by
      by_contra hc
      change (TM.finish >>= fun _ ↦ (Pure.pure s1 : TM SummaryRust)).run t1 = some (s', t') at hrun
      rw [StateT.run_bind] at hrun
      simp only [TM.finish, StateT.run] at hrun
      rw [ite_eq_right hc] at hrun
      simp at hrun
    obtain ⟨b, hrk, -⟩ := hbody _ _ _ hb
    have hinit : (TState.init proof ⟨seed, []⟩).toSpec =
        ⟨⟨seed, []⟩, proof.stream, proof.openings, []⟩ := by
      simp [TState.init, TState.toSpec]
    rw [hinit] at hrk
    have hprog : runK (leanVmVerifierProgram table publicInput)
        ⟨⟨seed, []⟩, proof.stream, proof.openings, []⟩ = some (true, t1.toSpec) := by
      unfold leanVmVerifierProgram
      rw [runK_bind, hrk]
      rfl
    have hs : t1.toSpec.stream = [] := by simp [TState.toSpec, hfin.1]
    have ho : t1.toSpec.openings = [] := by simp [TState.toSpec, hfin.2]
    rw [hprog]
    simp [hs, ho]

/-- **`walkRust_sound` for the structure `Bytecode::new` builds** from the words of `table`. -/
theorem walkRust_sound_new (table : List K) (bc : BytecodeRust) (publicInput : Digest)
    (proof : Proof) (summary : SummaryRust) (hnew : newRust (table.map BF64.toBitVec) = some bc)
    (hlen : table.length < 2 ^ 64)
    (h : verifyExecutionRust bc (byteBits (digestBytes publicInput)) proof = some summary) :
    verifyWith (m := Id) keccakF1600 table publicInput proof = true := by
  obtain ⟨bc', h1, h2, h3⟩ := newRust_spec (table.map BF64.toBitVec)
  rw [hnew, Option.some.injEq] at h1
  subst h1
  exact walkRust_sound table bc publicInput proof summary h3 h2 hlen h

/-! The axioms: Lean's three. -/

/-- info: 'Rv64Verifier.Model.walkRust_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms walkRust_sound

/-- info: 'Rv64Verifier.Model.walkRust_sound_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms walkRust_sound_new

end Rv64Verifier.Model
