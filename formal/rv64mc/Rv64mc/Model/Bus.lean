module

public import Rv64mc.Model.Layout
public import Rv64mc.Model.Bytecode

/-!
# `bus.rs` as the Rust runs it

Mirrors of `crates/verifier/src/bus.rs` in `TM` (`Model.Transcript`): `bus_grinding_bits`,
`verify_gkr_grand_products`, `bus_layout`, `verify_bus_balance` and `table_sumcheck`, each with its
simulation of the statement's program. A mirror fails exactly where the Rust returns `Err`; where
the Rust panics it may return anything. The forms the bus accumulates are related to the
statement's by value (`Model.Layout`).
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier

@[expose] public section

/-- `bus_grinding_bits(mu)`: `grinding_bits(1 << mu)`, a `u128` shift. -/
def busGrindingBitsRust (mu : ℕ) : ℕ := grindingBitsRust (1#128 <<< mu)

theorem busGrindingBitsRust_eq {mu : ℕ} (h : mu < 64) :
    busGrindingBitsRust mu = busGrindingBits mu := by
  rw [busGrindingBitsRust, grindingBitsRust_eq, busGrindingBits, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.one_mod_two_pow (by norm_num), one_mul,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]

/-! ## `verify_gkr_grand_products` -/

/-- One iteration of `verify_gkr_grand_products`' loop at `layer`: `step` levels, one when `layer`
is odd. The children's products are checked in checked mode. -/
def gkrStepRust (layer : ℕ) (values point : List E) : TM (List E × List E) := do
  let step := if layer % 2 = 1 then 1 else 2
  TM.grindCheck (grindingBitsRust (BitVec.ofNat 128 (3 - 1)))
  let combiner ← TM.sample
  let claim := polyEvalRust values combiner
  let (x, claim) ← TM.sumcheck claim ((1 <<< step) + 1) (point.map some)
  let child0 ← TM.nextScalars (1 <<< step)
  let child1 ← TM.nextScalars (1 <<< step)
  let child2 ← TM.nextScalars (1 <<< step)
  let children := [child0, child1, child2]
  TM.whenChecked (TM.require
    (claim = polyEvalRust (children.map fun child ↦ child.foldl (· * ·) 1) combiner))
  let last := layer == step
  TM.grindCheck (grindingBitsRust (BitVec.ofNat 128 (step <<< (if last then 1 else 0))))
  let y ← TM.samples step
  let values ← TM.ofOption (children.mapM fun child ↦ multilinearEvalRust child y)
  Pure.pure (values, y ++ x)

/-- The `while layer > 0` loop. -/
def gkrLoopRust (layer : ℕ) (values point : List E) : TM (List E × List E) :=
  if _h : 0 < layer then do
    let (values, point) ← gkrStepRust layer values point
    gkrLoopRust (layer - if layer % 2 = 1 then 1 else 2) values point
  else Pure.pure (values, point)
termination_by layer
decreasing_by split <;> omega

/-- `verify_gkr_grand_products(depth, transcript)`: the count root, the point, the values. -/
def verifyGkrRust (depth : ℕ) : TM (E × List E × List E) := do
  let shared ← TM.nextScalar
  let count ← TM.nextScalar
  let (values, point) ← gkrLoopRust depth [shared, shared, count] []
  Pure.pure (count, point, values)

private theorem mapM_some_eq {α β : Type} {f : α → Option β} {g : α → β}
    (hf : ∀ a b, f a = some b → b = g a) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r = l.map g
  | [], r, h => by simp only [List.mapM_nil] at h; cases h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some r' =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some] at h
        cases (Option.some.inj h : b :: r' = r)
        rw [hf a b ha, mapM_some_eq hf l r' hl]
        rfl

theorem SimR.gkrStep (layer : ℕ) (values point : List E) :
    SimR (gkrStepRust layer values point)
      (gkrStep (if layer % 2 = 1 then 1 else 2) (layer == if layer % 2 = 1 then 1 else 2)
        ⟨values, point⟩ >>= fun s ↦ VerifierProgram.ret (s.values, s.point))
      fun a b ↦ a = b ∧ a.2.length = (if layer % 2 = 1 then 1 else 2) + point.length := by
  have hs : (if layer % 2 = 1 then 1 else 2) ≤ 2 := by split <;> omega
  unfold gkrStepRust LeanVM.Protocol.Verifier.gkrStep
  dsimp only
  generalize (if layer % 2 = 1 then 1 else 2) = step at hs ⊢
  simp only [VerifierProgram.bind_assoc', Nat.one_shiftLeft, polyEvalRust_eq,
    grindingBitsRust_ofNat (show 3 - 1 < 2 ^ 64 by norm_num)]
  refine SimR.bindEq (Sim.grindCheck _) fun _ ↦ SimR.bindEq Sim.sample fun combiner ↦ ?_
  refine SimR.sumcheck_bind (count := 2 ^ step + 1) _
    (by have := Nat.one_le_two_pow (n := step); omega)
    (by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hs; omega) _ fun x c hx ↦ ?_
  refine SimR.bindEq (Sim.nextScalars _) fun c0 ↦ SimR.bindEq (Sim.nextScalars _) fun c1 ↦
    SimR.bindEq (Sim.nextScalars _) fun c2 ↦ ?_
  refine SimR.whenChecked_bind (SimR.bindEq (Sim.require_iff ?_) fun _ ↦ ?_)
  · simp only [List.map_cons, List.map_nil, polyEvalRust_eq, prodE]
  · have hg :
        grindingBitsRust (BitVec.ofNat 128 (step <<< (if (layer == step) = true then 1 else 0)))
        = grindingBits (if (layer == step) = true then 2 * step else step) := by
      rw [grindingBitsRust_ofNat (by split <;> simp [Nat.shiftLeft_eq] <;> omega)]
      congr 1
      split <;> simp [Nat.shiftLeft_eq, mul_comm]
    rw [hg]
    refine SimR.bindEq (Sim.grindCheck _) fun _ ↦
      SimR.bindPost (Sim.samples _) (Returns.samples _) fun y hy ↦ ?_
    refine SimR.ofOption_bind fun vs hvs ↦ ?_
    rw [mapM_some_eq (fun _ _ h ↦ multilinearEvalRust_some h) _ _ hvs]
    exact SimR.pure ⟨rfl, by simp [hy, hx]⟩

/-- `gkrLayers` peels the loop's first step, of `1` level when the depth is odd. -/
private theorem gkrLayers_succ (n : ℕ) (values point : List E) :
    gkrLayers (n + 1) ⟨values, point⟩ =
      LeanVM.Protocol.Verifier.gkrStep (if (n + 1) % 2 = 1 then 1 else 2)
        (n + 1 == if (n + 1) % 2 = 1 then 1 else 2)
        ⟨values, point⟩ >>= gkrLayers (n + 1 - if (n + 1) % 2 = 1 then 1 else 2) := by
  rcases n with _ | m
  · rfl
  · rw [gkrLayers]
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · rw [ite_eq_right (show ¬ m % 2 = 1 by omega),
        ite_eq_right (show ¬ (m + 1 + 1) % 2 = 1 by omega),
        show (m + 1 + 1 == 2) = decide (m = 0) by cases m <;> rfl,
        show m + 1 + 1 - 2 = m by omega]
    · rw [ite_eq_left hm, ite_eq_left (show (m + 1 + 1) % 2 = 1 by omega),
        show (m + 1 + 1 == 1) = false by simp, show m + 1 + 1 - 1 = m + 1 by omega]

theorem SimR.gkrLoop (layer : ℕ) : ∀ values point,
    SimR (gkrLoopRust layer values point)
      (gkrLayers layer ⟨values, point⟩ >>= fun s ↦ VerifierProgram.ret (s.values, s.point))
      fun a b ↦ a = b ∧ a.2.length = layer + point.length := by
  induction layer using Nat.strong_induction_on with
  | _ layer ih =>
    intro values point
    rw [gkrLoopRust]
    match layer with
    | 0 => exact SimR.pure ⟨rfl, by simp⟩
    | n + 1 =>
      simp only [Nat.zero_lt_succ, dite_true]
      have hstep := SimR.gkrStep (n + 1) values point
      have h := SimR.bind hstep (Q := fun vp ↦ gkrLayers (n + 1 - if (n + 1) % 2 = 1 then 1 else 2)
          ⟨vp.1, vp.2⟩ >>= fun s ↦ VerifierProgram.ret (s.values, s.point))
        (k := fun vp ↦ gkrLoopRust (n + 1 - if (n + 1) % 2 = 1 then 1 else 2) vp.1 vp.2)
        (r' := fun a b ↦ a = b ∧ a.2.length = n + 1 + point.length) fun a b ⟨hab, hl⟩ ↦ by
          subst hab
          refine SimR.mono (ih _ (by split <;> omega) a.1 a.2) fun c d ⟨hcd, hc⟩ ↦ ⟨hcd, ?_⟩
          rw [hc, hl]
          split <;> omega
      rw [VerifierProgram.bind_assoc'] at h
      rw [gkrLayers_succ, VerifierProgram.bind_assoc']
      exact h

theorem SimR.verifyGkr (depth : ℕ) :
    SimR (verifyGkrRust depth) (verifyGkrGrandProducts depth)
      fun a b ↦ a = b ∧ a.2.1.length = depth := by
  unfold verifyGkrRust verifyGkrGrandProducts
  refine SimR.bindEq Sim.nextScalar fun shared ↦ SimR.bindEq Sim.nextScalar fun count ↦ ?_
  have h := SimR.bind (SimR.gkrLoop depth [shared, shared, count] [])
    (k := fun vp ↦ (Pure.pure (count, vp.2, vp.1) : TM (E × List E × List E)))
    (Q := fun vp ↦ VerifierProgram.ret (count, vp.2, vp.1))
    (r' := fun a b ↦ a = b ∧ a.2.1.length = depth) fun a b ⟨hab, hl⟩ ↦
      SimR.pure ⟨by rw [hab], by simpa using hl⟩
  rw [VerifierProgram.bind_assoc'] at h
  exact h

/-! ### The GKR returns wherever the statement's does -/

theorem Comp.gkrStep (layer : ℕ) (values point : List E) :
    Comp (gkrStepRust layer values point)
      (gkrStep (if layer % 2 = 1 then 1 else 2) (layer == if layer % 2 = 1 then 1 else 2)
        ⟨values, point⟩ >>= fun s ↦ VerifierProgram.ret (s.values, s.point)) := by
  have hs : (if layer % 2 = 1 then 1 else 2) ≤ 2 := by split <;> omega
  unfold gkrStepRust LeanVM.Protocol.Verifier.gkrStep
  dsimp only
  generalize (if layer % 2 = 1 then 1 else 2) = step at hs ⊢
  simp only [VerifierProgram.bind_assoc', Nat.one_shiftLeft, polyEvalRust_eq,
    grindingBitsRust_ofNat (show 3 - 1 < 2 ^ 64 by norm_num)]
  refine Comp.bindEq (Comp.grindCheck _) (Sim.grindCheck _) fun _ ↦
    Comp.bindEq Comp.sample Sim.sample fun combiner ↦ ?_
  refine Comp.sumcheck_bind (count := 2 ^ step + 1) _
    (by have := Nat.one_le_two_pow (n := step); omega)
    (by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hs; omega) _ fun x c hx ↦ ?_
  refine Comp.bindPost (Comp.nextScalars _) (Sim.nextScalars _) (Returns.nextScalars _)
    fun c0 h0 ↦ Comp.bindPost (Comp.nextScalars _) (Sim.nextScalars _) (Returns.nextScalars _)
    fun c1 h1 ↦ Comp.bindPost (Comp.nextScalars _) (Sim.nextScalars _) (Returns.nextScalars _)
    fun c2 h2 ↦ ?_
  have hreq : c = polyEvalRust ([c0, c1, c2].map fun child ↦ child.foldl (· * ·) 1) combiner ↔
      c = polyEval ([c0, c1, c2].map prodE) combiner := by
    simp only [List.map_cons, List.map_nil, polyEvalRust_eq, prodE]
  refine Comp.whenChecked_bind (Comp.bindEq (Comp.require_iff hreq) (Sim.require_iff hreq)
    fun _ ↦ ?_)
  have hg :
      grindingBitsRust (BitVec.ofNat 128 (step <<< (if (layer == step) = true then 1 else 0)))
      = grindingBits (if (layer == step) = true then 2 * step else step) := by
    rw [grindingBitsRust_ofNat (by split <;> simp [Nat.shiftLeft_eq] <;> omega)]
    congr 1
    split <;> simp [Nat.shiftLeft_eq, mul_comm]
  rw [hg]
  refine Comp.bindEq (Comp.grindCheck _) (Sim.grindCheck _) fun _ ↦
    Comp.bindPost (Comp.samples _) (Sim.samples _) (Returns.samples _) fun y hy ↦ ?_
  refine Comp.ofOption_bind (mapM_eq_some_map _ (multilinearEval · y) _ fun child hc ↦
    multilinearEvalRust_eq _ _ ⟨by omega, ?_⟩) (Comp.pure _ _)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rwa [hy]

theorem Comp.gkrLoop (layer : ℕ) : ∀ values point,
    Comp (gkrLoopRust layer values point)
      (gkrLayers layer ⟨values, point⟩ >>= fun s ↦ VerifierProgram.ret (s.values, s.point)) := by
  induction layer using Nat.strong_induction_on with
  | _ layer ih =>
    intro values point
    rw [gkrLoopRust]
    match layer with
    | 0 => exact Comp.pure _ _
    | n + 1 =>
      simp only [Nat.zero_lt_succ, dite_true]
      have h := Comp.bind (Comp.gkrStep (n + 1) values point) (SimR.gkrStep (n + 1) values point)
        (Q := fun vp ↦ gkrLayers (n + 1 - if (n + 1) % 2 = 1 then 1 else 2)
          ⟨vp.1, vp.2⟩ >>= fun s ↦ VerifierProgram.ret (s.values, s.point))
        (k := fun vp ↦ gkrLoopRust (n + 1 - if (n + 1) % 2 = 1 then 1 else 2) vp.1 vp.2)
        fun a b ⟨hab, _⟩ ↦ by subst hab; exact ih _ (by split <;> omega) a.1 a.2
      rw [VerifierProgram.bind_assoc'] at h
      rw [gkrLayers_succ, VerifierProgram.bind_assoc']
      exact h

theorem Comp.verifyGkr (depth : ℕ) : Comp (verifyGkrRust depth) (verifyGkrGrandProducts depth) := by
  unfold verifyGkrRust verifyGkrGrandProducts
  refine Comp.bindEq Comp.nextScalar Sim.nextScalar fun shared ↦
    Comp.bindEq Comp.nextScalar Sim.nextScalar fun count ↦ ?_
  have h := Comp.bind (Comp.gkrLoop depth [shared, shared, count] [])
    (SimR.gkrLoop depth [shared, shared, count] [])
    (k := fun vp ↦ (Pure.pure (count, vp.2, vp.1) : TM (E × List E × List E)))
    (Q := fun vp ↦ VerifierProgram.ret (count, vp.2, vp.1)) fun _ _ _ ↦ Comp.pure _ _
  rw [VerifierProgram.bind_assoc'] at h
  exact h

/-! ## `bus_layout` -/

/-- `BusLayout`. -/
structure BusLayoutRust where
  /-- `depth`. -/
  depth : ℕ
  /-- `framework`. -/
  framework : List PlacementRust
  /-- `tables`. -/
  tables : List PlacementRust

/-- `bus_layout(framework_log_rows, blocks)`: the sizes stacked, their placements split after
the framework's (`split_off`). -/
def busLayoutRust (frameworkLogRows : List ℕ) (blocks : List BusBlock) : BusLayoutRust :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let stacked := stackOffsetsRust sizes
  let placements := (sizes.zip stacked.1).map fun (vars, index) ↦ (⟨vars, index⟩ : PlacementRust)
  ⟨stacked.2, placements.take frameworkLogRows.length, placements.drop frameworkLogRows.length⟩

private theorem zip_map_toSpec : ∀ (sizes : List ℕ) (offsets : List (BitVec 64)),
    ((sizes.zip offsets).map fun (p : ℕ × BitVec 64) ↦ (⟨p.1, p.2⟩ : PlacementRust)).map
        PlacementRust.toSpec =
      List.zipWith (fun size offset ↦ ({ variableCount := size, index := offset } : Placement))
        sizes (offsets.map BitVec.toNat)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | s :: ss, o :: os => by
    simp only [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons, zip_map_toSpec ss os]
    rfl

/-- **`bus_layout` is `busLayout`** while the stacked sizes fit in a `u64`. -/
theorem busLayoutRust_spec (frameworkLogRows : List ℕ) (blocks : List BusBlock)
    (h : ((frameworkLogRows ++ blocks.map (·.logRows)).map (2 ^ ·)).sum < 2 ^ 64) :
    (busLayoutRust frameworkLogRows blocks).depth = (busLayout frameworkLogRows blocks).depth ∧
      (busLayoutRust frameworkLogRows blocks).framework.map PlacementRust.toSpec =
        (busLayout frameworkLogRows blocks).framework ∧
      (busLayoutRust frameworkLogRows blocks).tables.map PlacementRust.toSpec =
        (busLayout frameworkLogRows blocks).tables := by
  obtain ⟨h1, h2⟩ := stackOffsetsRust_eq _ h
  have hS : stackOffsets (frameworkLogRows ++ blocks.map (·.logRows)) =
      ((stackOffsetsRust (frameworkLogRows ++ blocks.map (·.logRows))).1.map BitVec.toNat,
        (stackOffsetsRust (frameworkLogRows ++ blocks.map (·.logRows))).2) :=
    Prod.ext h1.symm h2.symm
  simp only [busLayoutRust, busLayout, hS, List.map_take, List.map_drop]
  refine ⟨trivial, ?_, ?_⟩ <;> rw [← zip_map_toSpec]

/-! ## `verify_bus_balance` -/

/-- `BusResult`. -/
structure BusResultRust where
  /-- `claims`. -/
  claims : List ColumnClaim
  /-- `bytecode_point`. -/
  bytecodePoint : List E
  /-- `point`. -/
  point : List E
  /-- `forms`. -/
  forms : List (List Form)
  /-- `totals`. -/
  totals : List E

/-- Forms by value, table by table. -/
def formsDen (forms : List (List Form)) : List (List ((ℕ → E) → E)) :=
  forms.map Forms.den

/-- The Rust's bus result is the statement's: the forms by value. -/
structure BusResultRust.Rel (r : BusResultRust) (R : BusResult) : Prop where
  claims : r.claims = R.claims
  bytecodePoint : r.bytecodePoint = R.bytecodePoint
  point : r.point = R.point
  forms : formsDen r.forms = formsDen R.forms
  totals : r.totals = R.totals
  formsLength : R.forms.length = tables.length

/-- The three framework fingerprints of a side (`framework`). -/
def frameworkRust (weights memory : List E) (memoryIndex bytecodeIndex bytecodeShare : E)
    (pc memoryCount bytecodeCount : E) : Option (List E) := do
  let a ← dotRust (weights.take 3) [1, pc, gpowRust 0]
  let b ← dotRust (weights.take 5)
    [gen, memoryIndex, memoryCount, memory.getD 0 0, memory.getD 1 0]
  let c ← dotRust (weights.take 3) [sepBytecodeRust, bytecodeIndex, bytecodeCount]
  Pure.pure [a, b, c + bytecodeShare]

/-- A block's form on a side: `constant(side_beta)`, then each coordinate times its slot's
weight. -/
def blockFormRust (block : BusBlock) (sideWeights : List E) (sideBeta : E) : Form :=
  block.coordinates.zipIdx.foldl
    (fun form (coordinate, slot) ↦ addScaledRust form coordinate (sideWeights.getD slot 0))
    (constantRust sideBeta)

/-- One iteration of a side's loop over its table blocks. -/
def sideStepRust (tables : List TableRust) (point : List E) (side : ℕ) (sideWeights : List E)
    (sideBeta : E) (acc : List (List Form) × E) (sb : E × BusBlock) : List (List Form) × E :=
  let blockForm := blockFormRust sb.2 sideWeights sideBeta
  let forms := acc.1.modify sb.2.owner fun row ↦
    row.modify side fun form ↦ addScaledRust form blockForm sb.1
  let padding := (tables.getD sb.2.owner default).padding
  let weight := paddingWeightRust (point.take sb.2.logRows) (BitVec.ofNat 64 sb.2.rows)
  (forms, acc.2 + sb.1 * weight * (formEvaluateRust blockForm padding + 1))

/-- One iteration of `verify_bus_balance`'s loop over the sides: the selectors, the known part,
the table blocks into the forms, and the side's total. -/
def sideRust (tables : List TableRust) (point treeValues : List E) (forms : List (List Form))
    (side : ℕ) (blocks : List BusBlock) (sideLayout : BusLayoutRust)
    (frameworkFingerprints sideWeights : List E) (sideBeta : E) :
    Option (List (List Form) × E) := do
  let frameworkSelectors ← sideLayout.framework.mapM (·.eqAbove point)
  let tableSelectors ← sideLayout.tables.mapM (·.eqAbove point)
  let known ← dotRust frameworkSelectors (frameworkFingerprints.map (sideBeta + ·))
  let r := (tableSelectors.zip blocks).foldl (sideStepRust tables point side sideWeights sideBeta)
    (forms, 0)
  let onesPadding := (frameworkSelectors ++ tableSelectors).foldl (· + ·) 0 + 1
  Pure.pure (r.1, treeValues.getD side 0 + known + onesPadding + r.2)

/-- `verify_bus_balance(layout, transcript)`, the bytecode the layout borrows passed alongside. -/
def verifyBusBalanceRust (layout : LayoutRust) (bc : BytecodeRust) : TM BusResultRust := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayoutRust frameworkLogRows layout.push
  let pullLayout := busLayoutRust frameworkLogRows layout.pull
  let countLayout := busLayoutRust [] layout.count
  TM.require (pushLayout.depth < 64)
  TM.grindCheck (busGrindingBitsRust pushLayout.depth)
  let weights ← TM.samples (1 <<< 4)
  let beta ← TM.sample
  let (countRoot, point, treeValues) ← verifyGkrRust pushLayout.depth
  TM.whenChecked (TM.require (countRoot ≠ 0))
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← TM.nextScalars 2
  let memoryFinal ← TM.nextScalar
  let bytecodeFinal ← TM.nextScalar
  let claims : List ColumnClaim :=
    ([0, 1].map fun column ↦ (⟨column, memoryLow, memory.getD column 0⟩ : ColumnClaim)) ++
      [⟨2, memoryLow, memoryFinal⟩, ⟨3, bytecodeLow, bytecodeFinal⟩]
  let memoryIndex := indexMleRust memoryLow
  let bytecodeIndex := indexMleRust bytecodeLow
  let bytecodeShare ← TM.nextScalar
  let (slotPoint, claim) ← TM.sumcheck bytecodeShare 3 (List.replicate 4 none)
  let bytecodeValue ← TM.nextScalar
  let bytecodePoint := bytecodeLow ++ slotPoint
  TM.whenChecked (do
    let d ← TM.ofOption (dotRust (eqKernelRust slotPoint) weights)
    TM.require (claim = d * bytecodeValue)
    let v ← TM.ofOption (evaluateRust bc bytecodePoint)
    TM.require (v = bytecodeValue))
  let pushFingerprints ← TM.ofOption
    (frameworkRust weights memory memoryIndex bytecodeIndex bytecodeShare (gpowRust 0) 1 1)
  let pullFingerprints ← TM.ofOption
    (frameworkRust weights memory memoryIndex bytecodeIndex bytecodeShare
      (gpowRust ((1#64 <<< (layout.logBytecode % 64)) - 1#64)) memoryFinal bytecodeFinal)
  let forms0 := List.replicate layout.tables.length (List.replicate 3 ({} : Form))
  let (forms1, total0) ← TM.ofOption (sideRust layout.tables point treeValues forms0 0 layout.push
    pushLayout pushFingerprints weights beta)
  let (forms2, total1) ← TM.ofOption (sideRust layout.tables point treeValues forms1 1 layout.pull
    pullLayout pullFingerprints weights beta)
  let (forms3, total2) ← TM.ofOption (sideRust layout.tables point treeValues forms2 2 layout.count
    countLayout [] [1] 0)
  Pure.pure ⟨claims, bytecodePoint, point, forms3, [total0, total1, total2]⟩

/-! ## The bus's pure steps are the statement's -/

section BusPure

private theorem map_modify {α β : Type} (g : α → β) (f : α → α) (f' : β → β)
    (h : ∀ a, g (f a) = f' (g a)) :
    ∀ (l : List α) (i : ℕ), (l.modify i f).map g = (l.map g).modify i f'
  | [], i => by simp
  | a :: l, 0 => by simp [h]
  | a :: l, i + 1 => by simp [map_modify g f f' h l i]

/-- The forms of a side after a block, by value. -/
theorem formsDen_modify {forms forms' : List (List Form)} (h : formsDen forms = formsDen forms')
    (owner side : ℕ) {b b' : Form} (hb : b.evaluate = b'.evaluate) (selector : E) :
    formsDen (forms.modify owner fun row ↦ row.modify side fun f ↦ addScaledRust f b selector) =
      formsDen (forms'.modify owner fun row ↦ row.modify side fun f ↦ f.addScaled b' selector) := by
  let F : ((ℕ → E) → E) → (ℕ → E) → E := fun d c ↦ d c + selector * b.evaluate c
  have hrow : ∀ row : List Form, Forms.den (row.modify side fun f ↦ addScaledRust f b selector) =
      (Forms.den row).modify side F := fun row ↦
    map_modify Form.evaluate (fun f ↦ addScaledRust f b selector) F
      (fun f ↦ by funext c; simp [F, evaluate_addScaledRust]) row side
  have hrow' : ∀ row : List Form, Forms.den (row.modify side fun f ↦ f.addScaled b' selector) =
      (Forms.den row).modify side F := fun row ↦
    map_modify Form.evaluate (fun f ↦ f.addScaled b' selector) F
      (fun f ↦ by funext c; simp [F, evaluate_addScaled, hb]) row side
  unfold formsDen
  rw [map_modify Forms.den _ (fun r ↦ r.modify side F) hrow forms owner,
    map_modify Forms.den _ (fun r ↦ r.modify side F) hrow' forms' owner]
  exact congrArg (List.modify · owner _) h

theorem den_blockForm (block block' : BusBlock) (h : Forms.den block.coordinates =
    Forms.den block'.coordinates) (sideWeights : List E) (sideBeta : E) :
    (blockFormRust block sideWeights sideBeta).evaluate =
      (blockForm block' sideWeights sideBeta).evaluate := by
  unfold blockFormRust blockForm
  generalize block.coordinates = cs at h
  generalize block'.coordinates = cs' at h
  suffices ∀ (n : ℕ) (a a' : Form), a.evaluate = a'.evaluate →
      ((cs.zipIdx n).foldl (fun form (coordinate, slot) ↦
        addScaledRust form coordinate (sideWeights.getD slot 0)) a).evaluate =
      ((cs'.zipIdx n).foldl (fun form (coordinate, slot) ↦
        form.addScaled coordinate (sideWeights.getD slot 0)) a').evaluate from this 0 _ _ rfl
  induction cs generalizing cs' with
  | nil => cases cs' with
    | nil => intro n a a' ha; exact ha
    | cons _ _ => cases h
  | cons c cs ih => cases cs' with
    | nil => cases h
    | cons c' cs' =>
      simp only [Forms.den, List.map_cons, List.cons.injEq] at h
      intro n a a' ha
      simp only [List.zipIdx_cons, List.foldl_cons]
      exact ih cs' h.2 (n + 1) _ _ (den_addScaledRust ha h.1 _)

theorem padding_getD (owner : ℕ) :
    (tablesRust.getD owner default).padding = (tables.getD owner default).padding := by
  have h := tablesRust_rel
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases List.forall₂_iff_get.mp h with ⟨hl, hg⟩
  by_cases ho : owner < tables.length
  · rw [List.getElem?_eq_getElem (by rw [hl]; exact ho), List.getElem?_eq_getElem ho,
      Option.getD_some, Option.getD_some]
    exact (hg owner (by rw [hl]; exact ho) ho).padding
  · rw [List.getElem?_eq_none (by rw [hl]; omega), List.getElem?_eq_none (by omega)]
    rfl

end BusPure

section BusSide

theorem mapM_eqAbove (point : List E) (hp : point.length ≤ 64) :
    ∀ ps : List PlacementRust,
      ps.mapM (·.eqAbove point) = some ((ps.map PlacementRust.toSpec).map (·.eqAbove point))
  | [] => rfl
  | p :: ps => by
    rw [List.mapM_cons, PlacementRust.eqAbove_eq p point hp, mapM_eqAbove point hp ps]
    rfl

private theorem sideFold (point : List E) (side : ℕ) (sw : List E) (beta : E) :
    ∀ (sels : List E) (bs bs' : List BusBlock), bs.map busBlockDen = bs'.map busBlockDen →
      (∀ b ∈ bs, b.logRows < 64 ∧ b.rows < 2 ^ 64) →
      ∀ (acc : List (List Form) × E) (acc' : List (List Form) × E),
        formsDen acc.1 = formsDen acc'.1 → acc.2 = acc'.2 →
        formsDen ((sels.zip bs).foldl (sideStepRust tablesRust point side sw beta) acc).1 =
          formsDen ((sels.zip bs').foldl (fun (forms, paddingRows) (selector, block) ↦
            let form := blockForm block sw beta
            let padding := (tables.getD block.owner default).padding
            (forms.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
              paddingRows + selector * paddingWeight (point.take block.logRows) block.rows *
                (form.evaluate (padding.getD · 0) + 1))) acc').1 ∧
        ((sels.zip bs).foldl (sideStepRust tablesRust point side sw beta) acc).2 =
          ((sels.zip bs').foldl (fun (forms, paddingRows) (selector, block) ↦
            let form := blockForm block sw beta
            let padding := (tables.getD block.owner default).padding
            (forms.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
              paddingRows + selector * paddingWeight (point.take block.logRows) block.rows *
                (form.evaluate (padding.getD · 0) + 1))) acc').2
  | [], bs, bs', _, _, acc, acc', h1, h2 => by simp [h1, h2]
  | _ :: _, [], bs', hbs, _, acc, acc', h1, h2 => by
    cases bs' with
    | nil => simp [h1, h2]
    | cons _ _ => cases hbs
  | s :: sels, b :: bs, [], hbs, _, _, _, _, _ => by cases hbs
  | s :: sels, b :: bs, b' :: bs', hbs, hb, acc, acc', h1, h2 => by
    simp only [List.map_cons, List.cons.injEq, busBlockDen, Prod.mk.injEq] at hbs
    obtain ⟨⟨hl, hr, hc, ho⟩, hbs⟩ := hbs
    obtain ⟨hlog, hrows⟩ := hb b (by simp)
    simp only [List.zip_cons_cons, List.foldl_cons]
    refine sideFold point side sw beta sels bs bs' hbs (fun x hx ↦ hb x (by simp [hx])) _ _ ?_ ?_
    · simp only [sideStepRust]
      rw [← ho]
      exact formsDen_modify h1 _ _ (den_blockForm b b' hc sw beta) s
    · simp only [sideStepRust]
      rw [h2, paddingWeightRust_eq _ _ (by rw [List.length_take]; omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hrows, formEvaluateRust_eq, den_blockForm b b' hc sw beta, ← ho, hl, hr,
        padding_getD]

theorem sideRust_spec (point treeValues : List E) (hp : point.length ≤ 64)
    {forms forms' : List (List Form)} (hf : formsDen forms = formsDen forms') (side : ℕ)
    {blocks blocks' : List BusBlock} (hbl : blocks.map busBlockDen = blocks'.map busBlockDen)
    (hb : ∀ b ∈ blocks, b.logRows < 64 ∧ b.rows < 2 ^ 64) {sl : BusLayoutRust} {SL : BusLayout}
    (hfw : sl.framework.map PlacementRust.toSpec = SL.framework)
    (htb : sl.tables.map PlacementRust.toSpec = SL.tables) (fps sw : List E) (beta : E)
    (hfps : fps.length = SL.framework.length) :
    ∃ f t, sideRust tablesRust point treeValues forms side blocks sl fps sw beta = some (f, t) ∧
      formsDen f =
        formsDen (accumulateSide forms' side blocks' SL fps sw beta point
          (treeValues.getD side 0)).1 ∧
      t = (accumulateSide forms' side blocks' SL fps sw beta point (treeValues.getD side 0)).2 := by
  have hfo := sideFold point side sw beta (SL.tables.map (·.eqAbove point)) blocks blocks' hbl hb
    (forms, 0) (forms', 0) hf rfl
  unfold sideRust accumulateSide
  simp only [mapM_eqAbove point hp, hfw, htb, Option.bind_eq_bind, Option.bind_some]
  rw [dotRust_eq (by simp [hfps])]
  simp only [Option.bind_some]
  exact ⟨_, _, rfl, hfo.1, by rw [hfo.2]; rfl⟩

end BusSide

section BusBalance

theorem busLayoutRust_framework_length (f : List ℕ) (bs : List BusBlock) :
    (busLayoutRust f bs).framework.length = f.length := by
  simp [busLayoutRust, stackOffsetsRust_length]

theorem busLayoutRust_den {f : List ℕ} {bs bs' : List BusBlock}
    (h : bs.map busBlockDen = bs'.map busBlockDen) : busLayoutRust f bs = busLayoutRust f bs' := by
  have : bs.map (·.logRows) = bs'.map (·.logRows) := by
    have := congrArg (List.map Prod.fst) h
    simpa [List.map_map, Function.comp_def, busBlockDen] using this
  simp only [busLayoutRust, this]

/-- A side's bus layout, of blocks at most `2^30` rows each and at most `1024` of them. -/
theorem busLayoutRust_side (f : List ℕ) (hf : ∀ x ∈ f, x ≤ 30) (hf3 : f.length ≤ 3)
    {bs bs' : List BusBlock} (h : bs.map busBlockDen = bs'.map busBlockDen)
    (hb : ∀ b ∈ bs, b.logRows ≤ 30) (hn : bs.length ≤ 1024) :
    (busLayoutRust f bs).depth = (busLayout f bs').depth ∧
      (busLayoutRust f bs).framework.map PlacementRust.toSpec = (busLayout f bs').framework ∧
      (busLayoutRust f bs).tables.map PlacementRust.toSpec = (busLayout f bs').tables := by
  rw [busLayoutRust_den h]
  have hl : bs.map (·.logRows) = bs'.map (·.logRows) := by
    have := congrArg (List.map Prod.fst) h
    simpa [List.map_map, Function.comp_def, busBlockDen] using this
  apply busLayoutRust_spec
  have hall : ∀ k ∈ f ++ bs'.map (·.logRows), k ≤ 30 := by
    intro k hk
    rw [List.mem_append] at hk
    rcases hk with hk | hk
    · exact hf k hk
    · rw [← hl] at hk
      obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hk
      exact hb b hb'
  have hlen : (f ++ bs'.map (·.logRows)).length ≤ 1027 := by
    rw [List.length_append, List.length_map, ← List.length_map (f := busBlockDen), ← h,
      List.length_map]
    omega
  have := sum_pow_le _ 30 hall
  have : (f ++ bs'.map (·.logRows)).length * 2 ^ 30 ≤ 1027 * 2 ^ 30 :=
    Nat.mul_le_mul_right _ hlen
  have : 1027 * 2 ^ 30 < 2 ^ 64 := by norm_num
  omega

theorem frameworkRust_eq (weights memory : List E) (hw : weights.length = 16)
    (hm : memory.length = 2) (memoryLow bytecodeLow : List E) (share pc mc bc : E) :
    frameworkRust weights memory (indexMleRust memoryLow) (indexMleRust bytecodeLow) share pc mc
        bc =
      some (fingerprints weights memory memoryLow bytecodeLow share pc mc bc) := by
  match memory, hm with
  | [m0, m1], _ =>
    unfold frameworkRust fingerprints
    rw [dotRust_eq (by simp [hw]), dotRust_eq (by simp [hw]), dotRust_eq (by simp [hw]),
      indexMleRust_eq, indexMleRust_eq, gpowRust_eq, sepBytecodeRust_eq]
    rfl


theorem accumulateSide_length (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sl : BusLayout) (fps sw : List E) (beta : E) (point : List E) (tv : E) :
    (accumulateSide forms side blocks sl fps sw beta point tv).1.length = forms.length := by
  unfold accumulateSide
  dsimp only
  generalize (List.zip (sl.tables.map (·.eqAbove point)) blocks) = zs
  suffices ∀ acc : List (List Form) × E, (zs.foldl (fun (forms, paddingRows) (selector, block) ↦
      let form := blockForm block sw beta
      let padding := (tables.getD block.owner default).padding
      (forms.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
        paddingRows + selector * paddingWeight (point.take block.logRows) block.rows *
          (form.evaluate (padding.getD · 0) + 1))) acc).1.length = acc.1.length from this _
  induction zs with
  | nil => intro acc; rfl
  | cons z zs ih => intro acc; rw [List.foldl_cons, ih]; simp

/-- **`verify_bus_balance` runs `verifyBusBalance`**, the deployed verifier's, on a layout
`build_layout` returned (`LayoutRust.Rel`, its blocks at most `2^30` rows each and at most `1024`
per side) and the prepared bytecode of the statement's words. -/
theorem SimR.verifyBusBalance (l : LayoutRust) (L : Layout) (hl : l.Rel L) (words : List K)
    (bc : BytecodeRust) (hbc : BytecodeOk words bc) (hw : L.bytecode = words)
    (hm : l.logMemory ≤ 30) (hlb : l.logBytecode ≤ 30)
    (hb : ∀ b ∈ l.push ++ l.pull ++ l.count, b.logRows ≤ 30 ∧ b.rows < 2 ^ 64)
    (hn : l.push.length ≤ 1024 ∧ l.pull.length ≤ 1024 ∧ l.count.length ≤ 1024) :
    SimR (verifyBusBalanceRust l bc) (verifyBusBalance computedBytecodeValue L)
      BusResultRust.Rel := by
  have hb' : ∀ b ∈ l.push ++ l.pull ++ l.count, b.logRows < 64 ∧ b.rows < 2 ^ 64 :=
    fun b h ↦ ⟨by have := (hb b h).1; omega, (hb b h).2⟩
  have hfw3 : ∀ x ∈ [0, l.logMemory, l.logBytecode], x ≤ 30 := by simp; omega
  obtain ⟨hpd, hpf, hpt⟩ := busLayoutRust_side _ hfw3 (by simp) hl.push
    (fun b h ↦ (hb b (by simp [h])).1) hn.1
  obtain ⟨-, hlf, hlt⟩ := busLayoutRust_side _ hfw3 (by simp) hl.pull
    (fun b h ↦ (hb b (by simp [h])).1) hn.2.1
  obtain ⟨-, hcf, hct⟩ := busLayoutRust_side [] (by simp) (by simp) hl.count
    (fun b h ↦ (hb b (by simp [h])).1) hn.2.2
  unfold verifyBusBalanceRust LeanVM.Protocol.Verifier.verifyBusBalance
    LeanVM.Protocol.Verifier.bytecodeShare computedBytecodeValue
  rw [← hl.logMemory, ← hl.logBytecode, hw]
  simp only [VerifierProgram.bind_assoc', pure_bind']
  refine SimR.bindPost (Sim.require_iff (by rw [hpd])) (Returns.require _) fun _ hd ↦ ?_
  rw [hpd] at hd ⊢
  rw [busGrindingBitsRust_eq hd, show (1 <<< 4 : ℕ) = 2 ^ busBits from rfl]
  refine SimR.bindEq (Sim.grindCheck _) fun _ ↦
    SimR.bindPost (Sim.samples _) (Returns.samples _) fun weights hw16 ↦
    SimR.bindEq Sim.sample fun beta ↦ ?_
  refine SimR.bind (SimR.verifyGkr _) fun g g' ⟨hg, hgl⟩ ↦ ?_
  subst hg
  obtain ⟨countRoot, point, treeValues⟩ := g
  simp only at hgl ⊢
  refine SimR.whenChecked_bind (SimR.bindEq (Sim.require _) fun _ ↦ ?_)
  refine SimR.bindPost (Sim.nextScalars 2) (Returns.nextScalars 2) fun memory hm2 ↦
    SimR.bindEq Sim.nextScalar fun memoryFinal ↦ SimR.bindEq Sim.nextScalar fun bytecodeFinal ↦
    SimR.bindEq Sim.nextScalar fun share ↦ ?_
  rw [show busBits = 4 from rfl]
  refine SimR.sumcheck_bind (count := 3) _ (by norm_num) (by norm_num) _ fun sp claim hsp ↦ ?_
  simp only [List.length_replicate] at hsp
  refine SimR.bindEq Sim.nextScalar fun value ↦ ?_
  refine SimR.whenChecked_bind ?_
  simp only [bind_assoc]
  rw [eqKernelRust_eq _ (by omega), dotRust_eq (by rw [hw16, eqKernel_length, hsp]; rfl)]
  simp only [TM.ofOption, pure_bind]
  refine SimR.bindEq (Sim.require _) fun _ ↦ ?_
  rw [hbc.evaluate]
  by_cases hcond : (List.take l.logBytecode point ++ sp).length < 64 ∧
      words.length = 2 ^ (List.take l.logBytecode point ++ sp).length
  · rw [ite_eq_left hcond]
    simp only [pure_bind]
    refine SimR.bindEq (Sim.require _) fun _ ↦ ?_
    rw [frameworkRust_eq _ _ hw16 hm2, frameworkRust_eq _ _ hw16 hm2]
    simp only [pure_bind]
    have hp : point.length ≤ 64 := by omega
    have hg0 : gpowRust 0 = gpow 0 := by rw [gpowRust_eq]; rfl
    have hgf : gpowRust (1#64 <<< (l.logBytecode % 64) - 1#64) = gpow (2 ^ l.logBytecode - 1) := by
      have hlt : 2 ^ l.logBytecode < 2 ^ 64 :=
        Nat.pow_lt_pow_right (a := 2) (by norm_num) (by omega)
      have h2 : (1#64 <<< (l.logBytecode % 64)).toNat = 2 ^ l.logBytecode := by
        rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : l.logBytecode < 64),
          Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.one_mod_two_pow (by norm_num), one_mul,
          Nat.mod_eq_of_lt hlt]
      rw [gpowRust_eq, BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, h2]; exact Nat.one_le_two_pow), h2]
      rfl
    have hf0 : formsDen (List.replicate l.tables.length (List.replicate 3 ({} : Form))) =
        formsDen (tables.map fun _ ↦ [{}, {}, {}]) := by
      rw [hl.tables, List.map_const']
      rfl
    rw [hg0, hgf, hl.tables]
    rw [hl.tables] at hf0
    obtain ⟨f1, t1, h1, hf1, ht1⟩ := sideRust_spec point treeValues hp hf0 0 hl.push
      (fun b h ↦ hb' b (by simp [h])) hpf hpt (fingerprints weights memory
        (List.take l.logMemory point) (List.take l.logBytecode point) share (gpow 0) 1 1)
      weights beta
      (by rw [← hpf, List.length_map, busLayoutRust_framework_length]; rfl)
    rw [h1]
    simp only [pure_bind]
    obtain ⟨f2, t2, h2, hf2, ht2⟩ := sideRust_spec point treeValues hp hf1 1 hl.pull
      (fun b h ↦ hb' b (by simp [h])) hlf hlt (fingerprints weights memory
        (List.take l.logMemory point) (List.take l.logBytecode point) share
        (gpow (2 ^ l.logBytecode - 1)) memoryFinal bytecodeFinal) weights beta
      (by rw [← hlf, List.length_map, busLayoutRust_framework_length]; rfl)
    rw [h2]
    simp only [pure_bind]
    obtain ⟨f3, t3, h3, hf3, ht3⟩ := sideRust_spec point treeValues hp hf2 2 hl.count
      (fun b h ↦ hb' b (by simp [h])) hcf hct [] [1] 0
      (by rw [← hcf, List.length_map, busLayoutRust_framework_length]; rfl)
    rw [h3]
    simp only [pure_bind]
    refine SimR.pure ⟨?_, rfl, rfl, hf3, by rw [ht1, ht2, ht3],
      by simp only [accumulateSide_length, List.length_map]⟩
    match memory, hm2 with
    | [m0, m1], _ => rfl
  · rw [ite_eq_right hcond]
    exact SimR.fail_bind

/-- **`verify_bus_balance` returns wherever the statement's does**, on a layout whose bytecode
point fits the words: the words are `2^(log_bytecode + 4)` (`BUS_BITS = 4`), and the push side's
cube has at least the bytecode's coordinates. -/
theorem Comp.verifyBusBalance (l : LayoutRust) (L : Layout) (hl : l.Rel L) (words : List K)
    (bc : BytecodeRust) (hbc : BytecodeOk words bc) (hw : L.bytecode = words)
    (hm : l.logMemory ≤ 30) (hlb : l.logBytecode ≤ 30)
    (hb : ∀ b ∈ l.push ++ l.pull ++ l.count, b.logRows ≤ 30 ∧ b.rows < 2 ^ 64)
    (hn : l.push.length ≤ 1024 ∧ l.pull.length ≤ 1024 ∧ l.count.length ≤ 1024)
    (hbw : words.length = 2 ^ (l.logBytecode + 4))
    (hdepth : l.logBytecode ≤ (busLayoutRust [0, l.logMemory, l.logBytecode] l.push).depth) :
    Comp (verifyBusBalanceRust l bc) (verifyBusBalance computedBytecodeValue L) := by
  have hb' : ∀ b ∈ l.push ++ l.pull ++ l.count, b.logRows < 64 ∧ b.rows < 2 ^ 64 :=
    fun b h ↦ ⟨by have := (hb b h).1; omega, (hb b h).2⟩
  have hfw3 : ∀ x ∈ [0, l.logMemory, l.logBytecode], x ≤ 30 := by simp; omega
  obtain ⟨hpd, hpf, hpt⟩ := busLayoutRust_side _ hfw3 (by simp) hl.push
    (fun b h ↦ (hb b (by simp [h])).1) hn.1
  obtain ⟨-, hlf, hlt⟩ := busLayoutRust_side _ hfw3 (by simp) hl.pull
    (fun b h ↦ (hb b (by simp [h])).1) hn.2.1
  obtain ⟨-, hcf, hct⟩ := busLayoutRust_side [] (by simp) (by simp) hl.count
    (fun b h ↦ (hb b (by simp [h])).1) hn.2.2
  unfold verifyBusBalanceRust LeanVM.Protocol.Verifier.verifyBusBalance
    LeanVM.Protocol.Verifier.bytecodeShare computedBytecodeValue
  rw [← hl.logMemory, ← hl.logBytecode, hw]
  simp only [VerifierProgram.bind_assoc', pure_bind']
  have hreq : (busLayoutRust [0, l.logMemory, l.logBytecode] l.push).depth < 64 ↔
      (busLayout [0, l.logMemory, l.logBytecode] L.push).depth < 64 := by rw [hpd]
  refine Comp.bindPost (Comp.require_iff hreq) (Sim.require_iff hreq) (Returns.require _)
    fun _ hd ↦ ?_
  rw [hpd] at hd hdepth ⊢
  rw [busGrindingBitsRust_eq hd, show (1 <<< 4 : ℕ) = 2 ^ busBits from rfl]
  refine Comp.bindEq (Comp.grindCheck _) (Sim.grindCheck _) fun _ ↦
    Comp.bindPost (Comp.samples _) (Sim.samples _) (Returns.samples _) fun weights hw16 ↦
    Comp.bindEq Comp.sample Sim.sample fun beta ↦ ?_
  refine Comp.bind (Comp.verifyGkr _) (SimR.verifyGkr _) fun g g' ⟨hg, hgl⟩ ↦ ?_
  subst hg
  obtain ⟨countRoot, point, treeValues⟩ := g
  have hgl' : point.length = _ := hgl
  refine Comp.whenChecked_bind (Comp.bindEq (Comp.require_iff Iff.rfl) (Sim.require _) fun _ ↦ ?_)
  refine Comp.bindPost (Comp.nextScalars 2) (Sim.nextScalars 2) (Returns.nextScalars 2)
    fun memory hm2 ↦ Comp.bindEq Comp.nextScalar Sim.nextScalar fun memoryFinal ↦
    Comp.bindEq Comp.nextScalar Sim.nextScalar fun bytecodeFinal ↦
    Comp.bindEq Comp.nextScalar Sim.nextScalar fun share ↦ ?_
  rw [show busBits = 4 from rfl]
  refine Comp.sumcheck_bind (count := 3) _ (by norm_num) (by norm_num) _ fun sp claim hsp ↦ ?_
  simp only [List.length_replicate] at hsp
  refine Comp.bindEq Comp.nextScalar Sim.nextScalar fun value ↦ ?_
  refine Comp.whenChecked_bind ?_
  simp only [bind_assoc]
  rw [eqKernelRust_eq _ (by omega), dotRust_eq (by rw [hw16, eqKernel_length, hsp]; rfl)]
  simp only [TM.ofOption, pure_bind]
  refine Comp.bindEq (Comp.require_iff Iff.rfl) (Sim.require _) fun _ ↦ ?_
  have hcond : (List.take l.logBytecode point ++ sp).length < 64 ∧
      words.length = 2 ^ (List.take l.logBytecode point ++ sp).length := by
    rw [List.length_append, List.length_take, hsp, hgl', min_eq_left hdepth, hbw]
    exact ⟨by omega, rfl⟩
  rw [hbc.evaluate, ite_eq_left hcond]
  simp only [pure_bind]
  refine Comp.bindEq (Comp.require_iff Iff.rfl) (Sim.require _) fun _ ↦ ?_
  rw [frameworkRust_eq _ _ hw16 hm2, frameworkRust_eq _ _ hw16 hm2]
  simp only [pure_bind]
  have hp : point.length ≤ 64 := by omega
  have hf0 : formsDen (List.replicate l.tables.length (List.replicate 3 ({} : Form))) =
      formsDen (tables.map fun _ ↦ [{}, {}, {}]) := by
    rw [hl.tables, List.map_const']
    rfl
  rw [hl.tables]
  rw [hl.tables] at hf0
  obtain ⟨f1, t1, h1, hf1, -⟩ := sideRust_spec point treeValues hp hf0 0 hl.push
    (fun b h ↦ hb' b (by simp [h])) hpf hpt (fingerprints weights memory
      (List.take l.logMemory point) (List.take l.logBytecode point) share (gpowRust 0) 1 1)
    weights beta
    (by rw [← hpf, List.length_map, busLayoutRust_framework_length]; rfl)
  rw [h1]
  simp only [pure_bind]
  obtain ⟨f2, t2, h2, hf2, -⟩ := sideRust_spec point treeValues hp hf1 1 hl.pull
    (fun b h ↦ hb' b (by simp [h])) hlf hlt (fingerprints weights memory
      (List.take l.logMemory point) (List.take l.logBytecode point) share
      (gpowRust (1#64 <<< (l.logBytecode % 64) - 1#64)) memoryFinal bytecodeFinal) weights beta
    (by rw [← hlf, List.length_map, busLayoutRust_framework_length]; rfl)
  rw [h2]
  simp only [pure_bind]
  obtain ⟨f3, t3, h3, -, -⟩ := sideRust_spec point treeValues hp hf2 2 hl.count
    (fun b h ↦ hb' b (by simp [h])) hcf hct [] [1] 0
    (by rw [← hcf, List.length_map, busLayoutRust_framework_length]; rfl)
  rw [h3]
  exact Comp.pure _ _

end BusBalance

/-! ## `table_sumcheck` -/

section TableSumcheck

/-- The tables' weights: for each coordinate, `weights[index] *= ...` over the heights. -/
def tableWeightsRust (count : ℕ) (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    heights.zipIdx.foldl (fun weights (height, index) ↦
      weights.modify index (· * if height > coord then equality else challenge)) weights)
    (List.replicate count 1)

/-- The checked terminal: `Σ weight · (dot(constraint powers, constraints) + dot(form powers,
forms))`, a `dot` panicking on unequal lengths (`none`). -/
def termsRust (tables : List TableRust) (rows : List (List E × List E))
    (busForms : List (List Form)) (weights constraintPowers formPowers : List E) : Option E :=
  ((((tables.zip rows).zip busForms).zip weights).foldlM
    (fun (acc : E × ℕ) (x : ((TableRust × (List E × List E)) × List Form) × E) ↦ do
      let table := x.1.1.1
      let evaluations := x.1.1.2.2
      let n := table.nConstraints
      let summand ← dotRust ((constraintPowers.drop acc.2).take n) (table.constraints evaluations)
      let values ← dotRust formPowers (x.1.2.map fun form ↦ formEvaluateRust form evaluations)
      Pure.pure (acc.1 + x.2 * (summand + values), acc.2 + n)) (0, 0)).map
    fun (r : E × ℕ) ↦ r.1

/-- `table_sumcheck(tables, table_log_heights, bus_forms, constraint_powers, form_powers,
equality_point, target, transcript)`. -/
def tableSumcheckRust (tables : List TableRust) (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    TM (List (List E × List E)) := do
  let (challenges, claim) ← TM.sumcheck target 4 (List.replicate (heights.foldl max 0) none)
  let point := challenges.reverse
  let weights := tableWeightsRust tables.length heights equalityPoint point
  let rows ← (tables.zip heights).mapM fun (table, height) ↦ do
    let evaluations ← TM.nextScalars table.width
    Pure.pure (point.take height, evaluations)
  TM.whenChecked (do
    let terminal ← TM.ofOption (termsRust tables rows busForms weights constraintPowers formPowers)
    TM.require (terminal = claim))
  Pure.pure rows

private theorem foldl_modify_zipIdx (g : ℕ → E → E) :
    ∀ (hs : List ℕ) (n : ℕ) (ws : List E), ws.length = n + hs.length →
      (hs.zipIdx n).foldl (fun ws (height, index) ↦ ws.modify index (g height)) ws =
        ws.take n ++ List.zipWith (fun w h ↦ g h w) (ws.drop n) hs
  | [], n, ws, hl => by simp [show ws.length = n by simpa using hl]
  | h :: hs, n, ws, hl => by
    simp only [List.zipIdx_cons, List.foldl_cons]
    have hn : n < ws.length := by simp at hl; omega
    rw [foldl_modify_zipIdx g hs (n + 1) _ (by simp at hl ⊢; omega),
      List.modify_eq_take_cons_drop hn]
    have hA : (ws.take n).length = n := by simp; omega
    have e1 : (ws.take n ++ g h ws[n] :: ws.drop (n + 1)).take (n + 1) =
        ws.take n ++ [g h ws[n]] := by
      rw [List.take_append, List.take_of_length_le (by rw [hA]; omega), hA,
        show n + 1 - n = 1 by omega]
      rfl
    have e2 : (ws.take n ++ g h ws[n] :: ws.drop (n + 1)).drop (n + 1) = ws.drop (n + 1) := by
      rw [List.drop_append, List.drop_of_length_le (by rw [hA]; omega), hA,
        show n + 1 - n = 1 by omega]
      rfl
    rw [e1, e2, List.drop_eq_getElem_cons hn, List.zipWith_cons_cons, List.append_assoc]
    rfl

theorem tableWeightsRust_eq (heights : List ℕ) (equalityPoint point : List E) :
    tableWeightsRust heights.length heights equalityPoint point =
      tableWeights heights equalityPoint point := by
  unfold tableWeightsRust tableWeights
  have h0 : List.replicate heights.length (1 : E) = heights.map fun _ ↦ 1 := by
    rw [List.map_const']
  rw [h0]
  have hl : (heights.map fun _ ↦ (1 : E)).length = heights.length := by simp
  generalize heights.map (fun _ ↦ (1 : E)) = ws0 at hl
  generalize point.zipIdx = pts
  induction pts generalizing ws0 with
  | nil => rfl
  | cons p pts ih =>
    obtain ⟨c, k⟩ := p
    rw [List.foldl_cons, List.foldl_cons]
    dsimp only
    rw [foldl_modify_zipIdx (fun height x ↦ x * if height > k then 1 + equalityPoint.getD k 0 + c
      else c) heights 0 _ (by simpa using hl)]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    exact ih _ (by simp [hl])

/-- The statement's terminal, accumulated as `tableTerms` accumulates it, over the evaluations
read. -/
def foldTerms (constraintPowers formPowers : List E) :
    List (Table × ℕ × List Form × E) → List (List E) → ℕ → E → E
  | (table, _, forms, weight) :: rest, evaluations :: evs, cursor, final =>
    foldTerms constraintPowers formPowers rest evs (cursor + table.nConstraints)
      (final + weight * (dot ((constraintPowers.drop cursor).take table.nConstraints)
        (table.constraints evaluations) +
        dot formPowers (forms.map (·.evaluate (evaluations.getD · 0)))))
  | _, _, _, final => final

theorem SimR.tableRows (point constraintPowers formPowers : List E) :
    ∀ {rowsR : List (TableRust × ℕ)} {rowsS : List (Table × ℕ × List Form × E)},
      List.Forall₂ (fun r s ↦ TableRust.Rel r.1 s.1 ∧ r.2 = s.2.1) rowsR rowsS →
      ∀ cursor final,
      SimR (rowsR.mapM fun (table, height) ↦ do
          let evaluations ← TM.nextScalars table.width
          Pure.pure (point.take height, evaluations))
        (tableTerms constraintPowers formPowers point rowsS cursor final)
        fun rows r ↦ r.2 = rows ∧
          r.1 = foldTerms constraintPowers formPowers rowsS (rows.map (·.2)) cursor final
  | _, _, .nil, cursor, final => by
    rw [List.mapM_nil]
    exact SimR.pure ⟨rfl, rfl⟩
  | (t, h) :: rs, (T, h', forms, w) :: Ss, .cons ⟨hT, hh⟩ hrs, cursor, final => by
    simp only at hh
    subst hh
    rw [List.mapM_cons, tableTerms]
    simp only [bind_assoc, pure_bind]
    rw [hT.width]
    refine SimR.bindEq (Sim.nextScalars _) fun evaluations ↦ ?_
    have := SimR.tableRows point constraintPowers formPowers hrs (cursor + T.nConstraints)
      (final + w * (dot ((constraintPowers.drop cursor).take T.nConstraints)
        (T.constraints evaluations) +
        dot formPowers (forms.map (·.evaluate (evaluations.getD · 0)))))
    refine SimR.bind this fun rows r ⟨h1, h2⟩ ↦ ?_
    obtain ⟨f, evs⟩ := r
    simp only at h1 h2
    subst h1
    exact SimR.pure ⟨rfl, by simp [foldTerms, h2]⟩

theorem termsRust_spec (constraintPowers formPowers : List E) :
    ∀ (ts : List TableRust) (Ts : List Table), List.Forall₂ TableRust.Rel ts Ts →
      ∀ (rows : List (List E × List E)) (bf bf' : List (List Form)) (ws : List E) (hs : List ℕ),
        formsDen bf = formsDen bf' → rows.length = ts.length → bf.length = ts.length →
        ws.length = ts.length → hs.length = ts.length → ∀ (acc : E × ℕ) (r : E × ℕ),
        (((ts.zip rows).zip bf).zip ws).foldlM
          (fun (acc : E × ℕ) (x : ((TableRust × (List E × List E)) × List Form) × E) ↦ do
            let table := x.1.1.1
            let evaluations := x.1.1.2.2
            let n := table.nConstraints
            let summand ← dotRust ((constraintPowers.drop acc.2).take n)
              (table.constraints evaluations)
            let values ← dotRust formPowers (x.1.2.map fun form ↦ formEvaluateRust form evaluations)
            Pure.pure (acc.1 + x.2 * (summand + values), acc.2 + n)) acc = some r →
        r.1 = foldTerms constraintPowers formPowers (Ts.zip (hs.zip (bf'.zip ws)))
          (rows.map (·.2)) acc.2 acc.1
  | [], [], .nil, rows, bf, bf', ws, hs, _, _, _, _, _, acc, r, h => by
    simp only [List.zip_nil_left, List.foldlM_nil] at h
    cases h
    rfl
  | t :: ts, T :: Ts, .cons hT hts, row :: rows, f :: bf, f' :: bf', w :: ws, hh :: hs, hbf, hr, hb,
      hw, hhs, acc, r, h => by
    simp only [formsDen, List.map_cons, List.cons.injEq] at hbf
    simp only [List.zip_cons_cons, List.foldlM_cons] at h
    cases hs1 : dotRust ((constraintPowers.drop acc.2).take t.nConstraints)
        (t.constraints row.2) with
    | none => simp [hs1] at h
    | some summand =>
      cases hs2 : dotRust formPowers (f.map fun form ↦ formEvaluateRust form row.2) with
      | none => simp [hs1, hs2] at h
      | some values =>
        simp only [hs1, hs2, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
        rw [termsRust_spec constraintPowers formPowers ts Ts hts rows bf bf' ws hs hbf.2
          (by simpa using hr) (by simpa using hb) (by simpa using hw) (by simpa using hhs) _ r h]
        rw [dotRust_some hs1, dotRust_some hs2, hT.constraints, hT.nConstraints]
        have hv : f.map (fun form ↦ formEvaluateRust form row.2) =
            f'.map (·.evaluate (row.2.getD · 0)) := by
          have := congrArg (List.map fun d : (ℕ → E) → E ↦ d (row.2.getD · 0)) hbf.1
          simpa [Forms.den, List.map_map, Function.comp_def, formEvaluateRust_eq] using this
        rw [hv]
        rfl
  | [], _ :: _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases h
  | _ :: _, [], h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases h
  | _ :: _, _ :: _, _, [], _, _, _, _, _, hr, _, _, _, _, _, _ => by simp at hr
  | _ :: _, _ :: _, _, _ :: _, [], _, _, _, _, _, hb, _, _, _, _, _ => by simp at hb
  | _ :: _, _ :: _, _, _ :: _, _ :: _, [], _, _, hbf, _, _, _, _, _, _, _ => by
    simp [formsDen] at hbf
  | _ :: _, _ :: _, _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, hw, _, _, _, _ => by simp at hw
  | _ :: _, _ :: _, _, _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, hhs, _, _, _ => by
    simp at hhs

theorem Returns.mapM_length {α β : Type} (f : α → TM β) :
    ∀ l : List α, Returns (l.mapM f) fun r ↦ r.length = l.length
  | [] => Returns.pure rfl
  | a :: l => by
    rw [List.mapM_cons]
    exact Returns.bindAll fun _ ↦ Returns.bind (Returns.mapM_length f l) fun r hr ↦
      Returns.pure (by simp [hr])

private theorem rows_rel : ∀ {ts : List TableRust} {Ts : List Table},
    List.Forall₂ TableRust.Rel ts Ts → ∀ (hs : List ℕ) (rest : List (List Form × E)),
      hs.length = ts.length → rest.length = ts.length →
      List.Forall₂ (fun r s ↦ TableRust.Rel r.1 s.1 ∧ r.2 = s.2.1) (ts.zip hs)
        (Ts.zip (hs.zip rest))
  | _, _, .nil, [], [], _, _ => .nil
  | _, _, .cons hT h, x :: hs, y :: rest, hl, hr =>
    .cons ⟨hT, rfl⟩ (rows_rel h hs rest (by simpa using hl) (by simpa using hr))
  | _, _, .nil, _ :: _, _, hl, _ => by simp at hl
  | _, _, .nil, [], _ :: _, _, hr => by simp at hr
  | _, _, .cons _ _, [], _, hl, _ => by simp at hl
  | _, _, .cons _ _, _ :: _, [], _, hr => by simp at hr

private theorem tableWeights_length (heights : List ℕ) (hh : heights.length = 6)
    (equalityPoint point : List E) : (tableWeights heights equalityPoint point).length = 6 := by
  unfold tableWeights
  generalize point.zipIdx = pts
  have : ∀ (ws : List E), ws.length = 6 → (pts.foldl (fun weights (challenge, coord) ↦
      let equality := 1 + equalityPoint.getD coord 0 + challenge
      List.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
        weights heights) ws).length = 6 := by
    induction pts with
    | nil => intro ws h; exact h
    | cons p pts ih => intro ws h; exact ih _ (by simp [h, hh])
  exact this _ (by simp [hh])

/-- **`table_sumcheck` runs `tableSumcheck`**, the bus's forms by value, a height and a form row
per table. -/
theorem SimR.tableSumcheck (heights : List ℕ) (hh : heights.length = 6)
    {busForms busForms' : List (List Form)} (hf : formsDen busForms = formsDen busForms')
    (hfl : busForms.length = 6) (constraintPowers formPowers equalityPoint : List E) (target : E) :
    Sim (tableSumcheckRust tablesRust heights busForms constraintPowers formPowers equalityPoint
        target)
      (tableSumcheck heights busForms' constraintPowers formPowers equalityPoint target) := by
  have hfl' : busForms'.length = 6 := by
    have := congrArg List.length hf
    simp only [formsDen, List.length_map] at this
    omega
  unfold tableSumcheckRust LeanVM.Protocol.Verifier.tableSumcheck
  refine SimR.sumcheck_bind (count := 4) _ (by norm_num) (by norm_num) _ fun ch claim _ ↦ ?_
  simp only
  rw [show tablesRust.length = heights.length by rw [hh]; rfl, tableWeightsRust_eq]
  have hw := tableWeights_length heights hh equalityPoint ch.reverse
  have hrows := rows_rel tablesRust_rel heights
    (busForms'.zip (tableWeights heights equalityPoint ch.reverse)) (by rw [hh]; rfl)
    (by simp [hfl', hw]; rfl)
  refine SimR.bind
    (SimR.and_returns (SimR.tableRows ch.reverse constraintPowers formPowers hrows 0 0)
    (Returns.mapM_length _ _)) fun rows r ⟨⟨h1, h2⟩, hlen⟩ ↦ ?_
  obtain ⟨final, evaluations⟩ := r
  simp only at h1 h2
  subst h1
  refine SimR.whenChecked_bind ?_
  simp only [bind_assoc]
  refine SimR.ofOption_bind fun t ht ↦ ?_
  unfold termsRust at ht
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp ht
  have := termsRust_spec constraintPowers formPowers tablesRust tables tablesRust_rel evaluations
    busForms
    busForms' _ heights hf (by rw [hlen]; simp [hh]; rfl) (by rw [hfl]; rfl) (by rw [hw]; rfl)
    (by rw [hh]; rfl) (0, 0) r hr
  rw [← h2] at this
  refine SimR.bindEq (Sim.require_iff (by rw [this])) fun _ ↦ SimR.pure rfl


/-! ### `table_sumcheck` returns wherever the statement's does -/

private theorem constraints_length : ∀ t ∈ tablesRust, ∀ columns : List E,
    (t.constraints columns).length = t.nConstraints := by
  have h : ∀ t ∈ tablesRust, (if t.opcode = 4 then 2 else 0) = t.nConstraints := by decide +kernel
  intro t ht columns
  rw [← h t ht, TableRust.constraints]
  split <;> rfl

/-- The checked terminal's dots have equal lengths: the constraint powers cover the tables', and
each table has a form per tree. -/
private theorem termsRust_some (constraintPowers formPowers : List E)
    (hfp : formPowers.length = 3) :
    ∀ (ts : List TableRust), (∀ t ∈ ts, t ∈ tablesRust) →
      ∀ (rows : List (List E × List E)) (bf : List (List Form)) (ws : List E) (acc : E × ℕ),
      (∀ f ∈ bf, f.length = 3) →
      acc.2 + (ts.map TableRust.nConstraints).sum ≤ constraintPowers.length →
      ∃ r, (((ts.zip rows).zip bf).zip ws).foldlM
          (fun (acc : E × ℕ) (x : ((TableRust × (List E × List E)) × List Form) × E) ↦ do
            let table := x.1.1.1
            let evaluations := x.1.1.2.2
            let n := table.nConstraints
            let summand ← dotRust ((constraintPowers.drop acc.2).take n)
              (table.constraints evaluations)
            let values ← dotRust formPowers (x.1.2.map fun form ↦ formEvaluateRust form evaluations)
            Pure.pure (acc.1 + x.2 * (summand + values), acc.2 + n)) acc = some r := by
  intro ts
  induction ts with
  | nil => intro _ rows bf ws acc _ _; exact ⟨acc, by simp⟩
  | cons t ts ih =>
    intro hts rows bf ws acc hbf hc
    cases rows with
    | nil => exact ⟨acc, by simp⟩
    | cons row rows =>
    cases bf with
    | nil => exact ⟨acc, by simp⟩
    | cons f bf =>
    cases ws with
    | nil => exact ⟨acc, by simp⟩
    | cons w ws =>
    simp only [List.zip_cons_cons, List.foldlM_cons]
    simp only [List.map_cons, List.sum_cons] at hc
    rw [dotRust_eq (by
        rw [constraints_length t (hts t (by simp)), List.length_take, List.length_drop]; omega),
      dotRust_eq (by rw [List.length_map, hbf f (by simp), hfp])]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    exact ih (fun t' h ↦ hts t' (by simp [h])) rows bf ws _ (fun f' h ↦ hbf f' (by simp [h]))
      (by dsimp only; omega)

theorem Comp.tableRows (point constraintPowers formPowers : List E) :
    ∀ {rowsR : List (TableRust × ℕ)} {rowsS : List (Table × ℕ × List Form × E)},
      List.Forall₂ (fun r s ↦ TableRust.Rel r.1 s.1 ∧ r.2 = s.2.1) rowsR rowsS →
      ∀ cursor final,
      Comp (rowsR.mapM fun (table, height) ↦ do
          let evaluations ← TM.nextScalars table.width
          Pure.pure (point.take height, evaluations))
        (tableTerms constraintPowers formPowers point rowsS cursor final)
  | _, _, .nil, cursor, final => by
    rw [List.mapM_nil]
    exact Comp.pure _ _
  | (t, h) :: rs, (T, h', forms, w) :: Ss, .cons ⟨hT, hh⟩ hrs, cursor, final => by
    simp only at hh
    subst hh
    rw [List.mapM_cons, tableTerms]
    simp only [bind_assoc, pure_bind]
    rw [hT.width]
    refine Comp.bindEq (Comp.nextScalars _) (Sim.nextScalars _) fun evaluations ↦ ?_
    exact Comp.bind (Comp.tableRows point constraintPowers formPowers hrs _ _)
      (SimR.tableRows point constraintPowers formPowers hrs _ _) fun _ _ _ ↦ Comp.pure _ _

/-- **`table_sumcheck` returns wherever `tableSumcheck` does**, on the powers `tablePhase` hands
it: two constraint powers, a form power per tree, and a form per tree in each table's row. -/
theorem Comp.tableSumcheck (heights : List ℕ) (hh : heights.length = 6)
    {busForms busForms' : List (List Form)} (hf : formsDen busForms = formsDen busForms')
    (hfl : busForms.length = 6) (hrow : ∀ f ∈ busForms, f.length = 3)
    (constraintPowers formPowers equalityPoint : List E) (hcp : constraintPowers.length = 2)
    (hfp : formPowers.length = 3) (target : E) :
    Comp (tableSumcheckRust tablesRust heights busForms constraintPowers formPowers equalityPoint
        target)
      (tableSumcheck heights busForms' constraintPowers formPowers equalityPoint target) := by
  have hfl' : busForms'.length = 6 := by
    have := congrArg List.length hf
    simp only [formsDen, List.length_map] at this
    omega
  unfold tableSumcheckRust LeanVM.Protocol.Verifier.tableSumcheck
  refine Comp.sumcheck_bind (count := 4) _ (by norm_num) (by norm_num) _ fun ch claim _ ↦ ?_
  simp only
  rw [show tablesRust.length = heights.length by rw [hh]; rfl, tableWeightsRust_eq]
  have hw := tableWeights_length heights hh equalityPoint ch.reverse
  have hrows := rows_rel tablesRust_rel heights
    (busForms'.zip (tableWeights heights equalityPoint ch.reverse)) (by rw [hh]; rfl)
    (by simp [hfl', hw]; rfl)
  refine Comp.bind (Comp.tableRows ch.reverse constraintPowers formPowers hrows 0 0)
    (SimR.and_returns (SimR.tableRows ch.reverse constraintPowers formPowers hrows 0 0)
    (Returns.mapM_length _ _)) fun rows r ⟨⟨h1, h2⟩, hlen⟩ ↦ ?_
  obtain ⟨final, evaluations⟩ := r
  simp only at h1 h2
  subst h1
  refine Comp.whenChecked_bind ?_
  simp only [bind_assoc]
  obtain ⟨r, hr⟩ := termsRust_some constraintPowers formPowers hfp tablesRust (fun _ h ↦ h)
    evaluations busForms (tableWeights heights equalityPoint ch.reverse) (0, 0) hrow
    (by rw [hcp]; decide +kernel)
  have := termsRust_spec constraintPowers formPowers tablesRust tables tablesRust_rel evaluations
    busForms busForms' _ heights hf (by rw [hlen]; simp [hh]; rfl) (by rw [hfl]; rfl)
    (by rw [hw]; rfl) (by rw [hh]; rfl) (0, 0) r hr
  rw [← h2] at this
  refine Comp.ofOption_bind (a := r.1) (by unfold termsRust; rw [hr]; rfl) ?_
  exact Comp.bindEq (Comp.require_iff (by rw [this])) (Sim.require_iff (by rw [this]))
    fun _ ↦ Comp.pure _ _

end TableSumcheck

end

end Rv64mc.Model
