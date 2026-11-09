module

public import Statement.Prover.Gkr
public import Statement.Prover.Columns

/-!
# The bus phase, executable

The prover of `verifyBusBalance` (`crates/verifier/src/bus.rs:106-213`) from the instance's columns
`cols` (by global column number): the three sides' leaves filled straight into arrays, each side's
blocks end to end in `stack_offsets`' order (`stackA`) and padded with ones; the batched GKR over
the three trees (`gkrA`); the framework columns' extensions at the point (`mleK`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## Stacking -/

/-- `stack_offsets`' order of blocks of the given log-sizes
(`crates/verifier/src/multilinear.rs:134-144`): the stable sort of the indices by size, larger
first. -/
def blockOrder (sizes : List ℕ) : List ℕ :=
  (List.range sizes.length).mergeSort fun i j ↦ decide (sizes.getD j 0 ≤ sizes.getD i 0)

/-- A side's leaves: the blocks' tables `tab b` in `stack_offsets`' order, padded with ones to
`2^D` entries. -/
def stackA (sizes : List ℕ) (tab : ℕ → Array E) (D : ℕ) : Array E :=
  let body := (blockOrder sizes).foldl (fun acc b ↦ acc ++ tab b) #[]
  body ++ Array.replicate (2 ^ D - body.size) 1

/-- A side's block log-sizes: the framework's, then the tables' blocks'. -/
def sideLogs (fw : List ℕ) (blocks : List BusBlock) : List ℕ := fw ++ blocks.map (·.logRows)

/-- `1, a, a², …`, `n` terms, by running products. -/
def powsA (a : E) (n : ℕ) : Array E :=
  (Nat.fold n (fun _ _ (acc : Array E × E) ↦ (acc.1.push acc.2, acc.2 * a))
    (Array.emptyWithCapacity n, 1)).1

/-! ## The leaves -/

/-- Row `x` of a table whose first global column is `base`, of `width` columns, as a function of
the local column (`0` past the width). -/
def busRowOf (cols : Array (Array K)) (base width x : ℕ) (i : ℕ) : E :=
  if i < width then ofK ((cols.getD (base + i) #[]).getD x 0) else 0

/-- A table block's leaves: `β` plus the block's fingerprint at every executed row of its owner,
`1` at a padding row. -/
def tableTabA (cols : Array (Array K)) (β : E) (w : List E) (b : BusBlock) : Array E :=
  let base := globalColumnBases.getD b.owner 0
  let width := (tables.getD b.owner default).width
  let coords := b.coordinates.zipIdx.map fun cs ↦ (w.getD cs.2 0, cs.1)
  Array.ofFn (n := 2 ^ b.logRows) fun x ↦
    if x.1 < b.rows then
      β + (coords.map fun aw ↦ aw.1 * aw.2.evaluate (busRowOf cols base width x.1)).sum
    else 1

/-- The state block's one leaf: `β` plus the fingerprint of `(SEP_STATE, pc, g⁰)`. -/
def stateTabA (β : E) (w : List E) (pc : E) : Array E :=
  #[β + dot (w.take 3) [sepState, pc, Protocol.Verifier.gpow 0]]

/-- The memory block's leaves: `β` plus the fingerprint of `(SEP_MEM, gʸ, count_y, m_y)`, the
powers of `g` read off `pows`. -/
def memTabA (cols : Array (Array K)) (logMem : ℕ) (pows : Array E) (β : E) (w : List E)
    (cnt : ℕ → E) : Array E :=
  let w6 := w.take 6
  let m0 := cols.getD memory0 #[]
  let m1 := cols.getD memory1 #[]
  let m2 := cols.getD memory2 #[]
  Array.ofFn (n := 2 ^ logMem) fun y ↦
    β + dot w6 ([sepMem, pows.getD y.1 0, cnt y.1] ++
      [ofK (m0.getD y.1 0), ofK (m1.getD y.1 0), ofK (m2.getD y.1 0)])

/-- The bytecode block's leaves: `β` plus the fingerprint of `(SEP_BYTECODE, gʸ, count_y)` and of
the instruction's sixteen slots. -/
def bcTabA (bc : Array K) (logBc : ℕ) (pows : Array E) (β : E) (w : List E) (cnt : ℕ → E) :
    Array E :=
  let w3 := w.take 3
  let wA := w.toArray
  let n := 2 ^ logBc
  Array.ofFn (n := n) fun y ↦
    β + (dot w3 [sepBytecode, pows.getD y.1 0, cnt y.1] +
      ((List.range 16).map fun k ↦ wA.getD k 0 * ofK (bc.getD (y.1 + n * k) 0)).sum)

/-- The push side's blocks: the framework (counts one), then the tables'. -/
def pushTabA (cols : Array (Array K)) (layout : Layout) (pows : Array E) (β : E) (w : List E) :
    ℕ → Array E
  | 0 => stateTabA β w (Protocol.Verifier.gpow 0)
  | 1 => memTabA cols layout.logMemory pows β w fun _ ↦ 1
  | 2 => bcTabA layout.bytecode.toArray layout.logBytecode pows β w fun _ ↦ 1
  | b + 3 => tableTabA cols β w (layout.push.getD b default)

/-- The pull side's blocks: the framework (the final counts), then the tables'. -/
def pullTabA (cols : Array (Array K)) (layout : Layout) (pows : Array E) (β : E) (w : List E) :
    ℕ → Array E
  | 0 => stateTabA β w (Protocol.Verifier.gpow (2 ^ layout.logBytecode - 1))
  | 1 => memTabA cols layout.logMemory pows β w fun y ↦
      ofK ((cols.getD memoryFinalCounters #[]).getD y 0)
  | 2 => bcTabA layout.bytecode.toArray layout.logBytecode pows β w fun y ↦
      ofK ((cols.getD bytecodeFinalCounters #[]).getD y 0)
  | b + 3 => tableTabA cols β w (layout.pull.getD b default)

/-- The count side's blocks: the count cells. -/
def countTabA (cols : Array (Array K)) (layout : Layout) (b : ℕ) : Array E :=
  tableTabA cols 0 [1] (layout.count.getD b default)

/-! ## The phase -/

/-- **The bus phase**: the fingerprint challenges `α` and `β`, the leaves, the GKR, the framework
values at the point. -/
def busFast (layout : Layout) (cols : Array (Array K)) : Script Unit :=
  (Script.sampleN busBits).bind fun alphas ↦ Script.sampleE.bind fun beta ↦
  let w := eqKernel alphas
  let fw := [0, layout.logMemory, layout.logBytecode]
  let D := (busLayout fw layout.push).depth
  let pows := powsA gen (2 ^ max layout.logMemory layout.logBytecode)
  let L₀ := stackA (sideLogs fw layout.push) (pushTabA cols layout pows beta w) D
  let L₁ := stackA (sideLogs fw layout.pull) (pullTabA cols layout pows beta w) D
  let L₂ := stackA (sideLogs [] layout.count) (countTabA cols layout) D
  (gkrA D (treeLayers D L₀) (treeLayers D L₁) (treeLayers D L₂)).bind fun g ↦
    let low := g.2.1.take layout.logMemory
    let memory := [mleK (cols.getD memory0 #[]) low, mleK (cols.getD memory1 #[]) low,
      mleK (cols.getD memory2 #[]) low]
    let mf := mleK (cols.getD memoryFinalCounters #[]) low
    let bf := mleK (cols.getD bytecodeFinalCounters #[]) (g.2.1.take layout.logBytecode)
    (Script.sendList memory).bind fun _ ↦ (Script.sendE mf).bind fun _ ↦ Script.sendE bf

end LeanVM.Prover

end
