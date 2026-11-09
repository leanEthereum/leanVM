module

public import Statement.Prover.Gkr
public import Statement.Prover.Columns

/-!
# The bus phase, executable

The prover of `verifyBusBalance` (`crates/verifier/src/bus.rs:130-247`; the Rust's
`prove_balance`, `crates/leanvm_core/src/leaf.rs`) from the instance's columns `cols` (by global
column number): the grind and the fingerprint, sixteen slot weights and `β`; the three sides'
leaves filled straight into arrays, each side's blocks end to end in `stack_offsets`' order
(`stackA`) and padded with ones; the batched GKR over the three trees (`gkrA`); the framework
columns' extensions at the point (`mleK`); the bytecode's share and its sumcheck
(`bytecodeShareA`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

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
word `m_y` its two limbs, the powers of `g` read off `pows`. -/
def memTabA (cols : Array (Array K)) (logMem : ℕ) (pows : Array E) (β : E) (w : List E)
    (cnt : ℕ → E) : Array E :=
  let w5 := w.take 5
  let m0 := cols.getD memory0 #[]
  let m1 := cols.getD memory1 #[]
  Array.ofFn (n := 2 ^ logMem) fun y ↦
    β + dot w5 ([sepMem, pows.getD y.1 0, cnt y.1] ++ [ofK (m0.getD y.1 0), ofK (m1.getD y.1 0)])

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

/-! ## The bytecode's share -/

/-- The stacked bytecode's slots at `low`: slot `x`'s `2^logBc` words' extension at `low`, `P(low, x)`
(`public_eval` of the bytecode block's public coordinates, `crates/leanvm_core/src/leaf.rs`; the
three slots before them hold zeros). -/
def bytecodeSlotsA (bc : Array K) (logBc : ℕ) (low : List E) : Array E :=
  Array.ofFn (n := 2 ^ busBits) fun x ↦
    mleK (bc.extract (x.1 * 2 ^ logBc) ((x.1 + 1) * 2 ^ logBc)) low

/-- A round of the share's sumcheck over the slot, the low bit first: the coefficients of
`Σ_pairs (a₀ + X(a₀ + a₁))(p₀ + X(p₀ + p₁))`, constant first. -/
def shareRound (st : Array E × Array E) : List E :=
  let pairs := (List.range (st.1.size / 2)).map fun i ↦
    (st.1.getD (2 * i) 0, st.1.getD (2 * i + 1) 0, st.2.getD (2 * i) 0, st.2.getD (2 * i + 1) 0)
  [sumE (pairs.map fun (a0, _, p0, _) ↦ a0 * p0),
    sumE (pairs.map fun (a0, a1, p0, p1) ↦ a0 * (p0 + p1) + (a0 + a1) * p0),
    sumE (pairs.map fun (a0, a1, p0, p1) ↦ (a0 + a1) * (p0 + p1))]

/-- The share's sumcheck fold at the challenge. -/
def shareFold (st : Array E × Array E) (r : E) : Array E × Array E :=
  (foldPairsA r st.1, foldPairsA r st.2)

/-- **The bytecode's share** (`prove_bytecode_share`, `crates/leanvm_core/src/leaf.rs`): the share
`Σ_x w_x·P(low, x)`, the sumcheck over the slot `x`, then `P(low, r⃗)` at its challenges. -/
def bytecodeShareA (w : List E) (slots : Array E) : Script Unit :=
  (Script.sendE (dot w slots.toList)).bind fun _ ↦
  (sumcheckBy shareRound shareFold (List.replicate busBits none) (w.toArray, slots)).bind fun r ↦
    Script.sendE (r.2.2.getD 0 0)

/-! ## The phase -/

/-- **The bus phase**: the grind for the push tree's depth, the fingerprint (sixteen slot weights
and `β`), the leaves, the GKR, the framework values at the point, the bytecode's share. -/
def busFast (layout : Layout) (cols : Array (Array K)) : Script Unit :=
  let fw := [0, layout.logMemory, layout.logBytecode]
  let D := (busLayout fw layout.push).depth
  (Script.grindBits (busGrindingBits D)).bind fun _ ↦
  (Script.sampleN (2 ^ busBits)).bind fun w ↦ Script.sampleE.bind fun beta ↦
  let pows := powsA gen (2 ^ max layout.logMemory layout.logBytecode)
  let L₀ := stackA (sideLogs fw layout.push) (pushTabA cols layout pows beta w) D
  let L₁ := stackA (sideLogs fw layout.pull) (pullTabA cols layout pows beta w) D
  let L₂ := stackA (sideLogs [] layout.count) (countTabA cols layout) D
  (gkrA D (treeLayers D L₀) (treeLayers D L₁) (treeLayers D L₂)).bind fun g ↦
    let low := g.2.1.take layout.logMemory
    let bcLow := g.2.1.take layout.logBytecode
    let memory := [mleK (cols.getD memory0 #[]) low, mleK (cols.getD memory1 #[]) low]
    let mf := mleK (cols.getD memoryFinalCounters #[]) low
    let bf := mleK (cols.getD bytecodeFinalCounters #[]) bcLow
    (Script.sendList memory).bind fun _ ↦ (Script.sendE mf).bind fun _ ↦
    (Script.sendE bf).bind fun _ ↦
    bytecodeShareA w (bytecodeSlotsA layout.bytecode.toArray layout.logBytecode bcLow)

end LeanVM.Prover

end
