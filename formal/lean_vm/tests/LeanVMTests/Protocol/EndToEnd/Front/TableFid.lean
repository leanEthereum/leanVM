import LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsa

/-!
# Tests: the table phase's identities at leanISA

* **Flushes at values in `E`.** At values of a table's columns outside `K`, every opcode table's
  verifier flushes evaluate to the instance's flush polynomials evaluated by `eval₂`, in order
  (`refFlush_evalE`), `KECCAK`'s twenty-eight flushes of a side included; `JUMP`'s constraints
  likewise (`jumpConstraints_evalE`).
* **The instance's shape.** The sumcheck tables are the six opcode tables, `B = 2`, and the
  boundary columns are the memory columns and `BFCNT`.
* **The weights.** The verifier's sixteen slot weights are the protocol's fingerprint weights.
* **The boundary blocks, and the mutation that makes the share load-bearing.** At a read whose
  share is the bytecode's the protocol's push boundary values are the verifier's framework
  fingerprints (`bnd_push`); at the same read with another share they are not.
* **Inhabitants.** A read of the right shape at the test's sizes, and the instantiated theorems.
-/

namespace LeanVMTests.Protocol.EndToEnd.Front.TableFid

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.TableSumcheck
open CompPoly CPoly

/-- Four `XOR` instructions. -/
def prog4 : LeanIsaProgram := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- A size vector with a table as tall as the memory. -/
def s₁ : Sizes := ⟨16, by decide, ![2 ^ 16, 2 ^ 3, 2 ^ 16, 2 ^ 4, 2 ^ 16, 2 ^ 16]⟩

/-- The instance at the test's sizes. -/
abbrev I₁ : M3Instance := leanIsaInstance prog4 s₁

/-! ## Flushes and constraints at values in `E` -/

/-- Values of table `t`'s columns outside `K`: `y`-multiples of the column index plus one. -/
def eOf (t : Fin 6) : Fin (width (opIdx t)) → E := fun i ↦ yE * (i.val : E) + 1

/-- The verifier's flushes of a side, evaluated at `eOf t`. -/
def refVals (t : Fin 6) (side : Side) : List (List E) :=
  (Complete.refSide t side).map fun coords ↦
    (List.range 16).map fun k ↦ (coords.getD k {}).evaluate (rowE (eOf t))

/-- The instance's flushes of a side, evaluated at `eOf t`. -/
def instVals (t : Fin 6) (side : Side) : List (List E) :=
  ((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map
    fun f ↦ f.2.toList.map fun P ↦ P.eval₂ (algebraMap K E) (eOf t)

#guard refVals 3 .push == instVals 3 .push
#guard refVals 3 .pull == instVals 3 .pull
#guard refVals 4 .push == instVals 4 .push
#guard refVals 4 .pull == instVals 4 .pull
#guard (Complete.refSide 5 .push).length == 28 && (Complete.refSide 5 .pull).length == 28
#guard refVals 5 .push == instVals 5 .push
#guard refVals 5 .pull == instVals 5 .pull

example (t : Fin 6) (side : Side) : refVals t side = instVals t side := refFlush_evalE t side (eOf t)

-- `JUMP`'s constraints at values outside `K`.
#guard jumpConstraints ((List.finRange 14).map fun i ↦ yE * (i.val : E) + 1) ==
  (LeanIsa.constraints (opIdx 4)).map fun P ↦
    P.eval₂ (algebraMap K E) fun i ↦ yE * (i.val : E) + 1

/-! ## The instance's shape -/

example : I₁.B = 2 := sumcheckB_leanIsa _ _
example : I₁.boundaryColumns = [memCol 0, memCol 1, memCol 2, bfcntCol] :=
  boundaryColumns_leanIsa _ _
example (j : Fin 9) (h : I₁.SumcheckTable j) : 3 ≤ j.val := three_le_of_sumcheckTable _ _ j h
example (t : Fin 6) : I₁.SumcheckTable (opIdx t) := sumcheckTable_opIdx _ _ t

example : I₁.τmax = (tableLogs s₁).foldl max 0 := τmax_leanIsa _ _
example : I₁.μBus ≠ 0 := μBus_ne_zero _ _
example : (busLayout [0, (verifierLayout prog4 s₁).logMemory, (verifierLayout prog4 s₁).logBytecode]
    (verifierLayout prog4 s₁).push).depth = I₁.μBus := busDepth_leanIsa _ _

/-! ## The weights -/

/-- Sixteen slot weights outside `K`. -/
def α₁₆ : List E := (List.range 16).map fun i : ℕ ↦ yE ^ (i + 1)

#guard (List.range 16).all fun k ↦
  α₁₆.getD k 0 == if h : k < 16 then (fingerprintWeights (toAlpha α₁₆))[k] else 0

example (k : Fin 16) : (fingerprintWeights (toAlpha α₁₆))[k.val] = α₁₆.getD k 0 :=
  fingerprintWeights_toAlpha rfl k

/-- Sizes with a one-variable memory and one-row tables, to evaluate the boundary blocks. -/
def sTiny : Sizes := ⟨1, by decide, ![1, 1, 1, 1, 1, 1]⟩

/-- The bytecode's true share at a point's low coordinates, for the slot weights `α₁₆`. -/
def trueShare (s : Sizes) (point : List E) : E :=
  shareTotal (vecOf (2 ^ 4) α₁₆)
    (slotValues (verifierLayout prog4 s).bytecode (point.take prog4.logSize))

/-- Whether the protocol's push boundary values at a read are the verifier's framework
fingerprints (`bnd_push`). -/
def bndPushAgrees (w : BusWit) : Bool :=
  ((boundary prog4 sTiny).filter fun b ↦ decide (b.side = Side.push)).map (fun b ↦
      arkB prog4 sTiny (toAlpha w.alphas) w.beta
        (w.vals _) w.point (.boundary b)) ==
    (fingerprints w.alphas w.memory (w.point.take sTiny.logMem)
      (w.point.take prog4.logSize) w.share (Verifier.gpow 0) 1 1).map (w.beta + ·)

/-- A read whose share is the bytecode's. -/
def r₁₆ : BusWit :=
  ⟨α₁₆, yE, [yE, 1, yE + 1, 1], [0, 1, yE], [1, yE], yE, 1,
    trueShare sTiny [yE, 1, yE + 1, 1], []⟩

/-- The same read with another share. -/
def rWrong : BusWit := { r₁₆ with share := r₁₆.share + 1 }

#guard bndPushAgrees r₁₆
-- Mutation: with a wrong share the boundary blocks are no longer the verifier's fingerprints, so
-- the totals (and `TableFid`'s target) differ.
#guard !bndPushAgrees rWrong

example : bndPushAgrees r₁₆ = true := by
  unfold bndPushAgrees
  rw [bnd_push prog4 sTiny r₁₆ rfl rfl rfl (by decide) (by decide)]
  simp

/-! ## Inhabitants -/

/-- A read of the bus phase of the right shape at the test's sizes. -/
def w₀ : BusWit :=
  ⟨α₁₆, yE, List.replicate I₁.μBus yE, [0, 1, yE], [1, yE], yE, 1,
    trueShare s₁ (List.replicate I₁.μBus yE), []⟩

example : w₀.Shaped I₁ (verifierLayout prog4 s₁) := ⟨by simp [w₀], rfl, rfl, rfl⟩

example (input : PublicInput) :
    TableFid I₁ (leanIsa_conditions _ _) input (verifierLayout prog4 s₁) refCol w₀ :=
  tableFid_leanIsa _ _ input _ w₀ ⟨by simp [w₀], rfl, rfl, rfl⟩ rfl

example (input : PublicInput) (ξ : E) :
    dot (fpsOf ξ) (w₀.result (verifierLayout prog4 s₁)).totals =
      powerBatch (claimed I₁ (busStmt I₁ (leanIsa_conditions _ _) input w₀)) ξ :=
  target_leanIsa _ _ input w₀ (by simp [w₀]) rfl rfl rfl ξ

#guard cpsOf yE == [1, yE]
#guard fpsOf yE == [yE ^ 2, yE ^ 3, yE ^ 4]

end LeanVMTests.Protocol.EndToEnd.Front.TableFid
