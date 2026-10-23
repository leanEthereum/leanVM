import LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsa

/-!
# Tests: the table phase's identities at leanISA

* **Flushes at values in `E`.** At values of a table's columns outside `K`, every opcode table's
  Python flushes evaluate to the instance's flush polynomials evaluated by `eval₂`, in order
  (`pyFlush_evalE`); `JUMP`'s constraints likewise (`jumpConstraints_evalE`).
* **The instance's shape.** The sumcheck tables are the six opcode tables, `B = 2`, and the
  boundary columns are the memory columns and `BFCNT`.
* **The weights, and the mutation that makes the length of `α` load-bearing.** For four `α` the
  Python's equality kernel is the protocol's fingerprint weights; for five it is not: the fifth
  coordinate `1` multiplies the first sixteen weights by `1 + 1 = 0`. `TableFid` is therefore
  stated for reads whose fingerprint challenges are four, which the wire guarantees
  (`abProg_bind_guard`).
* **The boundary blocks.** At a read with four challenges the protocol's push boundary values are
  the Python's framework fingerprints (`bnd_push`); at the same read with a fifth challenge they
  are not.
* **Inhabitants.** A read of the right shape at the test's sizes, and the instantiated theorems.
-/

namespace LeanVMTests.Protocol.EndToEnd.Front.TableFid

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.TableSumcheck
open CompPoly CPoly

/-- Four `XOR` instructions. -/
def prog4 : Program := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- A size vector with a table as tall as the memory. -/
def s₁ : Sizes := ⟨16, by decide, ![2 ^ 16, 2 ^ 3, 2 ^ 16, 2 ^ 4, 2 ^ 16, 2 ^ 16]⟩

/-- The instance at the test's sizes, with the deployed Flock specification. -/
abbrev I₁ : M3Instance := leanIsaInstance Blake2sFlock.blake2sFlockSpec prog4 s₁

/-! ## Flushes and constraints at values in `E` -/

/-- Values of table `t`'s columns outside `K`: `y`-multiples of the column index plus one. -/
def eOf (t : Fin 6) : Fin (width (opIdx t)) → E := fun i ↦ yE * (i.val : E) + 1

/-- The Python's flushes of a side, evaluated at `eOf t`. -/
def pyVals (t : Fin 6) (side : Side) : List (List E) :=
  (Complete.pySide t side).map fun coords ↦
    (List.range 16).map fun k ↦ (coords.getD k {}).evaluate (rowE (eOf t))

/-- The instance's flushes of a side, evaluated at `eOf t`. -/
def instVals (t : Fin 6) (side : Side) : List (List E) :=
  ((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map
    fun f ↦ f.2.toList.map fun P ↦ P.eval₂ (algebraMap K E) (eOf t)

#guard pyVals 3 .push == instVals 3 .push
#guard pyVals 3 .pull == instVals 3 .pull
#guard pyVals 4 .push == instVals 4 .push
#guard pyVals 4 .pull == instVals 4 .pull

example (t : Fin 6) (side : Side) : pyVals t side = instVals t side := pyFlush_evalE t side (eOf t)

-- `JUMP`'s constraints at values outside `K`.
#guard jumpConstraints ((List.finRange 14).map fun i ↦ yE * (i.val : E) + 1) ==
  (LeanIsa.constraints (opIdx 4)).map fun P ↦
    P.eval₂ (algebraMap K E) fun i ↦ yE * (i.val : E) + 1

/-! ## The instance's shape -/

example : I₁.B = 2 := sumcheckB_leanIsa _ _ _
example : I₁.boundaryColumns = [memCol 0, memCol 1, memCol 2, memCol 3, bfcntCol] :=
  boundaryColumns_leanIsa _ _ _
example (j : Fin 9) (h : I₁.SumcheckTable j) : 3 ≤ j.val := three_le_of_sumcheckTable _ _ _ j h
example (t : Fin 6) : I₁.SumcheckTable (opIdx t) := sumcheckTable_opIdx _ _ _ t

example : I₁.τmax = (tableLogs s₁).foldl max 0 := τmax_leanIsa _ _ _
example : I₁.μBus ≠ 0 := μBus_ne_zero _ _ _
example : (busLayout [0, (verifierLayout prog4 s₁).logMemory, (verifierLayout prog4 s₁).logBytecode]
    (verifierLayout prog4 s₁).push).depth = I₁.μBus := busDepth_leanIsa _ _ _

/-! ## The weights: four `α`, and the mutation with five -/

/-- Four challenges outside `K`. -/
def α₄ : List E := [yE, 0, 1, yE + 1]

#guard (List.range 16).all fun k ↦
  (eqKernel α₄).getD k 0 == if h : k < 16 then (fingerprintWeights (toAlpha α₄))[k] else 0

example (k : Fin 16) :
    (fingerprintWeights (toAlpha α₄))[k.val] = (eqKernel α₄).getD k 0 :=
  fingerprintWeights_toAlpha rfl k

/-- Five challenges: the fifth is `1`. -/
def α₅ : List E := [0, 0, 0, 0, 1]

-- Mutation: with five `α` the Python's first sixteen weights vanish, the protocol's do not.
#guard (List.range 16).all fun k ↦ (eqKernel α₅).getD k 0 == 0
#guard (fingerprintWeights (toAlpha α₅))[0] == 1

/-- Sizes with a one-variable memory and one-row tables, to evaluate the boundary blocks. -/
def sTiny : Sizes := ⟨1, by decide, ![1, 1, 1, 1, 1, 1]⟩

/-- Whether the protocol's push boundary values at a read are the Python's framework
fingerprints (`bnd_push`). -/
def bndPushAgrees (w : BusWit) : Bool :=
  ((boundary prog4 sTiny).filter fun b ↦ decide (b.side = Side.push)).map (fun b ↦
      arkB Blake2sFlock.blake2sFlockSpec prog4 sTiny (toAlpha w.alphas) w.beta
        (w.vals _) w.point (.boundary b)) ==
    (fingerprints (eqKernel w.alphas) w.memory (w.point.take sTiny.logMem)
      (w.point.take prog4.logSize)
      (multilinearEval ((verifierLayout prog4 sTiny).bytecode.map ofK)
        (w.point.take prog4.logSize ++ w.alphas)) (Verifier.gpow 0) 1 1).map
        (w.beta + ·)

/-- A read with four challenges. -/
def r₄ : BusWit := ⟨α₄, yE, [yE, 1, yE + 1, 1], [0, 1, yE], [1, yE, yE + 1], yE, 1⟩

/-- The same read with five challenges, the fifth `1`. -/
def r₅ : BusWit := { r₄ with alphas := α₅ }

#guard bndPushAgrees r₄
-- Mutation: with five challenges the boundary blocks are no longer the Python's fingerprints, so
-- the totals (and `TableFid`'s target) differ.
#guard !bndPushAgrees r₅

example : bndPushAgrees r₄ = true := by
  unfold bndPushAgrees
  rw [bnd_push Blake2sFlock.blake2sFlockSpec prog4 sTiny r₄ rfl rfl (by decide) (by decide)]
  simp

/-! ## Inhabitants -/

/-- A read of the bus phase of the right shape at the test's sizes, with four challenges. -/
def w₀ : BusWit :=
  ⟨α₄, yE, List.replicate I₁.μBus yE, [0, 1, yE], [1, yE, 0], yE, 1⟩

example : w₀.Shaped I₁ := ⟨by simp [w₀], rfl, rfl⟩

example (input : PublicInput) :
    TableFid I₁ (leanIsa_conditions _ _ _) input (verifierLayout prog4 s₁) pyCol w₀ :=
  tableFid_leanIsa _ _ _ input _ w₀ ⟨by simp [w₀], rfl, rfl⟩ rfl

example (input : PublicInput) (ξ : E) :
    dot (fpsOf ξ) (w₀.result (verifierLayout prog4 s₁)).totals =
      powerBatch (claimed I₁ (busStmt I₁ (leanIsa_conditions _ _ _) input w₀)) ξ :=
  target_leanIsa _ _ _ input w₀ (by simp [w₀]) rfl rfl ξ

#guard cpsOf yE == [1, yE]
#guard fpsOf yE == [yE ^ 2, yE ^ 3, yE ^ 4]

end LeanVMTests.Protocol.EndToEnd.Front.TableFid
