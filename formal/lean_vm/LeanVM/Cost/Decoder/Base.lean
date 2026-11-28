module

public import LeanVM.Cost.Decoder.Lib
public import LeanVM.Protocol.Extraction.Fast.Address
import all LeanVM.Protocol.Extraction.Fast.Address

/-!
# The guest decoder's compiled chain: its base, the machine's step

The decoder's compiled modules form one import chain (the compiler allocates function indices from
what a module imports). It starts past the library's compiled list and sorted-map functions
(`Cost/Extractor/Transcript.lean`) with the machine's step on a memory vector
(`Extraction.Fast.stepVec`, compiled as `stepVecC`), which the decoder's replay of the run calls
(`Decoder/Replay.lean`). In the bus era the step came from the extractor's runner, which the
decoder's chain followed; the decoder needs only the step, so its chain compiles it here.

Two restatements, each equal to the statement's text, so that the compiled code computes each
value once (the compiler substitutes a function-valued `let` without β-reducing, so a value holding
`cAt` is not found again once β-reduced, and a value used under the `∀ c` of the Keccak relation is
recomputed per cell and limb):

* `keccakRoundShared`: `Keccak.round` with `cAt` written out; θ, ρπ and χ each built once per round;
* `executeWithShared`: `executeWith` with Keccak-f of the input cells bound once per instruction.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Semantics LeanVM.Cost.FastLib

public section

open LeanVM.Semantics.Keccak in
/-- `Keccak.round`, `cAt` written out. -/
@[expose] def keccakRoundShared (a : KeccakState) (rc : UInt64) : KeccakState :=
  let c : Vector UInt64 5 := Vector.ofFn fun x ↦
    lane a x ^^^ lane a (x + 5) ^^^ lane a (x + 10) ^^^ lane a (x + 15) ^^^ lane a (x + 20)
  let a : KeccakState := Vector.ofFn fun i ↦
    lane a i ^^^ c.toArray.getD ((i.val + 4) % 5) 0 ^^^ rot (c.toArray.getD ((i.val + 1) % 5) 0) 1
  let b : KeccakState := (List.range 25).foldl
    (fun b i ↦ b.setIfInBounds (keccakPi i) (rot (lane a i) (keccakRho.getD i 0)))
    (Vector.replicate 25 0)
  let a : KeccakState := Vector.ofFn fun i ↦
    lane b i ^^^ (~~~ lane b (i.val - i.val % 5 + (i.val + 1) % 5) &&&
      lane b (i.val - i.val % 5 + (i.val + 2) % 5))
  a.setIfInBounds 0 (lane a 0 ^^^ rc)

theorem keccakRound_shared (a : KeccakState) (rc : UInt64) :
    Keccak.round a rc = keccakRoundShared a rc :=
  rfl

cost_rewrite keccakRound_shared

/-- `executeWith`, Keccak-f of the cells read computed once. -/
@[expose] def executeWithShared (read : K → Option E) (r : Registers K) :
    LeanIsaInstruction → Option (Registers K)
  | .xor oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA + vB)
    pure r.next
  | .mulNative oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA * vB)
    pure r.next
  | .setConstant o k => do
    let v ← read (r.fp * o)
    guard (v = k)
    pure r.next
  | .deref o1 o2 o3 mode => do
    let p ← read (r.fp * o1)
    guard (IsInK p)
    let v3 ← read (r.fp * o3)
    let v2 ← read (p.limb 0 * o2)
    guard (v2 = derefSource mode r v3)
    pure r.next
  | .jump oc od of => do
    let c ← read (r.fp * oc)
    let d ← read (r.fp * od)
    let f ← read (r.fp * of)
    guard (IsInK c ∧ IsInK d ∧ IsInK f)
    pure (if c = 0 then r.next else ⟨d.limb 0, f.limb 0⟩)
  | .keccak om otail ob8 ocap oout inOdd outOdd outCells => do
    let input ← readCells read r.fp (keccakInputCellOffset om otail ob8 ocap)
    let output ← readFirstCells read r.fp (fun c ↦ LeanVM.Parameters.g ^ c.val * oout)
      outCells.cellCount
    let s := keccakF1600 (stateOfCells input inOdd)
    guard (∀ c : Fin 13, outCells.cellCount ≤ c.val ∨ output c = cellsOfState s outOdd c)
    pure r.next

theorem executeWith_shared (read : K → Option E) (r : Registers K) (i : LeanIsaInstruction) :
    executeWith read r i = executeWithShared read r i := by
  cases i with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    have h : ∀ (input output : Fin 13 → E), KeccakCellsRelation input inOdd output outOdd outCells =
        (∀ c : Fin 13, outCells.cellCount ≤ c.val ∨
          output c = cellsOfState (keccakF1600 (stateOfCells input inOdd)) outOdd c) := by
      intro input output
      refine propext (forall_congr' fun c ↦ ?_)
      rw [imp_iff_not_or, Nat.not_lt]
    simp only [executeWith, executeWithShared, h]
  | _ => rfl

cost_rewrite executeWith_shared

-- the machine's step on a memory vector (`Extraction.Fast.stepVec`)
cost_compile stepVecC := stepVec

-- the address tables (`Extraction.Fast.powTable`), the memory's and the bytecode's
cost_compile powTableC := powTable

end

end LeanVM.Cost.Decoder
