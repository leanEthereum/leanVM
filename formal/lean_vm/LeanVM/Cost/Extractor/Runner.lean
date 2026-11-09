module

public import LeanVM.Cost.Extractor.Transcript
public import LeanVM.Protocol.Extraction.Fast.RunVec
public import LeanVM.Protocol.Extraction.Fast.Extract
import all LeanVM.Protocol.Extraction.Fast.RunVec
import all LeanVM.Protocol.Extraction.Fast.AfterRoot
import all LeanVM.Protocol.Extraction.Fast.Extract
import all LeanVM.Protocol.Extraction.Extractor

/-!
# The candidate runner and the fast path, compiled

`runnerTables prog layout` and `runWithTables tabs prog input layout` (`Fast/RunVec.lean`: the
address tables, the final registers and the step cap built once, then per stack the boundary check
`boundaryOfStack`, the memory vector `memoryVec` and the halting loop `haltLoopVec`, Keccak-f
inside the instructions) and
`fastStacksFast` (the fast path: each lane's word read as a codeword, `Fast/Extract.lean`).

The extractor's compiled modules form one import chain: this module follows the transcript's.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Semantics LeanVM.Cost.FastLib

public section

cost_enc LeanVM.Extraction.Fast.LayoutLite

/-- A column's stack index, the default placement's `0` where none is placed. -/
def placementIndexLite (layout : LayoutLite) (column : ℕ) : ℕ :=
  match layout.placements.getD column none with
  | some p => p.index
  | none => 0

theorem placement_index_eq (layout : LayoutLite) (column : ℕ) :
    (layout.placement column).index = placementIndexLite layout column := by
  unfold LayoutLite.placement placementIndexLite
  cases layout.placements.getD column none <;> rfl

cost_rewrite placement_index_eq

cost_compile fastStacksFastC := fastStacksFast

/-! ### Sharing in Keccak-f and the `KECCAK` instruction

Two restatements, each equal to the statement's text, so that the compiled code computes each
value once (the compiler substitutes a function-valued `let` without β-reducing, so a value holding
`cAt` is not found again once β-reduced, and a value used under the `∀ c` of the Keccak relation is
recomputed per cell and limb):

* `keccakRoundShared`: `Keccak.round` with `cAt` written out; θ, ρπ and χ each built once per round;
* `executeWithShared`: `executeWith` with Keccak-f of the input cells bound once per instruction. -/

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
@[expose] def executeWithShared (read : K → Option E) (r : Registers K) : LeanIsaInstruction → Option (Registers K)
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
    guard ((∀ c, IsCanonical128 (input c)) ∧
      ∀ c : Fin 13, outCells.cellCount ≤ c.val ∨ output c = cellsOfState s outOdd c)
    pure r.next

theorem executeWith_shared (read : K → Option E) (r : Registers K) (i : LeanIsaInstruction) :
    executeWith read r i = executeWithShared read r i := by
  cases i with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    have h : ∀ (input output : Fin 13 → E), KeccakCellsRelation input inOdd output outOdd outCells =
        ((∀ c, IsCanonical128 (input c)) ∧ ∀ c : Fin 13, outCells.cellCount ≤ c.val ∨
          output c = cellsOfState (keccakF1600 (stateOfCells input inOdd)) outOdd c) := by
      intro input output
      refine propext (and_congr Iff.rfl (forall_congr' fun c ↦ ?_))
      rw [imp_iff_not_or, Nat.not_lt]
    simp only [executeWith, executeWithShared, h]
  | _ => rfl

cost_rewrite executeWith_shared

-- the runner's tables (`runnerTables`), built once per layout
cost_compile runnerTablesC := runnerTables

-- a stack's execution from the tables (`runWithTables`): the per-stack work only. Its compilation
-- takes about 520000 heartbeats (`#count_heartbeats in`), over the default `200000`: the budget is
-- that, doubled.
set_option maxHeartbeats 1000000 in
cost_compile runWithTablesC := runWithTables

end

end LeanVM.Cost.Extractor
