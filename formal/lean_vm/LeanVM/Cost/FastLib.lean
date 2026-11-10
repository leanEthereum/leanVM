module

public import LeanVM.Cost.CompPolyLib
public import LeanVM.Cost.InitLib
public import LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.SortedMap
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.Replay
public import LeanVM.Guest.Core

/-!
# The fast extractor's data, for the compiler

The encodings of the fast extractor's types (constructors of their data fields), and the measures
its well-founded recursions decrease, registered for the compiler (`cost_measure`).
-/

namespace LeanVM.Cost.FastLib

open LeanVM.Cost LeanVM.Extraction.Fast LeanVM.Parameters

@[expose] public section

instance : MachineEncoding Hits where
  encodeValue | .none => .constructor 0 [] | .one x => .constructor 1 [encodeValue x] | .many => .constructor 2 []

instance {α β : Type} [Ord α] [MachineEncoding α] [MachineEncoding β] : MachineEncoding (Level α β) :=
  ⟨fun l ↦ .constructor 0 [encodeValue l.weight, encodeValue l.entries]⟩

instance {α β : Type} [Ord α] [MachineEncoding α] [MachineEncoding β] : MachineEncoding (SortedMap α β) :=
  ⟨fun m ↦ .constructor 0 [encodeValue m.levels]⟩

instance : MachineEncoding ReplayFast := ⟨fun τ ↦ .constructor 0 [encodeValue τ.fwd, encodeValue τ.inv, encodeValue τ.caps, encodeValue τ.paths]⟩

instance {R : Type} [Zero R] [MachineEncoding R] : MachineEncoding (CompPoly.CBivariate R) :=
  inferInstanceAs (MachineEncoding (CompPoly.CPolynomial (CompPoly.CPolynomial R)))

cost_enc CompPoly.GuruswamiSudan.GSInterpParams
cost_enc CompPoly.GuruswamiSudan.GSExecParams
cost_enc CompPoly.GuruswamiSudan.GSReceivedWord
cost_enc CompPoly.PolynomialMatrix.RowChoice
cost_enc CompPoly.GuruswamiSudan.LeeOSullivan.RowChoice
cost_enc CompPoly.CBivariate.Monomial
cost_enc LeanVM.Protocol.Compile.Sponge
cost_enc LeanVM.Protocol.Compile.VerifierProgramState
cost_enc LeanVM.Protocol.Verifier.Placement
cost_enc LeanVM.Protocol.Verifier.Form
cost_enc LeanVM.Protocol.Verifier.BusBlock
cost_enc LeanVM.Protocol.Verifier.Layout
cost_enc LeanVM.Parameters.Whir.Level
cost_enc LeanVM.Semantics.Registers
cost_enc LeanVM.Parameters.Opcode
-- the guest's value names, for the guest decoder's readers (a `Seg.i` names its callee by a string)
cost_enc LeanVM.Guest.Core.Seg
cost_enc LeanVM.Guest.Core.V

/-- Equality of registers: of both fields. -/
theorem decideEqRegisters {F : Type} [DecidableEq F] (x y : LeanVM.Semantics.Registers F)
    {inst : Decidable (x = y)} : @decide (x = y) inst = (decide (x.pc = y.pc) && decide (x.fp = y.fp)) := by
  obtain ⟨_, _⟩ := x; obtain ⟨_, _⟩ := y; simp

cost_rewrite decideEqRegisters

/-- Membership in `K`: the upper limb zero. -/
theorem decideIsInK (x : E) {inst : Decidable (IsInK x)} :
    @decide (IsInK x) inst = decide (x.limb 1 = 0) :=
  decide_eq_decide.2 Iff.rfl

cost_rewrite decideIsInK

open LeanVM.Semantics in
/-- The Keccak relation: each cell past those written, or the permuted state's. -/
theorem decideKeccakCells (input : Fin 13 → E) (inOdd : Bool) (output : Fin 13 → E) (outOdd : Bool)
    (outCells : KeccakOutputCells)
    {inst : Decidable (KeccakCellsRelation input inOdd output outOdd outCells)} :
    @decide (KeccakCellsRelation input inOdd output outOdd outCells) inst =
      decide (∀ c : Fin 13, outCells.cellCount ≤ c.val ∨
          output c = cellsOfState (keccakF1600 (stateOfCells input inOdd)) outOdd c) :=
  decide_eq_decide.2 (forall_congr' fun _ ↦ by rw [imp_iff_not_or, Nat.not_lt])

cost_rewrite decideKeccakCells

open LeanVM.Semantics LeanVM.Arithmetization in
/-- `KECCAK`'s output flags by cases on the cells written (the derived equality of
`KeccakOutputCells` has no machine encoding). -/
theorem keccakOutputFlagsCases (outCells : KeccakOutputCells) :
    keccakOutputFlags outCells = match outCells with
      | .one => (layoutFlagWord false, layoutFlagWord false)
      | .two => (layoutFlagWord true, layoutFlagWord false)
      | .all => (layoutFlagWord true, layoutFlagWord true) := by
  cases outCells <;> rfl

cost_rewrite keccakOutputFlagsCases

/-- `kToNat`: the word's number. -/
theorem kToNatLane (a : K) : LeanVM.Protocol.Verifier.kToNat a = (K.lane a).toNat := rfl

cost_rewrite kToNatLane

/-- The number of tables (their descriptors hold functions: not data). -/
theorem tablesLength : LeanVM.Protocol.Verifier.tables.length = 6 := rfl

cost_rewrite tablesLength

/-! The constants the layout derives from the tables' descriptors (which hold functions), as
literals. -/

open LeanVM.Protocol.Verifier in
theorem tableWidthsLit : tableWidths = [13, 13, 7, 14, 14, 92] := rfl

cost_rewrite tableWidthsLit

open LeanVM.Protocol.Verifier in
theorem globalColumnBasesLit : globalColumnBases = [5, 18, 31, 38, 52, 66] := rfl

cost_rewrite globalColumnBasesLit

open LeanVM.Protocol.Verifier in
theorem keccakOutputColumnsLit : keccakOutputColumns = (List.range 25).map (106 + ·) := rfl

cost_rewrite keccakOutputColumnsLit

open LeanVM.Protocol.Verifier in
theorem columnKappasLit (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) :
    columnKappas logMemory logBytecode tableLogHeights =
      [logMemory, logMemory, logMemory, logBytecode,
          tableLogHeights.getD opKeccak 0 + qkeccakSlotBits] ++
        [(13, 0), (13, 1), (7, 2), (14, 3), (14, 4), (92, 5)].flatMap fun p ↦
          List.replicate p.1 (tableLogHeights.getD p.2 0) := rfl

cost_rewrite columnKappasLit

open LeanVM.Protocol.Verifier in
theorem keccakSlotOfLit (l : ℕ) : keccakSlotOf l =
    if 15 ≤ l ∧ l < 15 + 25 then some (l - 15)
    else ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13].idxOf? l).map (50 + ·) := rfl

cost_rewrite keccakSlotOfLit

open LeanVM.Semantics in
/-- The opcodes' bus codes `g^0, …, g^5` as words. -/
theorem opcodeCodeLit (o : Opcode) : Opcode.busCode o = K.ofLane (match o with
    | .xor => 1 | .mulNative => 2 | .setConstant => 4 | .deref => 8 | .jump => 16
    | .keccak => 32) := by
  cases o <;> decide +kernel

cost_rewrite opcodeCodeLit

cost_measure searchIn := fun _ _ _ _ _ lo hi ↦ hi - lo

cost_measure mergeNewer := fun _ _ _ a b ↦ a.length + b.length

cost_measure findLane := fun _ _ lo hi ↦ hi - lo

end

end LeanVM.Cost.FastLib
