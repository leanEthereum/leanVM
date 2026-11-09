/-
  LeanVM.Facts.IsaWith

  leanISA under any `KECCAK` semantics (`KeccakSem`, `executeWithB`, `runB`, `ValidExecutionB`),
  moved here from `Statement/LeanIsa.lean` (no end statement names them), and under the deployed
  semantics it is leanISA: `executeWithB_deployed`, `stepB_deployed`, `runB_deployed`,
  `validExecutionB_deployed`.
-/

module

public import Statement.LeanIsa
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-!
# Executions under any `KECCAK` semantics

The relation `KECCAK` checks of its cells is a parameter of the machine here
(`KeccakSem`): the deployed one, `keccakDeployed`, is `KeccakCellsRelation`; the reduction-blind one,
`keccakFree`, only asks what the bus enforces of a `KECCAK` row when the proof does not bind the
row to the permutation: the cells read are canonical, and the cells written are canonical with
the limb holding no lane zero. Every definition below is `Statement/LeanIsa.lean`'s with the
check replaced, and is that one at `keccakDeployed` (`executeWithB_deployed`, `runB_deployed`,
`validExecutionB_deployed`). -/

/-- **A semantics of `KECCAK`**: the relation of the cells read in a layout and the cells written
in a layout, of which the instruction writes the first `outCells.cellCount`, decidable. -/
structure KeccakSem where
  /-- The relation. -/
  check : (Fin 13 → E) → Bool → (Fin 13 → E) → Bool → KeccakOutputCells → Prop
  /-- It is decidable. -/
  dec : ∀ input inOdd output outOdd outCells, Decidable (check input inOdd output outOdd outCells)

/-- The deployed semantics: Keccak-f[1600] (`KeccakCellsRelation`). -/
def keccakDeployed : KeccakSem := ⟨KeccakCellsRelation, fun _ _ _ _ _ ↦ inferInstance⟩

/-- The limb of the cells written that holds no lane in the layout `odd` is zero: cell `0`'s
low limb in the odd layout, cell `8`'s high limb in the even one, when the instruction writes
cell `8` (`outCells` is `all`). -/
def FreeLimbZero (output : Fin 13 → E) (odd : Bool) (outCells : KeccakOutputCells) : Prop :=
  if odd then (output 0).limb 0 = 0 else 8 < outCells.cellCount → (output 8).limb 1 = 0

instance {output : Fin 13 → E} {odd : Bool} {outCells : KeccakOutputCells} :
    Decidable (FreeLimbZero output odd outCells) := by
  unfold FreeLimbZero; infer_instance

/-- The cells read and the cells written are canonical, and the limb of the cells written holding
no lane is zero: all `keccakFree` asks. A cell past the first `outCells.cellCount` is not
written, and nothing is asked of it. -/
def CanonicalKeccak (input : Fin 13 → E) (_inOdd : Bool) (output : Fin 13 → E) (outOdd : Bool)
    (outCells : KeccakOutputCells) : Prop :=
  (∀ c, IsCanonical128 (input c)) ∧
    (∀ c : Fin 13, c.val < outCells.cellCount → IsCanonical128 (output c)) ∧
    FreeLimbZero output outOdd outCells

instance {input : Fin 13 → E} {inOdd : Bool} {output : Fin 13 → E} {outOdd : Bool}
    {outCells : KeccakOutputCells} : Decidable (CanonicalKeccak input inOdd output outOdd outCells) := by
  unfold CanonicalKeccak; infer_instance

/-- **The reduction-blind semantics**: any canonical output with its free limb zero. -/
def keccakFree : KeccakSem := ⟨CanonicalKeccak, fun _ _ _ _ _ ↦ inferInstance⟩

/-- `executeWith` under the semantics `S`. -/
def executeWithB (S : KeccakSem) (read : K → Option E) (r : Registers K) : LeanIsaInstruction → Option (Registers K)
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
    let output ← readFirstCells read r.fp (fun c ↦ g ^ c.val * oout) outCells.cellCount
    @guard Option _ (S.check input inOdd output outOdd outCells)
      (S.dec input inOdd output outOdd outCells)
    pure r.next

/-- One step under the semantics `S`. -/
noncomputable def stepB (S : KeccakSem) {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ) (r : Registers K) :
    Option (Registers K) :=
  prog.fetch r.pc >>= executeWithB S L.read r

/-- `n` steps under the semantics `S`, halting in the final state. -/
noncomputable def runB (S : KeccakSem) {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ) :
    ℕ → Registers K → Option (Registers K)
  | 0, r => some r
  | n + 1, r => if r = Registers.final prog then none else stepB S prog L r >>= runB S prog L n

/-- **A valid execution under the semantics `S`.** -/
def ValidExecutionB (S : KeccakSem) (prog : LeanIsaProgram) (input : PublicInput) (t : Execution
    prog) :
    Prop :=
  HoldsPublicInput input t ∧ runB S prog t.memory t.stepCount Registers.initial = some (Registers.final prog)


theorem executeWithB_deployed (read : K → Option E) (r : Registers K) (i : LeanIsaInstruction) :
    executeWithB keccakDeployed read r i = executeWith read r i := by
  cases i <;> rfl

theorem stepB_deployed {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ) (r : Registers K) :
    stepB keccakDeployed prog L r = step prog L r := by
  have : executeWithB keccakDeployed L.read r = executeWith L.read r :=
    funext (executeWithB_deployed L.read r)
  simp only [stepB, step, execute, this]

theorem runB_deployed {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ) :
    ∀ (n : ℕ) (r : Registers K), runB keccakDeployed prog L n r = run prog L n r
  | 0, _ => rfl
  | n + 1, r => by
    have : runB keccakDeployed prog L n = run prog L n := funext (runB_deployed prog L n)
    simp only [runB, run, stepB_deployed, this]

/-- **The deployed semantics gives the deployed valid executions.** -/
theorem validExecutionB_deployed (prog : LeanIsaProgram) (input : PublicInput) (t : Execution
    prog) :
    ValidExecutionB keccakDeployed prog input t ↔ ValidExecution prog input t := by
  simp only [ValidExecutionB, ValidExecution, runB_deployed]

end
end LeanVM.Semantics
