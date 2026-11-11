module

public import LeanVM.Cost.Bounds.Runner
public import LeanVM.Cost.DecoderProgram

/-!
# Bound: the decoder top's two ends and its entry, compiled

The prices of `Cost/Decoder/Ends.lean`'s functions and of the decoder's output
(`Cost/DecoderProgram.lean`):

* **`decoderTables_cost`**: the two address tables (`decoderTablesC`, the extractor's `powTable`
  twice), at most `(74κ + 121)·2^κ + (74ℓ + 121)·2^ℓ + 42`;
* **`memReader_cost`**: one memory read (`memReaderC`, the binary search in the table and the
  vector's entry), at most `111 + 36·log₂|memT|`; on the table `powTable κ`, `κ ≤ 30`, at most
  `111 + 36κ ≤ 1191` (`memReader_cost_deployed`), the price `R` of the reader closure the readers
  and the precondition's test take;
* `decodedOf_cost`: `7`;
* **`decoderOutput_cost`**: the seed (`decSeedC`, at most `A`) and the statement (`decStmtC`, the
  logarithm's tables given, at most `S`, the bounds of the chain `Log … Witness`), then
  `decodedOf`: at most `A + S + 15`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

/-! ## The input side -/

open Auto.LeanVM.Extraction.Fast in
/-- **The address tables** (`decoderTablesC`): the memory's `2^κ` addresses and the bytecode's
`2^ℓ`, each sorted. -/
theorem decoderTables_cost (hP : Includes P decoderTablesC.costDeps) (prog : LeanIsaProgram) (κ : ℕ)
    (hκ : κ ≤ 62) :
    machineCost P decoderTablesC.costIdx [encodeValue prog, encodeValue κ] ≤
      (74 * κ + 121) * 2 ^ κ + (74 * prog.logSize + 121) * 2 ^ prog.logSize + 42 := by
  have hls : prog.logSize ≤ 30 := prog.logSize_le
  rw [decoderTablesC.costEq P hP]
  have h1 := powTable_cost P (by includes) κ hκ
  have h2 := powTable_cost P (by includes) prog.logSize (by omega)
  omega

open Auto.LeanVM.Extraction.Fast in
/-- **One memory read** (`memReaderC`): the binary search in the address table and the vector's
entry, at most `111 + 36·log₂|memT|`. -/
theorem memReader_cost (hP : Includes P memReaderC.costDeps) (memT : Array (ℕ × ℕ))
    (ht : WordTable memT) {κ : ℕ} (hκ : κ < 64) (mem : Vector E (2 ^ κ)) (a : K) :
    machineCost P memReaderC.costIdx [encodeValue memT, encodeValue κ, encodeValue mem,
      encodeValue a] ≤ 111 + 36 * Nat.log2 memT.size := by
  rw [memReaderC.costEq P hP]
  have := gLogTable_cost P (by includes) memT ht κ hκ a
  have := optionMap_cost P (by includes) _
    (.closure stepVec.c258.lam0.lam0.lam0.costIdx [encodeValue κ, encodeValue mem])
    (fun i ↦ RunsApp.of_spec (stepVec.c258.lam0.lam0.lam0.costSpec P (by includes) mem i)) 12
    (gLogTable memT κ a) (fun i _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [stepVec.c258.lam0.lam0.lam0.costEq P (by includes), limbs_shift hκ,
        limbs_of_lt (by omega : κ < 2 ^ 64), Auto.Vector.get.c316.costEq P (by includes), max_self])
  omega

/-- **One memory read at the deployed shape** (the table `powTable κ`, `κ ≤ 30`): at most
`111 + 36κ ≤ 1191`. -/
theorem memReader_cost_deployed (hP : Includes P memReaderC.costDeps) {κ : ℕ} (hκ : κ ≤ 30)
    (mem : Vector E (2 ^ κ)) (a : K) :
    machineCost P memReaderC.costIdx [encodeValue (powTable κ), encodeValue κ, encodeValue mem,
      encodeValue a] ≤ 111 + 36 * κ := by
  have := memReader_cost P hP (powTable κ) (wordTable_powTable (by omega)) (by omega) mem a
  rwa [powTable_size, Nat.log2_two_pow] at this

/-! ## The output side -/

/-- A decoding of its fields (`decodedOfC`): `7`. -/
theorem decodedOf_cost (hP : Includes P decodedOfC.costDeps) (s : LeanVM.Protocol.Digest)
    (st : LeanVM.Node.NodeStatement) (w : LeanVM.Node.NodeWitness) :
    machineCost P decodedOfC.costIdx [encodeValue s, encodeValue st, encodeValue w] = 7 := by
  rw [decodedOfC.costEq P hP]

/-- **The decoding** (`decoderOutputC`): the seed (at most `A`), the statement (at most `S`) and
`15`. -/
theorem decoderOutput_cost (hP : Includes P decoderOutputC.costDeps) (D : DiscreteLogTables)
    (σ : LeanVM.Guest.Core.Val)
    (σVal : MachineValue) (hσ : ∀ a, RunsApp P σVal [encodeValue a] (encodeValue (σ a)))
    (rd : LeanVM.Guest.Core.Reader) (rdVal : MachineValue)
    (hrd : ∀ a, RunsApp P rdVal [encodeValue a] (encodeValue (rd a))) (w : LeanVM.Node.NodeWitness)
    (A S : ℕ) (hA : machineCost P decSeedC.costIdx [σVal] ≤ A)
    (hS : machineCost P decStmtC.costIdx [encodeValue D, σVal, rdVal] ≤ S) :
    machineCost P decoderOutputC.costIdx [encodeValue D, σVal, rdVal, encodeValue w] ≤ A + S + 15 := by
  rw [decoderOutputC.costEq P hP D σ σVal hσ rd rdVal hrd, decodedOf_cost P (by includes)]
  omega

/-! ## The entry -/

end

end LeanVM.Cost.Bounds
