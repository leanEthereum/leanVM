module

public import Statement.CostMachine
public import Statement.LeanVm

/-!
# The extractor a program computes

The cost machine's encodings of leanVM's objects (the fields, the public input, the permutation
queries, instructions and programs, proofs and executions), and the extractor a program of the
machine computes, its size bound and its budget.

**The extractor a program computes** (`LeanVM.extractorComputedBy P`, at the end): `P` run on the
encoded statement, transcript and proof within its size bound and budget, its output parsed as an
execution (`decodeExecution`, a linear parse). `Statement.Theorems` takes `P` as a parameter. What
excludes a vacuous statement: `P` is a program (no classical choice), its size bound leaves no room
for a useful table of witnesses beside the compiled extractor, its only runtime data is its input,
and its budget is a closed formula, polylogarithmic per query. The guest decoder is a program of the
same machine (`GuestKnowledgeSoundness`, `LeanVmGuest.lean`).
-/

namespace LeanVM.Cost

@[expose] public section

open LeanVM.Parameters LeanVM.Semantics Common LeanVM.Protocol.Compile

instance : MachineEncoding K := ⟨fun a ↦ .nat a.lane.toNat⟩
instance : MachineEncoding E :=
  ⟨fun x ↦ .constructor 0 [encodeValue (x.limb 0), encodeValue (x.limb 1)]⟩

instance {S : Type} [MachineEncoding S] : MachineEncoding (PermutationQuery S) where
  encodeValue
    | .forward x => .constructor 0 [encodeValue x]
    | .inverse y => .constructor 1 [encodeValue y]

instance : MachineEncoding PublicInput := ⟨fun p ↦ .constructor 0 [encodeFiniteFunction p.lanes]⟩

instance : MachineEncoding DerefMode where
  encodeValue | .cell => .constructor 0 [] | .pc => .constructor 1 [] | .fp => .constructor 2 []

instance : MachineEncoding KeccakOutputCells where
  encodeValue | .one => .constructor 0 [] | .two => .constructor 1 [] | .all => .constructor 2 []

instance : MachineEncoding LeanIsaInstruction where
  encodeValue
    | .xor a b c => .constructor 0 [encodeValue a, encodeValue b, encodeValue c]
    | .mulNative a b c => .constructor 1 [encodeValue a, encodeValue b, encodeValue c]
    | .setConstant o k => .constructor 2 [encodeValue o, encodeValue k]
    | .deref a b c m => .constructor 3 [encodeValue a, encodeValue b, encodeValue c, encodeValue m]
    | .jump c d f => .constructor 4 [encodeValue c, encodeValue d, encodeValue f]
    | .keccak om t b c o i j n =>
      .constructor 5 [encodeFiniteFunction om, encodeValue t, encodeValue b, encodeValue c,
        encodeValue o, encodeValue i, encodeValue j, encodeValue n]

instance : MachineEncoding Semantics.LeanIsaProgram :=
  ⟨fun p ↦ .constructor 0 [encodeValue p.logSize, encodeFiniteFunction p.instructions]⟩

instance : MachineEncoding Opening := ⟨fun o ↦ .constructor 0 [encodeValue o.leafIndex,
    encodeValue o.leaf, encodeValue o.path]⟩

instance : MachineEncoding Proof :=
  ⟨fun π ↦ .constructor 0 [encodeValue π.stream, encodeValue π.openings]⟩

instance {program : Semantics.LeanIsaProgram} : MachineEncoding (Execution program) :=
  ⟨fun execution ↦ .constructor 0 [encodeValue execution.logMemorySize,
    encodeFiniteFunction execution.memory, encodeValue execution.stepCount]⟩

/-- **The extractor's input**: the program, the public input, the transcript's permutation
queries, the proof. -/
def encodeLeanVmKnowledgeExtractorInput (program : Semantics.LeanIsaProgram) (input : PublicInput)
    (transcript : OracleQueryLog) (proof : Proof) : MachineValue :=
  .constructor 0 [encodeValue program, encodeValue input,
    encodeValue (permutationQueries transcript), encodeValue proof]

/-- A word of `E` from its encoding (each limb modulo `2^64`). -/
def decodeExtensionElement : MachineValue → Option E
  | .constructor 0 [.nat a, .nat b] => some (E.ofLimbs (K.ofLane a.toUInt64) (K.ofLane b.toUInt64))
  | _ => none

/-- **An execution from its encoding**: the memory's log-size `κ`, its `2^κ` words, the steps;
`none` on anything else. -/
def decodeExecution (program : Semantics.LeanIsaProgram) : MachineValue → Option (Execution program)
  | .constructor 0 [.nat κ, .array mem, .nat steps] =>
    match (mem.toList.mapM decodeExtensionElement) with
    | some words =>
      if h : words.length = 2 ^ κ then
        some ⟨κ, fun i ↦ words[i.val]'(by rw [h]; exact i.isLt), steps⟩
      else none
    | none => none
  | _ => none

/-! ## The extractor's budget -/

/-- **The extractor's budget**, for a proof announcing a stack of `2^μ` elements
(`stackLog = μ`) and a transcript of `N = permutationQueryCount` permutation queries: the most the
extractor's run may cost, in the machine's price (the sum of its steps' prices, each at least `1`,
so also the most steps it may execute), `2^max(58, 2μ + 9) + (N + 2^30)·(D + 2)²·(2^15 + 2D)`,
with `D = log₂(N + 2) + 1` the levels of the extractor's sorted tables of the transcript.
`lean_vm` proves the compiled extractor's price at most this wherever it extracts, at every shape
the replay admits (stack log-size `16` to `30`, rate exponent `1` to `4`, memory and program
log-sizes at most `30`): the first term bounds the descent from the final polynomial to level 0's
stack (each fold round's lanes decoded with at most one error on the columns of their agreement
set, level 0's descent dominating), level 0's stack, the candidate run and every other price
independent of the transcript; the second bounds, per query, the transcript's two indexes (its first
forward answers, and one preimage index every committed root shares) and, per committed leaf
or hashed block (`2^30` at most), their lookups. It passes `2^128` at about `N = 2^99.7`, where the
soundness bound is still about `2^-25` (`statement.tex`, *What is not proved*, says what the regime
leaves out). A proof announcing no layout is given the budget of `μ = 0`. -/
def leanVmKnowledgeExtractorBudget (stackLog permutationQueryCount : ℕ) : ℕ :=
  2 ^ max 58 (2 * stackLog + 9) +
    (permutationQueryCount + 2 ^ 30) * (Nat.log2 (permutationQueryCount + 2) + 3) ^ 2 *
      (2 ^ 15 + 2 * (Nat.log2 (permutationQueryCount + 2) + 1))

/-- The stack log-size a proof of `program` announces (`Verifier.announcedLayoutAndRate`), `0` if
it announces none. -/
def announcedStackLog (program : Semantics.LeanIsaProgram) (proof : Protocol.Compile.Proof) : ℕ :=
  ((Protocol.Verifier.announcedLayoutAndRate (bytecodeWords program) proof.stream).map
    (·.1.stackLog)).getD 0

end

end LeanVM.Cost

/-! ## The extractor a program computes -/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Common

@[expose] public section

/-- **The bound on the extractor program's size** (`MachineProgram.size`): `25380`, the compiled
extractor's size (`25260`: its `514` compiled bodies and the entry, at `545` indices, `30` of
them holes, a literal `0` each) and a slack of `120`, less than one leanXMSS signature's encoding
(`309`: two layers of `153`, each a randomizer, `58` chain values and a path of `16`, digests of
two limbs), so the compiled extractor could carry no useful table of witnesses beside its code. -/
def leanVmKnowledgeExtractorSizeBound : ℕ := 25380

/-- **The extractor a program computes**: the program, of size at most
`leanVmKnowledgeExtractorSizeBound`, run on the encoded statement, transcript and proof
(`encodeLeanVmKnowledgeExtractorInput`) within the budget at the transcript's number of permutation
queries and the stack size the proof announces (`leanVmKnowledgeExtractorBudget`,
`announcedStackLog`), its output parsed as an execution (`decodeExecution`);
`none` if the program is larger, or the run fails, exceeds its budget, or outputs no execution's
encoding. A larger program extracts nothing, so
`KnowledgeSoundness (extractorComputedBy knowledgeExtractorProgram)` fails for it: an adversary
running the honest prover is accepted. -/
def extractorComputedBy (knowledgeExtractorProgram : Cost.MachineProgram) : StraightLineExtractor :=
  fun program input transcript proof ↦
    (Cost.outputWithin knowledgeExtractorProgram leanVmKnowledgeExtractorSizeBound
        (Cost.leanVmKnowledgeExtractorBudget (Cost.announcedStackLog program proof)
          (permutationQueries transcript).length)
        (Cost.encodeLeanVmKnowledgeExtractorInput program input transcript proof)).bind
          (Cost.decodeExecution program)

end

end LeanVM
