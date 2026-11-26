module

public import LeanVM.Cost.Machine
public import Statement.LeanVm
public import LeanVM.Parameters.Field
public import CompPoly.Univariate.Basic

/-!
# Values of the cost machine for the extractor's data

`MachineEncoding α` encodes an `α` as a machine value. The encoding the end statement reads (`MachineEncoding`, its
instances for the extractor's input and output, `encodeLeanVmKnowledgeExtractorInput`, `decodeExecution`) is the statement's,
`Statement/CostMachine.lean`; here, the instances only the compiler needs (`UInt8`, `Unit`,
`Char`, `String`, `Ordering`, `Array`, CompPoly's polynomials, `Id`, subtypes) and the
proof that decoding inverts encoding (`decodeExecution_enc`).
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics Common LeanVM.Protocol.Compile

@[expose] public section

/-- A byte: its number. -/
instance : MachineEncoding UInt8 := ⟨fun x ↦ .nat x.toNat⟩
instance : MachineEncoding Unit := ⟨fun _ ↦ .constructor 0 []⟩

/-- A character: its code point. -/
instance : MachineEncoding Char := ⟨fun c ↦ .nat c.toNat⟩

/-- A string: the list of its characters. -/
instance : MachineEncoding String := ⟨fun s ↦ encodeValue s.toList⟩

instance : MachineEncoding Ordering where
  encodeValue | .lt => .constructor 0 [] | .eq => .constructor 1 [] | .gt => .constructor 2 []

instance {α : Type} [MachineEncoding α] : MachineEncoding (Array α) := ⟨fun a ↦ .array (a.map encodeValue)⟩

instance {α : Type} [MachineEncoding α] : MachineEncoding (CompPoly.CPolynomial.Raw α) := inferInstanceAs (MachineEncoding (Array α))

/-- The identity monad: the value. -/
instance {α : Type} [MachineEncoding α] : MachineEncoding (Id α) := inferInstanceAs (MachineEncoding α)

/-- A subtype: its value. -/
instance {α : Type} [MachineEncoding α] {p : α → Prop} : MachineEncoding (Subtype p) := ⟨fun x ↦ encodeValue x.val⟩

instance {α : Type} [Zero α] [MachineEncoding α] : MachineEncoding (CompPoly.CPolynomial α) :=
  inferInstanceAs (MachineEncoding { p : CompPoly.CPolynomial.Raw α // CompPoly.CPolynomial.Raw.IsCanonical p })

theorem decodeE_enc (x : E) : decodeExtensionElement (encodeValue x) = some x := by
  simp only [encodeValue, decodeExtensionElement, Nat.toUInt64_eq, UInt64.ofNat_toNat,
    show ∀ a : K, K.ofLane a.lane = a from fun _ ↦ rfl, ofLimbs_limb]

theorem mapM_decodeE (l : List E) : (l.map encodeValue).mapM decodeExtensionElement = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, decodeE_enc, ih]

/-- **Decoding inverts encoding.** -/
theorem decodeExecution_enc (prog : Semantics.LeanIsaProgram) (t : Execution prog) :
    decodeExecution prog (encodeValue t) = some t := by
  obtain ⟨κ, mem, steps⟩ := t
  have hm : ((Array.ofFn fun i ↦ encodeValue (mem i)).toList.mapM decodeExtensionElement) = some (List.ofFn mem) := by
    have : (List.ofFn fun i ↦ encodeValue (mem i)) = (List.ofFn mem).map encodeValue := by
      rw [List.map_ofFn]; rfl
    rw [Array.toList_ofFn, this, mapM_decodeE]
  show decodeExecution prog (.constructor 0 [.nat κ, .array (Array.ofFn fun i ↦ encodeValue (mem i)), .nat steps]) = _
  simp only [decodeExecution]
  rw [hm]
  simp only [List.length_ofFn, ↓reduceDIte, Option.some.injEq, Execution.mk.injEq, true_and,
    and_true, heq_eq_eq]
  funext i
  simp

end

end LeanVM.Cost
