module

public import LeanVM.Cost.CompPolyLib
public import LeanVM.Cost.InitLib
public import LeanVM.Protocol.Extraction.Fast.Transcript
public import LeanVM.Protocol.EndToEnd.Sound.SkelDefs
import all LeanVM.Protocol.Extraction.Fast.SortedMap
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.Replay

/-!
# The extractor's data, for the compiler

The encodings of the extractor's types (constructors of their data fields), and the measures its
well-founded recursions decrease, registered for the compiler (`cost_measure`).
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

/-- A column's values: the vector of its `2^n` entries. -/
instance {n : ℕ} : MachineEncoding (CompPoly.CMlPolynomialEval K n) :=
  inferInstanceAs (MachineEncoding (Vector K (2 ^ n)))

cost_enc LeanVM.Protocol.Compile.Sponge
cost_enc LeanVM.Protocol.Compile.VerifierProgramState
cost_enc LeanVM.Protocol.Verifier.Placement
cost_enc LeanVM.Parameters.Whir.Level
cost_enc LeanVM.Protocol.Verifier.Chunks
cost_enc LeanVM.Protocol.Column
cost_enc LeanVM.Protocol.EndToEnd.Sound.LayoutLite
cost_enc LeanVM.Protocol.EndToEnd.Sound.Op

/-- `kToNat`: the word's number. -/
theorem kToNatLane (a : K) : LeanVM.Protocol.Verifier.kToNat a = (K.lane a).toNat := rfl

cost_rewrite kToNatLane

cost_measure searchIn := fun _ _ _ _ _ lo hi ↦ hi - lo

cost_measure mergeNewer := fun _ _ _ a b ↦ a.length + b.length

end

end LeanVM.Cost.FastLib
