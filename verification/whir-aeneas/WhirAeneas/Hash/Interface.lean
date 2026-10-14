import Aeneas
import LeanVMCircuits.Blake2s.Spec

namespace WhirAeneas.Hash
open Aeneas Aeneas.Std

abbrev Rfc := LeanVMCircuits.Blake2s.Rfc7693.F
abbrev Word := BitVec 32
abbrev State := Aeneas.Std.Array U32 8#usize
abbrev Message := Aeneas.Std.Array U32 16#usize
abbrev Compression := State → Message → U64 → Bool → Result State

def encodeState (words : Vector Word 8) : State :=
  .from (words.toList.map (fun word => (⟨word⟩ : U32))) (by simp)

def encodeMessage (words : Vector Word 16) : Message :=
  .from (words.toList.map (fun word => (⟨word⟩ : U32))) (by simp)

/-- The compression boundary is exactly the existing RFC 7693 specification, with the generated mutable state returned on success. This requires total successful compression at every state, block, counter and flag, not merely agreement on tested transcripts. Allocator and ABI frame behavior remain outside this value-level relation. -/
def SatisfiesRfc7693 (compress : Compression) : Prop :=
  ∀ (h : Vector Word 8) (m : Vector Word 16) (t : BitVec 64) (last : Bool),
    compress (encodeState h) (encodeMessage m) ⟨t⟩ last =
      .ok (encodeState (Rfc h m t last))

end WhirAeneas.Hash
