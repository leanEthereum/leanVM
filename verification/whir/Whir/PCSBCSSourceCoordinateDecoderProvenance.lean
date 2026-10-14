import Whir.PCSBCSSourceCoordinateDecoderSource
import Whir.PublicCompressionCouplingTerminalSupport

/-! Decoding actual private raw queries preserves their existing public-terminal
or inspected-construction provenance. Non-source supermode keys may be rejected;
no reconstruction oracle or byte/frame equivalence premise is introduced. -/
namespace Whir.PCSBCSSourceCoordinateDecoder
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingRecognition PublicCompressionCouplingMixed RawOracleCoupling
open TypedOracleCompiler (Sampling)

-- Use the public simulator's executable dictionary at its memo endpoint.
local instance : DecidableEq Node := DuplexPublicSimulator.instDecidableEqNode

/-- Actual public recovery has both a literal coordinate and public compression
input/output provenance, not merely a coordinate supplied by a caller. -/
theorem recover_public_provenance {Q : Nat} {iv : Digest32} {log : PublicLog}
    {input : Node} {q : Coordinate} (recovered : recover Q iv log input = some q) :
    ∃ rest, Complete (input::rest) ∧ PublicBody log input.cv rest ∧
      extract (input::rest) = some (modeKey iv q) ∧ DuplexEncoding.Admissible q := by
  obtain ⟨key,ns,found,recognized,complete,extracted,valid,_⟩ := recover_sound recovered
  obtain ⟨rest,rfl,body⟩ := recognized_publicBody recognized
  exact ⟨rest,complete,body,extracted,valid⟩

/-- In the real causal compiler, successful decoding either retains an actual
public terminal witness or identifies the literal inspected construction. -/
theorem causalCompile_decoded_origin {R : Type} (Q : Nat) (seedTable : Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (log : PublicLog) (p : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p)
    (auth : NonterminalAuthentic seedTable log) {key : RawKey Q} {answer : Digest32}
    {q : Coordinate} (decoded : decode iv key = some q)
    (member : (⟨.inr key,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute (oracle seedTable ro) (causalCompile Q iv log p remaining cap counted)).2) :
    (∃ input rest, Complete (input::rest) ∧ Tree (compressionOf seedTable) input.cv rest ∧
      extract (input::rest) = some (modeKey iv q) ∧
      PublicBody (finalLog log (Sampling.eval (oracle seedTable ro)
        (compile Q iv log p remaining cap counted)).observations) input.cv rest) ∨
    (∃ construction ∈ (Sampling.eval (oracle seedTable ro)
      (causalCompile Q iv log p remaining cap counted)).2, construction.coordinate = q) := by
  have same := (decode_iff iv key q).mp decoded |>.2
  rcases causalCompile_raw_origin Q seedTable ro iv log p remaining cap counted auth member with
    publicOrigin | construction
  · obtain ⟨input,rest,complete,tree,extracted,body⟩ := publicOrigin
    exact Or.inl ⟨input,rest,complete,tree,by simpa only [same] using extracted,body⟩
  · obtain ⟨construction,inspected,bound,equal⟩ := construction
    have leftInverse := decode_constructionKey Q iv construction.coordinate construction.valid bound
    rw [← equal, decoded] at leftInverse
    exact Or.inr ⟨construction,inspected,Option.some.inj leftInverse.symm⟩

open Classical in
/-- The actual hidden-guess-complement support theorem, now with an executable
coordinate inverse. The source boundary is successful canonical decoding (or
`decode_of_sourceShape`), not a universal claim about arbitrary raw keys. -/
theorem actual_decoded_terminal_support {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (quiet : hiddenGuess Q iv p counted (oracle seedTable ro)=false)
    {key : RawKey Q} {answer : Digest32} {q : Coordinate}
    (decoded : decode iv key = some q)
    (stored : (Sampling.eval (oracle seedTable ro)
      (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2 (.inr key)=some answer) :
    ∃ input rest, Complete (input::rest) ∧ Tree (compressionOf seedTable) input.cv rest ∧
      extract (input::rest) = some (modeKey iv q) ∧
      (∀ n ∈ rest, (Sampling.eval (oracle seedTable ro)
        (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2
          (.inl n)=some (seedTable n)) ∧
      (input.cv ∈ publicCVTargets (Sampling.eval (oracle seedTable ro)
        (compile Q iv [] p Q (by rfl) counted)).observations →
        PublicBody (finalLog [] (Sampling.eval (oracle seedTable ro)
          (compile Q iv [] p Q (by rfl) counted)).observations) input.cv rest) := by
  obtain ⟨input,rest,complete,tree,extracted,cached,publicBody⟩ :=
    actual_terminal_support Q iv p counted seedTable ro quiet stored
  have same := (decode_iff iv key q).mp decoded |>.2
  exact ⟨input,rest,complete,tree,by simpa only [same] using extracted,cached,publicBody⟩

#print axioms recover_public_provenance
#print axioms causalCompile_decoded_origin
#print axioms actual_decoded_terminal_support
end Whir.PCSBCSSourceCoordinateDecoder
