module

public import LeanVM.Cost.AS.Descent
public import LeanVM.Protocol.Extraction.AS.TopC
import all LeanVM.Protocol.Extraction.AS.Forward
import all LeanVM.Protocol.Extraction.AS.Hash
import all LeanVM.Protocol.EndToEnd.Sound.Skeleton
import all LeanVM.Protocol.EndToEnd.Sound.SkelDecode
import all LeanVM.Protocol.EndToEnd.Sound.SkelWhir
import all LeanVM.Protocol.EndToEnd.Sound.SkelFront
import all LeanVM.Protocol.EndToEnd.Sound.SkelBus
import all LeanVM.Protocol.EndToEnd.Sound.SkelLeaves
import all Statement.Field
import all Statement.Keccak
import all LeanVM.Protocol.RunWithHash
import all Statement.LeanVmVerifier

/-!
# The agreement-set extractor's replay, compiled

The transcript's first forward answers (`fwdIndex`), Keccak-256 through them, the seed, the
skeletons' replay (`skelReplay`) and the decoders of the announced sizes and of the opening's
trace.
-/

namespace LeanVM.Cost.AS

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Extraction.AS LeanVM.Protocol.EndToEnd.Sound LeanVM.Extraction.Fast LeanVM.Protocol.Verifier

public section

cost_enc LeanVM.Protocol.EndToEnd.Sound.Op

cost_compile fwdStepC := fwdStep

cost_compile fwdIndexC := fwdIndex

cost_compile fwdFC := fwdF

/-- Keccak-256 through the index. -/
def hashM (M : SortedMap (List UInt64) KeccakState) (m : Bytes) : Option Digest :=
  KeccakHash.keccak256With (fwdF M) m

/-- The seed through the index. -/
def seedM (M : SortedMap (List UInt64) KeccakState) (bytecode : List K) (pd : Digest) :
    Option KeccakState :=
  seedWithHash (hashM M) (fwdF M) bytecode pd

/-- The skeleton's replay through the index. -/
def replayM (M : SortedMap (List UInt64) KeccakState) (sk : List Op) (s : VerifierProgramState) :
    Option (List EvP × VerifierProgramState) :=
  skelReplayP (fwdF M) sk s

cost_compile hashMC := hashM

/-- The version tag's bytes, `"leanvm-v1"`. -/
theorem versionTag_eq : versionTag = [108, 101, 97, 110, 118, 109, 45, 118, 49] := by
  unfold versionTag
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
  have hc : "leanvm-v1".toList = [Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 110,
      Char.ofNat 118, Char.ofNat 109, Char.ofNat 45, Char.ofNat 118, Char.ofNat 49] := by
    simp
  rw [hc]
  simp [List.utf8Encode, String.utf8EncodeChar]
  have hb : ([108, 101, 97, 110, 118, 109, 45, 118, 49] : List UInt8).toByteArray =
      ⟨#[108, 101, 97, 110, 118, 109, 45, 118, 49]⟩ := by
    cases h : ([108, 101, 97, 110, 118, 109, 45, 118, 49] : List UInt8).toByteArray with
    | mk d => rw [← List.data_toByteArray, h]
  rw [hb]
  decide +kernel

cost_rewrite versionTag_eq

cost_compile seedMC := seedM

cost_compile replayMC := replayM

end

end LeanVM.Cost.AS
