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

The transcript's first forward answers (`fwdIndex`), the lookup through them (`fwdF`), and
Keccak-256 through them (`hashM`, whose closure the extractor's seed and replays use); the
skeletons' replay and the decoders are compiled on demand by the top (`Cost/AS/Top.lean`).
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

end

end LeanVM.Cost.AS
