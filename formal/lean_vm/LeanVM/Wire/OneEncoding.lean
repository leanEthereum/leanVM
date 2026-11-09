/-
  LeanVM.Wire.OneEncoding

  Bytes that decode to a proof are that proof's encoding (`oneEncoding`): the encoding is the only
  one, decoding refuses every other byte string.
-/

module

public import LeanVM.Wire.RoundTrip
public import LeanVM.Wire.OneEncodingSib

/-!
# One encoding

`fromBytesWithHash h bytes = some proof → proof.toBytes = bytes`, for every hash `h`. The decoding
reads the bytes (`readProof`) and unprunes each phase; the encoding writes them back:

* the bytes `readProof` accepts are `encodePruned` of what it reads, each phase one `readPhase`
  accepted (`PhaseRead`) (`readProof_eq`, `LeanVM.Wire.ReadDet`);
* re-encoding such a phase unpruned with any hash writes its header and rows
  (`PhaseRead.phaseHeaderAndRows_unprunePhase`, `LeanVM.Wire.OneEncodingRow`) and its carried
  siblings (`PhaseRead.phaseSiblingBytes_unprunePhase`, `LeanVM.Wire.OneEncodingSib`): its bytes
  `encodePhase`.

`oneEncoding_of` composes them, the siblings' step taken as a hypothesis; `oneEncoding`
instantiates it. Nothing in the bytes written depends on the hash: the siblings written are the
ones the phase carries, never a hashed node.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- **One encoding from the siblings' step**: for a phase `readPhase` accepted, the siblings
written for the paths it unprunes to are the ones it carries. -/
theorem oneEncoding_of
    (siblings : ∀ (h : Bytes → Digest) (phase : PrunedPhase), PhaseRead phase →
      phaseSiblingBytes (unprunePhaseWithHash (m := Id) h phase) = encodePhaseSiblings phase) :
    OneEncodingStatement := by
  intro h bytes proof hdecode
  unfold fromBytesWithHash at hdecode
  cases hread : readProof bytes with
  | none => rw [hread] at hdecode; cases hdecode
  | some x =>
    obtain ⟨stream, phases⟩ := x
    rw [hread] at hdecode
    change some (⟨stream, (phases.mapM (unprunePhaseWithHash (m := Id) h)).run⟩ : Proof) =
      some proof at hdecode
    rw [List.idRun_mapM, Option.some.injEq] at hdecode
    subst hdecode
    obtain ⟨hencode, -, -, hread⟩ := readProof_eq hread
    rw [← hencode]
    simp only [Proof.toBytes, encodePruned, List.length_map, List.flatMap_map]
    congr 1
    exact List.flatMap_congr fun phase hphase ↦
      (hread phase hphase).phaseToBytes_unprunePhase h (siblings h phase (hread phase hphase))

/-- **One encoding**: bytes that decode, with any hash, to a proof are that proof's encoding. -/
theorem oneEncoding : OneEncodingStatement :=
  oneEncoding_of fun h _ hr ↦ hr.phaseSiblingBytes_unprunePhase h

/-- **One encoding of the transcribed decoding**, Keccak-256 over a permutation `π` in `Id`:
bytes that decode to a proof are its encoding. -/
theorem toBytes_of_fromBytes (π : KeccakState → Id KeccakState) {bytes : Bytes} {proof : Proof}
    (hdecode : Proof.fromBytes π bytes = some proof) : proof.toBytes = bytes := by
  rw [fromBytes_eq_withHash] at hdecode
  exact oneEncoding _ bytes proof hdecode

end LeanVM.Wire

end
