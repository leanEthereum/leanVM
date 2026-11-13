/-
  LeanVM.Wire.RoundTrip

  The transcribed decoding is the one with a hash of its own (`fromBytes_eq_withHash`), and a proof
  that survives its encoding decodes from it (`roundTrip`).
-/

module

public import LeanVM.Wire.Prune
public import LeanVM.Wire.Unprune

/-!
# The round trip of the wire encoding

`Proof.fromBytes π` hashes with `keccak256With π`, written into its definitions; it is
`fromBytesWithHash (keccak256With π)` (`fromBytes_eq_withHash`), level by level of the climb.

The round trip is the composition of two steps: reading the encoding back gives the stream and each
phase pruned (`readProof proof.toBytes = some (proof.stream, proof.openings.map prunePhase)`,
`LeanVM.Wire.readProof_toBytes`), and unpruning a pruned phase with the hash of its tree gives its
paths back (`unprunePhaseWithHash h (prunePhase paths) = paths`,
`LeanVM.Wire.unprunePhase_prunePhase`). `roundTrip_of` composes them, taken as hypotheses;
`roundTrip` instantiates them.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-! ## The transcribed decoding is the one with a hash -/

section Deployed

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

theorem climbLevel_eq_withHash (nodes carried : List (ℕ × Digest)) :
    climbLevel π nodes carried = climbLevelWithHash (keccak256With π) nodes carried := rfl

theorem climbLevels_eq_withHash (carried : List (List (ℕ × Digest))) (nodes : List (ℕ × Digest)) :
    climbLevels π carried nodes = climbLevelsWithHash (keccak256With π) carried nodes := by
  induction carried generalizing nodes with
  | nil => rfl
  | cons level above ih =>
    simp only [climbLevels, climbLevelsWithHash, climbLevel_eq_withHash, ih]

theorem unprunePhase_eq_withHash (phase : PrunedPhase) :
    unprunePhase π phase = unprunePhaseWithHash (keccak256With π) phase := by
  simp only [unprunePhase, unprunePhaseWithHash, climbLevels_eq_withHash]

/-- **The transcribed decoding is the decoding with Keccak-256 over `π`.** -/
theorem fromBytes_eq_withHash (bytes : Bytes) :
    Proof.fromBytes π bytes = fromBytesWithHash (keccak256With π) bytes := by
  unfold Proof.fromBytes fromBytesWithHash
  cases readProof bytes with
  | none => rfl
  | some x =>
    obtain ⟨stream, phases⟩ := x
    rw [show unprunePhase π = unprunePhaseWithHash (keccak256With π) from
      funext (unprunePhase_eq_withHash π)]

end Deployed

/-! ## The round trip from its two steps -/

/-- Decoding bytes that read back as `(stream, phases)`, with any hash in any monad: each phase
unpruned in order. -/
theorem fromBytesWithHash_of_readProof {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    {bytes : Bytes} {stream : List E} {phases : List PrunedPhase}
    (hread : readProof bytes = some (stream, phases)) :
    fromBytesWithHash H bytes = (do
      let openings ← phases.mapM (unprunePhaseWithHash H)
      pure (some ⟨stream, openings⟩)) := by
  unfold fromBytesWithHash
  rw [hread]

/-- In `Id`, unpruning each phase of a proof pruned by `prunePhase` gives its phases back, where
each phase is one a tree over `h` opens. -/
theorem mapM_unprunePhase_prunePhase (h : Bytes → Digest)
    (unprune_prune : ∀ paths height leafWords, PhaseDecodable h paths height leafWords →
      unprunePhaseWithHash (m := Id) h (prunePhase paths) = paths)
    (phases : List (List Opening))
    (hphases : ∀ phase ∈ phases, ∃ height leafWords, PhaseDecodable h phase height leafWords) :
    ((phases.map prunePhase).mapM (unprunePhaseWithHash (m := Id) h)).run = phases := by
  rw [List.idRun_mapM, List.map_map]
  refine (List.map_congr_left fun phase hmem ↦ ?_).trans (List.map_id phases)
  obtain ⟨height, leafWords, hp⟩ := hphases phase hmem
  exact unprune_prune phase height leafWords hp

/-- **The round trip from its two steps**: the reading of the encoding (`readProof_toBytes`) and
the unpruning of a pruned phase (`unprunePhase_prunePhase`). -/
theorem roundTrip_of
    (read_toBytes : ∀ (h : Bytes → Digest) (proof : Proof), WireDecodable h proof →
      readProof proof.toBytes = some (proof.stream, proof.openings.map prunePhase))
    (unprune_prune : ∀ (h : Bytes → Digest) paths height leafWords,
      PhaseDecodable h paths height leafWords →
        unprunePhaseWithHash (m := Id) h (prunePhase paths) = paths) :
    RoundTripStatement := by
  intro h proof hw
  rw [fromBytesWithHash_of_readProof _ (read_toBytes h proof hw)]
  have hmap := mapM_unprunePhase_prunePhase h (unprune_prune h) proof.openings hw.phases
  revert hmap
  generalize (proof.openings.map prunePhase).mapM (unprunePhaseWithHash (m := Id) h) = x
  intro hmap
  change some (⟨proof.stream, x.run⟩ : Proof) = some proof
  rw [hmap]

/-- **The round trip**: a proof that survives its encoding with the hash `h` decodes from it with
`h`: the encoding reads back as the proof's phases pruned (`readProof_toBytes`,
`LeanVM.Wire.Prune`), each of which unprunes back to its paths (`unprunePhase_prunePhase`,
`LeanVM.Wire.Unprune`). -/
theorem roundTrip : RoundTripStatement :=
  roundTrip_of (fun _ _ hw ↦ readProof_toBytes hw) fun _ _ _ _ hp ↦ unprunePhase_prunePhase hp

/-! ## The round trip in the deployed forms -/

end LeanVM.Wire

end
