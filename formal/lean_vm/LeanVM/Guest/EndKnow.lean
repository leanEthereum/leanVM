/-
  LeanVM.Guest.EndKnow

  The aggregation guest's soundness, its witness named: the decoder that reads a statement and
  its witness off a valid execution's memory, and `MemoryGuestKnowledge` (`GuestKnowledgeSoundness`
  of `Statement/LeanVmGuest.lean`, for a decoder of memories) for the deployed bytecode, from B2 and B1's statements
  (`MemoryAggregateSound`, in the random-permutation model, is composed in `LeanVM/Guest/EndRpm.lean`).
-/

module

public import LeanVM.Guest.EndLoc
public import LeanVM.Guest.Located.Interface
public import LeanVM.Guest.B1.Main.SoundV
public import LeanVM.Guest.Binding
public import LeanVM.Protocol.LeanVMSound

/-!
# The guest's witness, named

The decoder `decodeWith W` reads, off a memory `L`:

* the seed and the statement from `main`'s frame (`fp = 1`, the words of `main`'s certificate's
  cells `σ = Check.valG L 1 (certOf 1)`: `B1.Main.decSeed σ`, `B1.Main.decStmt σ L.read`);
* the witness `W σ L.read (Located.frameV L)`: `main`'s witness as a function of its valuation, the
  memory and the frame map of the memory, which gives each call the valuation of its frame, the
  first frame of the memory at which the callee's code holds on the call's words
  (`Located.frameOf`). With B1-f's `decWitV σ rd V piOf` for `W`, each signature, matrix, child
  proof and the batching's hints is read off the frames of the functions that checked them.

`SoundHyps W` gathers what the theorems rest on: B2 (`B2SoundL`, proved from the certificates
and B1's statements about the core IR in `EndSound.lean`) and `main`'s soundness with the
witness `W` over any
call relation that unfolds along a frame map (`Located.MainSoundV`).

* `guest_knowledge_of`: every valid execution of the guest on a public input decodes to a
  statement of that input's digest under the decoded seed, and a witness holding it (`NodeRelation`).
  B2 gives `main`'s body at its frame with every call located (`mainBodyL_of`); the located
  relation unfolds along the memory's frame map (`Located.unfoldsV_RL`), so B1 applies to it.
* `decode_binds_of`: a consumer whose own statement `s₀` (its deferred claim of the bytecode's
  shape) has, under the
  seed `iv`, the public input's digest learns that the decoded seed and statement are `iv` and
  `s₀`, or holds an explicit Keccak-256 collision (`collisionCandidates`).
* `aggregate_knowledge_of`, `aggregate_sound_outer_of : MemoryAggregateSound guest (decodeWith W)`:
  composed with knowledge soundness in the random-permutation model, in `LeanVM/Guest/EndRpm.lean`.

**With B1's witnesses** (`decodeV piOf`): `W σ rd V = B1.Main.decWitV σ rd V piOf`, `main`'s
witness with each callee's read off the frame map (B1-f), the child proof by `piOf` (B1-d). Then
`main`'s soundness is B1-f's `main_sound_V_of_sub`, from `verify_sub`'s statement with its proof
named (`B1.Main.SubSoundW bytecode piOf`), and the theorems rest on `B2SoundL` and
`SubSoundW bytecode piOf` alone (`soundHyps_of_sub`, `guest_knowledge_V`, `decode_binds_V`; and
`aggregate_sound_outer_V` in `EndRpm.lean`).
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **A decoder of memories**: from a memory, a seed, a statement and a witness. The statement's
decoder is a cost-machine program (`GuestKnowledgeSoundness`, `Statement/LeanVmGuest.lean`); this is
the proofs' form, which `LeanVM/Guest/DecoderProgram.lean` relates to it. -/
abbrev MemoryDecoder : Type := ∀ {κ : ℕ}, MemoryImage κ → SeedStatementAndWitness

/-- **Knowledge soundness of the guest program, for a decoder of memories**: from the memory of
every valid execution of `guest` on a public input, `decode` reads a seed, the node statement the
input commits to under that seed, and a witness proving it (`ExplainsPublicInput`). -/
def MemoryGuestKnowledge (guest : LeanIsaProgram) (decode : MemoryDecoder) : Prop :=
  ∀ input (t : Execution guest), ValidExecution guest input t →
    ExplainsPublicInput guest input (decode t.memory)

end

end LeanVM.Node

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Guest.Binding
open scoped ENNReal

@[expose] public section

/-- **The guest's decoder, for `main`'s witness function `W`**: the seed and the statement
`main`'s frame holds, and the witness `W` reads off `main`'s valuation, the memory and the
memory's frame map. -/
noncomputable def decodeWith (W : Val → Reader → FrameMap → NodeWitness) : MemoryDecoder :=
  fun {_} L ↦
  let σ := valG L 1 (certOf 1)
  ⟨B1.Main.decSeed σ, B1.Main.decStmt σ L.read, W σ L.read (Located.frameV L)⟩

/-- **What the guest's soundness rests on**, for `main`'s witness function `W`: B2, and `main`'s
soundness over any call relation that unfolds along a
frame map. -/
structure SoundHyps (W : Val → Reader → FrameMap → NodeWitness) : Prop where
  /-- B2 (`b2_step`, `b2_mainL`; `EndSound.b2SoundL_of`). -/
  b2 : B2SoundL
  /-- `main`'s soundness with the witness `W` (B1-f, B1-d, B1-b). -/
  main : Located.MainSoundV bytecode W

variable {W : Val → Reader → FrameMap → NodeWitness}

/-- **Soundness of the deployed guest, its witness named**: every valid execution of the guest on
a public input decodes, from its memory, to a statement of the input's digest under the decoded
seed and a witness holding it. -/
theorem guest_knowledge_of (h : SoundHyps W) : MemoryGuestKnowledge guestProgram (decodeWith W) := by
  intro input t hv
  obtain ⟨hb, h0, h1⟩ := mainBodyL_of h.b2 hv
  have hm : MemOk t.memory.read :=
    ⟨t.logMemorySize, hv.1.1, hv.1.2.1.trans (by decide), t.memory, rfl⟩
  exact h.main bytecode_length t.memory.read hm _ _ (Located.unfoldsV_RL t.memory)
    (Located.rlg_le_rel t.memory) _ _ h0 h1 hb

/-- **What a consumer learns**: a valid execution of the guest on the digest of its statement
`s₀` under the seed `iv` (`s₀`'s deferred claim of the bytecode's shape: `bytecode`'s `23`
coordinates, which the outer verifier's check that it holds implies) decodes to
`iv` and `s₀`, or its memory and `s₀` give a Keccak-256 collision among the explicit
candidates. -/
theorem decode_binds_of (h : SoundHyps W) {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) {iv : Digest} {s₀ : NodeStatement}
    (hs₀ : s₀.deferredClaim.HasBytecodeShape bytecode) (hpub : publicInputDigest input = statementDigest iv s₀) :
    ((decodeWith W t.memory).seed = iv ∧ (decodeWith W t.memory).statement = s₀) ∨
      HasCollision (collisionCandidates (decodeWith W t.memory).seed
        (decodeWith W t.memory).statement iv s₀) := by
  obtain ⟨hd, hrel⟩ := guest_knowledge_of h input t hv
  exact decoded_binds hs₀ hrel.hasBytecodeShape hpub hd

/-- **Soundness, the existential form**: a valid execution of the guest on `input` gives a seed
and a statement of the input's digest of the guest's shape that a witness holds (`NodeRelation`). -/
theorem guest_sound_of (h : SoundHyps W) (input : PublicInput) (t : Execution guestProgram)
    (hv : ValidExecution guestProgram input t) :
    ∃ seed s, statementDigest seed s = publicInputDigest input ∧ s.deferredClaim.HasBytecodeShape bytecode ∧
      ∃ w, NodeRelation bytecode seed s w := by
  obtain ⟨hd, hrel⟩ := guest_knowledge_of h input t hv
  exact ⟨_, _, hd, hrel.hasBytecodeShape, _, hrel⟩

/-! ## With B1's witnesses -/

/-- **The guest's decoder, for the child proof `piOf`**: the seed and the statement off `main`'s
frame, the witness `B1.Main.decWitV` off `main`'s valuation, the memory and the memory's frame
map. -/
noncomputable def decodeV (piOf : Reader → Val → FrameMap → Protocol.Compile.Proof) :
    MemoryDecoder :=
  decodeWith fun σ rd V ↦ B1.Main.decWitV σ rd V piOf

/-- **What the theorems rest on, with B1's witnesses**: B2, and `verify_sub`'s statement with its
proof named by `piOf`. -/
theorem soundHyps_of_sub {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof} (hb2 : B2SoundL)
    (hv : B1.Main.SubSoundW bytecode piOf) :
    SoundHyps fun σ rd V ↦ B1.Main.decWitV σ rd V piOf :=
  ⟨hb2, B1.Main.main_sound_V_of_sub hv⟩

/-- **Soundness of the deployed guest, its witness named**, from B2 and `verify_sub`'s statement. -/
theorem guest_knowledge_V {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof} (hb2 : B2SoundL)
    (hv : B1.Main.SubSoundW bytecode piOf) : MemoryGuestKnowledge guestProgram (decodeV piOf) :=
  guest_knowledge_of (soundHyps_of_sub hb2 hv)

/-- **What a consumer learns**, from B2 and `verify_sub`'s statement. -/
theorem decode_binds_V {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof} (hb2 : B2SoundL)
    (hv : B1.Main.SubSoundW bytecode piOf) {input : PublicInput} {t : Execution guestProgram}
    (hvt : ValidExecution guestProgram input t) {iv : Digest} {s₀ : NodeStatement}
    (hs₀ : s₀.deferredClaim.HasBytecodeShape bytecode) (hpub : publicInputDigest input = statementDigest iv s₀) :
    ((decodeV piOf t.memory).seed = iv ∧ (decodeV piOf t.memory).statement = s₀) ∨
      HasCollision (collisionCandidates (decodeV piOf t.memory).seed
        (decodeV piOf t.memory).statement iv s₀) :=
  decode_binds_of (soundHyps_of_sub hb2 hv) hvt hs₀ hpub

end
end LeanVM.Guest.End
