/-
  LeanVM.Guest.EndFinal

  The aggregation guest's soundness for the deployed bytecode, with nothing assumed: the decoder
  `decode`, which replays the run, and `MemoryGuestKnowledge` (`GuestKnowledgeSoundness` of
  `Statement/LeanVmGuest.lean` for a decoder of memories; `MemoryAggregateSound`, in the
  random-permutation model, is composed in `LeanVM/Guest/EndRpm.lean`).
-/

module

public import LeanVM.Guest.EndSound
public import LeanVM.Guest.Located.ReplayFast

/-!
# The guest's soundness

`decode` reads, off a memory `L`, through the sorted table of its `2^κ` addresses
(`Located.readTable`, `Extraction.Fast.powTable`, the extractor's binary search), the seed and
the statement from `main`'s frame (`fp = 1`, the words of `main`'s certificate's cells,
`mainValWith`) and the witness `B1.Main.decWitV` off `main`'s valuation, the memory and the
**replayed** frame map (`Located.replayFrameV`): the run from `(g^0, 1)` stepped through the
tables (`Located.statesTable`, the extractor's `stepTable`), each call given the valuation of the first frame at which the run
entered its callee (the entries indexed once, `Located.frameVFast`), its precondition holding
there (decided, `Located.preTest`) and its argument and return cells holding the call's words.
So each leanXMSS and leanSPHINCS signature is read off the frame of its check, the DA matrix off
`da_verify`'s and its callees' frames, each child's proof off its `verify_sub` frame and the
memory (`VerifySub.vsPiOf`: the stream words `verify_sub` reads, the openings `open_stacked`'s
queries hash), the batching's hints off `aggregate_claims`' frame and the memory. It chooses
nothing: it is computed by the compiled decoder program, a cost-machine program with no classical
choice (`Cost/Decoder/TopEq.lean`, `decTop_eq`). That it runs no verifier, only the machine
(whose `KECCAK` instruction checks Keccak-f[1600]), is checked by a test alone,
`tests/LeanVMTests/Guest/DecodeNoChoice.lean`, which follows every definition it unfolds to.

* `guest_knowledge : MemoryGuestKnowledge guest decode`: every valid execution of the guest on a
  public input decodes to a statement of that input's digest under the decoded seed, and a witness
  holding it (`NodeRelation`). B2 locates every call of `main` at a frame the run entered
  (`Check.EnteredAt`), so the located relation unfolds along the replayed frame map
  (`Located.unfoldsV_replay`), and B1 applies to it.
* `decode_eq`: on a memory of fewer than `2^64` words, `decode` is `decodeV`'s reading with the
  replayed frame map in place of `Located.frameV`.
* `aggregate_sound_outer : MemoryAggregateSound guest decode` (`EndRpm.lean`): in the
  random-permutation experiment, the verifier accepts a proof of the guest on the digest of a
  statement `s` under the deployed seed, `s` of the guest's shape, while no
  execution is extracted from the proof and the adversary's transcript, or the extracted one does
  not decode to the deployed seed, `s` and a witness holding it, nor give a Keccak-256 collision
  among `collisionCandidates`, with probability at most the bound of `KnowledgeSoundness`.
* `decode_binds`: a consumer whose statement `s₀` (its deferred claim of the bytecode's shape) has,
  under the seed
  `iv`, the public input's digest learns that the decoded seed and statement are `iv` and `s₀`,
  or holds an explicit Keccak-256 collision.

They rest on B2 (`b2SoundL`: the kernel-checked certificates, `VsDimsKnown`, `VsKnown` and
the walks' obligations) and B1 (`B1.Main.main_sound_V_of_sub` with
`VerifySub.verify_sub_sound_w`). Until B1's ports to the f128 guest land, they take what they
need of `verify_sub`, and the walks' obligations, as the hypothesis `EndPending`
(`EndSound.lean`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

@[expose] public section

/-- The words of `main`'s certificate's cells at `fp = 1`, read with `rd` (`Check.valG`). -/
noncomputable def mainValWith (rd : Reader) : Val :=
  fun v ↦ Located.wordWith rd 1 ((certOf 1).locs.getD v.idx 0)

/-- **The guest's decoder**, by replay: through the sorted table of the memory's addresses
(`Extraction.Fast.powTable`, the extractor's), the seed and the statement off `main`'s frame, the
witness off `main`'s valuation, the memory and the replayed frame map (the frames the run entered
the functions that checked it at, indexed once, `Located.frameVFast`). -/
noncomputable def decode : MemoryDecoder := fun {κ} L ↦
  let memT := Extraction.Fast.powTable κ
  let rd := Located.readTable memT L
  let states := Located.statesTable memT (Extraction.Fast.powTable guestProgram.logSize) guestProgram L
    Located.replayFuel ⟨addressOfIndex 0, 1⟩
  let σ := mainValWith rd
  ⟨B1.Main.decSeed σ, B1.Main.decStmt σ rd,
    B1.Main.decWitV σ rd (Located.frameVFast (Located.preTest rd) states rd) VerifySub.vsPiOf⟩

/-- On a memory of fewer than `2^64` words, the decoder reads `main`'s frame and the memory as
`decodeV` does, with the replayed frame map. -/
theorem decode_eq {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    decode L = ⟨B1.Main.decSeed (valG L 1 (certOf 1)),
      B1.Main.decStmt (valG L 1 (certOf 1)) L.read,
      B1.Main.decWitV (valG L 1 (certOf 1)) L.read (Located.replayFrameV L) VerifySub.vsPiOf⟩ := by
  have hV : Located.frameVFast (Located.preTest L.read)
      (Located.statesIn (Extraction.powIndex κ) (Extraction.powIndex guestProgram.logSize) guestProgram L
        Located.replayFuel ⟨addressOfIndex 0, 1⟩) L.read = Located.replayFrameV L := by
    rw [Located.replayFrameV, Located.readIn_powIndex hκ, Located.frameVWith_eq_frameVFast]
  simp only [decode, Located.readTable_powTable hκ, Located.statesTable_eq hκ, hV]
  rfl

/-- **Soundness of the deployed guest, its witness named**: every valid execution of the guest on
a public input decodes, from its memory, to a statement of the input's digest under the decoded
seed and a witness holding it. -/
theorem guest_knowledge (hP : EndPending) : MemoryGuestKnowledge guestProgram decode := by
  intro input t hv
  have hκ : t.logMemorySize < 64 := by
    have := hv.1.2.1
    unfold maxLogMem at this
    omega
  show ExplainsPublicInput guestProgram input (decode t.memory)
  rw [decode_eq hκ]
  obtain ⟨hb, h0, h1⟩ := mainBodyL_of (b2SoundL hP) hv
  have hm : MemOk t.memory.read := ⟨t.logMemorySize, hv.1.1, hv.1.2.1, t.memory, rfl⟩
  exact B1.Main.main_sound_V_of_sub hP.sound bytecode_length t.memory.read hm _ _
    (Located.unfoldsV_replay (b2SoundL hP) hv) (Located.rlg_le_rel t.memory) _ _ h0 h1 hb

/-- **What a consumer learns**: a valid execution of the guest on the digest of its statement
`s₀` under the seed `iv` (`s₀`'s deferred claim of the bytecode's shape: `bytecode`'s `23`
coordinates, which the outer verifier's check that it holds implies) decodes to
`iv` and `s₀`, or its memory and `s₀` give a Keccak-256 collision among the explicit
candidates. -/
theorem decode_binds (hP : EndPending) {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t)
    {iv : Digest} {s₀ : NodeStatement} (hs₀ : s₀.deferredClaim.HasBytecodeShape bytecode)
    (hpub : publicInputDigest input = statementDigest iv s₀) :
    ((decode t.memory).seed = iv ∧ (decode t.memory).statement = s₀) ∨
      HasCollision (collisionCandidates (decode t.memory).seed (decode t.memory).statement iv s₀) :=
  by
    obtain ⟨hd, hrel⟩ := guest_knowledge hP input t hv
    exact Binding.decoded_binds hs₀ hrel.hasBytecodeShape hpub hd

/-- **Soundness, the existential form**: a valid execution of the guest on `input` gives a seed and
a statement of the input's digest, of the guest's shape, that a witness holds (`NodeRelation`). -/
theorem guest_sound (hP : EndPending) (input : PublicInput) (t : Execution guestProgram)
    (hv : ValidExecution guestProgram input t) :
    ∃ seed s, statementDigest seed s = publicInputDigest input ∧ s.deferredClaim.HasBytecodeShape bytecode ∧
      ∃ w, NodeRelation bytecode seed s w :=
  guest_sound_of (soundHyps_of_sub (b2SoundL hP) hP.sound) input t hv

end
end LeanVM.Guest.End
