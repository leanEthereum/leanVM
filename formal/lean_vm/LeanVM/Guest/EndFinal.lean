/-
  LeanVM.Guest.EndFinal

  The aggregation guest's soundness for the deployed bytecode: the decoder `decode`, which replays
  the run, and `MemoryGuestKnowledge` from B2 and `verify_sub`'s statement with its proof named
  (`GuestKnowledgeSoundness` of `Statement/LeanVmGuest.lean` for a decoder of memories).
-/

module

public import LeanVM.Guest.EndKnow
public import LeanVM.Guest.EndSound
public import LeanVM.Guest.Located.ReplayFast
public import LeanVM.Guest.B1.Main.SoundV
public import LeanVM.Guest.B1.VerifySub.Proof
public import LeanVM.Guest.Binding
public import LeanVM.Guest.Batch.Node

/-!
# The guest's soundness

`decode` reads, off a memory `L`, through the sorted table of its `2^κ` addresses
(`Located.readTable`, `Extraction.Fast.powTable`, binary search), the seed and the statement from
`main`'s frame (`fp = 1`, the words of `main`'s certificate's cells, `mainValWith`) and the
witness `B1.Main.decWitV` off `main`'s valuation, the memory and the **replayed** frame map
(`Located.replayFrameV`): the run from `(g^0, 1)` stepped through the tables, each call given the
valuation of the first frame at which the run entered its callee (the entries indexed once,
`Located.frameVFast`), its precondition holding there (decided, `Located.preTest`) and its
argument and return cells holding the call's words. Each child's proof is read off its
`verify_sub` frame and the memory (`VerifySub.vsPiOf`: the stream words up to the cursor handed to
`open_stacked`, then `open_stacked`'s words and openings). It chooses nothing: it is computed by
the compiled decoder program (`Cost/Decoder/TopEq.lean`).

* `decode_eq`: on a memory of fewer than `2^64` words, `decode` is the reading with
  `Located.replayFrameV`;
* **`guest_knowledge_of (hb2 : B2SoundL) (hsub : SubSoundW bytecode vsPiOf) :
  MemoryGuestKnowledge guestProgram decode`**: every valid execution of the guest on a public input
  decodes to a statement of that input's digest under the decoded seed, and a witness holding it
  (`NodeRelation`). B2 gives `main`'s body at its frame with every call located (`mainBodyL_of`),
  the located relation unfolds along the replayed frame map (`Located.unfoldsV_replay`), and B1
  (`main_sound_V_of_sub`) applies to it.
* `guest_knowledge_of_obligations`: the same from B2's obligations (`b2SoundL_of`).
* **`guestKnowledgeSoundness_of_spec`**: `GuestKnowledgeSoundness P` for any cost-machine program
  `P` that computes `decode` within the size bound and the budget (`DecoderProgramSpec`).
* `decode_binds_of`: a consumer whose statement `s₀` has, under the seed `iv`, the public input's
  digest learns that the decoded seed and statement are `iv` and `s₀`, or holds an explicit
  Keccak-256 collision.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The words of `main`'s certificate's cells at `fp = 1`, read with `rd` (`Check.valG`). -/
noncomputable def mainValWith (rd : Reader) : Val :=
  fun v ↦ Located.wordWith rd 1 ((certOf 1).locs.getD v.idx 0)

/-- **The guest's decoder**, by replay: through the sorted table of the memory's addresses
(`Extraction.Fast.powTable`), the seed and the statement off `main`'s frame, the witness off
`main`'s valuation, the memory and the replayed frame map (the frames the run entered the
functions that checked it at, indexed once, `Located.frameVFast`), each child's proof by
`VerifySub.vsPiOf`. -/
noncomputable def decode : MemoryDecoder := fun {κ} L ↦
  let memT := Extraction.Fast.powTable κ
  let rd := Located.readTable memT L
  let states := Located.statesTable memT (Extraction.Fast.powTable guestProgram.logSize)
    guestProgram L Located.replayFuel ⟨addressOfIndex 0, 1⟩
  let σ := mainValWith rd
  ⟨B1.Main.decSeed σ, B1.Main.decStmt σ rd,
    B1.Main.decWitV σ rd (Located.frameVFast (Located.preTest rd) states rd) VerifySub.vsPiOf⟩

/-- On a memory of fewer than `2^64` words, the decoder reads `main`'s frame and the memory as
the replayed frame map does. -/
theorem decode_eq {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    decode L = ⟨B1.Main.decSeed (valG L 1 (certOf 1)),
      B1.Main.decStmt (valG L 1 (certOf 1)) L.read,
      B1.Main.decWitV (valG L 1 (certOf 1)) L.read (Located.replayFrameV L) VerifySub.vsPiOf⟩ := by
  have hV : Located.frameVFast (Located.preTest L.read)
      (Located.statesIn (Extraction.powIndex κ) (Extraction.powIndex guestProgram.logSize)
        guestProgram L Located.replayFuel ⟨addressOfIndex 0, 1⟩) L.read = Located.replayFrameV L := by
    rw [Located.replayFrameV, Located.readIn_powIndex hκ, Located.frameVWith_eq_frameVFast]
  simp only [decode, Located.readTable_powTable hκ, Located.statesTable_eq hκ, hV]
  rfl

/-- **Soundness of the deployed guest, its witness named**, from B2 and `verify_sub`'s statement
with its proof named by `vsPiOf`: every valid execution of the guest on a public input decodes,
from its memory, to a statement of the input's digest under the decoded seed and a witness
holding it. -/
theorem guest_knowledge_of (hb2 : B2SoundL)
    (hsub : B1.Main.SubSoundW bytecode VerifySub.vsPiOf) :
    MemoryGuestKnowledge guestProgram decode := by
  intro input t hv
  have hκ : t.logMemorySize < 64 := by
    have := hv.1.2.1
    unfold maxLogMem at this
    omega
  show ExplainsPublicInput guestProgram input (decode t.memory)
  rw [decode_eq hκ]
  obtain ⟨hb, h0, h1⟩ := mainBodyL_of hb2 hv
  have hm : MemOk t.memory.read :=
    ⟨t.logMemorySize, hv.1.1, hv.1.2.1.trans (by decide), t.memory, rfl⟩
  exact B1.Main.main_sound_V_of_sub hsub bytecode_length t.memory.read hm _ _
    (Located.unfoldsV_replay hb2 hv) (Located.rlg_le_rel t.memory) _ _ h0 h1 hb

/-- **Soundness of the deployed guest**, from B2's obligations (`b2SoundL_of`) and `verify_sub`'s
statement with its proof named. -/
theorem guest_knowledge_of_obligations (hkaps : VsKapsKnown) (hgmv : VsGmvKnown)
    (hwalk : WalkKnown) (hsub : B1.Main.SubSoundW bytecode VerifySub.vsPiOf) :
    MemoryGuestKnowledge guestProgram decode :=
  guest_knowledge_of (b2SoundL_of hkaps hgmv hwalk) hsub

/-- **`GuestKnowledgeSoundness` of a program computing the decoder**, from B2 and `verify_sub`'s
statement with its proof named. -/
theorem guestKnowledgeSoundness_of_spec {P : Cost.MachineProgram}
    (hspec : DecoderProgramSpec P fun t ↦ decode t.memory) (hb2 : B2SoundL)
    (hsub : B1.Main.SubSoundW bytecode VerifySub.vsPiOf) : GuestKnowledgeSoundness P :=
  guestKnowledge_of_memory hspec (guest_knowledge_of hb2 hsub)

/-- **What a consumer learns**: a valid execution of the guest on the digest of its statement
`s₀` under the seed `iv` (`s₀`'s deferred claim of the bytecode's shape) decodes to `iv` and `s₀`,
or its memory and `s₀` give a Keccak-256 collision among the explicit candidates. -/
theorem decode_binds_of (hb2 : B2SoundL) (hsub : B1.Main.SubSoundW bytecode VerifySub.vsPiOf)
    {input : PublicInput} {t : Execution guestProgram} (hv : ValidExecution guestProgram input t)
    {iv : Digest} {s₀ : NodeStatement} (hs₀ : s₀.deferredClaim.HasBytecodeShape bytecode)
    (hpub : publicInputDigest input = statementDigest iv s₀) :
    ((decode t.memory).seed = iv ∧ (decode t.memory).statement = s₀) ∨
      HasCollision (collisionCandidates (decode t.memory).seed (decode t.memory).statement iv s₀) := by
  obtain ⟨hd, hrel⟩ := guest_knowledge_of hb2 hsub input t hv
  exact Binding.decoded_binds hs₀ (NodeRelation.hasBytecodeShape hrel) hpub hd

end
end LeanVM.Guest.End
