/-
  LeanVM.Protocol.KnowledgeSoundness

  The end statement `LeanVM.KnowledgeSoundness` of `Statement/LeanVm.lean`, for an extractor a
  cost-machine program computes, from the link's interface and the program's agreement with the
  agreement-set extractor.
-/

module

public import LeanVM.Protocol.LeanVMRpmAS
public import LeanVM.Protocol.LeanVMSoundAS
public import Statement.CostMachine

/-!
# Knowledge soundness, composed

* `KnowledgeSoundness.of_imp`: an extractor that returns whatever a knowledge-sound extractor
  returns is knowledge sound (a break for it is a break for the other).
* `knowledgeSoundness_transcriptExtractor LI`: the agreement-set extractor on the adversary's
  transcript (`Relation.transcriptExtractor`) is knowledge sound, from the random-oracle bound
  `knowledgeSoundnessRomAS LI` (`LeanVMSoundAS.lean`) and the transfer
  `knowledgeSoundness_of_rom` (`LeanVMRpmAS.lean`).
* `knowledgeSoundness_of LI hext hmono`: the extractor a cost-machine program `P` computes
  (`LeanVM.extractorComputedBy`, `Statement/CostMachine.lean`) is knowledge sound, when it is an
  extractor `E'` (`hext`) that returns whatever `Relation.transcriptExtractor` returns (`hmono`).
  The compiled extractor need not equal the agreement-set extractor: it replays the verifier's
  transcript operations without its checks, so it may return where the agreement-set extractor
  fails, which only helps.
-/

namespace LeanVM

@[expose] public section

/-- **An extractor that returns whatever a knowledge-sound extractor returns is knowledge
sound.** -/
theorem KnowledgeSoundness.of_imp {E₁ E₂ : StraightLineExtractor}
    (h : ∀ prog input T proof t, E₁ prog input T proof = some t → E₂ prog input T proof = some t)
    (h₁ : KnowledgeSoundness E₁) : KnowledgeSoundness E₂ := fun A Q hQ ↦
  (prEvent_mono _ _ _ fun _ ho ↦ ⟨ho.1, fun ⟨t, ht, hv⟩ ↦ ho.2 ⟨t, h _ _ _ _ _ ht, hv⟩⟩).trans
    (h₁ A Q hQ)

/-- **The agreement-set extractor on the adversary's transcript is knowledge sound**, in the
random-permutation model, with the end statement's bound. -/
theorem knowledgeSoundness_transcriptExtractor (LI : Protocol.Relation.LinkIface) :
    KnowledgeSoundness Protocol.Relation.transcriptExtractor :=
  knowledgeSoundness_of_rom (knowledgeSoundnessRomAS LI)

/-- **Knowledge soundness of a compiled extractor**: the extractor the cost-machine program `P`
computes, if it is `E'` and `E'` returns whatever `Relation.transcriptExtractor` returns. -/
theorem knowledgeSoundness_of (LI : Protocol.Relation.LinkIface) {P : Cost.MachineProgram}
    {E' : StraightLineExtractor} (hext : extractorComputedBy P = E')
    (hmono : ∀ prog input T proof t, Protocol.Relation.transcriptExtractor prog input T proof =
      some t → E' prog input T proof = some t) :
    KnowledgeSoundness (extractorComputedBy P) := by
  rw [hext]
  exact KnowledgeSoundness.of_imp hmono (knowledgeSoundness_transcriptExtractor LI)

end

end LeanVM
