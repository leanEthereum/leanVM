module

public import Qrom.Sphincs.Bound.Reach

@[expose] public section

/-!
# The win event, split

On the side state `s` of the hidden game, with the data's public key and an honest log, the
adversary wins only if the verifier reads a protected input, or an input at which `G` hits, or the
data has an encoding collision, or the forgery's digest is covered (`Qrom.Sphincs.win_split`).
-/

open OracleComp OracleSpec FORS FORS.Security Quantum

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- The inputs a recorded trace reads, in the finite domain. -/
def outOf (b : Bool × List HashInput) : Finset Input := (b.2.filterMap embed).toFinset

theorem mem_outOf {b : Bool × List HashInput} {x : Input} : x ∈ outOf b ↔ x.1 ∈ b.2 := by
  simp only [outOf, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    rw [val_of_embed he]
    exact hl
  · intro hx
    exact ⟨x.1, hx, embed_val x⟩

theorem card_outOf_le (b : Bool × List HashInput) : (outOf b).card ≤ b.2.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem eval_verifier (f : Input → HashOutput) (pk : PublicKey) (F : Forgery) :
    evalWithAnswerFn (QueryImpl.ofFn f) (verifier (pk, F)) =
      (evalWithAnswerFn (QueryImpl.ofFn (extend f))
        (Concrete.verify pk F.message F.signature : OracleComp HashSpec Bool),
       queriedInputs (QueryImpl.ofFn (extend f))
        (Concrete.verify pk F.message F.signature : OracleComp HashSpec Bool)) := by
  rw [verifier, eval_liftH, eval_traced]

open Classical in
/-- **The win event, split.** -/
theorem win_split (d : Data) (s : Log) (G : Input → HashOutput) (F : Forgery) (hlog : HonestLog d s)
    (hw : win ((pkD d, F), evalWithAnswerFn (QueryImpl.ofFn ((hidGame d).answer s G))
      (verifier (pkD d, F))) s = true) :
    (∃ x ∈ outOf (evalWithAnswerFn (QueryImpl.ofFn ((hidGame d).answer s G)) (verifier (pkD d, F))),
      Prot d s x) ∨
    (∃ x ∈ outOf (evalWithAnswerFn (QueryImpl.ofFn ((hidGame d).answer s G)) (verifier (pkD d, F))),
      good d x (G x)) ∨
    BadEnc d ∨ CoverE d s G F.message F.signature.randomness := by
  rw [eval_verifier] at hw ⊢
  simp only [win, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hw
  obtain ⟨hver, hfresh⟩ := hw
  rcases classify d s G F.message F.signature hlog hver hfresh with
    ⟨l, hl, x, rfl, hp⟩ | ⟨l, hl, x, rfl, -, hg⟩ | hbad | hcov
  · exact Or.inl ⟨x, mem_outOf.mpr hl, hp⟩
  · exact Or.inr (Or.inl ⟨x, mem_outOf.mpr hl, hg⟩)
  · exact Or.inr (Or.inr (Or.inl hbad))
  · exact Or.inr (Or.inr (Or.inr hcov))

end Qrom.Sphincs
