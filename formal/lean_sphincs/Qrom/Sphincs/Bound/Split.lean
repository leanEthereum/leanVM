module

public import Qrom.Sphincs.Bound.Reach

@[expose] public section

/-!
# The win event, split

On the side state `s` of the hidden game, with the data's public key and an honest log, the
adversary wins only if the verifier reads a protected input, or an input at which `G` hits or the
data collides with an encoding word (`Qrom.Sphincs.HitE`), or the forgery's digest is covered
(`Qrom.Sphincs.win_split`).
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

/-- The inputs a recorded trace reads among its first `verifyQueries`. -/
def outK (b : Bool × List HashInput) : Finset Input := outOf (b.1, b.2.take verifyQueries)

theorem card_outK_le (b : Bool × List HashInput) : (outK b).card ≤ verifyQueries :=
  (card_outOf_le _).trans (List.length_take_le _ _)

theorem outK_verifier (f : Input → HashOutput) (x : PublicKey × Forgery) :
    outK (evalWithAnswerFn (QueryImpl.ofFn f) (verifier x)) =
      outOf (evalWithAnswerFn (QueryImpl.ofFn f) (verifier x)) := by
  rw [outK, eval_verifier]
  rw [List.take_of_length_le (length_queriedInputs_le _ (bound_verify _ _ _))]

/-- `G` hits the honest value of a dishonest input's address, or the data collides at an encoding
input. -/
def HitE (d : Data) (G : Input → HashOutput) (x : Input) : Prop :=
  (good d x (G x) ∧ ∀ k, pt (hOf d) (d none) k ≠ x) ∨ EncAt d x

open Classical in
/-- **The win event, split.** -/
theorem win_split (d : Data) (s : Log) (G : Input → HashOutput) (F : Forgery) (hlog : HonestLog d s)
    (hw : win ((pkD d, F), evalWithAnswerFn (QueryImpl.ofFn ((hidGame d).answer s G))
      (verifier (pkD d, F))) s = true) :
    (∃ x ∈ outOf (evalWithAnswerFn (QueryImpl.ofFn ((hidGame d).answer s G)) (verifier (pkD d, F))),
      Prot d s x) ∨
    (∃ x ∈ outOf (evalWithAnswerFn (QueryImpl.ofFn ((hidGame d).answer s G)) (verifier (pkD d, F))),
      HitE d G x) ∨ CoverE d s G F.message F.signature.randomness := by
  rw [eval_verifier] at hw ⊢
  simp only [win, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hw
  obtain ⟨hver, hfresh⟩ := hw
  rcases classify d s G F.message F.signature hlog hver hfresh with
    ⟨l, hl, x, rfl, hp⟩ | ⟨l, hl, x, rfl, hnh, hg⟩ | ⟨l, hl, x, rfl, hbad⟩ | hcov
  · exact Or.inl ⟨x, mem_outOf.mpr hl, hp⟩
  · exact Or.inr (Or.inl ⟨x, mem_outOf.mpr hl, Or.inl ⟨hg, fun k hk ↦ hnh k (congrArg Subtype.val hk)⟩⟩)
  · exact Or.inr (Or.inl ⟨x, mem_outOf.mpr hl, Or.inr hbad⟩)
  · exact Or.inr (Or.inr hcov)

/-- An event may assume the data's public key. -/
theorem sideW_pk_restrict (d : Data) (G : Input → HashOutput) {A : QReg} (adv : Adversary A)
    (ρ : SubState A)
    (ev : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) (PublicKey × Forgery) u) → Log → Bool) :
    OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ ev =
      OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ
        (fun p s ↦ ev p s && decide (p.2.2.1 = pkD d)) := by
  rw [OvGame.sideW_eq_sum (hidGame d) G _ (withKey adv), OvGame.sideW_eq_sum (hidGame d) G _ (withKey adv),
    ← (QuantumComp₂.leafEquiv _ _).tsum_eq, ← (QuantumComp₂.leafEquiv _ _).tsum_eq]
  refine tsum_congr fun v ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hv : v.1 = pkD d
  · have hd : decide (((QuantumComp₂.leafEquiv (QReg.of Unit) (PublicKey × Forgery)) v).2.2.1 = pkD d) =
        true := by
      rw [QuantumComp₂.leafEquiv_apply]
      exact decide_eq_true hv
    simp only [hd, Bool.and_true]
  · have hz := withKey_zero (hidGame d) G (pkD d) (fun _ ↦ rfl) adv ρ v.1 v.2 hv
    have hb : OvGame.blockW s (((hidGame d).sampled G).jointPost .instruments (withKey adv) ρ
        ((QuantumComp₂.leafEquiv _ _) v)).matrix = 0 := by
      change OvGame.blockW s (((hidGame d).sampled G).jointPost₂ .instruments (withKey adv) ρ (v.1, v.2)).matrix = 0
      rw [hz]
      simp [OvGame.blockW]
    rw [hb]
    simp only [ite_self]

open Classical in
/-- The verifier read a protected input. -/
def evProt (d : Data) (s : Log) (b : Bool × List HashInput) : Bool := decide (∃ x ∈ outK b, Prot d s x)

open Classical in
/-- `G` hits, or the data collides, at an input the verifier read. -/
def evHit (d : Data) (G : Input → HashOutput) (b : Bool × List HashInput) : Bool :=
  decide (∃ z ∈ outK b, HitE d G z)

open Classical in
/-- The forgery's digest is covered. -/
def evCov (d : Data) (s : Log) (G : Input → HashOutput) (F : Forgery) : Bool :=
  decide (CoverE d s G F.message F.signature.randomness)

open Classical in
theorem evProt_iff {d : Data} {s : Log} {b : Bool × List HashInput} :
    evProt d s b = true ↔ ∃ x ∈ outK b, Prot d s x := by
  unfold evProt; exact decide_eq_true_iff
open Classical in
theorem evHit_iff {d : Data} {G : Input → HashOutput} {b : Bool × List HashInput} :
    evHit d G b = true ↔ ∃ z ∈ outK b, HitE d G z := by
  unfold evHit; exact decide_eq_true_iff
open Classical in
theorem evCov_iff {d : Data} {s : Log} {G : Input → HashOutput} {F : Forgery} :
    evCov d s G F = true ↔ CoverE d s G F.message F.signature.randomness := by
  unfold evCov; exact decide_eq_true_iff

/-- The hidden game's answers in `s`. -/
abbrev hidAns (d : Data) (G : Input → HashOutput) (s : Log) : QueryImpl (Input →ₒ HashOutput) Id :=
  QueryImpl.ofFn ((hidGame d).answer s G)

open Classical in
/-- **The win weight is at most the weights of the three events.** -/
theorem sideW_win_le (d : Data) (G : Input → HashOutput) {A : QReg} (adv : Adversary A)
    (ρ : SubState A) :
    OvGame.sideW (hidGame d) G .instruments (gameProg adv) ρ (fun p s ↦ win p.2.2 s) ≤
      OvGame.sideW (hidGame d) G .instruments (gameProg adv) ρ (fun p s ↦ evProt d s p.2.2.2) +
      OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦
        evHit d G (evalWithAnswerFn (hidAns d G s) (verifier p.2.2))) +
      OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦ evCov d s G p.2.2.2) := by
  have hW := OvGame.sideW_withVerifier (hidGame d) G (withKey adv) verifier ρ fun v s ↦ win v s
  have hP := OvGame.sideW_withVerifier (hidGame d) G (withKey adv) verifier ρ
    fun v s ↦ evProt d s v.2
  change OvGame.sideW _ _ _ (OvGame.withVerifier (withKey adv) verifier) _ _ ≤
    OvGame.sideW _ _ _ (OvGame.withVerifier (withKey adv) verifier) _ _ + _ + _
  rw [hW, hP]
  rw [OvGame.sideW_restrict (hidGame d) G {s | ¬ HonestLog d s}
    (fun j s h hs ↦ h (honestLog_closed d j s hs)) (fun h ↦ h (honestLog_empty d)) .instruments
    (withKey adv) ρ, sideW_pk_restrict d G adv ρ]
  refine (OvGame.sideW_mono _ G _ _ ρ (ev' := fun p s ↦
      evProt d s (evalWithAnswerFn (hidAns d G s) (verifier p.2.2)) ||
      (evHit d G (evalWithAnswerFn (hidAns d G s) (verifier p.2.2)) || evCov d s G p.2.2.2)) fun p s hps ↦
      ?_).trans ?_
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Set.mem_ofPred_eq, not_not] at hps
    obtain ⟨⟨hw, hlog⟩, hpk⟩ := hps
    have hv : p.2.2 = (pkD d, p.2.2.2) := Prod.ext hpk rfl
    rw [hv] at hw ⊢
    simp only [Bool.or_eq_true]
    rcases win_split d s G p.2.2.2 hlog hw with h | h | h
    · exact Or.inl (evProt_iff.mpr (by rw [outK_verifier]; exact h))
    · exact Or.inr (Or.inl (evHit_iff.mpr (by rw [outK_verifier]; exact h)))
    · exact Or.inr (Or.inr (evCov_iff.mpr h))
  · rw [add_assoc]
    exact (OvGame.sideW_or_le _ G _ _ ρ _ _).trans (add_le_add le_rfl (OvGame.sideW_or_le _ G _ _ ρ _ _))

end Qrom.Sphincs
