/-
  LeanVM.Protocol.Relation.NoCommit

  Programs that commit nothing, and a fact about the commitments carried through their
  specifications.
-/

module

public import LeanVM.Protocol.Relation.Frame
public import LeanVM.Protocol.Relation.Front

/-!
# Programs without commitments

`NoCommit p`: no node of `p` reads a commitment. It is closed under `bind` (`NoCommit.bind`) and
holds of the verifier's reads, draws, grinds, sum-checks and checks; along a run of such a program
the commitments do not change (`NoCommit.commits_reach`), so a fact about them before the program
holds after it (`Spec.withCommits`).
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Protocol.Verifier VerifierProgram

@[expose] public section

variable {α β : Type}

/-- **No node of the program reads a commitment.** -/
inductive NoCommit : VerifierProgram α → Prop where
  | ret (a : α) : NoCommit (.ret a)
  | fail : NoCommit .fail
  | read {k : E → VerifierProgram α} : (∀ x, NoCommit (k x)) → NoCommit (.read k)
  | sample {k : E → VerifierProgram α} : (∀ x, NoCommit (k x)) → NoCommit (.sample k)
  | readPacked {n : ℕ} {k : List E → VerifierProgram α} : (∀ xs, NoCommit (k xs)) →
      NoCommit (.readPacked n k)
  | samplePacked {n : ℕ} {k : List E → VerifierProgram α} : (∀ xs, NoCommit (k xs)) →
      NoCommit (.samplePacked n k)
  | grind {b : ℕ} {k : VerifierProgram α} : NoCommit k → NoCommit (.grind b k)
  | query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} :
      (∀ rows, NoCommit (k rows)) → NoCommit (.query i ps k)

namespace NoCommit

theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoCommit p)
    (hf : ∀ a, NoCommit (f a)) : NoCommit (p.bind f) := by
  induction hp with
  | ret a => exact hf a
  | fail => exact .fail
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | readPacked _ ih => exact .readPacked ih
  | samplePacked _ ih => exact .samplePacked ih
  | grind _ ih => exact .grind ih
  | query _ ih => exact .query ih

theorem bind' {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoCommit p)
    (hf : ∀ a, NoCommit (f a)) : NoCommit (p >>= f) := hp.bind hf

theorem after : ∀ {p : VerifierProgram α} {l : List Ev} {q : VerifierProgram α}, NoCommit p →
    p.after l = some q → NoCommit q
  | _, [], _, hp, h => by simp only [VerifierProgram.after, Option.some.injEq] at h; exact h ▸ hp
  | _, _ :: _, _, .ret _, h => by simp [VerifierProgram.after] at h
  | _, _ :: _, _, .fail, h => by simp [VerifierProgram.after] at h
  | _, e :: _, _, .read hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact after (hk _) h
  | _, e :: _, _, .sample hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact after (hk _) h
  | _, e :: _, _, .readPacked hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    exact after (hk _) h
  | _, e :: _, _, .samplePacked hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    exact after (hk _) h
  | _, e :: _, _, .grind hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    exact after hk h
  | _, e :: _, _, .query hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact after (hk _) h

theorem not_commit {ht w : ℕ} {k : VerifierProgram α} (h : NoCommit (.commit ht w k)) : False := by
  cases h

/-- **Along a run of a program without commitments, none is read.** -/
theorem commits_reach {p : VerifierProgram α} (hp : NoCommit p) {h₀ l : List Ev}
    (hl : p.Reach h₀ l) : commits l = [] := by
  induction hl with
  | nil => rfl
  | read _ _ _ ih | sample _ _ _ ih | grind _ _ ih | query _ _ _ ih | readPacked _ _ _ _ ih
  | samplePacked _ _ _ _ ih =>
    rw [commits_append, ih]; rfl
  | commit _ _ ha _ _ => exact absurd (hp.after ha) not_commit

/-- **Along a history of a program without commitments, none is read.** -/
theorem commits_after : ∀ {p : VerifierProgram α} {l : List Ev} {q : VerifierProgram α},
    NoCommit p → p.after l = some q → commits l = []
  | _, [], _, _, _ => rfl
  | _, _ :: _, _, .ret _, h => by simp [VerifierProgram.after] at h
  | _, _ :: _, _, .fail, h => by simp [VerifierProgram.after] at h
  | _, e :: _, _, .read hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    simpa [commits] using commits_after (hk _) h
  | _, e :: _, _, .sample hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    simpa [commits] using commits_after (hk _) h
  | _, e :: _, _, .readPacked hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    simpa [commits] using commits_after (hk _) h
  | _, e :: _, _, .samplePacked hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    simpa [commits] using commits_after (hk _) h
  | _, e :: _, _, .grind hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    simpa [commits] using commits_after hk h
  | _, e :: _, _, .query hk, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    simpa [commits] using commits_after (hk _) h

end NoCommit

/-! ## The verifier's pieces -/

theorem noCommit_readScalars : ∀ n, NoCommit (readScalars n)
  | 0 => .ret _
  | n + 1 => .read fun _ ↦ (noCommit_readScalars n).bind fun _ ↦ .ret _

theorem noCommit_sampleChallenges : ∀ n, NoCommit (sampleChallenges n)
  | 0 => .ret _
  | n + 1 => .sample fun _ ↦ (noCommit_sampleChallenges n).bind fun _ ↦ .ret _

theorem noCommit_grindProofOfWork (b : ℕ) : NoCommit (grindProofOfWork b) := by
  unfold grindProofOfWork; split_ifs
  · exact .ret _
  · exact .grind (.ret _)

theorem noCommit_require (c : Prop) [Decidable c] : NoCommit (require c) := by
  unfold require; split_ifs
  · exact .ret _
  · exact .fail

theorem noCommit_liftOption (o : Option α) : NoCommit (liftOption o) := by
  cases o
  · exact .fail
  · exact .ret _

theorem noCommit_sumcheck (count : ℕ) :
    ∀ (eqs : List (Option E)) (claim : E), NoCommit (sumcheck claim count eqs)
  | [], _ => by unfold sumcheck; exact .ret _
  | e :: es, claim => by
    unfold sumcheck
    refine NoCommit.bind ?_ fun _ ↦ ?_
    · unfold sumcheckRoundPoly
      split
      · exact NoCommit.bind (.read fun _ ↦ .ret _) fun _ ↦
          (noCommit_readScalars _).bind fun _ ↦
            (noCommit_grindProofOfWork _).bind fun _ ↦ .ret _
      · exact (noCommit_readScalars _).bind fun _ ↦
          (noCommit_grindProofOfWork _).bind fun _ ↦ .ret _
    · exact NoCommit.bind (.sample fun _ ↦ .ret _) fun _ ↦
        (noCommit_sumcheck count es _).bind fun _ ↦ .ret _

/-! ## A fact about the commitments, carried -/

variable {p : VerifierProgram α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax L T : ENNReal}

open Classical in
/-- **A fact about the commitments, carried through a program that reads none.** -/
noncomputable def Spec.withCommits (S : Spec p Pre Post εmax L T) (hp : NoCommit p)
    (J : List (ℕ × ℕ × Word) → Prop) :
    Spec p (fun h ↦ Pre h ∧ J (commits h)) (fun a h ↦ Post a h ∧ J (commits h)) εmax L T where
  D h₀ l := S.D h₀ l ∧ J (commits h₀)
  V h₀ l := if J (commits h₀) then S.V h₀ l else 1
  le_one h₀ l := by split_ifs <;> first | exact S.le_one _ _ | exact le_rfl
  start_D h₀ h := ⟨S.start_D h₀ h.1, h.2⟩
  start_V h₀ h := by simp only [h.2, ite_true]; exact S.start_V h₀ h.1
  read x hl ha hD := ⟨S.read x hl ha hD.1, hD.2⟩
  readPacked xs hl ha hn hD := ⟨S.readPacked xs hl ha hn hD.1, hD.2⟩
  grind hl ha hD := ⟨S.grind hl ha hD.1, hD.2⟩
  commit word hl ha hw hD := ⟨S.commit word hl ha hw hD.1, hD.2⟩
  sample hl ha := by
    split_ifs with hJ
    · exact S.sample hl ha
    · exact avg_le_one _ fun _ ↦ le_rfl
  samplePacked hl ha := by
    split_ifs with hJ
    · exact S.samplePacked hl ha
    · exact (avgPk_const _ _).le
  query hl ha hq := by
    split_ifs with hJ
    · exact S.query hl ha hq
    · exact le_rfl
  moveEnd hl ha hm hD := by
    split_ifs with hJ
    · exact S.moveEnd hl ha hm fun h ↦ hD ⟨h, hJ⟩
    · exact le_rfl
  retEnd hl ha hD := by
    split_ifs with hJ
    · exact S.retEnd hl ha fun h ↦ hD ⟨h, hJ⟩
    · exact le_rfl
  retDoom hl ha hD := by simp only [hD.2, ite_true]; exact S.retDoom hl ha hD.1
  post hl ha hD := ⟨S.post hl ha hD.1, by
    rw [commits_append, hp.commits_reach hl, List.append_nil]; exact hD.2⟩
  bound hl hne hm hD := by simp only [hD.2, ite_true]; exact S.bound hl hne hm hD.1

end

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Protocol.Verifier VerifierProgram

public section

theorem noCommit_pure {γ : Type} (a : γ) : NoCommit (pure a : VerifierProgram γ) := .ret a

theorem noCommit_readScalar : NoCommit readScalar := .read fun _ ↦ .ret _

theorem noCommit_sampleChallenge : NoCommit sampleChallenge := .sample fun _ ↦ .ret _

theorem noCommit_readScalarsPacked (n : ℕ) : NoCommit (readScalarsPacked n) :=
  .readPacked fun _ ↦ .ret _

theorem noCommit_sampleChallengesPacked (n : ℕ) : NoCommit (sampleChallengesPacked n) :=
  .samplePacked fun _ ↦ .ret _

/-- Prove `NoCommit` of a `do`-block of the verifier's pieces. -/
scoped macro "no_commit" : tactic => `(tactic| (
  repeat' (first
    | exact NoCommit.ret _
    | exact NoCommit.fail
    | exact noCommit_readScalar
    | exact noCommit_sampleChallenge
    | exact noCommit_readScalarsPacked _
    | exact noCommit_sampleChallengesPacked _
    | exact noCommit_readScalars _
    | exact noCommit_sampleChallenges _
    | exact noCommit_grindProofOfWork _
    | exact noCommit_require _
    | exact noCommit_liftOption _
    | exact noCommit_sumcheck _ _ _
    | apply NoCommit.bind'
    | apply NoCommit.bind
    | intro _
    | split
    | dsimp only)))

theorem noCommit_verifyLink (layout : Layout) :
    NoCommit (verifyLink computedSplit layout) := by
  unfold verifyLink computedSplit
  no_commit

theorem noCommit_bindPublicInput (layout : Layout) (pd : Digest) :
    NoCommit (bindPublicInput layout pd) := by
  unfold bindPublicInput
  no_commit

theorem noCommit_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    NoCommit (keccakOpen logSteps claim first count value) := by
  unfold keccakOpen
  no_commit

theorem noCommit_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    NoCommit (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  no_commit

theorem noCommit_keccakLayers (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : KeccakClaim), NoCommit (keccakLayers logSteps steps claim)
  | [], _ => by unfold keccakLayers; exact .ret _
  | step :: steps, claim => by
    unfold keccakLayers
    exact (noCommit_verifyKeccakLayer _ _ _).bind' fun _ ↦ noCommit_keccakLayers logSteps steps _

/-- `no_commit` with every lemma applied at reducible transparency, for blocks whose terms the
elaborator must not evaluate. -/
scoped macro "no_commit_reducible" : tactic => `(tactic| (
  repeat' (first
    | with_reducible exact noCommit_keccakLayers _ _ _
    | with_reducible exact noCommit_keccakOpen _ _ _ _ _
    | with_reducible exact NoCommit.ret _
    | with_reducible exact noCommit_pure _
    | with_reducible exact NoCommit.fail
    | with_reducible exact noCommit_readScalar
    | with_reducible exact noCommit_sampleChallenge
    | with_reducible exact noCommit_readScalars _
    | with_reducible exact noCommit_sampleChallenges _
    | with_reducible exact noCommit_grindProofOfWork _
    | with_reducible exact noCommit_require _
    | with_reducible exact noCommit_liftOption _
    | with_reducible exact noCommit_sumcheck _ _ _
    | apply NoCommit.bind'
    | apply NoCommit.bind
    | intro _
    | split
    | dsimp only)))

theorem noCommit_keccakValidity (layout : Layout) (link : LinkEnd) :
    NoCommit (keccakValidity layout link) := by
  unfold keccakValidity verifyKeccak
  no_commit_reducible

/-- **The announced sizes read no commitment.** -/
theorem noCommit_readAnnouncedSizes (bytecode : List K) : NoCommit (readAnnouncedSizes bytecode) := by
  unfold readAnnouncedSizes
  no_commit

/-- **The front phases read no commitment.** -/
theorem noCommit_frontProg (layout : Layout) (input : LeanVM.Semantics.PublicInput) :
    NoCommit (Relation.frontProg layout input) := by
  unfold Relation.frontProg
  exact (noCommit_verifyLink layout).bind' fun link ↦
    (noCommit_bindPublicInput _ _).bind' fun _ ↦
      (noCommit_keccakValidity _ link).bind' fun _ ↦ .ret _

end

end LeanVM.Protocol.Compile
