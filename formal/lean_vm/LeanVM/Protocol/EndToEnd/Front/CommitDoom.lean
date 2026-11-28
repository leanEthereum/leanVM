/-
  LeanVM.Protocol.EndToEnd.Front.CommitDoom

  The stack's root and its out-of-domain sample, specified from any doom the root creates: the
  first commitment's word and candidates, and the OOD sample's specification on them.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.EndToEnd.Candidates
public import LeanVM.Protocol.EndToEnd.Front.OodBind

/-!
# The commitment's doom

Step 2 of the verifier program (`commitStack`, `readOod`; `verify_execution`,
`crates/verifier/src/lib.rs`) reads the stack's root, then its out-of-domain sample. Before the
root nothing is at stake; the root creates the doom (`commitSpec`, from no doom to any
postcondition `Post` created at the root). The OOD sample (`commitOodSpec`) keeps any doom `J` on
the commitments and adds that the root's candidates (`firstCands`, at a threshold `A μ R`) are
separated at its point, so that the phases after it face the one candidate `oodCands` leaves.

* `firstWord h`, `firstWordC cs`: the word of the first commitment, the stack's (commitment `0`).
* `firstCands μ R A cs`: the candidates of the first commitment's word; `firstCands_bound`: as
  finite and as few as the candidates of any word.

This is the generic part of the archived `EndToEnd/Front/CommitDoom.lean` (tag
`formal-bus-archive`); the doom the root creates is the assembly's.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The word of the first commitment of a history. -/
def firstWord (h : List Ev) : Option Word := (commits h).head?.map (·.2.2)

/-- The first commitment of a history extended past it is unchanged. -/
theorem firstWord_append {h : List Ev} {W : Word} (hW : firstWord h = some W) (l : List Ev) :
    firstWord (h ++ l) = some W := by
  unfold firstWord at hW ⊢
  rw [commits_append]
  rcases hc : commits h with _ | ⟨c, cs⟩
  · simp [hc] at hW
  · simpa [hc] using hW

/-- The first word of a list of commitments. -/
def firstWordC (cs : List (ℕ × ℕ × Word)) : Option Word := cs.head?.map (·.2.2)

theorem firstWord_eq (h : List Ev) : firstWord h = firstWordC (commits h) := rfl

/-- The candidates of the first commitment of a list, on `μ` variables at threshold `A`. -/
def firstCands (μ R A : ℕ) (cs : List (ℕ × ℕ × Word)) : Set (Column μ) :=
  {q | ∃ W, firstWordC cs = some W ∧ q ∈ Candidates μ R A W}

theorem firstCands_eq {μ R A : ℕ} {cs : List (ℕ × ℕ × Word)} {W : Word}
    (hW : firstWordC cs = some W) : firstCands μ R A cs = Candidates μ R A W := by
  ext q
  simp only [firstCands, hW, Option.some.injEq, exists_eq_left', Set.mem_ofPred_eq]

theorem firstCands_bound {μ R A L : ℕ}
    (hL : ∀ W, (Candidates μ R A W).Finite ∧ (Candidates μ R A W).ncard ≤ L)
    (cs : List (ℕ × ℕ × Word)) : (firstCands μ R A cs).Finite ∧ (firstCands μ R A cs).ncard ≤ L := by
  rcases hW : firstWordC cs with _ | W
  · have : firstCands μ R A cs = ∅ := by ext q; simp [firstCands, hW]
    rw [this]
    exact ⟨Set.finite_empty, by simp⟩
  · rw [firstCands_eq hW]
    exact hL W

/-- **The commitment's OOD sample**, from any doom `J` on the commitments: `readOod` at the
stack's variable count `μ`, with the root's candidates at the threshold `A μ R`, of which there
are at most `L` (`hL`, the level-0 list bound of the shape). Its group is charged
`C(L, 2)·μ/|E|`, discounted by the `15`-bit grind (`hε`). -/
noncomputable def commitOodSpec {εmax T : ENNReal} {μ R L : ℕ} (A : ℕ → ℕ → ℕ) (hμ : μ ≠ 0)
    (hL : ∀ W, (Candidates μ R (A μ R) W).Finite ∧ (Candidates μ R (A μ R) W).ncard ≤ L)
    (J : List (ℕ × ℕ × Word) → Prop) (he : oodError L μ < 1)
    (hε : (2 : ENNReal)⁻¹ ^ Whir.oodGrindingBits * (oodError L μ + 0) ≤ εmax) (hT : T ≤ εmax) :
    Spec (readOod μ) (fun h ↦ J (commits h)) (OodPost (firstCands μ R (A μ R)) J) εmax 0 T :=
  oodSpec (firstCands μ R (A μ R)) J hμ (fun cs _ ↦ (firstCands_bound hL cs).1)
    (fun cs _ ↦ (firstCands_bound hL cs).2) he hε hT

variable {εmax T : ENNReal}

/-- **The stack's root with any postcondition**: from no doom, the doom after the root is
`Post ()`, created by the commitment. The boundary after the root carries the follower's lead
`T`. -/
noncomputable def commitSpec (Post : Unit → List Ev → Prop) (logN logInvRate : ℕ)
    (hT : T ≤ εmax) : Spec (commitStack logN logInvRate) (fun _ ↦ False) Post εmax 0 T :=
  Spec.bind (Spec.dead : Spec _ _ (fun _ _ ↦ False) εmax 0 0) fun config ↦ by
    cases config with
    | nil => exact Spec.fail
    | cons level _ =>
      exact Spec.commitP _ _ (fun _ _ h _ ↦ h.elim) hT

/-- The doom of the stack's root, right after it: the postcondition. -/
theorem commitSpec_D (Post : Unit → List Ev → Prop) {logN logInvRate : ℕ} (hT : T ≤ εmax)
    {level : Whir.Level} {rest : List Whir.Level}
    (hc : Whir.ladder logN logInvRate = some (level :: rest)) (h₀ : List Ev) (e : Ev) :
    (commitSpec Post logN logInvRate hT).D h₀ [e] ↔ Post () (h₀ ++ [e]) := by
  have hs : (liftOption (Whir.ladder logN logInvRate)).retSplit [e] =
      some (level :: rest, [], [e]) := by
    rw [hc]
    exact VerifierProgram.retSplit_of_after (VerifierProgram.ret (level :: rest)) [] [e] rfl
  rw [commitSpec, Spec.bind_D, Spec.bindD_after hs (List.cons_ne_nil _ _)]
  simp only [List.append_nil]
  rfl

end
end LeanVM.Protocol.EndToEnd.Front
