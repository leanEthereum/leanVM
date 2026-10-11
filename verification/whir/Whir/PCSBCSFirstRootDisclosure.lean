import Whir.PCSStateRestorationLatentProbability

/-! Root-table capture occurs at the first source-key mention of its complete
shape address, before that packet answer is disclosed. Capturing at a later
commitment announcement would not justify causality against prefix prequeries.
This finder is a ghost of the unchanged operational request sequence. -/
namespace Whir.PCSBCSFirstRootDisclosure
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent
set_option autoImplicit false

universe u v w z
variable {Key : Type u} {Answer : Key → Type v} {Root : Type w} {R : Type z}

section
variable [DecidableEq Key] [DecidableEq Root]

/-- Addresses include every semantic tree/image/occupied shape field. One
source key can mention several roots; the literal parser must derive them. -/
def firstMention (address : Key → List Root) (root : Root) : {n : Nat} →
    Sampling Key Answer R n → Table Key Answer → Option (List (Sigma Answer))
  | _, .ret _, _ => none
  | _, .draw key next, table =>
    if root ∈ address key then some [] else
      (firstMention address root (next (table key)) table).map
        (fun before => ⟨key,table key⟩ :: before)

/-- The complete public prefix used to capture a referenced root is independent
of the current packet's entire answer, including undisclosed continuation bits.
No assumption about query chronology, novelty or warmed ancestors is made. -/
theorem first_mention_answer_independent (address : Key → List Root)
    (target : Key) (root : Root) (mentioned : root ∈ address target)
    {n : Nat} (source : Sampling Key Answer R n) (table : Table Key Answer)
    (answer : Answer target) :
    firstMention address root source (Function.update table target answer) =
      firstMention address root source table := by
  induction source with
  | ret result => rfl
  | draw key next ih =>
    by_cases sameRoot : root ∈ address key
    · simp only [firstMention,sameRoot,↓reduceIte]
    · have different : key ≠ target := by
        intro same
        subst key
        exact sameRoot mentioned
      simp only [firstMention,sameRoot,↓reduceIte,Function.update_of_ne different,ih]

/-- Any deterministic public-log extraction from that prefix inherits the same
current-answer erasure law. Its implementation must still be identified with
the actual public compression log, not a full hidden virtual-table dump. -/
theorem captured_metadata_answer_independent {Metadata : Type*}
    (address : Key → List Root) (target : Key) (root : Root)
    (mentioned : root ∈ address target) {n : Nat}
    (source : Sampling Key Answer R n) (capture : Option (List (Sigma Answer)) → Metadata)
    (table : Table Key Answer) (answer : Answer target) :
    capture (firstMention address root source (Function.update table target answer)) =
      capture (firstMention address root source table) := by
  rw [first_mention_answer_independent address target root mentioned source table answer]

omit [DecidableEq Key] in
/-- Every actually requested referencing key has an earlier first capture.
This uses the adaptive operational trace, not a proposed verifier schedule. -/
theorem first_mention_exists (address : Key → List Root) (target : Key) (root : Root)
    (mentioned : root ∈ address target) {n : Nat}
    (source : Sampling Key Answer R n) (table : Table Key Answer)
    (visited : target ∈ ((Sampling.execute table source).2.map Sigma.fst)) :
    ∃ before, firstMention address root source table = some before := by
  induction source with
  | ret result => simp only [Sampling.execute,List.map_nil,List.not_mem_nil] at visited
  | draw key next ih =>
    by_cases hit : root ∈ address key
    · exact ⟨[],by simp only [firstMention,hit,↓reduceIte]⟩
    · have different : key ≠ target := by
        intro same
        subst key
        exact hit mentioned
      simp only [Sampling.execute,List.map_cons,List.mem_cons] at visited
      obtain ⟨before,found⟩ := ih (table key) (visited.resolve_left (Ne.symm different))
      exact ⟨⟨key,table key⟩::before,by simp only
        [firstMention,hit,↓reduceIte,found,Option.map_some]⟩


omit [DecidableEq Key] in
/-- The finder stores only the actual earlier query prefix, at most the
declared operational query count, even with repeated or off-image requests. -/
theorem first_mention_length (address : Key → List Root) (root : Root) {n : Nat}
    (source : Sampling Key Answer R n) (table : Table Key Answer)
    (before : List (Sigma Answer)) (found : firstMention address root source table = some before) :
    before.length ≤ n := by
  induction source generalizing before with
  | ret result => cases found
  | draw key next ih =>
    by_cases hit : root ∈ address key
    · simp only [firstMention,hit,↓reduceIte,Option.some.injEq] at found
      subst before
      exact Nat.zero_le _
    · simp only [firstMention,hit,↓reduceIte] at found
      cases earlier : firstMention address root (next (table key)) table with
      | none => simp only [earlier,Option.map_none] at found; contradiction
      | some prior =>
        simp only [earlier,Option.map_some,Option.some.injEq] at found
        subst before
        exact Nat.succ_le_succ (ih (table key) prior earlier)

end

#print axioms first_mention_answer_independent
#print axioms captured_metadata_answer_independent
#print axioms first_mention_exists
#print axioms first_mention_length
end Whir.PCSBCSFirstRootDisclosure
