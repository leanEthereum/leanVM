import Whir.PublicCompressionCouplingKeys

/-! The cached-missed-recognition case is a public-log invariant, not an
exception to the observer API. A previously incomplete terminal cannot acquire
a body when a newly published answer avoids the earlier chaining positions.
Chosen known CVs remain allowed; only actual late answer matches are bad. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator

/-- Erasing one fresh answer record preserves every body whose chaining
positions avoid that answer. No restriction is placed on the new input CV. -/
 theorem PublicBody.erase_record {log : PublicLog} {input : Node} {answer cv : Digest32}
    {ns : List Node} (tree : PublicBody (observe log input answer) cv ns)
    (avoidInputs : ∀ n d, (n,d) ∈ log → answer ≠ n.cv)
    (avoidRoot : answer ≠ cv) : PublicBody log cv ns := by
  induction tree with
  | seed member seed =>
    rcases List.mem_cons.mp member with equal | old
    · have conflict := congrArg Prod.snd equal
      exact False.elim (avoidRoot conflict.symm)
    · exact PublicBody.seed old seed
  | @step n d rest member internal child ih =>
    rcases List.mem_cons.mp member with equal | old
    · have conflict := congrArg Prod.snd equal
      exact False.elim (avoidRoot conflict.symm)
    · exact PublicBody.step old internal (ih (avoidInputs n d old))

/-- A repeated record cannot create a body either. In particular, a repeated
cached terminal never requires fresh Seed or RO randomness. -/
 theorem PublicBody.erase_repeat {log : PublicLog} {input : Node} {answer cv : Digest32}
    {ns : List Node} (old : (input,answer) ∈ log)
    (tree : PublicBody (observe log input answer) cv ns) : PublicBody log cv ns := by
  induction tree with
  | seed member seed =>
    apply PublicBody.seed _ seed
    rcases List.mem_cons.mp member with equal | prior
    · simpa only [equal] using old
    · exact prior
  | step member internal child ih =>
    apply PublicBody.step _ internal ih
    rcases List.mem_cons.mp member with equal | prior
    · simpa only [equal] using old
    · exact prior

/-- When the newly recorded input is terminal it cannot be a body node, even
if its output coincides with a previous chosen chaining value. -/
 theorem PublicBody.erase_terminal {log : PublicLog} {input : Node} {answer cv : Digest32}
    {ns : List Node} (terminal : isTerminal input)
    (tree : PublicBody (observe log input answer) cv ns) : PublicBody log cv ns := by
  induction tree with
  | seed member seed =>
    rcases List.mem_cons.mp member with equal | prior
    · have nodes := congrArg Prod.fst equal
      dsimp only at nodes
      exact False.elim (terminal_not_seed terminal (nodes ▸ seed))
    · exact PublicBody.seed prior seed
  | step member internal child ih =>
    rcases List.mem_cons.mp member with equal | prior
    · have nodes := congrArg Prod.fst equal
      dsimp only at nodes
      exact False.elim (terminal_not_internal terminal (nodes ▸ internal))
    · exact PublicBody.step prior internal ih

/-- Precisely the cached missed-recognition case: if the terminal was
unrecognized before a non-late publication, it is still unrecognized after it.
The assumptions are structural facts about the previous actual log and the
single actual answer, not cryptographic or observer-exclusion premises. -/
 theorem recognized_none_after_nonlate {log : PublicLog} {input target : Node}
    {answer : Digest32} (functional : Functional log) (clean : ¬OutputCollision log)
    (incomplete : recognized log target = none)
    (avoidInputs : ∀ n d, (n,d) ∈ log → answer ≠ n.cv)
    (avoidTarget : answer ≠ target.cv) :
    recognized (observe log input answer) target = none := by
  cases found : recognized (observe log input answer) target with
  | none => rfl
  | some ns =>
    obtain ⟨rest,rfl,body⟩ := recognized_publicBody found
    have old := PublicBody.erase_record body avoidInputs avoidTarget
    have terminal := (recognized_sound found).1
    obtain ⟨t,tail,equal,ht,hb⟩ := terminal
    have head : t = target := by simpa using (congrArg List.head? equal).symm
    subst t
    have prior := recognized_complete functional clean ht old
    rw [incomplete] at prior
    cases prior

#print axioms PublicBody.erase_record
#print axioms recognized_none_after_nonlate
end Whir.PublicCompressionCouplingRecognition
