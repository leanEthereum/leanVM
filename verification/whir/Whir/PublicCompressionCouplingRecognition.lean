import Whir.PublicCompressionCouplingInspection

/-! Recognition lemmas for the actual pinned simulator. Every nonterminal
public reply is from its same seed table. Recognized raw keys therefore carry
actual seed-table trees, including chosen seed chaining values. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open DuplexPublicSimulator

 def NonterminalAuthentic (seed : Seed) (log : PublicLog) : Prop :=
  ∀ n d, (n,d) ∈ log → ¬isTerminal n → seed n = d

 theorem privateKey_notterminal (Q : Nat) (log : PublicLog) (input : Node)
    (h : ¬isTerminal input) : privateKey Q log input = none := by
  simp [privateKey,recognized,h]

 theorem answer_nonterminal (Q : Nat) (ro : RawKey Q → Digest32) (state : DuplexPublicSimulator.State)
    (auth : NonterminalAuthentic state.seed state.publicLog) (input : Node)
    (h : ¬isTerminal input) :
    (runRO ro ((simulator Q).answer state input)).1.2 = state.seed input := by
  cases hit : lookup state.publicLog input with
  | some answer =>
    rw [repeated_no_query Q state input answer hit]
    exact (auth _ _ (lookup_mem hit) h).symm
  | none => simp [simulator,hit,privateKey_notterminal Q state.publicLog input h,runRO]

 theorem answer_nonterminal_authentic (Q : Nat) (ro : RawKey Q → Digest32)
    (state : DuplexPublicSimulator.State) (auth : NonterminalAuthentic state.seed state.publicLog) (input : Node) :
    NonterminalAuthentic (runRO ro ((simulator Q).answer state input)).1.1.seed
      (runRO ro ((simulator Q).answer state input)).1.1.publicLog := by
  rw [answer_seed,answer_publicLog]
  intro node digest member nonterminal
  rcases List.mem_cons.mp member with equal | old
  · cases equal
    exact (answer_nonterminal Q ro state auth input nonterminal).symm
  · exact auth node digest old nonterminal

 theorem PublicBody.seed_tree {log : PublicLog} {cv : Digest32} {ns : List Node}
    (tree : PublicBody log cv ns) (seed : Seed) (auth : NonterminalAuthentic seed log) :
    Tree (compressionOf seed) cv ns := by
  induction tree with
  | seed member hs =>
    have eq := auth _ _ member (fun terminal => terminal_not_seed terminal hs)
    simpa [nodeValue,compressionOf,eq] using Tree.seed (c:=compressionOf seed) _ hs
  | step member hi child ih =>
    have eq := auth _ _ member (fun terminal => terminal_not_internal terminal hi)
    simpa [nodeValue,compressionOf,eq] using Tree.step _ _ hi ih

 theorem privateKey_seed_tree {Q : Nat} {log : PublicLog} {input : Node} {key : RawKey Q}
    (seed : Seed) (auth : NonterminalAuthentic seed log)
    (found : privateKey Q log input = some key) :
    ∃ rest, Complete (input::rest) ∧ Tree (compressionOf seed) input.cv rest ∧
      extract (input::rest) = some (expandKey key) := by
  obtain ⟨ns,recognized,complete,extracted⟩ := privateKey_sound found
  obtain ⟨rest,rfl,body⟩ := recognized_publicBody recognized
  exact ⟨rest,complete,PublicBody.seed_tree body seed auth,extracted⟩

#print axioms answer_nonterminal_authentic
#print axioms privateKey_seed_tree
end Whir.PublicCompressionCouplingRecognition
