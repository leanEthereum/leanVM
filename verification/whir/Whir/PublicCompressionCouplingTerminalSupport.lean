import Whir.PublicCompressionCouplingROOrigins
import Whir.PublicCompressionCouplingInspectionSupport
import Whir.PublicCompressionCouplingLabels

/-! Actual consumed raw-key terminal witnesses have all seed nodes recorded in
the causal cache. Target-matching construction bodies are public on the actual
hidden-guess complement; publicly recognized bodies are public already. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed RawOracleCoupling
open TypedOracleCompiler (Sampling)
set_option backward.isDefEq.respectTransparency false

private theorem actual_raw_key_dictionary (Q : Nat) :
    (fun a b : RawKey Q => Classical.propDecidable (a=b)) =
      (inferInstance : DecidableEq (RawKey Q)) := Subsingleton.elim _ _

 theorem publicBody_cache_nodes {Q : Nat} {seedTable : Seed} {ro : RawKey Q → Digest32}
    {cache : Key Q → Option Digest32} {log : PublicLog} {cv : Digest32} {ns : List Node}
    (body : PublicBody log cv ns) (witnessed : Witnessed Q seedTable cache log)
    (consistent : ∀ key answer, cache key=some answer → oracle seedTable ro key=answer) :
    ∀ n ∈ ns, cache (.inl n)=some (seedTable n) := by
  induction body with
  | seed member valid =>
    intro n hn
    have nodes := List.mem_singleton.mp hn
    subst n
    have stored := Witnessed.nonterminal_stored witnessed member
      (fun terminal => terminal_not_seed terminal valid)
    have actual := consistent _ _ stored
    simp only [oracle] at actual
    simpa only [actual] using stored
  | step member internal child ih =>
    intro n hn
    rcases List.mem_cons.mp hn with equal | later
    · subst n
      have stored := Witnessed.nonterminal_stored witnessed member
        (fun terminal => terminal_not_internal terminal internal)
      have actual := consistent _ _ stored
      simp only [oracle] at actual
      simpa only [actual] using stored
    · exact ih n later

open Classical in
 theorem construction_cache_nodes {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    {construction : InspectedConstruction}
    (member : construction ∈ (Sampling.eval (oracle seedTable ro)
      (causalCompile Q iv [] p Q (by rfl) counted)).2) :
    ∀ n ∈ (traceHistory (compressionOf seedTable) iv construction.coordinate.history).nodes,
      (Sampling.eval (oracle seedTable ro) (memo (causalCompile Q iv [] p Q (by rfl) counted)
        (fun _ => none))).2 (.inl n)=some (seedTable n) := by
  have inspected : construction ∈ Sampling.eval (oracle seedTable ro)
      (inspect Q iv (Sampling.eval (oracle seedTable ro)
        (compile Q iv [] p Q (by rfl) counted)).observations) := by
    simpa only [causalCompile_eval] using member
  intro node nodeMember
  have prefixStored := actual_causal_prefix_stored Q iv p counted _ member
    (node := node) (answer := seedTable node)
  rw [actual_raw_key_dictionary Q] at prefixStored
  apply prefixStored
  rw [inspect_construction_nodes Q seedTable ro iv _ inspected]
  exact List.mem_map.mpr ⟨node,by simpa only [List.mem_reverse] using nodeMember,rfl⟩

/-- The complete consumed-terminal graph facts needed for source-aware joint
alignment. These are derived below from the actual compiler/cache, not supplied
as a primitive security hypothesis. -/
def TerminalSupport (Q : Nat) (seedTable : Seed) (cache : Key Q → Option Digest32)
    (log : PublicLog) (targets : Finset Digest32) (key : RawKey Q) : Prop :=
  ∃ input rest, Complete (input::rest) ∧ Tree (compressionOf seedTable) input.cv rest ∧
    extract (input::rest)=some (expandKey key) ∧
    (∀ n ∈ rest, cache (.inl n)=some (seedTable n)) ∧
    (input.cv ∈ targets → PublicBody log input.cv rest)

open Classical in
 theorem actual_terminal_support {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (quiet : hiddenGuess Q iv p counted (oracle seedTable ro)=false)
    {key : RawKey Q} {answer : Digest32}
    (stored : (Sampling.eval (oracle seedTable ro)
      (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2 (.inr key)=some answer) :
    TerminalSupport Q seedTable
      (Sampling.eval (oracle seedTable ro)
        (memo (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none))).2
      (finalLog [] (Sampling.eval (oracle seedTable ro)
        (compile Q iv [] p Q (by rfl) counted)).observations)
      (publicCVTargets (Sampling.eval (oracle seedTable ro)
        (compile Q iv [] p Q (by rfl) counted)).observations) key := by
  have trace := PublicCompressionCouplingTargetCache.memo_empty_trace _ _ stored
  have origin := causalCompile_raw_origin Q seedTable ro iv [] p Q (by rfl) counted
    (by intro n d member; cases member) trace
  have witnessed := actual_causal_cache_witnessed Q iv p counted seedTable ro
  rw [actual_raw_key_dictionary Q] at witnessed
  have consistent := memo_eval_consistent (causalCompile Q iv [] p Q (by rfl) counted)
    (fun _ => none) (oracle seedTable ro) (by intro k d impossible; cases impossible)
  rcases origin with publicOrigin | privateOrigin
  · obtain ⟨input,rest,complete,tree,extracted,body⟩ := publicOrigin
    exact ⟨input,rest,complete,tree,extracted,publicBody_cache_nodes body witnessed consistent,fun _ => body⟩
  · obtain ⟨construction,member,budget,equal⟩ := privateOrigin
    subst key
    let c := compressionOf seedTable
    let history := traceHistory c iv construction.coordinate.history
    let input := terminalNode history.state.cv construction.coordinate.terminal
    refine ⟨input,history.nodes,?_,?_,?_,construction_cache_nodes Q iv p counted seedTable ro member,?_⟩
    · exact coordinateTree_complete c iv construction.coordinate construction.valid.1
    · change Tree c (terminalNode history.state.cv construction.coordinate.terminal).cv history.nodes
      rw [terminalNode_cv]
      exact (traceHistory_valid c iv construction.coordinate.history construction.valid.1).1
    · simpa only [expand_constructionKey,coordinateTree,input,history,c] using
        coordinateTree_key c iv construction.coordinate construction.valid
    · intro target
      have inspected : construction ∈ Sampling.eval (oracle seedTable ro)
          (inspect Q iv (Sampling.eval (oracle seedTable ro)
            (compile Q iv [] p Q (by rfl) counted)).observations) := by
        simpa only [causalCompile_eval] using member
      have rootTarget : evalHistory c iv construction.coordinate.history ∈
          publicCVTargets (Sampling.eval (oracle seedTable ro)
            (compile Q iv [] p Q (by rfl) counted)).observations := by
        simpa only [input,history,terminalNode_cv,traceHistory_cv] using target
      simpa only [input,history,c,terminalNode_cv,traceHistory_cv] using
        actual_inspection_publicBody Q iv p counted seedTable ro quiet inspected rootTarget

#print axioms actual_terminal_support
end Whir.PublicCompressionCouplingRecognition
