import Whir.PCSBCSMerkleSeedProjection
import Whir.PublicMerkleProgram

/-! Ordinary Merkle consistency for the historical pre-#607 #552 simulator.
Only role-zero primitive replies are authenticated by the fallback seed. Raw
construction replies and all other primitive replies remain unrestricted.
The initial-state theorems derive this property from actual mixed compilation,
without a supplied log/lookup certificate. Ordinary counters are the exact
real-byte counters of PublicMerkleLog.node, not counters with ignored bits. -/
set_option autoImplicit false
namespace Whir.PCSBCSMixedOrdinaryMerkle
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler

/-- Exact role-zero condition on the actual UInt64 counter. -/
theorem tag_zero_iff (input : Node) : tag input = 0 ↔ input.tweak.toNat < 2^56 := by
  simp only [tag]
  omega

/-- The machine-level condition includes UInt64 reduction. The no-wrap source
bound below is deliberately stronger; wrapping is not source domain separation. -/
theorem node_tag_zero_iff_mod (cv : Digest32) (count : Nat) (bytes : List Byte)
    (last : Bool) :
    tag (PublicMerkleLog.node cv count bytes last) = 0 ↔
      (count + bytes.length) % 2^64 < 2^56 := by
  rw [tag_zero_iff]
  simp only [PublicMerkleLog.node, UInt64.toNat_ofNat']

/-- A nonwrapped ordinary request has role zero exactly when its cumulative
real-byte count is below 2^56; padding does not enter that count. -/
theorem node_tag_zero_iff (cv : Digest32) (count : Nat) (bytes : List Byte)
    (last : Bool) (noWrap : count + bytes.length < 2^64) :
    tag (PublicMerkleLog.node cv count bytes last) = 0 ↔ count + bytes.length < 2^56 := by
  rw [node_tag_zero_iff_mod, Nat.mod_eq_of_lt noWrap]

/-- Neither finality nor the purpose label can turn a role-zero input into a
recognized duplex terminal. -/
theorem ordinary_privateKey_none (Q : Nat) (log : DuplexPublicSimulator.PublicLog)
    (input : Node) (ordinary : tag input = 0) :
    DuplexPublicSimulator.privateKey Q log input = none :=
  PCSBCSMerkleSeedProjection.privateKey_none Q log ordinary

/-- Concrete source formula for a single compression request. -/
theorem node_privateKey_none (Q : Nat) (log : DuplexPublicSimulator.PublicLog)
    (cv : Digest32) (count : Nat) (bytes : List Byte) (last : Bool)
    (bound : count + bytes.length < 2^56) :
    DuplexPublicSimulator.privateKey Q log (PublicMerkleLog.node cv count bytes last) = none :=
  ordinary_privateKey_none Q log _ (PublicMerkleLog.ordinary_tag_zero cv count bytes last bound)

/-- The induction invariant is only the ordinary sublog, never the full log. -/
theorem primitiveCalls_ordinary (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (log : DuplexPublicSimulator.PublicLog)
    (auth : PCSBCSMerkleSeedProjection.OrdinaryAuthentic seed log) (input : Node)
    (ordinary : tag input = 0) :
    Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.primitiveCalls Q log input) =
      (DuplexPublicSimulator.observe log input (seed input), seed input) := by
  cases hit : DuplexPublicSimulator.lookup log input with
  | some answer =>
    have eq : seed input = answer := auth input answer
      (DuplexPublicSimulator.lookup_mem hit) ordinary
    simp [PublicCompressionCouplingMixed.primitiveCalls, hit, eq, Sampling.eval]
  | none =>
    simp [PublicCompressionCouplingMixed.primitiveCalls, hit,
      ordinary_privateKey_none Q log input ordinary, Sampling.eval,
      PublicCompressionCouplingMixed.oracle]

/-- Covers a first call and every cache hit, including hits after arbitrary
construction calls (which do not update the simulator log). -/
theorem simulator_ordinary_answer (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (log : DuplexPublicSimulator.PublicLog)
    (auth : PCSBCSMerkleSeedProjection.OrdinaryAuthentic seed log) (input : Node)
    (ordinary : tag input = 0) :
    (runRO ro ((DuplexPublicSimulator.simulator Q).answer ⟨seed,log⟩ input)).1 =
      (⟨seed,DuplexPublicSimulator.observe log input (seed input)⟩,seed input) := by
  rw [PublicCompressionCouplingMixed.primitiveCalls_actual,
    primitiveCalls_ordinary Q seed ro log auth input ordinary]

/-- All purposes are covered, rather than assuming a purpose identifies a
hash domain. There is no conclusion about construction or nonzero-role replies. -/
theorem mixed_compile_ordinary {R : Type} (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (program : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    PCSBCSMerkleSeedProjection.AuthenticObservations seed
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)).observations :=
  PCSBCSMerkleSeedProjection.compile_empty_authentic Q seed ro iv program remaining cap counted

/-- Actual ideal execution, starting from the simulator's actual empty log. -/
theorem runIdeal_initial_ordinary {R : Type} (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (program : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    PCSBCSMerkleSeedProjection.AuthenticObservations seed
      (runIdeal (DuplexPublicSimulator.simulator Q) ro iv
        ((DuplexPublicSimulator.simulator Q).initial seed)
        program remaining cap counted).view.observations := by
  have actual := mixed_compile_ordinary Q seed ro iv program remaining cap counted
  rw [PublicCompressionCouplingMixed.compile_actual] at actual
  exact actual

/-- Native acceptance's primitive-only consistency interface, derived rather
than supplied. Verification is just one of the purposes covered above. -/
theorem runIdeal_initial_answers {R : Type} (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (program : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    ∀ o ∈ (runIdeal (DuplexPublicSimulator.simulator Q) ro iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      program remaining cap counted).view.observations,
      ∀ input, o.query = .primitive .verification input → tag input = 0 → o.answer = seed input := by
  intro o member input query ordinary
  have eq : o = (⟨.primitive .verification input,o.answer⟩ : Observation) := by
    cases o
    simp_all
  have auth := runIdeal_initial_ordinary Q seed ro iv program remaining cap counted
  exact (auth .verification input o.answer (eq ▸ member) ordinary).symm

/-- Chronological folding retains only public primitive records, in newest
first cache order. Independent construction answers are never inserted. -/
theorem finalLog_ordinary (seed : DuplexPublicSimulator.Seed)
    (seen : List Observation) (auth : PCSBCSMerkleSeedProjection.AuthenticObservations seed seen)
    (log : DuplexPublicSimulator.PublicLog)
    (initial : PCSBCSMerkleSeedProjection.OrdinaryAuthentic seed log) :
    PCSBCSMerkleSeedProjection.OrdinaryAuthentic seed (DuplexPublicSimulator.finalLog log seen) := by
  induction seen generalizing log with
  | nil => exact initial
  | cons o rest ih =>
    have tail : PCSBCSMerkleSeedProjection.AuthenticObservations seed rest := by
      intro purpose input answer member
      exact auth purpose input answer (List.mem_cons_of_mem _ member)
    cases o with
    | mk query answer =>
      cases query with
      | primitive purpose input =>
        exact ih tail _ (PCSBCSMerkleSeedProjection.observe_preserves seed log initial input answer
          (auth purpose input answer (List.mem_cons_self)))
      | construction coordinate valid => exact ih tail log initial

/-- Every prefix, not just a completed run, has the same ordinary cache answer.
No consistency requirement is imposed on nonordinary records in that prefix. -/
theorem mixed_prefix_lookup {R : Type} (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (program : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program)
    (earlier : List Observation)
    (included : ∀ o ∈ earlier, o ∈
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)).observations)
    (input : Node) (answer : Digest32) (ordinary : tag input = 0)
    (hit : DuplexPublicSimulator.lookup (DuplexPublicSimulator.finalLog [] earlier) input = some answer) :
    answer = seed input := by
  have auth := PCSBCSMerkleSeedProjection.observations_prefix
    (mixed_compile_ordinary Q seed ro iv program remaining cap counted) included
  have logAuth := finalLog_ordinary seed earlier auth []
    (by simp [PCSBCSMerkleSeedProjection.OrdinaryAuthentic])
  exact (logAuth input answer (DuplexPublicSimulator.lookup_mem hit) ordinary).symm

/-- The first-record chronological Merkle interpreter agrees too, including
repeated queries. Its filtered log is authentic, but the full observed log is not
claimed to be authentic under Seed. -/
theorem mixed_chronological_log {R : Type} (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (program : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    PublicMerkleLog.AuthenticLog seed (PCSBCSMerkleSeedProjection.ordinaryObservations
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)).observations) :=
  PCSBCSMerkleSeedProjection.ordinaryObservations_authentic seed _
    (mixed_compile_ordinary Q seed ro iv program remaining cap counted)

/-- The counter bound follows the production recursion count+b.length, on
actual adaptive hash runs, not just on a predeclared seed-generated plan. -/
theorem hashFrom_trace_tag_zero {cv : Digest32} {count : Nat}
    {bs : List (List Byte)} {hne : bs ≠ []} {trace : List Observation} {digest : Digest32}
    (run : PublicMerkleProgram.Runs (PublicMerkleProgram.hashFrom cv count bs hne) trace digest)
    (bound : count + bs.flatten.length < 2^56) :
    ∀ o ∈ trace, ∃ input, o.query = .primitive .verification input ∧ tag input = 0 := by
  induction bs generalizing cv count trace digest with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil =>
      cases run with
      | ask answer run =>
        cases run
        intro o member
        have eq := List.mem_singleton.mp member
        subst o
        refine ⟨_,rfl,PublicMerkleLog.ordinary_tag_zero _ _ _ _ ?_⟩
        simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using bound
    | cons next rest =>
      cases run with
      | ask answer run =>
        have tailBound : count + b.length + (next :: rest).flatten.length < 2^56 := by
          simpa only [List.flatten_cons,List.length_append,Nat.add_assoc] using bound
        intro o member
        rcases List.mem_cons.mp member with rfl | prior
        · refine ⟨_,rfl,PublicMerkleLog.ordinary_tag_zero _ _ _ _ ?_⟩
          omega
        · exact ih run tailBound o prior

/-- Exact source precondition: total unpadded input byte length is below 2^56.
This covers the empty-input final block as well as every multi-block prefix. -/
theorem hash_trace_tag_zero {bytes : List Byte} {trace : List Observation} {digest : Digest32}
    (run : PublicMerkleProgram.Runs (PublicMerkleProgram.hash bytes) trace digest)
    (bound : bytes.length < 2^56) :
    ∀ o ∈ trace, ∃ input, o.query = .primitive .verification input ∧ tag input = 0 :=
  hashFrom_trace_tag_zero run
    (by simpa only [PublicMerkleLog.chunks_flatten,Nat.zero_add] using bound)

#print axioms node_tag_zero_iff_mod
#print axioms node_privateKey_none
#print axioms simulator_ordinary_answer
#print axioms mixed_compile_ordinary
#print axioms runIdeal_initial_answers
#print axioms mixed_prefix_lookup
#print axioms mixed_chronological_log
#print axioms hash_trace_tag_zero
end Whir.PCSBCSMixedOrdinaryMerkle
