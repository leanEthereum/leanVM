/-
  LeanVM.Protocol.Rpm.Embed

  The two calls of `Statement.lean` read on bytes keep the duplex discipline and the permutation
  calls: the pieces of the random-permutation transfer for any verifier (`Rpm.Generic`).
-/

module

public import LeanVM.Protocol.Rpm.Game
public import LeanVM.Protocol.Rpm.Duplex
public import LeanVM.Protocol.Rpm.Cost
public import LeanVM.Protocol.Rpm.RpmRelabel
public import Common.Lanes

@[expose] public section

/-!
# The transfer's embeddings

`common`'s two-oracle transfer (`Common.keccak256_transfer2`) reads its games on bytes. Here:
an admissible permutation call on lanes is admissible on bytes (`admissible_toRpm`), so a
computation that follows the duplex discipline on lanes follows `common`'s on bytes
(`duplex_toRHF`, and through a map, `duplex_map`); and the permutation calls of the adversary's
and the verifier's queries carry over to the game's (`isWeightBound_advEmbed`,
`isWeightBound_hfEmbed_toRHF`). These were proved for leanVM's verifier in the bus era
(`Protocol/LeanVMRpm.lean`, tag `formal-bus-archive`), and are stated here for any computation.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

/-- An admissible permutation call on lanes is admissible on bytes. -/
theorem admissible_toRpm {hist : List KeccakState} {x : KeccakState} (h : AdmissibleVm hist x) :
    Common.Admissible Common.KState.zero Common.keccakNF (hist.map KState.toRpm)
      (KState.toRpm x) := by
  rcases h with h | ⟨y, hy, h⟩
  · left
    have hk := keccakNF_of_keep x (Vector.replicate 25 0) fun i hi ↦ by simp [h i hi]
    rw [toRpm_zero] at hk
    exact hk
  · right
    exact ⟨KState.toRpm y, List.mem_map_of_mem hy, keccakNF_of_keep x y h⟩

/-- **The discipline on lanes is the discipline on bytes**: a computation over the calls of
`Statement.lean` (`KeccakCalls`) whose permutation calls follow the duplex discipline on lanes,
read on bytes, follows `common`'s duplex discipline (`Common.Duplex`, at the zero state, for the
non-final blocks `Common.keccakNF`). -/
theorem duplex_toRHF {β : Type} (V : OracleComp KeccakCalls β) (hist : List KeccakState)
    (hV : DuplexVm V hist) :
    Common.Duplex Common.KState.zero Common.keccakNF (simulateQ toRHF V)
      (hist.map KState.toRpm) := by
  induction V using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [duplexVm_query_bind] at hV
    rcases t with m | x
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHF,
        bind_map_left]
      intro d
      exact ih _ hist (hV _)
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHF,
        bind_map_left]
      refine ⟨admissible_toRpm hV.1, fun y ↦ ?_⟩
      have := ih (KState.ofRpm y) (KState.ofRpm y :: hist) (hV.2 _)
      rw [List.map_cons, toRpm_ofRpm] at this
      exact this

/-- A map keeps the duplex discipline. -/
theorem duplex_map {α β : Type} (f : α → β) (X : OracleComp HFSpec α)
    (hist : List Common.KState)
    (hX : Common.Duplex Common.KState.zero Common.keccakNF X hist) :
    Common.Duplex Common.KState.zero Common.keccakNF (f <$> X) hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [map_bind]
    rcases t with n | m | x
    · exact fun u ↦ ih u hist (hX u)
    · exact fun u ↦ ih u hist (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (y :: hist) (hX.2 y)⟩

/-- Weight bounds through a stateless simulation. -/
theorem isWeightBound_simulateQ' {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {α : Type} (impl : QueryImpl spec (OracleComp spec')) (w : ι → ℕ) (w' : ι' → ℕ)
    (h : ∀ t, Common.QueryCostAtMost (impl t) w' (w t)) {X : OracleComp spec α} {n : ℕ}
    (hX : Common.QueryCostAtMost X w n) : Common.QueryCostAtMost (simulateQ impl X) w' n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at hX
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    exact ((h t).bind fun u ↦ ih u (hX.2 u)).mono (by omega)

/-- The cost of the adversary's queries (`Common.queryCost`). -/
abbrev advCost : RSpec.Domain → ℕ :=
  Common.queryCost (Dg := Common.DigestBytes) (St := Common.KState) Common.keccakPadding

/-- The cost of the game's queries (`Common.queryCost2`): a hash of `n` bytes `⌊n / 136⌋ + 1`,
a permutation query or call one. -/
abbrev gameCost : D2Spec.Domain → ℕ := Common.queryCost2 (Dg := Common.DigestBytes) Common.keccakPadding

theorem isWeightBound_advEmbed {α : Type} {X : OracleComp RSpec α} {n : ℕ}
    (hX : Common.QueryCostAtMost X advCost n) :
    Common.QueryCostAtMost (simulateQ Common.advEmbed X) gameCost n := by
  refine isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hX
  rcases t with k | m | q
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inl k)
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inl m))
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inr (.inl q)))

theorem isWeightBound_hfEmbed_toRHF {β : Type} {V : OracleComp KeccakCalls β} {n : ℕ}
    (hV : Common.QueryCostAtMost V hashBlocks n) :
    Common.QueryCostAtMost (simulateQ Common.hfEmbed (simulateQ toRHF V)) gameCost n := by
  rw [← QueryImpl.simulateQ_compose]
  refine isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hV
  rcases t with m | x
  · simp only [QueryImpl.apply_compose, toRHF, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.hQuery, hq_eq, simulateQ_spec_query]
    have := Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inl m))
    rwa [show gameCost (.inr (.inl m)) = hashBlocks (.inl m) from Common.keccakPad_length m]
      at this
  · simp only [QueryImpl.apply_compose, toRHF, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.fQuery, hq_eq, simulateQ_spec_query]
    exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inr (.inr _)))

end LeanVM.Rpm

end
