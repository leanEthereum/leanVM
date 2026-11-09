/-
  LeanVM.Protocol.Rpm.RpmRelabel

  The random-permutation experiment of `Statement/LeanVm.lean`, on lane states, is the real world
  of `common`'s transfer game, on byte states.
-/

import LeanVM.Protocol.Rpm.Game
import Common.Keccak
import LeanVM.Protocol.WithHash

/-!
# The experiment on lanes is the real world on bytes

A uniformly random permutation of the lane states, read on bytes through `stateEquiv`, is a
uniformly random permutation of the byte states: the lazily sampled permutation on lanes
(`Common.lazyRandomPermutation` at `KState`) is the one on bytes (at `Common.KState`) with its edges read
on lanes (`lazyPerm_relabel`, `Common/Lanes.lean`). With Keccak-256 over the permutation on lanes being `common`'s sponge
over it (`keccak256With_rpm`), the experiment `rpmExperiment` (`Statement/LeanVm.lean`) of a
deterministic adversary (`detExperiment`, `Coins.lean`) is the real world `Common.realGame2` of the
transfer game `game` (`detExperiment_evalDistEq`), and so is the
completeness experiment (`rpmCompleteness_evalDistEq`).
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ## The real world of the game -/

/-- The real world of `common`'s two-oracle model: `H` the sponge over the lazily sampled
permutation, `π`, `π⁻¹` and `F = π` the permutation. -/
noncomputable abbrev RR : QueryImpl D2Spec (StateT (Common.PermutationEdges Common.KState) ProbComp) :=
  Common.realImpl Common.keccakPadding Common.KState.zero ∘ₛ Common.toOne

theorem RR_advEmbed_perm (q : Common.PermutationQuery Common.KState) :
    (RR ∘ₛ Common.advEmbed) (.inr (.inr q)) = Common.lazyRandomPermutation q := by
  simp [Common.advEmbed, Common.toOne, Common.realImpl]

theorem hq_eq {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] (t : ι) :
    Common.hq (hs := hs) t = (liftM ((unifSpec + hs).query (.inr t)) : OracleComp _ _) := rfl

theorem RR_hfEmbed_toRHF_F (x : KeccakState) :
    (RR ∘ₛ Common.hfEmbed ∘ₛ toRHF) (.inr x) =
      KState.ofRpm <$> Common.lazyRandomPermutation (.forward (KState.toRpm x)) := by
  simp [toRHF, hq_eq, Common.hfEmbed, Common.toOne, Common.realImpl]

theorem RR_hfEmbed_toRHF_H (m : Bytes) :
    (RR ∘ₛ Common.hfEmbed ∘ₛ toRHF) (.inl m) =
      Digest.ofRpm <$> Common.spongeWith Common.keccakPadding Common.KState.zero
        (fun x ↦ Common.lazyRandomPermutation (.forward x)) m := by
  simp [toRHF, hq_eq, Common.hfEmbed, Common.toOne, Common.realImpl]

/-! ## The verifier's queries -/

/-- `π` on lanes is the lane reading of `π` on bytes. -/
theorem perm_eq_lanePerm :
    (lazyPermutationForward : KeccakState → StateT (Common.PermutationEdges KeccakState) ProbComp KeccakState) =
      lanePerm (fun x ↦ KState.toRpm <$> lazyPermutationForward (KState.ofRpm x)) := by
  funext s
  simp only [lanePerm, Functor.map_map, ofRpm_toRpm, id_map']

/-- A forward query on bytes is the forward query on lanes, read on bytes. -/
theorem lazyPerm_fwd_rel (x : Common.KState) :
    StRel projLog (Common.lazyRandomPermutation (.forward x)) (KState.toRpm <$> lazyPermutationForward (KState.ofRpm x)) :=
  fwd_rel x

/-- **The verifier's queries on bytes in the real world are the verifier's queries in the
random-permutation experiment**, the permutation's edges read on lanes. -/
theorem post_relabel {β : Type} (X : OracleComp KeccakCalls β) (s : Common.PermutationEdges Common.KState) :
    Prod.map id projLog <$> (simulateQ (RR ∘ₛ Common.hfEmbed ∘ₛ toRHF) X).run s =ᵈ
      (simulateQ keccakCallsOverRandomPermutation X).run (projLog s) := by
  refine Common.map_run_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) projLog
    (fun _ _ _ _ _ ↦ trivial) (fun t s' _ ↦ ?_) X s trivial
  rcases t with m | x
  · rw [RR_hfEmbed_toRHF_H]
    change _ =ᵈ (keccak256With lazyPermutationForward m).run _
    rw [perm_eq_lanePerm, keccak256With_rpm]
    exact (StRel.map (absorbAll_rel _ _ lazyPerm_fwd_rel _ _) _).map _ s'
  · rw [RR_hfEmbed_toRHF_F]
    change _ =ᵈ (Common.lazyRandomPermutation (.forward x)).run _
    have h := lazyPerm_relabel stateEquiv (.forward x) s'
    simp only [mapQ, stateEquiv_apply] at h
    rw [StateT.run_map, Functor.map_map]
    exact h

/-! ## The adversary -/

/-- **The adversary on bytes with its transcript, in the real world, is the adversary of the
random-permutation experiment**, the permutation's edges read on lanes. -/
theorem adv_relabel {α : Type} (A : OracleComp (Common.permutationOracleSpec KeccakState) α) (s : Common.PermutationEdges Common.KState)
    (T : PermutationTranscript) :
    (fun p ↦ (p.1.1, (projLog p.2, p.1.2))) <$>
        (simulateQ (RR ∘ₛ Common.advEmbed) ((simulateQ logRel A).run T)).run s =ᵈ
      (simulateQ loggedPermDet A).run (projLog s, T) := by
  induction A using OracleComp.inductionOn generalizing s T with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact EvalDistEq.rfl
  | query_bind q k ih =>
    have hq : mapQ stateEquiv q = permQueryToRpm q := by cases q <;> rfl
    have hrel : simulateQ (RR ∘ₛ Common.advEmbed) (relP q) =
        KState.ofRpm <$> Common.lazyRandomPermutation (permQueryToRpm q) := by
      rw [relP, simulateQ_map, simulateQ_spec_query, RR_advEmbed_perm]
    simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query, logRel, loggedPermDet,
      loggedRandomPermutationOracles, StateT.run_mk, hrel, bind_map_left, map_bind]
    calc _ =ᵈ ((Common.lazyRandomPermutation (permQueryToRpm q)).run s >>= fun a ↦
            (simulateQ loggedPermDet (k (KState.ofRpm a.1))).run
              (projLog a.2, T ++ [(q, KState.ofRpm a.1)])) :=
          EvalDistEq.bind_right _ fun a ↦ ih _ _ _
      _ = ((Prod.map KState.ofRpm projLog <$> (Common.lazyRandomPermutation (permQueryToRpm q)).run s) >>=
            fun a ↦ (simulateQ loggedPermDet (k a.1)).run (a.2, T ++ [(q, a.1)])) := by
          rw [bind_map_left]; rfl
      _ =ᵈ _ := EvalDistEq.bind_left (by rw [← hq]; exact lazyPerm_relabel stateEquiv q s) _

/-! ## The experiments -/

theorem post_relabel' {β : Type} (X : OracleComp KeccakCalls β) (s : Common.PermutationEdges Common.KState) :
    (simulateQ (RR ∘ₛ Common.hfEmbed ∘ₛ toRHF) X).run' s =ᵈ
      (simulateQ keccakCallsOverRandomPermutation X).run' (projLog s) := by
  have h := (post_relabel X s).map Prod.fst
  simp only [Functor.map_map] at h
  simpa [StateT.run'_eq] using h

theorem realGame2_eq {δ : Type} (D : OracleComp D2Spec δ) :
    Common.realGame2 Common.keccakPadding Common.KState.zero D = (simulateQ RR D).run' [] := by
  rw [Common.realGame2, Common.realGame, QueryImpl.simulateQ_compose]

/-- **The random-permutation experiment is the real world of the transfer game.** -/
theorem detExperiment_evalDistEq (A : DetAdversary) :
    detExperiment A =ᵈ Common.realGame2 Common.keccakPadding Common.KState.zero (game A) := by
  rw [realGame2_eq, game, Common.rpmGame2]
  simp only [simulateQ_pure, pure_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  simp only [postR, simulateQ_map, StateT.run_map, Functor.map_map, RR,
    QueryImpl.simulateQ_compose]
  have hadv := (adv_relabel A [] []).symm
  simp only [projLog, logMap, List.map_nil, QueryImpl.simulateQ_compose] at hadv
  rw [detExperiment, advR]
  refine EvalDistEq.trans (EvalDistEq.bind_left hadv _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun p ↦ ?_
  have h := (post_relabel' (verifierWithHash callKeccak256 callKeccakF1600 p.1.1.1.1 p.1.1.1.2 p.1.1.2) p.2).symm.map
    fun v ↦ ((p.1.1, v), p.1.2)
  simp only [StateT.run'_eq, Functor.map_map, QueryImpl.simulateQ_compose, projLog, logMap] at h
  simp only [StateT.run'_eq, bind_pure_comp, Functor.map_map]
  exact h

/-- The completeness game: nothing before, no adversary, then the honest computation with the
hash and the direct permutation calls. -/
def honestGame {β : Type} (X : OracleComp KeccakCalls β) : OracleComp D2Spec β :=
  Common.rpmGame2 (pure ()) (fun _ ↦ (pure () : OracleComp RSpec Unit))
    (fun _ _ ↦ simulateQ toRHF X)

/-- **An honest computation in the random-permutation model is the real world of its game.** -/
theorem rpmHonest_evalDistEq {β : Type} (X : OracleComp KeccakCalls β) :
    (simulateQ keccakCallsOverRandomPermutation X).run' [] =ᵈ
      Common.realGame2 Common.keccakPadding Common.KState.zero (honestGame X) := by
  rw [realGame2_eq, honestGame, Common.rpmGame2]
  simp only [simulateQ_pure, pure_bind]
  have h := (post_relabel' X []).symm
  simp only [projLog, logMap, List.map_nil] at h
  refine h.trans ?_
  simp only [RR, QueryImpl.simulateQ_compose]
  exact EvalDistEq.rfl

end LeanVM.Rpm
