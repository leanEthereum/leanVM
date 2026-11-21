module

public import Common.Compose.Joint
public import Common.Lemmas
public import Common.Rerun

@[expose] public section

/-!
# The forger: the multi-key game is the joint world, the roles swapped

The forger against `k` keys of the scheme (`forger`) runs the composed adversary with the game's
permutation as `π_h`: its coins forwarded, its `π` lazily sampled by the forger with coins (and
recorded), its `π_h` asked of the game's `π`, its requests asked of the game's signing oracle (and
logged by the forger). It outputs the candidate of its own record and log.

`run_forgeryGame`: the multi-key forgery game against the forger is the joint world
(`jointOracles`), its second log the game's (`forger_step`, through `run_nest` and
`run_writerAsState`): the game's permutation is `π_h`, the forger's is `π`. The joint world
keeps both logs equal (`jointOracles_logs`), so a candidate that `π_h` accepts wins the game
(`prob_jointGame_le`). The forger makes the adversary's calls of `π_h` (`forger_permutationCost`)
and its requests to each key (`forger_requestCost`).
-/

open OracleComp OracleSpec
open scoped ENNReal
open LeanVM LeanVM.Node LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open Common.SufCma

namespace Common.Compose

variable {Seed PK SK Req Resp F : Type}

/-- The forger's oracles: the game's coins, `π` and `π⁻¹` (`π_h` to the composed adversary) and the
signing oracle. -/
abbrev ForgerOracles (k : ℕ) (Req Resp : Type) :=
  RandomPermutationOracles + (Fin k × Req →ₒ Resp)

/-- The forger's coins. -/
def forgerCoins (k : ℕ) (Req Resp : Type) :
    QueryImpl unifSpec (OracleComp (ForgerOracles k Req Resp)) :=
  fun n ↦ liftM ((ForgerOracles k Req Resp).query (.inl (.inl n)))

/-- The forger's state: `π`'s edges, `π`'s record and the request log. -/
abbrev ForgerState (k : ℕ) (Req Resp : Type) :=
  PermutationEdges KeccakState × PermutationRecord × RequestLog k Req Resp

/-- **The forger's answers** to the composed adversary: coins forwarded; `π` lazily sampled with
the game's coins and recorded; `π_h` asked of the game's `π`; a request asked of the game's
signing oracle and logged. -/
noncomputable def forgerOracles (k : ℕ) :
    QueryImpl (ComposedOracles k Req Resp)
      (StateT (ForgerState k Req Resp) (OracleComp (ForgerOracles k Req Resp)))
  | .inl (.inl (.inl n)) => StateT.lift (liftM ((ForgerOracles k Req Resp).query (.inl (.inl n))))
  | .inl (.inl (.inr q)) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2.1 ++ [(q, z.1)], s.2.2))) <$>
        simulateQ (forgerCoins k Req Resp) ((lazyRandomPermutation q).run s.1)
  | .inl (.inr q) => StateT.lift (liftM ((ForgerOracles k Req Resp).query (.inl (.inr q))))
  | .inr r => StateT.mk fun s ↦
      (fun u ↦ (u, (s.1, s.2.1, s.2.2 ++ [⟨r, u⟩]))) <$>
        liftM ((ForgerOracles k Req Resp).query (.inr r))

variable (scheme : Scheme Seed PK SK Req Resp F) (k : ℕ)
  (guest : LeanIsaProgram) (decoder : Cost.MachineProgram)
  (extractor : StraightLineExtractor) (raws : NodeWitness → List (PK × F))
  (deployedVerify : PK → F → Bool)

/-- **The forger**: the composed adversary run by the forger's answers from no edge, then the
candidate of its record and log, or `fallback` when there is none. -/
noncomputable def forger (fallback : Fin k × F) (A : ComposedAdversary k PK Req Resp)
    (pks : Fin k → PK) : OracleComp (ForgerOracles k Req Resp) (Fin k × F) :=
  (fun y ↦ (candidate scheme k guest decoder extractor raws deployedVerify
      (outcomeOf y.1 y.2.2.1) pks y.2.2.2).getD fallback) <$>
    (simulateQ (forgerOracles k) (A pks)).run ([], [], [])

/-! ## The forger's costs -/

/-- A step of the forger's answers weighs at most the query's weight, for a weight of the
forger's oracles that charges no coin, and charges `π_h` and the requests at most as `w`. -/
theorem forgerOracles_cost (w : (ComposedOracles k Req Resp).Domain → ℕ)
    (w' : (ForgerOracles k Req Resp).Domain → ℕ) (hc : ∀ n, w' (.inl (.inl n)) = 0)
    (hh : ∀ q, w' (.inl (.inr q)) ≤ w (.inl (.inr q))) (hr : ∀ r, w' (.inr r) ≤ w (.inr r))
    (t : (ComposedOracles k Req Resp).Domain) (s : ForgerState k Req Resp) :
    QueryCostAtMost ((forgerOracles k t).run s) w' (w t) := by
  rcases t with ((n | q) | q) | r
  · show QueryCostAtMost ((liftM ((ForgerOracles k Req Resp).query (.inl (.inl n))) :
      OracleComp _ _) >>= fun a ↦ pure (a, s)) _ _
    rw [bind_pure_comp]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by rw [hc n]; exact Nat.zero_le _))
  · show QueryCostAtMost (_ <$> simulateQ (forgerCoins k Req Resp) _) _ _
    exact isWeightBound_map _ ((isWeightBound_simulateQ (forgerCoins k Req Resp) (fun _ ↦ 0) w'
      (fun n ↦ (isWeightBound_query w' (.inl (.inl n))).mono (le_of_eq (hc n)))
      (QueryCostAtMost.zero_weight _)).mono (Nat.zero_le _))
  · show QueryCostAtMost ((liftM ((ForgerOracles k Req Resp).query (.inl (.inr q))) :
      OracleComp _ _) >>= fun a ↦ pure (a, s)) _ _
    rw [bind_pure_comp]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (hh q))
  · show QueryCostAtMost (_ <$> (liftM ((ForgerOracles k Req Resp).query (.inr r)) :
      OracleComp _ _)) _ _
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (hr r))

/-- **The forger makes the adversary's calls of `π_h`.** -/
theorem forger_permutationCost (fallback : Fin k × F) (A : ComposedAdversary k PK Req Resp)
    (qh : ℕ) (hqh : ∀ pks, QueryCostAtMost (A pks) piHCost qh) (pks : Fin k → PK) :
    QueryCostAtMost (forger scheme k guest decoder extractor raws deployedVerify fallback A pks)
      adversaryPermutationCost qh :=
  isWeightBound_map _ (isWeightBound_run_simulateQ _ piHCost _
    (forgerOracles_cost k piHCost adversaryPermutationCost (fun _ ↦ rfl) (fun _ ↦ le_rfl)
      (fun _ ↦ le_rfl)) (hqh pks) _)

/-- **The forger makes the adversary's requests to key `j`.** -/
theorem forger_requestCost (fallback : Fin k × F) (A : ComposedAdversary k PK Req Resp)
    (n : ℕ) (hn : ∀ pks j, QueryCostAtMost (A pks) (requestToKey j) n) (pks : Fin k → PK)
    (j : Fin k) :
    QueryCostAtMost (forger scheme k guest decoder extractor raws deployedVerify fallback A pks)
      (signingRequestToKeyCost j) n :=
  isWeightBound_map _ (isWeightBound_run_simulateQ _ (requestToKey j) _
    (forgerOracles_cost k (requestToKey j) (signingRequestToKeyCost j) (fun _ ↦ rfl)
      (fun _ ↦ Nat.zero_le _) (fun _ ↦ le_rfl)) (hn pks j) _)

/-! ## The forgery game is the joint world -/

/-- The forgery game's oracles for the `k` keys `sks`. -/
abbrev gameOracles (sks : Fin k → SK) :=
  QueryImpl.ofLift RandomPermutationOracles
      (WriterT (RequestLog k Req Resp) (OracleComp RandomPermutationOracles)) +
    QueryImpl.withLogging (spec := Fin k × Req →ₒ Resp) ((scheme.multiKey k).sign sks)

/-- The forger's three layers: its answers, the game's oracles, the game's permutation. -/
noncomputable def forgerWorld (sks : Fin k → SK) :
    QueryImpl (ComposedOracles k Req Resp)
      (StateT ((ForgerState k Req Resp × RequestLog k Req Resp) × PermutationEdges KeccakState)
        ProbComp) :=
  nest (nest (forgerOracles k) (writerAsState (gameOracles scheme k sks)))
    lazyRandomPermutationOracles

/-- The joint state of the forger's world: the forger's `π` is `π`, the game's is `π_h`. -/
def forgerProj (s : (ForgerState k Req Resp × RequestLog k Req Resp) ×
    PermutationEdges KeccakState) : JointState k Req Resp :=
  (s.1.1.1, s.2, s.1.1.2.1, s.1.1.2.2, s.1.2)

/-- A query lifted into the game's writer writes nothing. -/
theorem run_liftM_writer {ι : Type} {spec : OracleSpec.{0, 0} ι} {L : Type} [EmptyCollection L]
    [Append L] (t : spec.Domain) :
    (liftM (spec.query t) : WriterT L (OracleComp spec) _).run =
      (·, ∅) <$> (liftM (spec.query t) : OracleComp spec _) := rfl

/-- The forger's coins, through the game's oracles and permutation, keep their distribution. -/
theorem run_forgerCoins (sks : Fin k → SK) {α : Type} (p : ProbComp α) (l : RequestLog k Req Resp)
    (E : PermutationEdges KeccakState) :
    (simulateQ lazyRandomPermutationOracles ((simulateQ (writerAsState (gameOracles scheme k sks))
      (simulateQ (forgerCoins k Req Resp) p)).run l)).run E = (fun a ↦ ((a, l), E)) <$> p := by
  rw [run_nest, ← QueryImpl.simulateQ_compose, run_simulateQ_coins _ (fun n s ↦ ?_) p (l, E),
    Functor.map_map]
  simp only [QueryImpl.apply_compose, forgerCoins, simulateQ_spec_query]
  simp [nest, writerAsState, run_liftM_writer, lazyRandomPermutationOracles]

/-- **The forger's world, read through `forgerProj`, is the joint world.** -/
theorem forger_step (sks : Fin k → SK) (t : (ComposedOracles k Req Resp).Domain)
    (s : (ForgerState k Req Resp × RequestLog k Req Resp) × PermutationEdges KeccakState) :
    Prod.map id (forgerProj k) <$> (forgerWorld scheme k sks t).run s =
      (jointOracles scheme k sks t).run (forgerProj k s) := by
  rcases t with ((n | q) | q) | r
  · simp [forgerWorld, nest, forgerOracles, writerAsState, jointOracles, forgerProj,
      run_liftM_writer, lazyRandomPermutationOracles]
  · simp [forgerWorld, nest, forgerOracles, jointOracles, forgerProj, run_forgerCoins]
  · simp [forgerWorld, nest, forgerOracles, writerAsState, jointOracles, forgerProj,
      run_liftM_writer, lazyRandomPermutationOracles]
  · simp [forgerWorld, nest, forgerOracles, writerAsState, jointOracles, forgerProj,
      Scheme.multiKey]

/-- **The forgery game against the forger is the joint world**: the honest keys over the game's
permutation (`π_h`), the adversary answered by the joint world, then the forger's forgery verified
over `π_h` and judged on the game's log (the joint state's second log). -/
theorem run_forgeryGame (fallback : Fin k × F) (A : ComposedAdversary k PK Req Resp) :
    runWithRandomPermutation (forgeryGame (scheme.multiKey k)
        (forger scheme k guest decoder extractor raws deployedVerify fallback A)) =
      honestKeys scheme k >>= fun keys ↦
        (simulateQ (jointOracles scheme k keys.1.2) (A keys.1.1)).run ([], keys.2, [], [], []) >>=
          fun y ↦
            (fun v ↦ scheme.winningCondition (keyLog ((candidate scheme k guest decoder extractor
                raws deployedVerify (outcomeOf y.1 y.2.2.2.1) keys.1.1
                y.2.2.2.2.1).getD fallback).1 y.2.2.2.2.2) ((candidate scheme k guest decoder
                extractor raws deployedVerify (outcomeOf y.1 y.2.2.2.1) keys.1.1
                y.2.2.2.2.1).getD fallback).2 && v) <$>
              (simulateQ lazyRandomPermutationOracles (scheme.verify (keys.1.1 ((candidate scheme
                k guest decoder extractor raws deployedVerify (outcomeOf y.1 y.2.2.2.1) keys.1.1
                y.2.2.2.2.1).getD fallback).1) ((candidate scheme k guest decoder extractor raws
                deployedVerify (outcomeOf y.1 y.2.2.2.1) keys.1.1
                y.2.2.2.2.1).getD fallback).2)).run' y.2.2.1 := by
  unfold runWithRandomPermutation forgeryGame honestKeys
  rw [StateT.run'_eq]
  simp only [simulateQ_bind, StateT.run_bind, run_lazy_liftM, bind_map_left, map_bind, bind_assoc]
  refine bind_congr fun seeds ↦ bind_congr fun keys ↦ ?_
  obtain ⟨⟨pks, sks⟩, E⟩ := keys
  dsimp only
  have h := map_run_simulateQ_eq_of_query_map_eq_inv' (forgerWorld scheme k sks)
    (jointOracles scheme k sks) (fun _ ↦ True) (forgerProj k) (fun _ _ _ _ _ ↦ trivial)
    (fun t s _ ↦ forger_step scheme k sks t s) (A pks) ((([], [], []), ∅), E) trivial
  unfold forger
  rw [simulateQ_map, WriterT.run_map', run_eq_writerAsState, run_nest, simulateQ_map,
    simulateQ_map, StateT.run_map, StateT.run_map, run_nest]
  rw [show (([], E, [], [], []) : JointState k Req Resp) = forgerProj k ((([], [], []), ∅), E)
    from rfl, ← h]
  simp only [bind_map_left, Functor.map_map, StateT.run'_eq, simulateQ_pure, StateT.run_pure,
    map_pure]
  refine bind_congr fun a ↦ ?_
  rw [bind_pure_comp]
  rfl

/-- **The joint world keeps its two logs equal.** -/
theorem jointOracles_logs (sks : Fin k → SK) {α : Type}
    (X : OracleComp (ComposedOracles k Req Resp) α) (s : JointState k Req Resp)
    (hs : s.2.2.2.1 = s.2.2.2.2) :
    ∀ y ∈ support ((simulateQ (jointOracles scheme k sks) X).run s), y.2.2.2.2.1 = y.2.2.2.2.2 :=
  simulateQ_run_preserves_inv_of_query _ (fun s ↦ s.2.2.2.1 = s.2.2.2.2) (fun t s hs y hy ↦ by
    rcases t with ((n | q) | q) | r <;> simp [jointOracles] at hy <;>
      (first | (obtain ⟨_, _, rfl⟩ := hy) | (obtain ⟨_, _, _, rfl⟩ := hy)) <;> simp [hs]) X s hs

/-- A candidate is a candidate. -/
theorem isCandidate_of_candidate {o : ExperimentOutcome} {pks : Fin k → PK}
    {log : RequestLog k Req Resp} {j : Fin k} {f : F}
    (h : candidate scheme k guest decoder extractor raws deployedVerify o pks log = some (j, f)) :
    IsCandidate scheme k guest decoder extractor raws deployedVerify o pks log j f := by
  unfold candidate at h
  split_ifs at h with hc
  cases h
  exact hc.choose_spec.choose_spec

/-- **A candidate that `π_h` accepts wins the forgery game against the forger.** -/
theorem prob_jointGame_le (fallback : Fin k × F) (A : ComposedAdversary k PK Req Resp) :
    Pr{let z ← jointGame scheme k guest decoder extractor raws deployedVerify A}[
        z.1.isSome ∧ z.2 = true] ≤
      Pr{let b ← runWithRandomPermutation (forgeryGame (scheme.multiKey k)
        (forger scheme k guest decoder extractor raws deployedVerify fallback A))}[b = true] := by
  rw [run_forgeryGame]
  unfold jointGame
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun keys _ ↦ ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun y hy ↦ ?_
  have hlog := jointOracles_logs scheme k keys.1.2 (A keys.1.1) _ rfl y hy
  rcases hc : candidate scheme k guest decoder extractor raws deployedVerify
    (outcomeOf y.1 y.2.2.2.1) keys.1.1 y.2.2.2.2.1 with _ | ⟨j, f⟩
  · simp
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hwin⟩ :=
      isCandidate_of_candidate scheme k guest decoder extractor raws deployedVerify hc
    rw [hlog] at hwin
    simp [verdictRun, hwin]

end Common.Compose
