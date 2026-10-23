import Sphincs.BridgeDetInternalize
import Sphincs.BridgeReduce

/-! **The scheme seed.** Key generation hashes the key's seed `S0` into the scheme seed
`S = H(leanSPHINCS || S0)` and derives everything else from `S`. In the eager form of the
internalized game, swapping the table's answer at `leanSPHINCS || S0` with an independent uniform
value makes `S` uniform and independent of the table. The two tables then differ only at that one
input, which a run that does not depend on `S0` names with chance `2^-256` per hash call, so the game
is the game from a uniform scheme seed (`experimentMasterDet`) at the same budget, up to
`q / 2^256`. No input of the scheme needs to differ from `leanSPHINCS || S0`: every call that names
it is charged, honest or not. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Det

open Completeness SeedCoupling Short Internalize Eager Reduce

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-! ### Naming `S0` -/

theorem schemeSeedInput_injective : Function.Injective schemeSeedInput := fun seed seed' h => by
  unfold schemeSeedInput at h
  exact bytesLE_injective (List.append_cancel_left h)

theorem schemeSeedInput_probability_le (input : HashInput) :
    Pr{let seed ← sampleMasterSeed}[schemeSeedInput seed = input] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  letI := SampleableType.ofFintype MasterSeed
  rw [show sampleMasterSeed = ($ᵗ MasterSeed : ProbComp MasterSeed) from rfl,
    SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter fun seed => schemeSeedInput seed = input).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro seed hseed seed' hseed'
    exact schemeSeedInput_injective ((Finset.mem_filter.mp hseed).2.trans (Finset.mem_filter.mp hseed').2.symm)
  rw [show Fintype.card MasterSeed = 2 ^ 256 by simp, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

theorem probEvent_bind_le_add_const {α β : Type} (p : ProbComp α) (k k' : α → ProbComp β)
    (event event' : β → Prop) (c : ℝ≥0∞) (h : ∀ a, Pr{let x ← k a}[event x] ≤ Pr{let x ← k' a}[event' x] + c) :
    Pr{let x ← p >>= k}[event x] ≤ Pr{let x ← p >>= k'}[event' x] + c := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' a, (Pr{let x ← p}[x = a] * Pr{let x ← k' a}[event' x] + Pr{let x ← p}[x = a] * c) :=
      ENNReal.tsum_le_tsum fun a => (mul_le_mul' le_rfl (h a)).trans_eq (mul_add ..)
    _ = (∑' a, Pr{let x ← p}[x = a] * Pr{let x ← k' a}[event' x]) + ∑' a, Pr{let x ← p}[x = a] * c := ENNReal.tsum_add
    _ ≤ _ := by
      refine add_le_add le_rfl ?_
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le (OracleComp.tsum_prEvent_le_one _)

theorem probEvent_bind_le_bad {α β : Type} (p : ProbComp α) (k k' : α → ProbComp β)
    (event : β → Prop) (bad : α → Prop) (h : ∀ a, ¬bad a → k a = k' a) :
    Pr{let x ← p >>= k}[event x] ≤ Pr{let x ← p}[bad x] + Pr{let x ← p >>= k'}[event x] := by
  have hbind := probEvent_bind_le_add p k (fun a => (pure a : ProbComp α)) k' event bad event
    (fun a => by
      by_cases ha : bad a
      · rw [prEvent_pure, ite_eq_left ha]
        exact (prEvent_le_one _).trans le_self_add
      · rw [h a ha]
        exact le_add_self)
  rwa [bind_pure] at hbind

set_option linter.constructorNameAsVariable false in
/-- Reprogramming the fixed answer at `leanSPHINCS || S0`, for a uniform `S0`, moves the probability
of a budgeted event by at most `q / 2^256`. -/
theorem probEvent_update_seed_le {α : Type} (comp : OracleComp OracleWorld α)
    (F : HashInput → HashOutput) (u : HashOutput) (event : α → Prop) (q : ℕ) :
    Pr{let result ← (sampleMasterSeed >>= fun seed =>
        simulateQ (fixedRom (Function.update F (schemeSeedInput seed) u)) (countHashQueries comp))}[event result.1 ∧ result.2 ≤ q] ≤
      Pr{let result ← simulateQ (fixedRom F) (countHashQueries comp)}[event result.1 ∧ result.2 ≤ q] + q / (2 : ℝ≥0∞) ^ 256 := by
  induction comp using OracleComp.inductionOn generalizing event q with
  | pure value =>
      have hpure : ∀ G : HashInput → HashOutput,
          simulateQ (fixedRom G) (countHashQueries (pure value : OracleComp OracleWorld α)) = pure (value, 0) :=
        fun G => by rw [countHashQueries, SphincsBase.QueryCap.counted_pure, simulateQ_pure]
      simp only [hpure]
      exact probEvent_bind_le_of _ _ _ _ fun _ => le_self_add
  | query_bind input next ih =>
      simp only [countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rcases input with draw | input
      · simp only [fixedRom, reduceCtorEq, ite_false, zero_add, Prod.mk.eta, bind_pure]
        rw [(OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed _ _).prEvent_eq]
        exact probEvent_bind_le_add_const _ _ _ _ _ _ fun answer => ih answer event q
      · simp only [fixedRom, ite_true, pure_bind]
        rcases q with _ | q
        · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _
            fun result hresult hevent => ?_)) zero_le
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
          obtain ⟨seed, -, inner, -, rfl⟩ := hresult
          have h := hevent.2
          simp only at h
          omega
        · have hshift : ∀ (G : HashInput → HashOutput) (answer : HashOutput),
              Pr{let result ← (simulateQ (fixedRom G) (countHashQueries (next answer)) >>= fun result =>
                  pure (result.1, 1 + result.2))}[event result.1 ∧ result.2 ≤ q + 1] =
              Pr{let result ← simulateQ (fixedRom G) (countHashQueries (next answer))}[event result.1 ∧ result.2 ≤ q] := by
            intro G answer
            rw [bind_pure_comp, prEvent_map]
            refine prEvent_congr_of_support _ _ _ (fun result _ => ?_)
            simp only
            constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
          calc
            _ ≤ Pr{let seed ← sampleMasterSeed}[schemeSeedInput seed = input] +
                Pr{let result ← (sampleMasterSeed >>= fun seed =>
                  simulateQ (fixedRom (Function.update F (schemeSeedInput seed) u))
                    (countHashQueries (next (F input))) >>= fun result => pure (result.1, 1 + result.2))}[event result.1 ∧ result.2 ≤ q + 1] := by
              refine probEvent_bind_le_bad _ _ _ _ _ fun seed hseed => ?_
              rw [Function.update_of_ne (Ne.symm hseed)]
            _ = Pr{let seed ← sampleMasterSeed}[schemeSeedInput seed = input] +
                Pr{let result ← (sampleMasterSeed >>= fun seed =>
                  simulateQ (fixedRom (Function.update F (schemeSeedInput seed) u))
                    (countHashQueries (next (F input))))}[event result.1 ∧ result.2 ≤ q] := by
              refine congrArg (Pr{let seed ← sampleMasterSeed}[schemeSeedInput seed = input] + ·) ?_
              rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
              exact tsum_congr fun seed => by rw [hshift]
            _ ≤ 1 / (2 : ℝ≥0∞) ^ 256 + (Pr{let result ← simulateQ (fixedRom F) (countHashQueries (next (F input)))}[event result.1 ∧ result.2 ≤ q] + q / (2 : ℝ≥0∞) ^ 256) :=
              add_le_add (schemeSeedInput_probability_le input) (ih (F input) event q)
            _ = _ := by
              rw [hshift F (F input), Nat.cast_succ, ENNReal.add_div]
              exact (add_comm _ _).trans (add_assoc _ _ _)

/-! ### Swapping the answer at `leanSPHINCS || S0` -/

noncomputable local instance pointPairSampleable : SampleableType (Eager.Table × MasterSeed) :=
  SampleableType.ofFintype _

/-- Swap the table's answer at `point` with an independent value. -/
noncomputable def swapPoint (point : ShortIn) (pair : Eager.Table × MasterSeed) : Eager.Table × MasterSeed :=
  (Function.update pair.1 point pair.2, pair.1 point)

theorem swapPoint_involutive (point : ShortIn) : Function.Involutive (swapPoint point) := by
  rintro ⟨table, value⟩
  simp [swapPoint]

/-- A uniform table read at `point` is a uniform value, and the table updated there with it. -/
theorem evalDist_table_point {β : Type} (point : ShortIn) (H : MasterSeed → Eager.Table → ProbComp β) :
    (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table => H (table point) table) =ᵈ
      (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table => sampleMasterSeed >>= fun value =>
        H value (Function.update table point value)) := by
  letI : SampleableType MasterSeed := SampleableType.ofFintype MasterSeed
  have hfst : (Prod.fst <$> ($ᵗ (Eager.Table × MasterSeed) : ProbComp (Eager.Table × MasterSeed))) =ᵈ
      ($ᵗ Eager.Table : ProbComp Eager.Table) := fun p => by
    rw [prEvent_map, SampleableType.prEvent_uniformSample_inst_irrel _
      (instSampleableTypeProd Eager.Table MasterSeed)]
    exact SampleableType.prEvent_uniformSample_fst p
  have hswap : (swapPoint point <$> ($ᵗ (Eager.Table × MasterSeed) : ProbComp (Eager.Table × MasterSeed))) =ᵈ
      ($ᵗ (Eager.Table × MasterSeed) : ProbComp (Eager.Table × MasterSeed)) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective (swapPoint_involutive point).bijective
  have hpair := evalDist_independent_uniform_pair (α := Eager.Table) (β := MasterSeed)
  refine (hfst.bind_left (fun table => H (table point) table)).symm.trans ?_
  rw [bind_map_left]
  refine (hswap.bind_left (fun pair => H (pair.1 point) pair.1)).symm.trans ?_
  rw [bind_map_left]
  simp only [swapPoint, Function.update_self]
  refine (hpair.bind_left (fun pair => H pair.2 (Function.update pair.1 point pair.2))).symm.trans ?_
  simp only [bind_assoc, pure_bind]
  rfl

/-! ### The game -/

theorem evalDist_counted_eager {α : Type} (next : MasterSeed → OracleComp OracleWorld α)
    (h : ∀ seed, OnlyW (next seed)) :
    ((simulateQ countedOracle
      ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= next)).run.run' ∅) =ᵈ
      (sampleMasterSeed >>= fun seed => ($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table =>
        simulateQ (fixedRom (extend ∅ table)) (countHashQueries (next seed))) := by
  rw [← simulateQ_countHashQueries, countHashQueries_sampling_bind]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_lift_prob, bind_map_left, map_bind]
  refine EvalDistEq.bind_right _ fun seed => ?_
  exact evalDist_romImpl_eq_table _ (Assembly.OnlyW.counted _ _ (h seed)) ∅

theorem extend_empty_update (table : Eager.Table) (point : ShortIn) (value : HashOutput) :
    extend ∅ (Function.update table point value) = Function.update (extend ∅ table) point.1 value := by
  funext input
  by_cases hinput : input = point.1
  · subst hinput
    simp [extend, point.2]
  · rw [Function.update_of_ne hinput]
    simp only [extend]
    split
    · rename_i hshort
      rw [Function.update_of_ne (fun heq => hinput (congrArg Subtype.val heq))]
    · rfl

theorem schemeSeedInput_short (seed : MasterSeed) : IsShort (schemeSeedInput seed) := by
  simp [IsShort, bound, schemeSeedInput_length]

variable [Params]

/-- One fixed table: the game after `S0` is one hash call, then the game after `S`. -/
theorem fixed_gameAfterSeedDet (adversary : Adversary) (F : HashInput → HashOutput) (seed : MasterSeed) :
    simulateQ (fixedRom F) (countHashQueries (gameAfterSeedDet adversary seed)) =
      (fun result => (result.1, 1 + result.2)) <$>
        simulateQ (fixedRom F) (countHashQueries (gameAfterMasterDet adversary (F (schemeSeedInput seed)))) := by
  rw [gameAfterSeedDet_eq_master]
  change simulateQ (fixedRom F) (countHashQueries
    (liftM (OracleWorld.query (.inr (schemeSeedInput seed))) >>= gameAfterMasterDet adversary)) = _
  simp only [countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, fixedRom,
    ite_true, pure_bind, map_eq_bind_pure_comp]
  rfl

/-- **The scheme seed.** A budgeted win of the internalized game is a budgeted win of the game from
a uniform scheme seed, at the same budget, or a guess of `S0` among at most `q` hash calls. -/
theorem budgetedWin_le_master (adversary : Adversary) (q : ℕ) :
    Pr{let result ← experimentDet (internalize adversary)}[result.1 = true ∧ result.2 ≤ q] ≤
      Pr{let result ← experimentMasterDet (internalize adversary)}[result.1 = true ∧ result.2 ≤ q] + q / (2 : ℝ≥0∞) ^ 256 := by
  set game := gameAfterMasterDet (internalize adversary)
  set run : (HashInput → HashOutput) → MasterSeed → ProbComp (Bool × ℕ) :=
    fun F master => simulateQ (fixedRom F) (countHashQueries (game master)) with hrun
  have hnew : experimentDet (internalize adversary) =ᵈ
      (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table => sampleMasterSeed >>= fun master =>
        sampleMasterSeed >>= fun seed =>
          (fun result => (result.1, 1 + result.2)) <$>
            run (Function.update (extend ∅ table) (schemeSeedInput seed) master) master) := by
    rw [experimentDet, gameCoreDet_eq_sampling]
    refine (evalDist_counted_eager _ (OnlyW.gameAfterSeedDet_internalize adversary)).trans ?_
    conv_lhs => enter [2, seed, 2, table]; rw [fixed_gameAfterSeedDet]
    calc
      _ =ᵈ (sampleMasterSeed >>= fun seed => ($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table =>
            sampleMasterSeed >>= fun master =>
              (fun result => (result.1, 1 + result.2)) <$>
                run (Function.update (extend ∅ table) (schemeSeedInput seed) master) master) := by
        refine EvalDistEq.bind_right _ fun seed => ?_
        have h := evalDist_table_point ⟨schemeSeedInput seed, schemeSeedInput_short seed⟩
          (fun master table => (fun result => (result.1, 1 + result.2)) <$> run (extend ∅ table) master)
        simp only [extend_empty_update] at h
        refine EvalDistEq.trans ?_ h
        simp only [extend, dite_eq_left (schemeSeedInput_short seed), hrun]
        rfl
      _ =ᵈ _ := by
        refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
        refine EvalDistEq.bind_right _ fun table => ?_
        exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  have hold : experimentMasterDet (internalize adversary) =ᵈ
      (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table => sampleMasterSeed >>= fun master =>
        run (extend ∅ table) master) := by
    rw [experimentMasterDet, gameCoreMasterDet]
    exact (evalDist_counted_eager _ (OnlyW.gameAfterMasterDet_internalize adversary)).trans
      (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  rw [hnew.prEvent_eq, hold.prEvent_eq]
  refine probEvent_bind_le_add_const _ _ _ _ _ _ fun table => ?_
  refine probEvent_bind_le_add_const _ _ _ _ _ _ fun master => ?_
  refine le_trans (probEvent_bind_mono _ _ _ _ fun seed => ?_) (probEvent_update_seed_le (game master)
    (extend ∅ table) master (fun won => won = true) q)
  rw [prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun result _ hresult =>
    ⟨hresult.1, by have := hresult.2; simp only at this; omega⟩
