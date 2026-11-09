module

public import FORS.Reduction.WinValue

@[expose] public section

/-! **Seed elimination for the deterministic-randomizer game.** The SUF-CMA advantage against
`Seeded.sign` is at most the seed-free, budget-capped win probability of the internalized
memoizing adversary, plus `2 q / 2^256` for naming a hidden key value: `SK.seed` in a derivation
input or a key-seed input, or `SK.prf` in a randomizer-derivation input. The statement keeps
`3 q / 2^256`, its consumers' slack.

The eager table is split at `SK.prf`'s randomizer-derivation inputs into an independent uniform
randomizer table; the two runs agree until such an input is queried. Memoizing and then averaging
the randomizer table (one base `R0` per message, each read at most once) gives the fresh-randomizer cost game. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.Det

variable [Params]

open Completeness SeedCoupling Internalize Eager Short SeedModel Graph Assembly Stop HiddenCost
  GraphView Reduce DetValue

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-! ### Randomizer-derivation inputs -/

/-- This input derives a randomizer from the given `SK.prf`. -/
def RandHit (input : HashInput) (prf : HashOutput) : Prop :=
  ∃ parameter message, randomizerHashInput prf parameter message = input

theorem randHit_unique {input : HashInput} {prf prf' : HashOutput}
    (h : RandHit input prf) (h' : RandHit input prf') : prf = prf' := by
  obtain ⟨parameter, message, heq⟩ := h
  obtain ⟨parameter', message', heq'⟩ := h'
  exact (randomizerHashInput_injective (heq.trans heq'.symm)).1

theorem randHit_probability_le (input : HashInput) :
    Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[(RandHit input) x] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  rw [SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter (RandHit input)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro prf hprf prf' hprf'
    exact randHit_unique (Finset.mem_filter.mp hprf).2 (Finset.mem_filter.mp hprf').2
  rw [show Fintype.card HashOutput = 2 ^ 256 by simp [hashOutputBits], Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

/-- The inputs whose answers the seed-free run must not see. -/
def Marked (seed : MasterSeed) (prf : HashOutput) (input : HashInput) : Prop :=
  SeedGuess.SeedHit input seed ∨ RandHit input prf

/-- Ordinary entries of a trace. -/
def ordinaryCount : List (Entry HashInput) → Nat
  | [] => 0
  | .inl _ :: rest => ordinaryCount rest + 1
  | .inr _ :: rest => ordinaryCount rest

theorem ordinaryCount_le_traceCost (entries : List (Entry HashInput)) :
    ordinaryCount entries ≤ traceCost entries := by
  induction entries with
  | nil => simp [ordinaryCount, traceCost]
  | cons entry rest ih =>
      cases entry with
      | inl input => simp only [ordinaryCount, traceCost, List.map_cons, List.sum_cons, entryCost] at ih ⊢; omega
      | inr amount => simp only [ordinaryCount, traceCost, List.map_cons, List.sum_cons, entryCost] at ih ⊢; omega

theorem trace_marked_probability {S : Type} (secret : ProbComp S) (Bad : S → HashInput → Prop)
    (ε : ℝ≥0∞) (hε : ∀ input, Pr{let s ← secret}[Bad s input] ≤ ε)
    (entries : List (Entry HashInput)) :
    Pr{let s ← secret}[Hits (Bad s) entries] ≤ ordinaryCount entries * ε := by
  induction entries with
  | nil => simp [Hits, ordinaryCount]
  | cons entry rest ih =>
      cases entry with
      | inl input =>
          have hevent : (fun s => Hits (Bad s) (.inl input :: rest)) =
              fun s => Bad s input ∨ Hits (Bad s) rest := by
            funext s
            apply propext
            constructor
            · rintro ⟨x, hx, hm⟩
              rcases List.mem_cons.1 hx with heq | hx
              · cases heq
                exact Or.inl hm
              · exact Or.inr ⟨x, hx, hm⟩
            · rintro (hm | ⟨x, hx, hm⟩)
              · exact ⟨input, List.mem_cons_self, hm⟩
              · exact ⟨x, List.mem_cons_of_mem _ hx, hm⟩
          rw [hevent]
          refine (prEvent_or_le _ _ _).trans ?_
          refine (add_le_add (hε input) ih).trans (le_of_eq ?_)
          simp only [ordinaryCount, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          rw [add_comm]
      | inr amount =>
          have hevent : (fun s => Hits (Bad s) (.inr amount :: rest)) =
              fun s => Hits (Bad s) rest := by
            funext s
            apply propext
            constructor
            · rintro ⟨x, hx, hm⟩
              rcases List.mem_cons.1 hx with heq | hx
              · cases heq
              · exact ⟨x, hx, hm⟩
            · rintro ⟨x, hx, hm⟩
              exact ⟨x, List.mem_cons_of_mem _ hx, hm⟩
          rw [hevent]
          simpa only [ordinaryCount] using ih

/-- Naming a hidden secret, drawn independently of a run whose traces cost at most `q`, where each
input names it with probability at most `ε`. -/
theorem marked_hit_le {S Ω γ : Type} (secret : ProbComp S) (Bad : S → HashInput → Prop) (ε : ℝ≥0∞)
    (hε : ∀ input, Pr{let s ← secret}[Bad s input] ≤ ε) (program : ProbComp Ω)
    (entries : Ω → List (Entry HashInput)) (q : ℕ)
    (hcost : ∀ result ∈ support program, traceCost (entries result) ≤ q) (pack : S → Ω → γ)
    (event : γ → Prop) (hevent : ∀ s result, event (pack s result) → Hits (Bad s) (entries result)) :
    Pr{let x ← secret >>= fun s => pack s <$> program}[event x] ≤ q * ε := by
  calc
    _ = Pr{let x ← program >>= fun result => (fun s => pack s result) <$> secret}[event x] := by
      have h := OracleComp.EvalDistEq.bind_bind_swap secret program
        (fun s result => (pure (pack s result) : ProbComp _))
      simp only [bind_pure_comp] at h
      exact h.prEvent_eq _
    _ ≤ ∑' result, Pr{let x ← program}[x = result] * (q * ε) := by
      rw [OracleComp.prEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun result => ?_
      by_cases hr : result ∈ support program
      · refine mul_le_mul' le_rfl ?_
        rw [prEvent_map]
        refine (prEvent_mono_of_support _ _ _ fun s _ hs => hevent s result hs).trans ?_
        refine (trace_marked_probability secret Bad ε hε (entries result)).trans ?_
        refine mul_le_mul' ?_ le_rfl
        exact_mod_cast (ordinaryCount_le_traceCost _).trans (hcost result hr)
      · rw [(prEvent_eq_zero_of_not_mem_support _) hr]
        simp
    _ ≤ q * ε := tsum_prob_mul_le _ _

/-! ### Splitting the eager table at `SK.prf`'s randomizer-derivation inputs -/

/-- The short input deriving the randomizer base of `message`. -/
def randIn (prf : HashOutput) (parameter : PublicParameter) (message : Message) : ShortIn :=
  ⟨randomizerHashInput prf parameter message, randomizerHashInput_short prf parameter message⟩

theorem randIn_injective {prf : HashOutput} {parameter : PublicParameter} {message message' : Message}
    (h : randIn prf parameter message = randIn prf parameter message') :
    message = message' :=
  (randomizerHashInput_injective (congrArg Subtype.val h)).2.2

/-- The table with its randomizer-derivation entries for `(prf, parameter)` taken from `rnd`. -/
noncomputable def plant (prf : HashOutput) (parameter : PublicParameter) (table : Eager.Table)
    (rnd : RTable) : Eager.Table := fun input =>
  if h : ∃ message : Message, input = randIn prf parameter message then
    rnd (Classical.choose h)
  else table input

theorem plant_randIn (prf : HashOutput) (parameter : PublicParameter) (table : Eager.Table)
    (rnd : RTable) (message : Message) :
    plant prf parameter table rnd (randIn prf parameter message) = rnd message := by
  have h : ∃ message' : Message,
      randIn prf parameter message = randIn prf parameter message' := ⟨message, rfl⟩
  rw [plant, dite_eq_left h]
  rw [randIn_injective (Classical.choose_spec h).symm]

theorem plant_other (prf : HashOutput) (parameter : PublicParameter) (table : Eager.Table)
    (rnd : RTable) (input : ShortIn) (hinput : ∀ message, input ≠ randIn prf parameter message) :
    plant prf parameter table rnd input = table input := by
  rw [plant, dite_eq_right]
  rintro ⟨message, hmessage⟩
  exact hinput message hmessage

/-- Swap the randomizer entries of a table with an independent randomizer table. -/
noncomputable def swapPair (prf : HashOutput) (parameter : PublicParameter)
    (pair : Eager.Table × RTable) : Eager.Table × RTable :=
  (plant prf parameter pair.1 pair.2, fun message => pair.1 (randIn prf parameter message))

theorem swapPair_involutive (prf : HashOutput) (parameter : PublicParameter) :
    Function.Involutive (swapPair prf parameter) := by
  rintro ⟨table, rnd⟩
  simp only [swapPair, plant_randIn, Prod.mk.injEq, and_true]
  funext input
  by_cases h : ∃ message : Message, input = randIn prf parameter message
  · obtain ⟨message, rfl⟩ := h
    rw [plant_randIn]
  · have hother : ∀ message, input ≠ randIn prf parameter message :=
      fun message heq => h ⟨message, heq⟩
    rw [plant_other _ _ _ _ _ hother, plant_other _ _ _ _ _ hother]

noncomputable local instance pairSampleable : SampleableType (Eager.Table × RTable) :=
  SampleableType.ofFintype _

/-- A uniform table is a uniform table with its randomizer entries replaced by an independent
uniform randomizer table. -/
theorem evalDist_table_split {β : Type} (prf : HashOutput) (parameter : PublicParameter)
    (F : Eager.Table → ProbComp β) :
    (($ᵗ Eager.Table : ProbComp Eager.Table) >>= F) =ᵈ (do
        let table ← ($ᵗ Eager.Table : ProbComp Eager.Table)
        let rnd ← ($ᵗ RTable : ProbComp RTable)
        F (plant prf parameter table rnd)) := by
  have hfst : (Prod.fst <$> ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable))) =ᵈ
      ($ᵗ Eager.Table : ProbComp Eager.Table) := EvalDistEq.of_forall_prEvent_eq fun p => by
    rw [prEvent_map, SampleableType.prEvent_uniformSample_inst_irrel _
      (instSampleableTypeProd Eager.Table RTable)]
    exact SampleableType.prEvent_uniformSample_fst p
  have hswap : (swapPair prf parameter <$>
      ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable))) =ᵈ
      ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective
      (swapPair_involutive prf parameter).bijective
  have hpair := evalDist_independent_uniform_pair (α := Eager.Table) (β := RTable)
  refine (hfst.bind_left F).symm.trans ?_
  rw [bind_map_left]
  refine (hswap.bind_left (fun pair => F pair.1)).symm.trans ?_
  rw [bind_map_left]
  simp only [swapPair]
  refine (hpair.bind_left (fun pair => F (plant prf parameter pair.1 pair.2))).symm.trans ?_
  simp only [bind_assoc, pure_bind, EvalDistEq.refl]

/-! ### Splitting the randomizer table into base randomizers and step halves -/

/-- The step halves of a randomizer table. -/
def highsOf (rnd : RTable) : LTable := fun message => upperHash (rnd message)

theorem highsOf_joinTable (lows highs : LTable) : highsOf (joinTable lows highs) = highs := by
  funext message
  exact upperHash_joinHalves _ _

noncomputable local instance halvesSampleable : SampleableType (LTable × LTable) :=
  SampleableType.ofFintype _

/-- A uniform randomizer table is a uniform table of step halves and an independent uniform table
of base randomizers. -/
theorem evalDist_rtable_split {β : Type} (F : RTable → ProbComp β) :
    (($ᵗ RTable : ProbComp RTable) >>= F) =ᵈ (do
        let highs ← ($ᵗ LTable : ProbComp LTable)
        let lows ← ($ᵗ LTable : ProbComp LTable)
        F (joinTable lows highs)) := by
  have hjoin : ((fun pair : LTable × LTable => joinTable pair.1 pair.2) <$>
      ($ᵗ (LTable × LTable) : ProbComp (LTable × LTable))) =ᵈ ($ᵗ RTable : ProbComp RTable) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective joinTable_bijective
  have hpair := evalDist_independent_uniform_pair (α := LTable) (β := LTable)
  refine (hjoin.bind_left F).symm.trans ?_
  rw [bind_map_left]
  refine (hpair.bind_left (fun pair => F (joinTable pair.1 pair.2))).symm.trans ?_
  simp only [bind_assoc, pure_bind]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-! ### One sample -/

noncomputable local instance detLabelsSampleable' : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

theorem preparedCache_randomizer (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (prf : HashOutput) (parameter : PublicParameter) (message : Message) :
    preparedCache material seed answers (randomizerHashInput prf parameter message) = none := by
  rw [preparedCache_other material seed answers _ (fun position => ?_)]
  · rw [programCache_other ∅ seed material _ (fun h => ?_) (fun h => ?_) (fun position h => ?_)]
    · rfl
    · exact keySeedInput_ne_randomizerHashInput _ _ _ _ _ h.symm
    · exact keySeedInput_ne_randomizerHashInput _ _ _ _ _ h.symm
    · exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ h
  · refine randomizerHashInput_ne_tweakableHashInput _ _ _ _ _ ?_
    rw [List.length_flatMap]
    simp only [bytesLE_length, List.map_const', List.sum_replicate, smul_eq_mul]
    omega

theorem sampleFn_randomizer (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) (rnd : RTable) (message : Message) :
    sampleFn material seed answers (plant (prf material) (SeedModel.parameter material) table rnd)
      (randomizerHashInput (prf material) (SeedModel.parameter material) message) = rnd message := by
  unfold sampleFn extend
  rw [preparedCache_randomizer, Option.getD_none, dite_eq_left (randomizerHashInput_short _ _ _)]
  exact plant_randIn _ _ table rnd message

theorem sampleFn_plant_agree (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) (rnd : RTable) (input : HashInput) (hnot : ¬Marked seed (prf material) input) :
    sampleFn material seed answers (plant (prf material) (SeedModel.parameter material) table rnd) input =
      graphFn material answers table input := by
  rw [sampleFn_agree _ _ _ _ _ (fun h => hnot (Or.inl h))]
  unfold graphFn extend
  by_cases hshort : IsShort input
  · rw [dite_eq_left hshort, dite_eq_left hshort, plant_other (prf material) (SeedModel.parameter material) table rnd
      ⟨input, hshort⟩ fun message heq => hnot (Or.inr
        ⟨SeedModel.parameter material, message, (congrArg Subtype.val heq).symm⟩)]
  · rw [dite_eq_right hshort, dite_eq_right hshort]

/-! ### The whole game -/

theorem noRepeat_internalize_memoAdv (adversary : Adversary) :
    (Memo.memoAdv (internalize adversary)).NoRepeat := by
  rw [← Memo.internalize_memoAdv]
  exact ForsPotential.noRepeat_internalize_adversary _ (Memo.memoAdv_noRepeat adversary)

attribute [local irreducible] experiment sampleMasterSeed

end FORS.Security.Det
