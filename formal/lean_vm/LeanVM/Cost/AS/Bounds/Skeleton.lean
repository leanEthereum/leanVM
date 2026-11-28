module

public import LeanVM.Cost.AS.Bounds.Tactic
import all LeanVM.Protocol.EndToEnd.Sound.SkelDefs
import all LeanVM.Protocol.Extraction.AS.Lite
import all Statement.Verifier.Layout
import all Statement.Verifier.Link

/-!
# Bounds: the skeletons

The prices of the cut verifier's skeletons and of the lite extractor's decoders, at an admissible
layout (`LayOk`):

* the leaves (`skGrind_cost`, `skRound_cost`, `skSum_cost`, `skOod_cost`, `skRing_cost`, …), the
  opening (`skLevels_cost` by `skLevelsPrice`, `skWhir_cost`), the ladders' facts at every
  admissible shape by the kernel (`ladder_facts`, `ladder_dec`);
* the link (`skLink_cost`), the Keccak reduction (`skKeccak_cost`), and **`length_skBody`**
  (`≤ 40000`), **`packedSum_skBody`** (`≤ 1000`), **`skBody_cost`** (`≤ 10^9`);
* the decoders: `decLevelsP_cost` by `decLevelsPrice`, `decWhirCutP_cost`, **`decBodyL_cost`**
  (whatever the events), **`decSizesL_cost`** (`80·n + 8·|bytecode| + 10^10`).
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Extraction.AS LeanVM.Cost.Extractor
open LeanVM.Cost.Auto.LeanVM.Extraction.AS

public section

variable (P : MachineProgram)

/-! ## The body's skeleton -/

section Skeleton

open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Cost.Auto.LeanVM.Protocol.EndToEnd.Sound

/-- `grindingBits` (`grindingBits.c415`), a numerator below `2^128`: at most `1900`. -/
theorem grindingBits_cost (hP : Includes P Auto.LeanVM.Protocol.Compile.grindingBits.c415.costDeps)
    (n : ℕ) (hn : n < 2 ^ 128 := by omega) :
    machineCost P Auto.LeanVM.Protocol.Compile.grindingBits.c415.costIdx [encodeValue n] ≤ 1900 := by
  rw [Auto.LeanVM.Protocol.Compile.grindingBits.c415.costEq P hP]
  have hl1 : limbCount n ≤ 3 := limbs_le_wl (E := 128) (by omega)
  have hs : securityBits = 125 := rfl
  rw [hs, limbs_of_lt (by norm_num : (125 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : 128 - 125 < 2 ^ 64)]
  have hlog : Nat.log2 (n - 1) < 128 := by
    rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
    · rw [h0]; simp
    · exact (Nat.log2_lt (by omega)).2 (by omega)
  have hr := log2Rec_cost P (by includes) (n - 1) (by omega)
  split_ifs with h
  · simp only [limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64)]
    omega
  · rw [limbs_of_lt (by omega : Nat.log2 (n - 1) + 1 < 2 ^ 64),
      limbs_of_lt (by omega : Nat.log2 (n - 1) < 2 ^ 64)]
    simp only [max_self]
    nlinarith

theorem grindingBits_le (n : ℕ) (hn : n < 2 ^ 128) : grindingBits n ≤ 128 := by
  unfold grindingBits
  split_ifs
  · omega
  · have hlog : Nat.log2 (n - 1) < 128 := by
      rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
      · rw [h0]; simp
      · exact (Nat.log2_lt (by omega)).2 (by omega)
    omega

/-- A grind's skeleton (`skGrind.c400`): at most `11`. -/
theorem skGrind_cost (hP : Includes P skGrind.c400.costDeps) (bits : ℕ) (hb : bits < 2 ^ 64 := by omega) :
    machineCost P skGrind.c400.costIdx [encodeValue bits] ≤ 11 := by
  rw [skGrind.c400.costEq P hP, limbs_of_lt hb]
  split_ifs <;> omega

theorem length_skGrind (bits : ℕ) :
    (LeanVM.Protocol.EndToEnd.Sound.skGrind bits).length ≤ 1 := by
  unfold LeanVM.Protocol.EndToEnd.Sound.skGrind; split_ifs <;> simp

theorem length_skRound (count : ℕ) (b : Bool) :
    (LeanVM.Protocol.EndToEnd.Sound.skRound count b).length ≤ count + 2 := by
  cases b <;> simp only [LeanVM.Protocol.EndToEnd.Sound.skRound, List.length_cons,
    List.length_append, List.length_replicate] <;>
    have := length_skGrind (grindingBits (count - 1)) <;>
    have := length_skGrind (grindingBits (count - 1 + 1)) <;> omega

/-- A sumcheck round's skeleton (`skRound.c420`): at most `30·count + 2000`. -/
theorem skRound_cost (hP : Includes P skRound.c420.costDeps) (count : ℕ) (b : Bool)
    (hc : count < 2 ^ 60 := by omega) :
    machineCost P skRound.c420.costIdx [encodeValue count, encodeValue b] ≤ 30 * count + 2000 := by
  rw [skRound.c420.costEq P hP]
  have g1 := grindingBits_cost P (by includes) (count - 1) (by omega)
  have g2 := grindingBits_cost P (by includes) (count - 1 + 1) (by omega)
  have s1 := skGrind_cost P (by includes) (grindingBits (count - 1))
    (by have := grindingBits_le (count - 1) (by omega); omega)
  have s2 := skGrind_cost P (by includes) (grindingBits (count - 1 + 1))
    (by have := grindingBits_le (count - 1 + 1) (by omega); omega)
  cases b <;> dsimp only <;> cost_calls [] <;>
    simp only [List.length_cons, List.length_replicate] at * <;> omega

theorem length_skSum (count : ℕ) (eqs : List Bool) :
    (LeanVM.Protocol.EndToEnd.Sound.skSum count eqs).length ≤ eqs.length * (count + 3) := by
  unfold LeanVM.Protocol.EndToEnd.Sound.skSum
  induction eqs with
  | nil => simp
  | cons b eqs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_append, List.length_singleton,
      List.length_cons]
    have := length_skRound count b
    nlinarith

/-- A sumcheck's skeleton (`skSum.c418`): at most `(52·count + 2100)·|eqs| + 12`. -/
theorem skSum_cost (hP : Includes P skSum.c418.costDeps) (count : ℕ) (eqs : List Bool)
    (hc : count < 2 ^ 60 := by omega) :
    machineCost P skSum.c418.costIdx [encodeValue count, encodeValue eqs] ≤
      (52 * count + 2100) * eqs.length + 12 := by
  rw [skSum.c418.costEq P hP]
  have h1 := map_cost P (by includes) _ (.closure skSum.c418.lam0.costIdx [encodeValue count])
    (fun b ↦ RunsApp.of_spec (skSum.c418.lam0.costSpec P (by includes) count b))
    (41 * count + 2040) eqs (fun b _ ↦ by
      rw [appCost_fn, List.singleton_append, skSum.c418.lam0.costEq P (by includes)]
      have := skRound_cost P (by includes) count b hc
      have := append_cost P (by includes) (LeanVM.Protocol.EndToEnd.Sound.skRound count b)
        [LeanVM.Protocol.EndToEnd.Sound.Op.sample]
      have := length_skRound count b
      simp only [List.length_singleton]
      omega)
  have h2 := flatten_cost P (by includes) (count + 3)
    (List.map (fun b ↦ LeanVM.Protocol.EndToEnd.Sound.skRound count b ++
      [LeanVM.Protocol.EndToEnd.Sound.Op.sample]) eqs) (fun l hl ↦ by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hl
        have := length_skRound count b
        simp only [List.length_append, List.length_singleton]
        omega)
  simp only [List.length_map] at h2
  nlinarith

end Skeleton

section Skeleton2

open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Cost.Auto.LeanVM.Protocol.EndToEnd.Sound

/-- The protocol's constants the skeletons read. -/
theorem skConsts : keccakDepth = 12 ∧ keccakSegments = 2 ∧
    keccakSegmentBits = 1 ∧ keccakLaneBits = 5 ∧ keccakLocalBits = 11 ∧ qkeccakSlotBits = 6 ∧
    kBits = 64 ∧ ringMapWidth = 8 ∧ embedBits = 24 ∧ productBits = 47 ∧ opKeccak = 5 ∧
    Whir.oodGrindingBits = 15 ∧ Whir.batchGrindingBits = 13 ∧ Whir.foldGrindingBits = 7 ∧
    Whir.queryGrindingBits = 17 ∧ securityBits = 125 ∧ windowBits = 4 ∧ maxPointerWidth = 24 ∧
    bytecodeSlotBits = 4 ∧ nTables = 6 := by
  decide +kernel

theorem length_skOod (s : ℕ) : (skOod s).length = s + 2 := by
  simp [skOod, LeanVM.Protocol.EndToEnd.Sound.skGrind, Whir.oodGrindingBits]

/-- The out-of-domain sample's skeleton (`skOod.c399`). -/
theorem skOod_cost (hP : Includes P skOod.c399.costDeps) (s : ℕ) (hs : s < 2 ^ 60 := by omega) :
    machineCost P skOod.c399.costIdx [encodeValue s] ≤ 26 * s + 60 := by
  have hk := skConsts
  rw [skOod.c399.costEq P hP]
  cost_calls [skGrind_cost]
  len_facts [length_skGrind]
  omega

theorem length_skRing : skRing.length = 2 := by decide

/-- Ring switching's skeleton (`skRing.c426`): at most `300`. -/
theorem skRing_cost (hP : Includes P skRing.c426.costDeps) :
    machineCost P skRing.c426.costIdx [] ≤ 300 := by
  have hk := skConsts
  rw [skRing.c426.costEq P hP]
  cost_calls [skGrind_cost]
  len_facts [length_skGrind]
  omega

theorem length_skFoldRound : skFoldRound.length = 7 := by decide

/-- A fold round's skeleton (`skFoldRound.c430`): at most `200`. -/
theorem skFoldRound_cost (hP : Includes P skFoldRound.c430.costDeps) :
    machineCost P skFoldRound.c430.costIdx [] ≤ 200 := by
  have hk := skConsts
  rw [skFoldRound.c430.costEq P hP]
  cost_calls [skGrind_cost]
  len_facts [length_skGrind]
  omega

theorem length_skFoldRounds : ∀ n, (skFoldRounds n).length = 7 * n
  | 0 => rfl
  | n + 1 => by
    rw [skFoldRounds, List.length_append, length_skFoldRound, length_skFoldRounds n]; ring

/-- `n` fold rounds' skeleton (`skFoldRounds.c429`): at most `300·n + 5`. -/
theorem skFoldRounds_cost (hP : Includes P skFoldRounds.c429.costDeps) :
    ∀ n : ℕ, n < 2 ^ 60 → machineCost P skFoldRounds.c429.costIdx [encodeValue n] ≤ 300 * n + 5
  | 0, _ => by rw [skFoldRounds.c429.costEq P hP]; simp
  | n + 1, hn => by
    rw [skFoldRounds.c429.costEq P hP]
    dsimp only
    have := skFoldRounds_cost hP n (by omega)
    have := skFoldRound_cost P (by includes)
    have := append_cost P (by includes) skFoldRound (skFoldRounds n)
    rw [length_skFoldRound] at this
    rw [limbs_of_lt (by omega : n + 1 < 2 ^ 64)]
    omega

theorem productBits_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.productBits.c425.costDeps) :
    machineCost P Auto.LeanVM.Protocol.Verifier.productBits.c425.costIdx [] ≤ 5 := by
  have hk := skConsts
  rw [Auto.LeanVM.Protocol.Verifier.productBits.c425.costEq P hP]
  cost_calls []
  omega

theorem bitLength_cost' (hP : Includes P bitLengthC.costDeps) (n : ℕ) (hn : n < 2 ^ 64 := by omega) :
    machineCost P bitLengthC.costIdx [encodeValue n] ≤ 771 := bitLength_cost P hP n hn

theorem foldl_max_le (M : ℕ) : ∀ (hs : List ℕ) (a : ℕ), a ≤ M → (∀ x ∈ hs, x ≤ M) →
    hs.foldl max a ≤ M
  | [], _, ha, _ => ha
  | x :: hs, a, ha, h => foldl_max_le M hs (max a x) (max_le ha (h x (by simp)))
      (fun y hy ↦ h y (by simp [hy]))

theorem getD_le_of (hs : List ℕ) (i M : ℕ) (h : ∀ x ∈ hs, x ≤ M) : hs.getD i 0 ≤ M := by
  rcases getD_mem_or hs i 0 with hm | hm
  · exact h _ hm
  · rw [hm]; omega

theorem natCasesOn_one {C : ℕ → Sort _} (z : C 0) (f : ∀ n, C (n + 1)) :
    (Nat.casesOn 1 z f : C 1) = f 0 := rfl

theorem natCasesOn_zero {C : ℕ → Sort _} (z : C 0) (f : ∀ n, C (n + 1)) :
    (Nat.casesOn 0 z f : C 0) = z := rfl

/-! ### The opening's skeleton -/

theorem sqSamples_le (depth : ℕ) : ∀ fuel rem, sqSamples depth fuel rem ≤ fuel
  | 0, _ => le_rfl
  | fuel + 1, rem => by
    unfold sqSamples
    split_ifs
    · omega
    · have := sqSamples_le depth fuel (rem - min (128 / depth) rem); omega

/-- The query samples' count (`sqSamples.c432`): at most `31·fuel + 10`. -/
theorem sqSamples_cost (hP : Includes P sqSamples.c432.costDeps) (depth : ℕ) (hd : depth < 2 ^ 64) :
    ∀ fuel rem, fuel < 2 ^ 60 → rem < 2 ^ 64 →
      machineCost P sqSamples.c432.costIdx [encodeValue depth, encodeValue fuel, encodeValue rem] ≤
        31 * fuel + 10
  | 0, rem, _, _ => by rw [sqSamples.c432.costEq P hP]; simp
  | fuel + 1, rem, hf, hr => by
    rw [sqSamples.c432.costEq P hP]
    dsimp only
    have hsub : rem - min (128 / depth) rem ≤ rem := Nat.sub_le _ _
    have := sqSamples_cost hP depth hd fuel (rem - min (128 / depth) rem) (by omega) (by omega)
    have := sqSamples_le depth fuel (rem - min (128 / depth) rem)
    have : 128 / depth ≤ 128 := Nat.div_le_self _ _
    have : min (128 / depth) rem ≤ 128 := (min_le_left _ _).trans this
    rw [limbs_of_lt (by omega : fuel + 1 < 2 ^ 64), limbs_of_lt hr, limbs_of_lt hd,
      limbs_of_lt (by omega : 128 / depth < 2 ^ 64),
      limbs_of_lt (by omega : min (128 / depth) rem < 2 ^ 64),
      limbs_of_lt (by omega : 1 + sqSamples depth fuel (rem - min (128 / depth) rem) < 2 ^ 64),
      limbs_of_lt (by omega : sqSamples depth fuel (rem - min (128 / depth) rem) < 2 ^ 64)]
    split_ifs <;> omega

/-- A level's commitment shape (`levelShape.c398`): at most `11`. -/
theorem levelShape_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.levelShape.c398.costDeps)
    (m : ℕ) (l : Whir.Level) (w : ℕ) (hm : m < 2 ^ 60 := by omega) (hf : l.fold < 2 ^ 60 := by omega)
    (hr : l.logInvRate < 2 ^ 60 := by omega) :
    machineCost P Auto.LeanVM.Protocol.Verifier.levelShape.c398.costIdx [encodeValue m, encodeValue l,
      encodeValue w] ≤ 11 := by
  rw [Auto.LeanVM.Protocol.Verifier.levelShape.c398.costEq P hP]
  cost_calls []
  omega

/-- A level's facts the skeleton's prices need. -/
@[expose] def LevelOk (l : Whir.Level) : Prop := l.fold < 50 ∧ l.logInvRate < 50 ∧ l.queries < 2 ^ 20

instance (l : Whir.Level) : Decidable (LevelOk l) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem length_skMidTail (logN A : ℕ) (l n : Whir.Level) :
    (skMidTail logN A l n).length ≤ l.fold + logN + l.queries + 8 := by
  have := sqSamples_le (logN - A + l.logInvRate) l.queries l.queries
  have := length_skGrind Whir.oodGrindingBits
  have := length_skGrind Whir.queryGrindingBits
  simp only [skMidTail, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at *
  omega

/-- A level's tail's skeleton (`skMidTail.c431`). -/
theorem skMidTail_cost (hP : Includes P skMidTail.c431.costDeps) (logN A : ℕ) (l n : Whir.Level)
    (hN : logN < 2 ^ 20) (hA : A < 2 ^ 60) (hl : LevelOk l) (hn : LevelOk n) :
    machineCost P skMidTail.c431.costIdx [encodeValue logN, encodeValue A, encodeValue l,
      encodeValue n] ≤ 150 * (l.fold + logN + l.queries) + 1000 := by
  have hk := skConsts
  obtain ⟨hl1, hl2, hl3⟩ := hl
  obtain ⟨hn1, hn2, hn3⟩ := hn
  have hsq := sqSamples_le (logN - A + l.logInvRate) l.queries l.queries
  have hs := sqSamples_cost P (by includes) (logN - A + l.logInvRate) (by omega) l.queries l.queries
    (by omega) (by omega)
  have h2 : 2 ^ n.fold < 2 ^ 50 := Nat.pow_lt_pow_right (by norm_num) hn1
  rw [skMidTail.c431.costEq P hP]
  simp only [Nat.one_shiftLeft]
  cost_calls [skGrind_cost]
  len_facts [length_skGrind]
  omega

/-- A price of `skLevels` (`skLevels.c428`) from `A` folds made. -/
@[expose] def skLevelsPrice (logN : ℕ) : ℕ → List Whir.Level → ℕ
  | _, [] => 3
  | A, [l] => 377 * l.fold + 15 * (2 ^ (logN - (A + l.fold)) + l.fold) + 40
  | A, l :: n :: rest => 377 * l.fold + (150 * (l.fold + logN + l.queries) + 1000) +
      11 * (8 * l.fold + logN + l.queries + 8) + skLevelsPrice logN (A + l.fold) (n :: rest) + 50

/-- **The levels' skeleton** (`skLevels.c428`): at most `skLevelsPrice`. -/
theorem skLevels_cost (hP : Includes P skLevels.c428.costDeps) (logN : ℕ) (hN : logN < 50) :
    ∀ (levels : List Whir.Level) (A : ℕ), (∀ l ∈ levels, LevelOk l) →
      A + 50 * levels.length < 2 ^ 40 →
      machineCost P skLevels.c428.costIdx [encodeValue logN, encodeValue A, encodeValue levels] ≤
        skLevelsPrice logN A levels
  | [], A, _, _ => by rw [skLevels.c428.costEq_nil P hP]; rfl
  | [l], A, hl, hA => by
    obtain ⟨hl1, hl2, hl3⟩ := hl l (by simp)
    simp only [List.length_singleton] at hA
    have h2' : 2 ^ (logN - (A + l.fold)) < 2 ^ 50 :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [skLevels.c428.costEq_cons P hP]
    dsimp only
    simp only [Nat.one_shiftLeft]
    have := skFoldRounds_cost P (by includes) l.fold (by omega)
    cost_calls []
    have := length_skFoldRounds l.fold
    unfold skLevelsPrice
    omega
  | l :: n :: rest, A, hl, hA => by
    have hl' := hl l (by simp)
    have hn' := hl n (by simp)
    obtain ⟨hl1, hl2, hl3⟩ := hl'
    simp only [List.length_cons] at hA
    rw [skLevels.c428.costEq_cons P hP]
    dsimp only
    have h1 := skFoldRounds_cost P (by includes) l.fold (by omega)
    have h2 := skMidTail_cost P (by includes) logN (A + l.fold) l n (by omega) (by omega)
      ⟨hl1, hl2, hl3⟩ hn'
    have h3 := skLevels_cost hP logN hN (n :: rest) (A + l.fold)
      (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons]; omega)
    have h4 := length_skFoldRounds l.fold
    have h5 := length_skMidTail logN (A + l.fold) l n
    cost_calls []
    simp only [List.length_append] at *
    unfold skLevelsPrice
    omega

/-- The stack's commitment's skeleton (`skCommitStack.c397`): at most `3600`. -/
theorem skCommitStack_cost (hP : Includes P skCommitStack.c397.costDeps) (logN ρ : ℕ)
    (hN : logN < 2 ^ 60) (hρ : ρ < 2 ^ 60) :
    machineCost P skCommitStack.c397.costIdx [encodeValue logN, encodeValue ρ] ≤ 3600 := by
  rw [skCommitStack.c397.costEq P hP]
  have hl := ladder_cost P (by includes) logN ρ (by omega) (by omega)
  rcases h : Whir.ladder logN ρ with _ | lv
  · dsimp only; omega
  · rcases lv with _ | ⟨l, rest⟩
    · dsimp only; omega
    · dsimp only
      obtain ⟨h1, h2⟩ := ladder_head h
      have h6 : l.fold = 6 := h1
      simp only [Nat.one_shiftLeft]
      have := levelShape_cost P (by includes) logN l (2 ^ l.fold) (by omega) (by omega) (by omega)
      rw [h6]
      rw [h6] at this
      cost_calls []
      omega

theorem length_skCommitStack (logN ρ : ℕ) : (skCommitStack logN ρ).length ≤ 1 := by
  unfold skCommitStack
  split <;> simp

theorem ladder_some_bounds {μ ρ : ℕ} {lv : List Whir.Level} (h : Whir.ladder μ ρ = some lv) :
    μ < 31 ∧ ρ < 5 := by
  unfold Whir.ladder at h
  split_ifs at h with ha
  · obtain ⟨-, h2, -, h4⟩ := ha
    exact ⟨by unfold Whir.maxLogStack at h2; omega, by omega⟩

/-- The ladders' facts at every admissible shape, by the kernel. -/
theorem ladder_facts_all : ∀ μ < 31, ∀ ρ < 5, (Whir.ladder μ ρ).all (fun lv ↦
    decide ((∀ l ∈ lv, LevelOk l) ∧ lv.length ≤ 6 ∧ skLevelsPrice μ 0 lv ≤ 110000 ∧
      (skLevels μ 0 lv).length ≤ 410)) = true := by
  decide +kernel

theorem ladder_facts {μ ρ : ℕ} {lv : List Whir.Level} (h : Whir.ladder μ ρ = some lv) :
    (∀ l ∈ lv, LevelOk l) ∧ lv.length ≤ 6 ∧ skLevelsPrice μ 0 lv ≤ 110000 ∧
      (skLevels μ 0 lv).length ≤ 410 := by
  obtain ⟨h1, h2⟩ := ladder_some_bounds h
  have := ladder_facts_all μ h1 ρ h2
  rw [h] at this
  simpa using this

theorem length_skWhir (μ ρ : ℕ) : (skWhir μ ρ).length ≤ 410 := by
  unfold skWhir
  split
  · next lv h => exact (ladder_facts h).2.2.2
  · simp

/-- **The opening's skeleton** (`skWhir.c427`): at most `113600`. -/
theorem skWhir_cost (hP : Includes P skWhir.c427.costDeps) (μ ρ : ℕ) (hμ : μ < 2 ^ 64)
    (hρ : ρ < 2 ^ 64) :
    machineCost P skWhir.c427.costIdx [encodeValue μ, encodeValue ρ] ≤ 113600 := by
  rw [skWhir.c427.costEq P hP]
  have hl := ladder_cost P (by includes) μ ρ hμ hρ
  rcases h : Whir.ladder μ ρ with _ | lv
  · dsimp only; omega
  · dsimp only
    obtain ⟨h1, h2, h3, -⟩ := ladder_facts h
    have hb := ladder_some_bounds h
    have := skLevels_cost P (by includes) μ (by omega) lv 0 h1 (by omega)
    omega

/-! ### The decoders -/

/-- `List.mapM` with `Option` (`mapM.loop.c392`): the closure's price and `43` per element, `11` per
element of the accumulator, `10`. -/
theorem mapMLoop_cost (hP : Includes P Auto.List.mapM.loop.c392.costDeps) {α β : Type}
    [MachineEncoding α] [MachineEncoding β] (f : α → Option β) (fVal : MachineValue)
    (hf : ∀ a, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ)
    (hB : ∀ a : α, appCost P fVal [encodeValue a] ≤ B) :
    ∀ (xs : List α) (acc : List β),
      machineCost P Auto.List.mapM.loop.c392.costIdx [fVal, encodeValue xs, encodeValue acc] ≤
        (B + 43) * xs.length + 11 * acc.length + 10
  | [], acc => by
    rw [Auto.List.mapM.loop.c392.costEq_nil P hP f fVal hf]
    have := reverseAux_cost P (by includes) acc []
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
    omega
  | x :: xs, acc => by
    rw [Auto.List.mapM.loop.c392.costEq_cons P hP f fVal hf]
    have h1 := hB x
    have h2 := bind_cost P (by includes) _ (.closure 393 [encodeValue xs, fVal, encodeValue acc])
      (fun b ↦ RunsApp.of_spec (Auto.List.mapM.loop.c392.lam0.costSpec P (by includes) xs f fVal hf
        acc b)) ((B + 43) * xs.length + 11 * acc.length + 32) (fun b ↦ by
          rw [appCost_fn, show (393 : ℕ) = Auto.List.mapM.loop.c392.lam0.costIdx from rfl]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [Auto.List.mapM.loop.c392.lam0.costEq P (by includes) xs f fVal hf]
          have := mapMLoop_cost hP f fVal hf B hB xs (b :: acc)
          simp only [List.length_cons] at this
          omega) (f x)
    simp only [List.length_cons]
    have : (B + 43) * (xs.length + 1) = (B + 43) * xs.length + B + 43 := by ring
    omega

/-- The reads' values (`mapM` with `decSizesLC.lam1`): `45` per event, `10`. -/
theorem mapMReads_cost (hP : Includes P Auto.List.mapM.loop.c392.costDeps)
    (h1 : Includes P decSizesLC.lam1.costDeps) (xs : List EvP) :
    machineCost P Auto.List.mapM.loop.c392.costIdx [.closure decSizesLC.lam1.costIdx [],
      encodeValue xs, encodeValue ([] : List E)] ≤ 45 * xs.length + 10 := by
  have := mapMLoop_cost P hP (fun p : EvP ↦ p.1) (.closure decSizesLC.lam1.costIdx [])
    (fun p ↦ RunsApp.of_spec (decSizesLC.lam1.costSpec P h1 p)) 2 (fun p ↦ by
      rw [appCost_fn, List.nil_append, decSizesLC.lam1.costEq P h1]; rfl) xs []
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at this
  omega

theorem listCases_le {α : Type} (l : List α) (a b : ℕ) :
    (List.casesOn l a (fun _ _ ↦ b) : ℕ) ≤ max a b := by
  cases l <;> simp

theorem listRec_le {α : Type} (l : List α) (a b : ℕ) :
    (List.rec a (fun _ _ _ ↦ b) l : ℕ) ≤ max a b := by
  cases l <;> simp

/-- A fold round's challenges (`decRoundP.c442`): at most `200`. -/
theorem decRoundP_cost (hP : Includes P decRoundP.c442.costDeps) (h : List EvP) :
    machineCost P decRoundP.c442.costIdx [encodeValue h] ≤ 200 := by
  have hk := skConsts
  rw [decRoundP.c442.costEq P hP]
  have hg : (skGrind Whir.foldGrindingBits).length = 1 := by decide
  have b1 := bind_cost P (by includes) _ (.closure decRoundP.c442.lam0.lam1.costIdx [])
    (fun p ↦ RunsApp.of_spec (decRoundP.c442.lam0.lam1.costSpec P (by includes) p)) 2 (fun p ↦ by
      rw [appCost_fn, List.nil_append, decRoundP.c442.lam0.lam1.costEq P (by includes)]; rfl)
    (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h).head?
  have b2 := bind_cost P (by includes) _ (.closure decRoundP.c442.lam0.costIdx
      [encodeValue (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)])
    (fun a ↦ RunsApp.of_spec (decRoundP.c442.lam0.costSpec P (by includes) _ a)) 58 (fun a ↦ by
      rw [appCost_fn, List.singleton_append, decRoundP.c442.lam0.costEq P (by includes)]
      have := drop_cost P (by includes) 1 (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)
        (by norm_num)
      have := bind_cost P (by includes) _ (.closure decRoundP.c442.lam0.lam1.costIdx [])
        (fun p ↦ RunsApp.of_spec (decRoundP.c442.lam0.lam1.costSpec P (by includes) p)) 2 (fun p ↦ by
          rw [appCost_fn, List.nil_append, decRoundP.c442.lam0.lam1.costEq P (by includes)]; rfl)
        (List.drop 1 (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)).head?
      have := optionMap_cost P (by includes) _ (.closure decRoundP.c442.lam0.lam0.costIdx
          [encodeValue a])
        (fun b ↦ RunsApp.of_spec (decRoundP.c442.lam0.lam0.costSpec P (by includes) a b)) 6
        ((List.drop 1 (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)).head?.bind
          fun p ↦ p.2) (fun b _ ↦ by
          rw [appCost_fn, List.singleton_append, decRoundP.c442.lam0.lam0.costEq P (by includes)]
          rfl)
      have := listRec_le (List.drop 1 (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h)) 1 5
      simp only [List.length_singleton]
      omega) ((List.drop (4 + (skGrind Whir.foldGrindingBits).length) h).head?.bind fun p ↦ p.2)
  have := skGrind_cost P (by includes) Whir.foldGrindingBits
  have := length_cost P (by includes) (skGrind Whir.foldGrindingBits) (by omega)
  have := drop_cost P (by includes) (4 + (skGrind Whir.foldGrindingBits).length) h (by omega)
  have := listCases_le (List.drop (4 + (skGrind Whir.foldGrindingBits).length) h) 1 5
  rw [hg] at *
  rw [limbs_of_lt (by norm_num : 4 + 1 < 2 ^ 64), limbs_of_lt (by norm_num : 1 < 2 ^ 64)]
  omega

/-- The fold rounds' challenges (`decRoundsP.c439`): at most `(500·n + 1100)·n + 7`. -/
theorem decRoundsP_cost (hP : Includes P decRoundsP.c439.costDeps) :
    ∀ (n : ℕ) (h : List EvP), n < 2 ^ 30 →
      machineCost P decRoundsP.c439.costIdx [encodeValue n, encodeValue h] ≤ (500 * n + 1100) * n + 7
  | 0, h, _ => by rw [decRoundsP.c439.costEq P hP]; simp
  | k + 1, h, hk => by
    rw [decRoundsP.c439.costEq P hP]
    dsimp only
    have h1 := skFoldRound_cost P (by includes)
    have h2 := decRoundP_cost P (by includes) (List.take skFoldRound.length h)
    have h3 := bind_cost P (by includes) _ (.closure 441 [encodeValue k, encodeValue h])
      (fun r ↦ RunsApp.of_spec (decRoundsP.c439.lam1.costSpec P (by includes) k h r))
      ((500 * k + 1100) * k + 7 + 500 * k + 450) (fun r ↦ by
        rw [appCost_fn, show (441 : ℕ) = decRoundsP.c439.lam1.costIdx from rfl]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [decRoundsP.c439.lam1.costEq P (by includes)]
        have := skFoldRounds_cost P (by includes) k (by omega)
        have := skFoldRound_cost P (by includes)
        have := decRoundsP_cost hP k (List.take (skFoldRounds k).length (List.drop skFoldRound.length h))
          (by omega)
        have := optionMap_cost P (by includes) _ (.closure decRoundsP.c439.lam0.costIdx [encodeValue r])
          (fun rs ↦ RunsApp.of_spec (decRoundsP.c439.lam0.costSpec P (by includes) r rs)) 6
          (decRoundsP k (List.take (skFoldRounds k).length (List.drop skFoldRound.length h)))
          (fun rs _ ↦ by
            rw [appCost_fn, List.singleton_append, decRoundsP.c439.lam0.costEq P (by includes)]; rfl)
        have := length_skFoldRounds k
        have := length_skFoldRound
        cost_calls []
        omega) (decRoundP (List.take skFoldRound.length h))
    have := length_skFoldRound
    cost_calls []
    have : (500 * (k + 1) + 1100) * (k + 1) = (500 * k + 1100) * k + 1000 * k + 1600 := by ring
    omega

/-- A level's high part (`decHighP.c448`): at most `64·fold + 43`. -/
theorem decHighP_cost (hP : Includes P decHighP.c448.costDeps) (fold : ℕ) (h : List EvP)
    (hf : fold < 2 ^ 30) :
    machineCost P decHighP.c448.costIdx [encodeValue fold, encodeValue h] ≤ 64 * fold + 43 := by
  rw [decHighP.c448.costEq P hP]
  have := mapMReads_cost P (by includes) (by includes) (List.take fold (List.drop 1 h))
  have : (List.take fold (List.drop 1 h)).length ≤ fold := List.length_take_le _ _
  cost_calls []
  omega

theorem skLevelsPrice_cons₂ (logN A : ℕ) (l n : Whir.Level) (rest : List Whir.Level) :
    skLevelsPrice logN A (l :: n :: rest) = 377 * l.fold + (150 * (l.fold + logN + l.queries) + 1000) +
      11 * (8 * l.fold + logN + l.queries + 8) + skLevelsPrice logN (A + l.fold) (n :: rest) + 50 := rfl

theorem length_skLevels_le (logN : ℕ) : ∀ (levels : List Whir.Level) (A : ℕ),
    (skLevels logN A levels).length ≤ skLevelsPrice logN A levels
  | [], A => by simp [skLevels, skLevelsPrice]
  | [l], A => by
    simp only [skLevels, skLevelsPrice, List.length_append, List.length_replicate, length_skFoldRounds]
    omega
  | l :: n :: rest, A => by
    have := length_skLevels_le logN (n :: rest) (A + l.fold)
    have := length_skMidTail logN (A + l.fold) l n
    rw [skLevelsPrice_cons₂]
    simp only [skLevels, List.length_append, length_skFoldRounds] at *
    omega

/-- A price of `decLevelsP` (`decLevelsP.c436`) from `A` folds made. -/
@[expose] def decLevelsPrice (logN : ℕ) : ℕ → List Whir.Level → ℕ
  | _, [] => 3
  | A, [l] => (500 * l.fold + 1100) * l.fold + 1000 * l.fold +
      64 * (2 ^ (logN - (A + l.fold)) + l.fold) + 210
  | A, l :: n :: rest => (500 * l.fold + 1100) * l.fold + 1100 * l.fold +
      (150 * (l.fold + logN + l.queries) + 1000) + 45 * (skMidTail logN (A + l.fold) l n).length +
      skLevelsPrice logN (A + l.fold) (n :: rest) + 30 * (skLevels logN (A + l.fold) (n :: rest)).length +
      decLevelsPrice logN (A + l.fold) (n :: rest) + 410

/-- **The cut levels' trace** (`decLevelsP.c436`): at most `decLevelsPrice`, whatever the events. -/
theorem decLevelsP_cost (hP : Includes P decLevelsP.c436.costDeps) (logN : ℕ) (hN : logN < 50) :
    ∀ (levels : List Whir.Level) (A : ℕ) (h : List EvP), (∀ l ∈ levels, LevelOk l) →
      A + 50 * levels.length < 2 ^ 40 → skLevelsPrice logN A levels < 2 ^ 60 →
      machineCost P decLevelsP.c436.costIdx [encodeValue logN, encodeValue A, encodeValue levels,
        encodeValue h] ≤ decLevelsPrice logN A levels
  | [], A, h, _, _, _ => by rw [decLevelsP.c436.costEq_nil P hP]; rfl
  | [l], A, h, hl, hA, _ => by
    obtain ⟨hl1, hl2, hl3⟩ := hl l (by simp)
    simp only [List.length_singleton] at hA
    have h2 : 2 ^ (logN - (A + l.fold)) < 2 ^ 50 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [decLevelsP.c436.costEq_cons P hP]
    dsimp only
    have hlen := length_skFoldRounds l.fold
    have c1 := skFoldRounds_cost P (by includes) l.fold (by omega)
    have c2 := decRoundsP_cost P (by includes) l.fold (List.take (skFoldRounds l.fold).length h)
      (by omega)
    have c3 := bind_cost P (by includes) _ (.closure decLevelsP.c436.lam0.costIdx
        [encodeValue l, encodeValue logN, encodeValue A, encodeValue h])
      (fun rs ↦ RunsApp.of_spec (decLevelsP.c436.lam0.costSpec P (by includes) l logN A h rs))
      (461 * l.fold + 64 * (2 ^ (logN - (A + l.fold)) + l.fold) + 80) (fun rs ↦ by
        rw [appCost_fn]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [decLevelsP.c436.lam0.costEq P (by includes)]
        simp only [Nat.one_shiftLeft]
        have := mapMReads_cost P (by includes) (by includes) (List.take (2 ^ (logN - (A + l.fold)) +
          l.fold) (List.drop (skFoldRounds l.fold).length h))
        have := List.length_take_le (2 ^ (logN - (A + l.fold)) + l.fold)
          (List.drop (skFoldRounds l.fold).length h)
        have := optionMap_cost P (by includes) _ (.closure decLevelsP.c436.lam0.lam0.costIdx
            [encodeValue rs])
          (fun f ↦ RunsApp.of_spec (decLevelsP.c436.lam0.lam0.costSpec P (by includes) rs f)) 6
          (List.mapM (fun p : EvP ↦ p.1) (List.take (2 ^ (logN - (A + l.fold)) + l.fold)
            (List.drop (skFoldRounds l.fold).length h))) (fun f _ ↦ by
              rw [appCost_fn, List.singleton_append, decLevelsP.c436.lam0.lam0.costEq P (by includes)]
              rfl)
        cost_calls []
        omega) (decRoundsP l.fold (List.take (skFoldRounds l.fold).length h))
    cost_calls []
    unfold decLevelsPrice
    omega
  | l :: n :: rest, A, h, hl, hA, hPr => by
    have hl' := hl l (by simp)
    have hn' := hl n (by simp)
    obtain ⟨hl1, hl2, hl3⟩ := hl'
    simp only [List.length_cons] at hA
    rw [skLevelsPrice_cons₂] at hPr
    rw [decLevelsP.c436.costEq_cons P hP]
    dsimp only
    have hlen := length_skFoldRounds l.fold
    have hml := length_skMidTail logN (A + l.fold) l n
    have hsl := length_skLevels_le logN (n :: rest) (A + l.fold)
    have c1 := skFoldRounds_cost P (by includes) l.fold (by omega)
    have c2 := decRoundsP_cost P (by includes) l.fold (List.take (skFoldRounds l.fold).length h)
      (by omega)
    have c3 := bind_cost P (by includes) _ (.closure 449 [encodeValue n, encodeValue rest,
        encodeValue l, encodeValue logN, encodeValue A, encodeValue h])
      (fun rs ↦ RunsApp.of_spec (decLevelsP.c436.lam3.costSpec P (by includes) n rest l logN A h rs))
      (461 * l.fold + (150 * (l.fold + logN + l.queries) + 1000) + 45 * (skMidTail logN (A + l.fold) l n).length +
        skLevelsPrice logN (A + l.fold) (n :: rest) + 30 * (skLevels logN (A + l.fold) (n :: rest)).length +
        decLevelsPrice logN (A + l.fold) (n :: rest) + 64 * l.fold + 250) (fun rs ↦ by
        rw [appCost_fn, show (449 : ℕ) = decLevelsP.c436.lam3.costIdx from rfl]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [decLevelsP.c436.lam3.costEq P (by includes)]
        have d1 := skMidTail_cost P (by includes) logN (A + l.fold) l n (by omega) (by omega)
          ⟨hl1, hl2, hl3⟩ hn'
        have d2 := decHighP_cost P (by includes) l.fold (List.take (skMidTail logN (A + l.fold) l n).length
          (List.drop (skFoldRounds l.fold).length h)) (by omega)
        have d3 := bind_cost P (by includes) _ (.closure decLevelsP.c436.lam2.costIdx
            [encodeValue n, encodeValue rest, encodeValue l, encodeValue logN, encodeValue A,
              encodeValue rs, encodeValue (skMidTail logN (A + l.fold) l n).length, encodeValue (List.drop (skFoldRounds l.fold).length h)])
          (fun hi ↦ RunsApp.of_spec (decLevelsP.c436.lam2.costSpec P (by includes) n rest l logN A rs
            (skMidTail logN (A + l.fold) l n).length (List.drop (skFoldRounds l.fold).length h) hi))
          (skLevelsPrice logN (A + l.fold) (n :: rest) + 27 * (skLevels logN (A + l.fold) (n :: rest)).length + 15 * (skMidTail logN (A + l.fold) l n).length +
            decLevelsPrice logN (A + l.fold) (n :: rest) + 90) (fun hi ↦ by
            rw [appCost_fn]
            simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
            rw [decLevelsP.c436.lam2.costEq P (by includes)]
            have e1 := skLevels_cost P (by includes) logN hN (n :: rest) (A + l.fold)
              (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons]; omega)
            have e2 := decLevelsP_cost hP logN hN (n :: rest) (A + l.fold)
              (List.take (skLevels logN (A + l.fold) (n :: rest)).length (List.drop (skMidTail logN (A + l.fold) l n).length (List.drop (skFoldRounds l.fold).length h)))
              (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons]; omega)
              (by omega)
            have e3 := optionMap_cost P (by includes) _ (.closure decLevelsP.c436.lam1.costIdx
                [encodeValue rs, encodeValue hi])
              (fun tr ↦ RunsApp.of_spec (decLevelsP.c436.lam1.costSpec P (by includes) rs hi tr)) 9
              (decLevelsP logN (A + l.fold) (n :: rest)
                (List.take (skLevels logN (A + l.fold) (n :: rest)).length (List.drop (skMidTail logN (A + l.fold) l n).length (List.drop (skFoldRounds l.fold).length h))))
              (fun tr _ ↦ by
                rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
                  decLevelsP.c436.lam1.costEq P (by includes)]
                rfl)
            cost_calls []
            omega) (decHighP l.fold (List.take (skMidTail logN (A + l.fold) l n).length (List.drop (skFoldRounds l.fold).length h)))
        cost_calls []
        omega) (decRoundsP l.fold (List.take (skFoldRounds l.fold).length h))
    cost_calls []
    unfold decLevelsPrice
    omega

/-- The cut levels' prices at every admissible shape, by the kernel. -/
theorem ladder_dec_all : ∀ μ < 31, ∀ ρ < 5, (Whir.ladder μ ρ).all (fun lv ↦
    decide (decLevelsPrice μ 0 lv ≤ 400000)) = true := by
  decide +kernel

theorem ladder_dec {μ ρ : ℕ} {lv : List Whir.Level} (h : Whir.ladder μ ρ = some lv) :
    decLevelsPrice μ 0 lv ≤ 400000 := by
  obtain ⟨h1, h2⟩ := ladder_some_bounds h
  have := ladder_dec_all μ h1 ρ h2
  rw [h] at this
  simpa using this

/-- **The cut opening's trace** (`decWhirCutP.c434`): at most `403600`, whatever the events. -/
theorem decWhirCutP_cost (hP : Includes P decWhirCutP.c434.costDeps) (μ ρ : ℕ) (h : List EvP)
    (hμ : μ < 2 ^ 64) (hρ : ρ < 2 ^ 64) :
    machineCost P decWhirCutP.c434.costIdx [encodeValue μ, encodeValue ρ, encodeValue h] ≤ 403600 := by
  rw [decWhirCutP.c434.costEq P hP]
  have hl := ladder_cost P (by includes) μ ρ hμ hρ
  have hb := bind_le P (by includes) _ (.closure decWhirCutP.c434.lam0.costIdx
      [encodeValue μ, encodeValue h])
    (fun c ↦ RunsApp.of_spec (decWhirCutP.c434.lam0.costSpec P (by includes) μ h c))
    (Whir.ladder μ ρ) 400007 (fun lv hlv ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [decWhirCutP.c434.lam0.costEq P (by includes)]
      obtain ⟨h1, h2, h3, -⟩ := ladder_facts hlv
      have hb := ladder_some_bounds hlv
      have := decLevelsP_cost P (by includes) μ (by omega) lv 0 h h1 (by omega) (by omega)
      have := ladder_dec hlv
      omega)
  omega

end Skeleton2

section Front

open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Cost.Auto.LeanVM.Protocol.EndToEnd.Sound

/-! ### The Keccak reduction's skeleton -/

theorem length_skKeccakLayer (n : ℕ) : (skKeccakLayer n).length ≤ 6 * n + 140 := by
  have := length_skSum 3 (List.replicate n true)
  have := length_skSum 4 (List.replicate keccakLocalBits false)
  have := length_skGrind (grindingBits (productBits - 1))
  have := length_skGrind (grindingBits 2)
  have hk := skConsts
  simp only [skKeccakLayer, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at *
  omega

/-- A Keccak layer's skeleton (`skKeccakLayer.c424`), at a point of `n` coordinates. -/
theorem skKeccakLayer_cost (hP : Includes P skKeccakLayer.c424.costDeps) (n : ℕ)
    (hn : n < 2 ^ 50 := by omega) :
    machineCost P skKeccakLayer.c424.costIdx [encodeValue n] ≤ 2600 * n + 40000 := by
  have hk := skConsts
  have := grindingBits_le (productBits - 1) (by omega)
  have := grindingBits_le 2 (by omega)
  rw [skKeccakLayer.c424.costEq P hP]
  cost_calls [skGrind_cost, grindingBits_cost, skSum_cost, productBits_cost]
  len_facts [length_skGrind, length_skSum]
  omega

theorem length_skKeccakOpen : skKeccakOpen.length ≤ 36 := by
  have := length_skSum 3 (List.replicate qkeccakSlotBits false)
  have hk := skConsts
  simp only [skKeccakOpen, List.length_replicate] at *
  omega

theorem length_keccakLayers (L : ℕ) :
    ((List.range keccakDepth).flatMap fun _ ↦ skKeccakLayer (L - 4 + keccakSegmentBits)).length ≤
      12 * (6 * L + 146) := by
  have hk := skConsts
  rw [List.length_flatMap, List.map_const', List.sum_replicate, List.length_range, hk.1, smul_eq_mul]
  have := length_skKeccakLayer (L - 4 + keccakSegmentBits)
  omega

theorem length_skKeccak (L : ℕ) : (skKeccak L).length ≤ 72 * L + 2000 := by
  have hk := skConsts
  have := length_keccakLayers L
  have := length_skKeccakOpen
  have := length_skGrind (grindingBits (keccakSegmentBits + keccakLaneBits))
  have := length_skSum 3 (List.replicate 4 false)
  simp only [skKeccak, List.length_append, List.length_replicate, List.length_singleton] at *
  omega

/-- The Keccak reduction's skeleton (`skKeccak.c422`), over `2^L` steps. -/
theorem skKeccak_cost (hP : Includes P skKeccak.c422.costDeps) (L : ℕ) (hL : L ≤ 2 ^ 30) :
    machineCost P skKeccak.c422.costIdx [encodeValue L] ≤ 40000 * L + 1000000 := by
  have hk := skConsts
  have hlay := length_keccakLayers L
  have hop := length_skKeccakOpen
  have := grindingBits_le (keccakSegmentBits + keccakLaneBits) (by omega)
  have hr := rangeLoop_cost P (by includes) keccakDepth [] (by omega)
  have hmap := map_cost P (by includes) _ (.closure skKeccak.c422.lam0.costIdx [encodeValue L])
    (fun x ↦ RunsApp.of_spec (skKeccak.c422.lam0.costSpec P (by includes) L x))
    (2600 * L + 44000) (List.range keccakDepth) (fun x _ ↦ by
      rw [appCost_fn, List.singleton_append, skKeccak.c422.lam0.costEq P (by includes)]
      have := skKeccakLayer_cost P (by includes) (L - 4 + keccakSegmentBits)
      have := bitLength_cost' P (by includes) (keccakSegments - 1)
      rw [limbs_of_lt (by omega : L < 2 ^ 64), limbs_of_lt (by omega : keccakDepth < 2 ^ 64),
        limbs_of_lt (by omega : keccakSegments < 2 ^ 64),
        limbs_of_lt (by omega : L - 4 + keccakSegmentBits < 2 ^ 64),
        limbs_of_lt (by omega : L - 4 < 2 ^ 64), limbs_of_lt (by omega : keccakSegmentBits < 2 ^ 64)]
      simp only [List.length_singleton, max_self]
      omega)
  have hfl := flatten_cost P (by includes) (6 * L + 146)
    (List.map (fun _ ↦ skKeccakLayer (L - 4 + keccakSegmentBits)) (List.range keccakDepth))
    (fun l hl ↦ by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      have := length_skKeccakLayer (L - 4 + keccakSegmentBits)
      omega)
  have hlen : (List.range keccakDepth).length = 12 := by rw [List.length_range, hk.1]
  rw [List.length_map, hlen] at hfl
  rw [hlen] at hmap
  rw [skKeccak.c422.costEq P hP]
  cost_calls [grindingBits_cost, skGrind_cost, skSum_cost, bitLength_cost']
  len_facts [length_skGrind, length_skSum]
  omega


/-! ### The link's skeleton -/

theorem optCases_le {α : Type} (o : Option α) (a b : ℕ) :
    (Option.casesOn o a (fun _ ↦ b) : ℕ) ≤ max a b := by
  cases o <;> simp

theorem optRec_le {α : Type} (o : Option α) (a b : ℕ) :
    (Option.rec a (fun _ ↦ b) o : ℕ) ≤ max a b := by
  cases o <;> simp

/-- `List.find?` (`find?.c385`): `11` per element and the predicate's price, `3` at the end. -/
theorem find_cost (hP : Includes P Auto.List.find?.c385.costDeps) {α : Type} [MachineEncoding α]
    (p : α → Bool) (pVal : MachineValue) (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a)))
    (B : ℕ) : ∀ l : List α, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.find?.c385.costIdx [pVal, encodeValue l] ≤ (B + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.find?.c385.costEq_nil P hP p pVal hp]; omega
  | cons a l ih =>
    intro hB
    rw [Auto.List.find?.c385.costEq_cons P hP p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.length_cons]
    generalize p a = b
    cases b <;> dsimp only <;> nlinarith

theorem skFoldrAdd_le (M : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ M) →
    l.foldr (fun x1 x2 ↦ x1 + x2) 0 ≤ l.length * M
  | [], _ => by simp
  | x :: l, h => by
    have := skFoldrAdd_le M l (fun y hy ↦ h y (by simp [hy]))
    have := h x (by simp)
    simp only [List.foldr_cons, List.length_cons]
    nlinarith

theorem skFoldlAdd_le (M : ℕ) : ∀ (l : List ℕ) (a : ℕ), (∀ x ∈ l, x ≤ M) →
    l.foldl (fun x1 x2 ↦ x1 + x2) a ≤ a + l.length * M
  | [], _, _ => by simp
  | x :: l, a, h => by
    have := skFoldlAdd_le M l (a + x) (fun y hy ↦ h y (by simp [hy]))
    have := h x (by simp)
    simp only [List.foldl_cons, List.length_cons]
    nlinarith

/-- A sum of word-sized values (`List.sum.c405`): `14` per element, `7`. -/
theorem sum405_cost (hP : Includes P Auto.List.sum.c405.costDeps) (M : ℕ) (l : List ℕ)
    (hl : (l.length + 1) * M < 2 ^ 64) (hs : ∀ x ∈ l, x ≤ M) :
    machineCost P Auto.List.sum.c405.costIdx [encodeValue l] ≤ 14 * l.length + 7 := by
  rw [Auto.List.sum.c405.costEq P hP]
  have := foldrSuffix_cost P (by includes) (fun x1 x2 : ℕ ↦ x1 + x2)
    (.closure Auto.List.sum.c405.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (Auto.List.sum.c405.lam0.costSpec P (by includes) a b)) 3 0 l
    (fun x tl h ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, Auto.List.sum.c405.lam0.costEq P (by includes)]
      have hx := hs x (h.subset (by simp))
      have ht := skFoldrAdd_le M tl (fun y hy ↦ hs y (h.subset (by simp [hy])))
      have hlen : tl.length + 1 ≤ l.length := by have := h.length_le; simpa using this
      have : tl.length * M + M ≤ (l.length + 1) * M := by nlinarith
      rw [limbs_of_lt (by omega : x + tl.foldr (fun x1 x2 ↦ x1 + x2) 0 < 2 ^ 64),
        limbs_of_lt (by omega : x < 2 ^ 64),
        limbs_of_lt (by omega : tl.foldr (fun x1 x2 ↦ x1 + x2) 0 < 2 ^ 64)]
      simp only [max_self]
      omega)
  omega

/-- The starts of runs (`exclusivePrefix.c411`), at most `30` sizes of at most `2^30`: at most
`12000`. -/
theorem exclusivePrefix_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.exclusivePrefix.c411.costDeps)
    (sizes : List ℕ) (hl : sizes.length ≤ 30) (hs : ∀ x ∈ sizes, x ≤ 2 ^ 30) :
    machineCost P Auto.LeanVM.Protocol.Verifier.exclusivePrefix.c411.costIdx [encodeValue sizes] ≤
      12000 := by
  rw [Auto.LeanVM.Protocol.Verifier.exclusivePrefix.c411.costEq P hP]
  have := listFoldl_le_idx P (by includes)
    (fun (acc : List ℕ × ℕ) size ↦ (acc.1 ++ [acc.2], acc.2 + size))
    (.closure Auto.LeanVM.Protocol.Verifier.exclusivePrefix.c411.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec
      (Auto.LeanVM.Protocol.Verifier.exclusivePrefix.c411.lam0.costSpec P (by includes) a b)) 350
    (fun k acc ↦ acc.1.length + k ≤ 30 ∧ acc.2 + k * 2 ^ 30 ≤ 30 * 2 ^ 30) sizes
    (fun k acc hI b hb ↦ by
      have hb' := hs b hb
      obtain ⟨h1, h2⟩ := hI
      refine ⟨⟨by simp only [List.length_append, List.length_singleton]; omega, by
        simp only; nlinarith⟩, ?_⟩
      rw [appCost_fn, List.nil_append, List.length_nil,
        Auto.LeanVM.Protocol.Verifier.exclusivePrefix.c411.lam0.costEq P (by includes)]
      have := append_cost P (by includes) acc.1 [acc.2]
      rw [limbs_of_lt (by nlinarith : acc.2 + b < 2 ^ 64), limbs_of_lt (by nlinarith : acc.2 < 2 ^ 64),
        limbs_of_lt (by omega : b < 2 ^ 64)]
      simp only [max_self]
      omega) sizes ([], 0) (fun b hb ↦ hb) ⟨by simp; omega, by simp only; nlinarith⟩
  nlinarith

theorem chunkCands_facts (r : ℕ) : ∀ c ∈ List.map (fun d ↦ List.map
      (fun i ↦ r / d + if i < r % d then 1 else 0) (List.range d))
      (List.map (fun x ↦ x + 1) (List.range r)), c.length ≤ r ∧ ∀ x ∈ c, x ≤ r + 1 := by
  intro c hc
  simp only [List.mem_map, List.mem_range] at hc
  obtain ⟨d, ⟨j, hj, rfl⟩, rfl⟩ := hc
  refine ⟨by simp; omega, fun x hx ↦ ?_⟩
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  have := Nat.div_le_self r (j + 1)
  split <;> omega

theorem chunkTail_facts (r low : ℕ) :
    let tail : List ℕ := if 0 < r then ((List.map (fun d ↦ List.map
      (fun i ↦ r / d + if i < r % d then 1 else 0) (List.range d))
      (List.map (fun x ↦ x + 1) (List.range r))).find?
        fun widths ↦ decide ((widths.map (2 ^ ·)).sum ≤ 64 - 2 ^ low)).getD [] else []
    tail.length ≤ r ∧ ∀ x ∈ tail, x ≤ r + 1 := by
  intro tail
  simp only [tail]
  split
  · generalize hf : List.find? _ _ = o
    cases o with
    | none => simp
    | some c => exact chunkCands_facts r c (List.mem_of_find?_eq_some hf)
  · simp

theorem chunksNew_facts {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) :
    c.width = w ∧ 1 ≤ w ∧ w ≤ 24 ∧ c.widths.length ≤ 25 ∧ ∀ x ∈ c.widths, x ≤ 25 := by
  have hk := skConsts
  unfold Chunks.new at h
  split_ifs at h with hw
  obtain rfl := Option.some.inj h
  have ht := chunkTail_facts (w - min w windowBits) (min w windowBits)
  simp only at ht
  refine ⟨rfl, hw.1, by omega, ?_, ?_⟩
  · simp only [List.length_cons]; omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ht.2 x hx; omega

/-- `Chunks::new` (`Chunks.new.c403`) of a word-sized width: at most `100000`. -/
theorem chunksNew_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.costDeps)
    (w : ℕ) (hw : w < 2 ^ 64) :
    machineCost P Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.costIdx [encodeValue w] ≤ 100000 := by
  have hk := skConsts
  rw [Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.costEq P hP]
  by_cases hin : 1 ≤ w ∧ w ≤ maxPointerWidth
  swap
  · simp only [hin, ↓reduceIte]
    rw [limbs_of_lt hw, limbs_of_lt (by omega : maxPointerWidth < 2 ^ 64)]
    split_ifs <;> omega
  simp only [hin, ↓reduceIte, and_self]
  have ht := chunkTail_facts (w - min w windowBits) (min w windowBits)
  simp only at ht
  have hcf := chunkCands_facts (w - min w windowBits)
  set r := w - min w windowBits with hr
  set low := min w windowBits with hlow
  have hr20 : r ≤ 24 := by omega
  have hl4 : low ≤ 4 := by omega
  set cands := List.map (fun d ↦ List.map (fun i ↦ r / d + if i < r % d then 1 else 0) (List.range d))
    (List.map (fun x ↦ x + 1) (List.range r)) with hc
  have hcl : cands.length = r := by simp [cands]
  set tail : List ℕ := (if 0 < r then (cands.find?
    fun widths ↦ decide ((widths.map (2 ^ ·)).sum ≤ 64 - 2 ^ low)).getD [] else []) with htl
  -- the candidates' search
  have c1 := rangeLoop_cost P (by includes) r [] (by omega)
  have c2 := map_cost P (by includes) (fun x : ℕ ↦ x + 1)
    (.closure Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam2.costIdx [])
    (fun x ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam2.costSpec P (by includes) x))
    3 (List.range r) (fun x hx ↦ by
      simp only [List.mem_range] at hx
      rw [appCost_fn, List.nil_append, Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam2.costEq P
        (by includes), limbs_of_lt (by omega : x + 1 < 2 ^ 64), limbs_of_lt (by omega : x < 2 ^ 64)]
      simp)
  have c3 := map_cost P (by includes)
    (fun d ↦ List.map (fun i ↦ r / d + if i < r % d then 1 else 0) (List.range d))
    (.closure Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam1.costIdx [encodeValue r, encodeValue low])
    (fun d ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam1.costSpec P (by includes)
      r low d)) 1100 (List.map (fun x ↦ x + 1) (List.range r)) (fun d hd ↦ by
      simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam1.costEq P (by includes)]
      have := rangeLoop_cost P (by includes) (j + 1) [] (by omega)
      have := map_cost P (by includes) (fun i ↦ r / (j + 1) + if i < r % (j + 1) then 1 else 0)
        (.closure Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam1.lam0.costIdx
          [encodeValue r, encodeValue (j + 1)])
        (fun i ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam1.lam0.costSpec P
          (by includes) r (j + 1) i)) 13 (List.range (j + 1)) (fun i hi ↦ by
            simp only [List.mem_range] at hi
            rw [appCost_fn]
            simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
            rw [Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam1.lam0.costEq P (by includes)]
            have := Nat.div_le_self r (j + 1)
            have := Nat.mod_lt r (show j + 1 > 0 by omega)
            have : (if i < r % (j + 1) then 1 else 0) ≤ 1 := by split <;> omega
            rw [limbs_of_lt (by omega : r < 2 ^ 64), limbs_of_lt (by omega : j + 1 < 2 ^ 64),
              limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : r % (j + 1) < 2 ^ 64),
              limbs_of_lt (by omega : r / (j + 1) < 2 ^ 64),
              limbs_of_lt (by split <;> omega : (if i < r % (j + 1) then 1 else 0) < 2 ^ 64),
              limbs_of_lt (by split <;> omega :
                r / (j + 1) + (if i < r % (j + 1) then 1 else 0) < 2 ^ 64)]
            split_ifs <;> omega)
      simp only [List.length_range] at *
      omega)
  have c4 := find_cost P (by includes)
    (fun widths : List ℕ ↦ decide ((widths.map (2 ^ ·)).sum ≤ 64 - 2 ^ low))
    (.closure Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.costIdx [encodeValue low])
    (fun c ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.costSpec P
      (by includes) low c)) 800 cands (fun c hc' ↦ by
      obtain ⟨hcl', hcx⟩ := hcf c hc'
      rw [appCost_fn, List.singleton_append, List.length_singleton,
        Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.costEq P (by includes)]
      have hm := map_cost P (by includes) (fun x : ℕ ↦ 2 ^ x)
        (.closure Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.lam0.costIdx [])
        (fun x ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.lam0.costSpec P
          (by includes) x)) 3 c (fun x hx ↦ by
            have := hcx x hx
            rw [appCost_fn, List.nil_append,
              Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.lam0.costEq P (by includes),
              limbs_shift (by omega), limbs_of_lt (by omega : x < 2 ^ 64)]
            simp)
      have hpow : ∀ y ∈ c.map (fun x : ℕ ↦ 2 ^ x), y ≤ 33554432 := fun y hy ↦ by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        exact (Nat.pow_le_pow_right (by norm_num) (by have := hcx x hx; omega : x ≤ 25)).trans
          (by norm_num)
      have hs := sum405_cost P (by includes) 33554432 (c.map (fun x : ℕ ↦ 2 ^ x))
        (by simp only [List.length_map]
            have : (c.length + 1) * 33554432 ≤ 26 * 33554432 := Nat.mul_le_mul_right _ (by omega)
            omega) hpow
      have hsv : (c.map (fun x : ℕ ↦ 2 ^ x)).sum ≤ 25 * 33554432 := by
        have h1 := skFoldrAdd_le 33554432 (c.map (fun x : ℕ ↦ 2 ^ x)) hpow
        rw [List.length_map] at h1
        have h2 : c.length * 33554432 ≤ 25 * 33554432 := Nat.mul_le_mul_right _ (by omega)
        rw [List.sum_eq_foldr]
        exact h1.trans h2
      have h2l : 2 ^ low ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hl4
      have h64 : 64 - 2 ^ low ≤ 64 := Nat.sub_le _ _
      simp only [List.length_map] at hs
      rw [limbs_shift (by omega), limbs_of_lt (by omega : low < 2 ^ 64),
        limbs_of_lt (by omega : 2 ^ low < 2 ^ 64),
        limbs_of_lt (by omega : (c.map (fun x : ℕ ↦ 2 ^ x)).sum < 2 ^ 64),
        limbs_of_lt (by omega : 64 - 2 ^ low < 2 ^ 64)]
      simp only [max_self]
      omega)
  have c5 := optCases_le (cands.find? fun widths ↦ decide ((widths.map (2 ^ ·)).sum ≤ 64 - 2 ^ low))
    1 2
  have c5' := optRec_le (cands.find? fun widths ↦ decide ((widths.map (2 ^ ·)).sum ≤ 64 - 2 ^ low))
    1 2
  -- the chunks' starts
  have hwl : ∀ x ∈ low :: tail, x ≤ 25 := fun x hx ↦ by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ht.2 x hx; omega
  have c6 := exclusivePrefix_cost P (by includes) (low :: tail)
    (by simp only [List.length_cons]; omega) (fun x hx ↦ by have := hwl x hx; omega)
  have c7 := exclusivePrefix_cost P (by includes) ((low :: tail).map (2 ^ ·))
    (by simp only [List.length_map, List.length_cons]; omega) (fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact Nat.pow_le_pow_right (by norm_num) (by have := hwl x hx; omega))
  have c8 := map_cost P (by includes) (fun x : ℕ ↦ 2 ^ x)
    (.closure Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.lam0.costSpec P
      (by includes) x)) 3 (low :: tail) (fun x hx ↦ by
        have := hwl x hx
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Protocol.Verifier.Chunks.new.c403.lam0.lam0.costEq P (by includes),
          limbs_shift (by omega), limbs_of_lt (by omega : x < 2 ^ 64)]
        simp)
  simp only [List.length_range, List.length_map, List.length_cons] at c2 c3 c4 c8
  rw [hcl] at c4
  rw [limbs_of_lt hw, limbs_of_lt (by omega : maxPointerWidth < 2 ^ 64),
    limbs_of_lt (by omega : windowBits < 2 ^ 64), limbs_of_lt (by omega : low < 2 ^ 64),
    limbs_of_lt (by omega : r < 2 ^ 64)]
  split_ifs <;> omega

/-- `pointer_width` (`pointerWidth.c413`) on word-sized sizes: at most `10000`. -/
theorem pointerWidth_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.pointerWidth.c413.costDeps)
    (lm lb cyc : ℕ) (hm : lm < 2 ^ 64) (hb : lb < 2 ^ 64) (hc : cyc < 2 ^ 64) :
    machineCost P Auto.LeanVM.Protocol.Verifier.pointerWidth.c413.costIdx [encodeValue lm,
      encodeValue lb, encodeValue cyc] ≤ 10000 := by
  rw [Auto.LeanVM.Protocol.Verifier.pointerWidth.c413.costEq P hP]
  have := bitLength_cost' P (by includes) cyc
  have := bitLength_lt hc
  cost_calls []
  split_ifs <;> omega

theorem pointerWidth_le {lm lb cyc : ℕ} (hm : lm ≤ 30) (hb : lb ≤ 30) (hc : cyc < 2 ^ 64) :
    pointerWidth lm lb cyc ≤ 64 := by
  have := bitLength_lt hc
  unfold pointerWidth
  omega

theorem tableRows_sum_le (lay : LayoutLite) (hl : LayOk lay) :
    lay.tableRows.foldl (fun x1 x2 ↦ x1 + x2) 0 ≤ 6 * 2 ^ 30 := by
  obtain ⟨-, -, -, -, -, h6, h7⟩ := hl
  have := skFoldlAdd_le (2 ^ 30) lay.tableRows 0 h7
  have : lay.tableRows.length * 2 ^ 30 ≤ 6 * 2 ^ 30 := Nat.mul_le_mul_right _ h6
  omega

/-- **The link's chunks** (`chunksL.c402`) at an admissible layout: at most `10^7`. -/
theorem chunksL_cost (hP : Includes P Auto.LeanVM.Protocol.EndToEnd.Sound.chunksL.c402.costDeps)
    (lay : LayoutLite) (hl : LayOk lay) :
    machineCost P Auto.LeanVM.Protocol.EndToEnd.Sound.chunksL.c402.costIdx [encodeValue lay] ≤
      10 ^ 7 := by
  have hs := tableRows_sum_le lay hl
  obtain ⟨-, h2, h3, -, -, h6, h7⟩ := hl
  rw [Auto.LeanVM.Protocol.EndToEnd.Sound.chunksL.c402.costEq P hP]
  have c1 := listFoldl_le_idx P (by includes) (fun x1 x2 : ℕ ↦ x1 + x2)
    (.closure Auto.List.sum.c405.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (Auto.List.sum.c405.lam0.costSpec P (by includes) a b)) 3
    (fun k acc ↦ acc + k * 2 ^ 30 ≤ 6 * 2 ^ 30) lay.tableRows
    (fun k acc hI b hb ↦ by
      have := h7 b hb
      have hI' : acc + (k + 1) * 2 ^ 30 ≤ 6 * 2 ^ 30 := hI
      refine ⟨show acc + b + k * 2 ^ 30 ≤ 6 * 2 ^ 30 by nlinarith, ?_⟩
      rw [appCost_fn, List.nil_append, List.length_nil, Auto.List.sum.c405.lam0.costEq P (by includes)]
      have := limbs_of_lt (by nlinarith : acc + b < 2 ^ 64)
      have := limbs_of_lt (by nlinarith : acc < 2 ^ 64)
      have := limbs_of_lt (by omega : b < 2 ^ 64)
      omega) lay.tableRows 0 (fun b hb ↦ hb) (by
        have : lay.tableRows.length * 2 ^ 30 ≤ 6 * 2 ^ 30 := Nat.mul_le_mul_right _ h6
        omega)
  have c2 := pointerWidth_cost P (by includes) lay.logMemory lay.logBytecode
    (lay.tableRows.foldl (fun x1 x2 ↦ x1 + x2) 0) (by omega) (by omega) (by omega)
  have c3 := chunksNew_cost P (by includes)
    (pointerWidth lay.logMemory lay.logBytecode (lay.tableRows.foldl (fun x1 x2 ↦ x1 + x2) 0))
    (by have := pointerWidth_le h2 h3 (by omega : lay.tableRows.foldl (fun x1 x2 ↦ x1 + x2) 0 < 2 ^ 64)
        omega)
  omega

theorem chunksL_facts {lay : LayoutLite} {c : Chunks} (h : chunksL lay = some c) :
    c.width ≤ 24 ∧ c.widths.length ≤ 25 ∧ ∀ x ∈ c.widths, x ≤ 25 := by
  obtain ⟨h1, -, h3, h4, h5⟩ := chunksNew_facts h
  exact ⟨by omega, h4, h5⟩

/-- `packed_challenges` (`packedChallengesL.c416`) at `nRows ≤ 30`: at most `101000`. -/
theorem packedChallengesL_cost (hP : Includes P packedChallengesL.c416.costDeps) (nRows width : ℕ)
    (hn : nRows ≤ 30) (hw : width ≤ 64) :
    machineCost P packedChallengesL.c416.costIdx [encodeValue nRows, encodeValue width] ≤ 101000 := by
  have hk := skConsts
  have hd : (Option.map Chunks.d (Chunks.new width)).getD 0 ≤ 25 := by
    rcases h : Chunks.new width with _ | c
    · simp
    · have := chunksNew_facts h; simpa [Chunks.d] using this.2.2.2.1
  rw [packedChallengesL.c416.costEq P hP]
  have c1 := chunksNew_cost P (by includes) width (by omega)
  have c2 := optionMap_cost P (by includes) Chunks.d (.closure packedChallengesL.c416.lam0.costIdx [])
    (fun c ↦ RunsApp.of_spec (packedChallengesL.c416.lam0.costSpec P (by includes) c)) 300
    (Chunks.new width) (fun c hc ↦ by
      have := (chunksNew_facts hc).2.2.2.1
      rw [appCost_fn, List.nil_append, List.length_nil, packedChallengesL.c416.lam0.costEq P (by includes)]
      have := length_cost P (by includes) c.widths (by omega)
      omega)
  have c3 := optCases_le (Option.map Chunks.d (Chunks.new width)) 1 2
  have : nAccessesL = 39 := rfl
  have : nPointersL = 33 := rfl
  cost_calls []
  omega

theorem packedChallengesL_le (nRows width : ℕ) :
    packedChallengesL nRows width ≤ 88 + nRows + width + 25 := by
  have hk := skConsts
  have hd : (Option.map Chunks.d (Chunks.new width)).getD 0 ≤ 25 := by
    rcases h : Chunks.new width with _ | c
    · simp
    · have := chunksNew_facts h; simpa [Chunks.d] using this.2.2.2.1
  have : nAccessesL = 39 := rfl
  have : nPointersL = 33 := rfl
  unfold packedChallengesL
  omega

/-- `round_coefficients` (`roundCoefficients.c421`), a word-sized count: at most `40`. -/
theorem roundCoefficients_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.roundCoefficients.c421.costDeps)
    (d : ℕ) (hd : d < 2 ^ 60 := by omega) :
    machineCost P Auto.LeanVM.Protocol.Verifier.roundCoefficients.c421.costIdx [encodeValue d] ≤ 40 := by
  rw [Auto.LeanVM.Protocol.Verifier.roundCoefficients.c421.costEq P hP]
  cost_calls []
  split_ifs <;> omega

theorem log2Ceil_nPointersL : log2Ceil nPointersL = 6 := by decide

theorem length_skLink (lay : LayoutLite) (hl : LayOk lay) : (skLink lay).length ≤ 2000 := by
  have hm := foldl_max_le 30 lay.tableLogHeights 0 (by omega) hl.2.2.2.2.1
  unfold skLink
  rcases h : chunksL lay with _ | c
  · simp
  · obtain ⟨h1, h2, -⟩ := chunksL_facts h
    dsimp only
    have := length_skGrind (grindingBits (max (lay.tableLogHeights.foldl max 0 + 3 + bytecodeSlotBits)
      (c.width + 1)))
    have := length_skSum 3 (List.replicate c.width false)
    have := length_skSum (roundCoefficients c.d).1 (List.replicate (lay.tableLogHeights.foldl max 0) false)
    have := length_skSum (roundCoefficients c.d).2 (List.replicate (log2Ceil nPointersL) false)
    have hd : c.d ≤ 25 := h2
    have hr : (roundCoefficients c.d).1 ≤ 28 ∧ (roundCoefficients c.d).2 ≤ 27 := by
      unfold roundCoefficients; omega
    rw [log2Ceil_nPointersL] at *
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at *
    have : (lay.tableLogHeights.foldl max 0) * ((roundCoefficients c.d).1 + 3) ≤ 30 * 31 :=
      Nat.mul_le_mul hm (by omega)
    have : 6 * ((roundCoefficients c.d).2 + 3) ≤ 6 * 30 := Nat.mul_le_mul_left _ (by omega)
    have : c.width * (3 + 3) ≤ 24 * 6 := Nat.mul_le_mul_right _ h1
    omega

theorem packedSum_cons (op : Op) (l : List Op) : packedSum (op :: l) = packedSum [op] + packedSum l := by
  cases op <;> simp [packedSum]

theorem packedSum_replicate (op : Op) : ∀ n, packedSum (List.replicate n op) = n * packedSum [op]
  | 0 => by simp
  | n + 1 => by rw [List.replicate_succ, packedSum_cons, packedSum_replicate op n]; ring

theorem packedSum_skGrind (b : ℕ) : packedSum (skGrind b) = 0 := by
  unfold skGrind; split <;> rfl

theorem packedSum_skRound (c : ℕ) (b : Bool) : packedSum (skRound c b) = 0 := by
  cases b <;> simp [skRound, packedSum_append, packedSum_replicate, packedSum_skGrind, packedSum]

theorem packedSum_skSum (c : ℕ) : ∀ eqs : List Bool, packedSum (skSum c eqs) = 0
  | [] => rfl
  | b :: eqs => by
    have := packedSum_skSum c eqs
    simp only [skSum, List.flatMap_cons] at *
    rw [packedSum_append, packedSum_append, packedSum_skRound, this]
    rfl

theorem packedSum_skLink (lay : LayoutLite) (hl : LayOk lay) : packedSum (skLink lay) ≤ 400 := by
  have hm := foldl_max_le 30 lay.tableLogHeights 0 (by omega) hl.2.2.2.2.1
  have hk := skConsts
  unfold skLink
  rcases h : chunksL lay with _ | c
  · simp
  · obtain ⟨h1, -, -⟩ := chunksL_facts h
    dsimp only
    have := packedChallengesL_le (lay.tableLogHeights.foldl max 0) c.width
    have : nValuesL = 80 := rfl
    simp only [packedSum_append, packedSum_skGrind, packedSum_skSum, packedSum]
    omega

/-- **The link's skeleton** (`skLink.c401`) at an admissible layout: at most `2·10^7`. -/
theorem skLink_cost (hP : Includes P skLink.c401.costDeps) (lay : LayoutLite) (hl : LayOk lay) :
    machineCost P skLink.c401.costIdx [encodeValue lay] ≤ 20000000 := by
  have hk := skConsts
  have hm := foldl_max_le 30 lay.tableLogHeights 0 (by omega) hl.2.2.2.2.1
  have c0 := chunksL_cost P (by includes) lay hl
  have hlen := length_skLink lay hl
  rw [skLink.c401.costEq P hP]
  unfold skLink at hlen
  rcases h : chunksL lay with _ | c
  · dsimp only; omega
  · obtain ⟨h1, h2, -⟩ := chunksL_facts h
    rw [h] at hlen
    dsimp only at hlen ⊢
    have hd : c.d ≤ 25 := h2
    have hr : (roundCoefficients c.d).1 ≤ 28 ∧ (roundCoefficients c.d).2 ≤ 27 := by
      unfold roundCoefficients; omega
    have c1 := listFoldl_le P (by includes) (fun a b : ℕ ↦ max a b)
      (.closure skLink.c401.lam0.costIdx [])
      (fun a b ↦ RunsApp.of_spec (skLink.c401.lam0.costSpec P (by includes) a b)) 7 (fun a ↦ a ≤ 30)
      lay.tableLogHeights 0 (by omega) (fun acc hacc b hb ↦ by
        have := hl.2.2.2.2.1 b hb
        refine ⟨by omega, ?_⟩
        rw [appCost_fn, List.nil_append, List.length_nil, skLink.c401.lam0.costEq P (by includes),
          limbs_of_lt (by omega : acc < 2 ^ 64), limbs_of_lt (by omega : b < 2 ^ 64)]
        split_ifs <;> omega)
    have c2 := packedChallengesL_cost P (by includes) (lay.tableLogHeights.foldl max 0) c.width hm
      (by omega)
    have c3 := length_cost P (by includes) c.widths (by omega)
    have c4 := grindingBits_le (max (lay.tableLogHeights.foldl max 0 + 3 + bytecodeSlotBits) (c.width + 1))
      (by omega)
    have : nPointersL = 33 := rfl
    have c5 := bitLength_cost' P (by includes) (nPointersL - 1)
    have c6 := grindingBits_cost P (by includes)
      (max (lay.tableLogHeights.foldl max 0 + 3 + bytecodeSlotBits) (c.width + 1))
    have : nValuesL = 80 := rfl
    have hl6 := log2Ceil_nPointersL
    have hlen6 := hl.2.2.2.1
    rw [hl6]
    cost_calls [grindingBits_cost, skGrind_cost, skSum_cost, roundCoefficients_cost]
    len_facts [length_skGrind, length_skSum]
    simp only [hl6] at *
    have : lay.tableLogHeights.length ≤ 6 := hlen6
    have : (52 * (roundCoefficients c.d).1 + 2100) * lay.tableLogHeights.foldl max 0 ≤ 3556 * 30 :=
      Nat.mul_le_mul (by omega) hm
    have : (52 * (roundCoefficients c.d).2 + 2100) * 6 ≤ 3504 * 6 := Nat.mul_le_mul_right _ (by omega)
    have : (52 * 3 + 2100) * c.width ≤ 2256 * 24 := Nat.mul_le_mul_left _ h1
    have : lay.tableLogHeights.foldl max 0 * ((roundCoefficients c.d).1 + 3) ≤ 30 * 31 :=
      Nat.mul_le_mul hm (by omega)
    have : 6 * ((roundCoefficients c.d).2 + 3) ≤ 6 * 30 := Nat.mul_le_mul_left _ (by omega)
    have : c.width * (3 + 3) ≤ 24 * 6 := Nat.mul_le_mul_right _ h1
    have : (7 + 11) * lay.tableLogHeights.length ≤ 18 * 6 := Nat.mul_le_mul_left _ hlen6
    split_ifs <;> omega

/-! ### The body's skeleton -/

theorem packedSum_flatMap {α : Type} (f : α → List Op) (h : ∀ a, packedSum (f a) = 0) :
    ∀ l : List α, packedSum (l.flatMap f) = 0
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, packedSum_append, h a, packedSum_flatMap f h l]

theorem packedSum_skKeccak (L : ℕ) : packedSum (skKeccak L) = 0 := by
  have hl : ∀ n, packedSum (skKeccakLayer n) = 0 := fun n ↦ by
    simp [skKeccakLayer, packedSum_append, packedSum_replicate, packedSum_skGrind, packedSum_skSum,
      packedSum]
  simp [skKeccak, skKeccakOpen, packedSum_append, packedSum_replicate, packedSum_skGrind,
    packedSum_skSum, packedSum_flatMap _ (fun _ ↦ hl _), packedSum]

theorem packedSum_skFoldRounds : ∀ n, packedSum (skFoldRounds n) = 0
  | 0 => rfl
  | n + 1 => by
    rw [skFoldRounds, packedSum_append, packedSum_skFoldRounds n]
    simp [skFoldRound, packedSum_append, packedSum_skGrind, packedSum]

theorem packedSum_skLevels (logN : ℕ) : ∀ (A : ℕ) (levels : List Whir.Level),
    packedSum (skLevels logN A levels) = 0
  | _, [] => rfl
  | A, [l] => by
    simp [skLevels, packedSum_append, packedSum_replicate, packedSum_skFoldRounds, packedSum]
  | A, l :: n :: rest => by
    have := packedSum_skLevels logN (A + l.fold) (n :: rest)
    simp only [skLevels, packedSum_append, packedSum_skFoldRounds, this]
    simp [skMidTail, packedSum_append, packedSum_replicate, packedSum_skGrind, packedSum]

theorem packedSum_skWhir (μ ρ : ℕ) : packedSum (skWhir μ ρ) = 0 := by
  unfold skWhir
  split
  · exact packedSum_skLevels μ 0 _
  · rfl

theorem packedSum_skCommitStack (μ ρ : ℕ) : packedSum (skCommitStack μ ρ) = 0 := by
  unfold skCommitStack
  split <;> rfl

theorem packedSum_skOod (s : ℕ) : packedSum (skOod s) = 0 := by
  simp [skOod, packedSum_append, packedSum_replicate, packedSum_skGrind, packedSum]

theorem packedSum_skRing : packedSum skRing ≤ 100 := by decide

/-- **The body's packed scalars** at an admissible layout: at most `1000`. -/
theorem packedSum_skBody (lay : LayoutLite) (ρ : ℕ) (hl : LayOk lay) : packedSum (skBody lay ρ) ≤ 1000 := by
  have := packedSum_skLink lay hl
  have := packedSum_skRing
  simp only [skBody, skBodyHead, packedSum_append, packedSum_skCommitStack, packedSum_skOod,
    packedSum_skKeccak, packedSum_skWhir]
  simp only [packedSum]
  omega

theorem length_skBodyHead (lay : LayoutLite) (ρ : ℕ) (hl : LayOk lay) :
    (skBodyHead lay ρ).length ≤ 7000 := by
  have := length_skCommitStack lay.stackLog ρ
  have := length_skOod lay.stackLog
  have := length_skLink lay hl
  have := length_skKeccak (lay.tableLogHeights.getD opKeccak 0)
  have := getD_le_of lay.tableLogHeights opKeccak 30 hl.2.2.2.2.1
  have := length_skRing
  have := hl.1
  simp only [skBodyHead, List.length_append, List.length_singleton] at *
  omega

/-- **The body's skeleton's length** at an admissible layout: at most `40000`. -/
theorem length_skBody (lay : LayoutLite) (ρ : ℕ) (hl : LayOk lay) : (skBody lay ρ).length ≤ 40000 := by
  have := length_skBodyHead lay ρ hl
  have := length_skWhir lay.stackLog ρ
  simp only [skBody, List.length_append]
  omega

/-- The body's skeleton before the opening (`skBodyHead.c396`) at an admissible layout. -/
theorem skBodyHead_cost (hP : Includes P skBodyHead.c396.costDeps) (lay : LayoutLite) (ρ : ℕ)
    (hl : LayOk lay) (hρ : ρ ≤ 4) :
    machineCost P skBodyHead.c396.costIdx [encodeValue lay, encodeValue ρ] ≤ 30000000 := by
  have hk := skConsts
  have h1 := hl.1
  have hlen6 := hl.2.2.2.1
  have hg := getD_le_of lay.tableLogHeights opKeccak 30 hl.2.2.2.2.1
  have c1 := skCommitStack_cost P (by includes) lay.stackLog ρ (by omega) (by omega)
  have c2 := skOod_cost P (by includes) lay.stackLog
  have c3 := skLink_cost P (by includes) lay hl
  have c4 := getD_cost P (by includes) lay.tableLogHeights opKeccak 0 (by omega)
  have c5 := skKeccak_cost P (by includes) (lay.tableLogHeights.getD opKeccak 0) (by omega)
  have c6 := skRing_cost P (by includes)
  have l1 := length_skCommitStack lay.stackLog ρ
  have l2 := length_skOod lay.stackLog
  have l3 := length_skLink lay hl
  have l4 := length_skKeccak (lay.tableLogHeights.getD opKeccak 0)
  have l5 := length_skRing
  rw [skBodyHead.c396.costEq P hP]
  cost_calls []
  simp only [List.length_append, List.length_singleton] at *
  omega

/-- **The body's skeleton** (`skBodyC`) at an admissible layout and rate: at most `10^9`. -/
theorem skBody_cost (hP : Includes P skBodyC.costDeps) (lay : LayoutLite) (ρ : ℕ) (hl : LayOk lay)
    (hρ : ρ ≤ 4) : machineCost P skBodyC.costIdx [encodeValue lay, encodeValue ρ] ≤ 1000000000 := by
  have c1 := skBodyHead_cost P (by includes) lay ρ hl hρ
  have c2 := skWhir_cost P (by includes) lay.stackLog ρ (by have := hl.1; omega) (by omega)
  have l1 := length_skBodyHead lay ρ hl
  rw [skBodyC.costEq P hP]
  cost_calls []
  omega

/-- **The body's trace** (`decBodyLC`) at an admissible layout and rate, whatever the events: at
most `2·10^9`. -/
theorem decBodyL_cost (hP : Includes P decBodyLC.costDeps) (lay : LayoutLite) (ρ : ℕ) (h : List EvP)
    (hl : LayOk lay) (hρ : ρ ≤ 4) :
    machineCost P decBodyLC.costIdx [encodeValue lay, encodeValue ρ, encodeValue h] ≤ 2000000000 := by
  have l1 := length_skBodyHead lay ρ hl
  have c1 := skBodyHead_cost P (by includes) lay ρ hl hρ
  have c2 := decWhirCutP_cost P (by includes) lay.stackLog ρ
    (List.drop (skBodyHead lay ρ).length h) (by have := hl.1; omega) (by omega)
  rw [decBodyLC.costEq P hP]
  cost_calls []
  omega

/-! ### The announced sizes -/

theorem skKToNat_lt (a : K) : kToNat a < 2 ^ 64 := by
  unfold kToNat; exact a.toBitVec.isLt

theorem skLength_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, -, rs, hrs, rfl⟩ := h
    simp [skLength_of_mapM hrs]

/-- `List.lookup` (`lookup.c388`) of a word in word-keyed pairs: `15` per pair, `3`. -/
theorem skLookup_cost (hP : Includes P Auto.List.lookup.c388.costDeps) (a : ℕ) (ha : a < 2 ^ 64) :
    ∀ l : List (ℕ × ℕ), (∀ p ∈ l, p.1 < 2 ^ 64) →
      machineCost P Auto.List.lookup.c388.costIdx [encodeValue a, encodeValue l] ≤ 15 * l.length + 3
  | [], _ => by rw [Auto.List.lookup.c388.costEq P hP]; simp
  | (k, v) :: l, h => by
    rw [Auto.List.lookup.c388.costEq P hP]
    have := skLookup_cost hP a ha l (fun p hp ↦ h p (by simp [hp]))
    have hk := h (k, v) (by simp)
    dsimp only at hk ⊢
    rw [limbs_of_lt ha, limbs_of_lt hk]
    simp only [List.length_cons]
    cases (a == k) <;> dsimp only <;> omega

theorem skLookup_mem {a b : ℕ} : ∀ {l : List (ℕ × ℕ)}, l.lookup a = some b → ∃ k, (k, b) ∈ l
  | [], h => by simp at h
  | (k, v) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · obtain rfl := Option.some.inj h; exact ⟨k, by simp⟩
    · obtain ⟨k', hk'⟩ := skLookup_mem h; exact ⟨k', by simp [hk']⟩

theorem skSlot_lt {c v : ℕ} (h : qkeccakSlot c = some v) : v < 64 := by
  have := keccakInLit; have := keccakOutLit; have := qkeccakSlotsLit; have := qkeccakSpareLit
  unfold qkeccakSlot at h
  dsimp only at h
  split at h
  · split at h
    · next k hk =>
      obtain rfl := Option.some.inj h
      have := List.mem_of_find?_eq_some hk
      simp only [List.mem_range] at this
      omega
    · split at h
      · obtain rfl := Option.some.inj h
        omega
      · simp at h
  · simp at h

/-- `qkeccak_slot` (`qkeccakSlot.c384`) of a word-sized column: at most `3000`. -/
theorem skQkeccakSlot_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.qkeccakSlot.c384.costDeps)
    (column : ℕ) (hc : column < 2 ^ 64) :
    machineCost P Auto.LeanVM.Protocol.Verifier.qkeccakSlot.c384.costIdx [encodeValue column] ≤ 3000 := by
  have hk := skConsts
  have := keccakInLit; have := keccakOutLit; have := qkeccakSlotsLit; have := qkeccakSpareLit
  have := keccakIxLit
  have hb : globalColumnBases.getD opKeccak 0 = 48 := by decide +kernel
  have hgl : globalColumnBases.length = 6 := by decide +kernel
  rw [Auto.LeanVM.Protocol.Verifier.qkeccakSlot.c384.costEq P hP]
  have c1 := getD_cost P (by includes) globalColumnBases opKeccak 0 (by omega)
  have c2 := rangeLoop_cost P (by includes) qkeccakSpare [] (by omega)
  have c3 := find_cost P (by includes) _ (.closure Auto.LeanVM.Protocol.Verifier.qkeccakSlot.c384.lam0.costIdx
      [encodeValue (column - globalColumnBases.getD opKeccak 0), encodeValue (globalColumnBases.getD opKeccak 0)])
    (fun x ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Verifier.qkeccakSlot.c384.lam0.costSpec P (by includes)
      _ _ x)) 40 (List.range qkeccakSpare) (fun x hx ↦ by
        simp only [List.mem_range] at hx
        rw [appCost_fn]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [Auto.LeanVM.Protocol.Verifier.qkeccakSlot.c384.lam0.costEq P (by includes),
          Auto.LeanVM.Protocol.Verifier.spareLocal.c387.costEq P (by includes)]
        have : spareLocal x ≤ 100 := by unfold spareLocal; split_ifs <;> omega
        cost_calls []
        split_ifs <;> omega)
  simp only [List.length_range] at c3
  have hW : ∀ x : ℕ, x ≤ 0 → limbCount x ≤ 1 := fun x _ ↦ (limbs_of_lt (by omega)).le
  rcases hf : List.find? (fun x ↦ decide (spareLocal x = column - globalColumnBases.getD opKeccak 0))
    (List.range qkeccakSpare) with _ | k
  · dsimp only
    limbs_bound hW
    split_ifs <;> omega
  · have := List.mem_of_find?_eq_some hf
    simp only [List.mem_range] at this
    dsimp only
    limbs_bound hW
    split_ifs <;> omega

/-- `columnKappasL` (`columnKappasL.c375`) at six heights of at most `30`: at most `20000`. -/
theorem skColumnKappasL_cost (hP : Includes P columnKappasL.c375.costDeps) (lm : ℕ) (hs : List ℕ)
    (hl : hs.length ≤ 6) (h : ∀ x ∈ hs, x ≤ 30) :
    machineCost P columnKappasL.c375.costIdx [encodeValue lm, encodeValue hs] ≤ 20000 := by
  have hk := skConsts
  have hw : ∀ x ∈ tableWidthsL, x ≤ 68 := by decide
  have hwl : tableWidthsL.length = 6 := rfl
  rw [columnKappasL.c375.costEq P hP]
  have c1 := getD_cost P (by includes) hs opKeccak 0 (by omega)
  have g1 := getD_le_of hs opKeccak 30 h
  have c2 := rangeLoop_cost P (by includes) nTables [] (by omega)
  have c3 := map_cost P (by includes) _ (.closure columnKappasL.c375.lam0.costIdx [encodeValue hs])
    (fun t ↦ RunsApp.of_spec (columnKappasL.c375.lam0.costSpec P (by includes) hs t)) 1300
    (List.range nTables) (fun t ht ↦ by
      simp only [List.mem_range] at ht
      rw [appCost_fn, List.singleton_append, List.length_singleton,
        columnKappasL.c375.lam0.costEq P (by includes)]
      have := Auto.LeanVM.Protocol.EndToEnd.Sound.tableWidthsL.c377.costEq P (by includes)
      have := getD_cost P (by includes) tableWidthsL t 0 (by omega)
      have := getD_cost P (by includes) hs t 0 (by omega)
      have hwt := getD_le_of tableWidthsL t 68 hw
      have := replicate_cost P (by includes) (hs.getD t 0) (tableWidthsL.getD t 0) (by omega)
      omega)
  have c4 := flatten_cost P (by includes) 68
    (List.map (fun t ↦ List.replicate (tableWidthsL.getD t 0) (hs.getD t 0)) (List.range nTables))
    (fun l hl ↦ by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hl
      simp only [List.length_replicate]
      exact getD_le_of tableWidthsL t 68 hw)
  simp only [List.length_map, List.length_range] at c3 c4
  cost_calls []
  simp only [List.length_cons, List.length_nil] at *
  omega

theorem skColumnKappasL_facts (lm : ℕ) (hs : List ℕ) (h : ∀ x ∈ hs, x ≤ 30) :
    (columnKappasL lm hs).length = 116 ∧ ∀ x ∈ columnKappasL lm hs, x ≤ lm ∨ x ≤ 36 := by
  have hk := skConsts
  refine ⟨by simp [columnKappasL, tableWidthsL, nTables, List.range_succ], fun x hx ↦ ?_⟩
  have := getD_le_of hs opKeccak 30 h
  unfold columnKappasL at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · obtain ⟨t, -, ht⟩ := List.mem_flatMap.1 hx
    have := List.eq_of_mem_replicate ht
    have := getD_le_of hs t 30 h
    omega

theorem skStack_facts (kappas : List ℕ) (h : ∀ x ∈ kappas, x ≤ 40) :
    (stack kappas).1.length ≤ 52 ∧ (∀ p ∈ (stack kappas).1, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 63) ∧
      (stack kappas).2 ≤ 64 := by
  have hsc : stackColumns.length = 52 := by decide
  have hsx : ∀ x ∈ stackColumns, x ≤ 115 := by decide
  have hb := stackOffsets_bounds (stackColumns.map fun c ↦ kappas.getD c 0)
    (by simp [hsc]) (fun x hx ↦ by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact getD_le_of kappas c 40 h)
  rw [stackLit]
  unfold stackOfColumns
  dsimp only
  refine ⟨?_, fun p hp ↦ ?_, ?_⟩
  · rw [List.length_zip, hsc]; omega
  · obtain ⟨a, b⟩ := p
    obtain ⟨h1, h2⟩ := List.of_mem_zip hp
    exact ⟨by have := hsx a h1; omega, hb.1 b h2⟩
  · have : Whir.minLogStack = 16 := rfl
    have := hb.2
    omega

/-- `stack` on the stacked columns (`stackOfColumns.c378`): at most `975000000`. -/
theorem skStackOfColumns_cost (hP : Includes P Auto.LeanVM.Cost.AS.stackOfColumns.c378.costDeps)
    (kappas : List ℕ) (hl : kappas.length ≤ 200) (h : ∀ x ∈ kappas, x ≤ 40) :
    machineCost P Auto.LeanVM.Cost.AS.stackOfColumns.c378.costIdx [encodeValue kappas] ≤ 975000000 := by
  have hsc : stackColumns.length = 52 := by decide
  have hsx : ∀ x ∈ stackColumns, x ≤ 115 := by decide
  have hsizes : ∀ x ∈ stackColumns.map (fun c ↦ kappas.getD c 0), x ≤ 40 := fun x hx ↦ by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact getD_le_of kappas c 40 h
  have hb := stackOffsets_bounds (stackColumns.map fun c ↦ kappas.getD c 0) (by simp [hsc]) hsizes
  have hcol : machineCost P Auto.LeanVM.Cost.AS.stackColumns.c380.costIdx [] ≤ 3000 := by
    rw [Auto.LeanVM.Cost.AS.stackColumns.c380.costEq P (by includes)]
    have := rangeLoop_cost P (by includes) 45 [] (by omega)
    have := map_cost P (by includes) (fun x : ℕ ↦ x + 3)
      (.closure Auto.LeanVM.Cost.AS.stackColumns.c380.lam0.costIdx [])
      (fun x ↦ RunsApp.of_spec (Auto.LeanVM.Cost.AS.stackColumns.c380.lam0.costSpec P (by includes) x))
      3 (List.range 45) (fun x hx ↦ by
        simp only [List.mem_range] at hx
        rw [appCost_fn, List.nil_append, List.length_nil,
          Auto.LeanVM.Cost.AS.stackColumns.c380.lam0.costEq P (by includes),
          limbs_of_lt (by omega : x + 3 < 2 ^ 64), limbs_of_lt (by omega : x < 2 ^ 64)]
        simp)
    simp only [List.length_range] at this
    cost_calls []
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil] at *
    omega
  rw [Auto.LeanVM.Cost.AS.stackOfColumns.c378.costEq P hP]
  have c1 := map_cost P (by includes) (fun c ↦ kappas.getD c 0)
    (.closure Auto.LeanVM.Cost.AS.stackOfColumns.c378.lam0.costIdx [encodeValue kappas])
    (fun c ↦ RunsApp.of_spec (Auto.LeanVM.Cost.AS.stackOfColumns.c378.lam0.costSpec P (by includes)
      kappas c)) 3100 stackColumns (fun c hc ↦ by
        have := hsx c hc
        rw [appCost_fn, List.singleton_append, List.length_singleton,
          Auto.LeanVM.Cost.AS.stackOfColumns.c378.lam0.costEq P (by includes)]
        have := getD_cost P (by includes) kappas c 0 (by omega)
        omega)
  have c2 := stackOffsets_cost P (by includes) (stackColumns.map fun c ↦ kappas.getD c 0)
    (by simp [hsc]) hsizes
  have c3 := listZipWith_le P (by includes) (fun a b : ℕ ↦ (a, b))
    (.closure Auto.LeanVM.Cost.AS.stackOfColumns.c378.lam1.costIdx [])
    (fun a b ↦ RunsApp.of_spec (Auto.LeanVM.Cost.AS.stackOfColumns.c378.lam1.costSpec P (by includes)
      a b)) 5 stackColumns (stackOffsets (stackColumns.map fun c ↦ kappas.getD c 0)).1
    (fun a _ b _ ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil,
        Auto.LeanVM.Cost.AS.stackOfColumns.c378.lam1.costEq P (by includes)])
  have : Whir.minLogStack = 16 := rfl
  have hmin : min stackColumns.length (stackOffsets (stackColumns.map fun c ↦ kappas.getD c 0)).1.length
      ≤ 52 := by rw [hsc]; omega
  rw [hsc] at c1
  have := hb.2
  cost_calls []
  have : (5 + 19) * min stackColumns.length
      (stackOffsets (stackColumns.map fun c ↦ kappas.getD c 0)).1.length ≤ 24 * 52 :=
    Nat.mul_le_mul_left _ hmin
  split_ifs <;> omega

/-- One placement of `buildLayoutLite` (`buildLayoutLite.c372.lam2`): at most `10000`. -/
theorem skLayoutLam2_cost (hP : Includes P buildLayoutLite.c372.lam2.costDeps) (fst : List (ℕ × ℕ))
    (hf : fst.length ≤ 52) (hfp : ∀ p ∈ fst, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 63) (kappa column : ℕ)
    (hk : kappa ≤ 66) (hc : column < 2 ^ 64) :
    appCost P (.closure buildLayoutLite.c372.lam2.costIdx [encodeValue fst])
      [encodeValue (kappa, column)] ≤ 10000 := by
  have hq : qkeccak = 2 := rfl
  rw [appCost_fn, List.singleton_append, List.length_singleton,
    buildLayoutLite.c372.lam2.costEq P (by includes)]
  dsimp only
  have c1 := skQkeccakSlot_cost P (by includes) column hc
  have c2 := skLookup_cost P (by includes) column hc fst (fun p hp ↦ (hfp p hp).1)
  have c3 := skLookup_cost P (by includes) qkeccak (by omega) fst (fun p hp ↦ (hfp p hp).1)
  have c4 : ∀ o : Option ℕ, machineCost P Auto.Option.map.c90.costIdx
      [.closure buildLayoutLite.c372.lam2.lam1.costIdx [encodeValue kappa], encodeValue o] ≤ 14 :=
    fun o ↦ optionMap_cost P (by includes) _
      (.closure buildLayoutLite.c372.lam2.lam1.costIdx [encodeValue kappa])
      (fun i ↦ RunsApp.of_spec (buildLayoutLite.c372.lam2.lam1.costSpec P (by includes) kappa i)) 6 o
      (fun i _ ↦ by
        rw [appCost_fn, List.singleton_append, List.length_singleton,
          buildLayoutLite.c372.lam2.lam1.costEq P (by includes)])
  rcases hs : qkeccakSlot column with _ | val
  · dsimp only
    have := c4 (List.lookup column fst)
    omega
  · have hv := skSlot_lt hs
    dsimp only
    have := c4 (Option.map (fun x ↦ x + val <<< kappa) (List.lookup qkeccak fst))
    have c5 := optionMap_cost P (by includes) _
      (.closure buildLayoutLite.c372.lam2.lam0.costIdx [encodeValue val, encodeValue kappa])
      (fun x ↦ RunsApp.of_spec (buildLayoutLite.c372.lam2.lam0.costSpec P (by includes) val kappa x)) 20
      (List.lookup qkeccak fst) (fun x hx ↦ by
        obtain ⟨k, hkx⟩ := skLookup_mem hx
        have hx63 := (hfp _ hkx).2
        have hsh : val <<< kappa < 2 ^ 72 := by
          rw [Nat.shiftLeft_eq]
          calc val * 2 ^ kappa < 2 ^ 6 * 2 ^ 66 :=
                Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by norm_num) hk)
                  (by positivity)
            _ = 2 ^ 72 := by norm_num
        rw [appCost_fn]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [buildLayoutLite.c372.lam2.lam0.costEq P (by includes)]
        have := limbs_le_two (by omega : val <<< kappa < 2 ^ 128)
        have := limbs_le_two (by omega : x + val <<< kappa < 2 ^ 128)
        have := limbs_of_lt (by omega : val < 2 ^ 64)
        have := limbs_of_lt (by omega : kappa < 2 ^ 64)
        have := limbs_of_lt (by omega : x < 2 ^ 64)
        omega)
    omega

theorem skBuildLayoutLite_stackLog {bc : List K} {lm : ℕ} {rows : List ℕ} {L : LayoutLite}
    (h : buildLayoutLite bc lm rows = some L) : L.stackLog ≤ 64 := by
  unfold buildLayoutLite at h
  split at h
  · simp at h
  · split_ifs at h with hc
    obtain ⟨-, h2, h3, -⟩ := hc
    have hmt : maxTableLog = 30 := rfl
    have hrows : ∀ r ∈ rows, r ≤ 2 ^ 30 := fun r hr' ↦ by
      have := List.all_eq_true.1 h3 r hr'
      simp only [decide_eq_true_eq] at this
      rw [hmt] at this
      exact this
    obtain ⟨hh1, hh2⟩ := heights_facts rows hrows
    have kf := skColumnKappasL_facts lm _ hh2
    have hm : maxLogMemory = 30 := rfl
    have hsf := skStack_facts (columnKappasL lm (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor)
      rows tableLogFloors)) (fun x hx ↦ by have := kf.2 x hx; omega)
    simp only [Option.some.injEq] at h
    subst h
    exact hsf.2.2

/-- `buildLayout` on the sizes (`buildLayoutLite.c372`): `8` per bytecode word, `2·10^9`. -/
theorem skBuildLayoutLite_cost (hP : Includes P buildLayoutLite.c372.costDeps) (bytecode : List K)
    (lm : ℕ) (rows : List ℕ) (hb : bytecode.length < 2 ^ 63) (hm : lm < 2 ^ 64)
    (hr : ∀ r ∈ rows, r < 2 ^ 64) (hl : rows.length ≤ 6) :
    machineCost P buildLayoutLite.c372.costIdx [encodeValue bytecode, encodeValue lm, encodeValue rows] ≤
      8 * bytecode.length + 2000000000 := by
  have hk := skConsts
  have hmt : maxTableLog = 30 := rfl
  have hmm : maxLogMemory = 30 := rfl
  have hfl : tableLogFloors = [0, 0, 0, 0, 0, 9] := rfl
  have : minLogMemory = 1 := rfl
  have : LeanVM.Protocol.Verifier.maxLogBytecode = 30 := rfl
  rw [buildLayoutLite.c372.costEq P hP]
  have c1 := length_cost P (by includes) bytecode (by omega)
  have c2 := log2Strict_cost P (by includes) bytecode.length (by omega)
  have hW : ∀ x : ℕ, x ≤ 0 → limbCount x ≤ 1 := fun x _ ↦ (limbs_of_lt (by omega)).le
  rcases hv : log2Strict bytecode.length with _ | val
  · dsimp only; omega
  dsimp only
  have hval := log2Strict_le (by omega) hv
  have c3 := all_cost P (by includes) _ (.closure buildLayoutLite.c372.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (buildLayoutLite.c372.lam0.costSpec P (by includes) x)) 10 rows
    (fun x hx ↦ by
      have := hr x hx
      rw [appCost_fn, List.nil_append, List.length_nil, buildLayoutLite.c372.lam0.costEq P (by includes),
        hmt, limbs_shift (by omega), limbs_of_lt (by omega : (30 : ℕ) < 2 ^ 64), limbs_of_lt (hr x hx),
        limbs_of_lt (by norm_num : (2 : ℕ) ^ 30 < 2 ^ 64)]
      simp)
  have c4 := length_cost P (by includes) rows (by omega)
  by_cases hc : minLogMemory ≤ lm ∧ lm ≤ maxLogMemory ∧ rows.all (· ≤ 2 ^ maxTableLog) ∧
      bytecodeSlotBits ≤ val ∧ val ≤ LeanVM.Protocol.Verifier.maxLogBytecode + bytecodeSlotBits ∧
      rows.length = nTables
  swap
  · rw [ite_eq_right hc]
    limbs_bound hW
    split_ifs <;> omega
  rw [ite_eq_left hc]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  have hrows : ∀ r ∈ rows, r ≤ 2 ^ 30 := fun r hr' ↦ by
    have := List.all_eq_true.1 h3 r hr'
    simp only [decide_eq_true_eq] at this
    rw [hmt] at this
    exact this
  obtain ⟨hh1, hh2⟩ := heights_facts rows hrows
  have kf := skColumnKappasL_facts lm _ hh2
  have c5 := skColumnKappasL_cost P (by includes) lm _ hh1 hh2
  have c6 := skStackOfColumns_cost P (by includes) (columnKappasL lm (List.zipWith
    (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors)) (by omega)
    (fun x hx ↦ by have := kf.2 x hx; omega)
  have hsf := skStack_facts (columnKappasL lm (List.zipWith
    (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors))
    (fun x hx ↦ by have := kf.2 x hx; omega)
  have c7 := listZipWith_le P (by includes) (fun rows floor ↦ max (log2Ceil rows) floor)
    (.closure buildLayoutLite.c372.lam1.costIdx [])
    (fun a b ↦ RunsApp.of_spec (buildLayoutLite.c372.lam1.costSpec P (by includes) a b)) 2000 rows
    tableLogFloors (fun a ha b hb ↦ by
      have := hr a ha
      have hb9 : b ≤ 9 := by rw [hfl] at hb; simp at hb; omega
      have := log2Ceil_lt (hr a ha)
      have := bitLength_cost' P (by includes) (a - 1)
      rw [appCost_fn, List.nil_append, List.length_nil, buildLayoutLite.c372.lam1.costEq P (by includes)]
      cost_calls []
      split_ifs <;> omega)
  have c8 := Extractor.tableLogFloorsC.costEq P (by includes)
  have c9 := zipIdx_cost P (by includes) (columnKappasL lm (List.zipWith
    (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors)) 0 (by omega)
  rcases hst : stack (columnKappasL lm (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor)
    rows tableLogFloors)) with ⟨fst, snd⟩
  rw [hst] at hsf
  dsimp only at hsf ⊢
  have c10 := map_cost P (by includes) _ (.closure buildLayoutLite.c372.lam2.costIdx [encodeValue fst])
    (fun x ↦ RunsApp.of_spec (buildLayoutLite.c372.lam2.costSpec P (by includes) fst x)) 10000
    (columnKappasL lm (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows
      tableLogFloors)).zipIdx (fun x hx ↦ by
      obtain ⟨k, c⟩ := x
      obtain ⟨-, hc', hkx⟩ := List.mem_zipIdx hx
      have hk66 : k ≤ 66 := by
        have hmem : k ∈ columnKappasL lm (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor)
            rows tableLogFloors) := by
          rw [hkx]; exact List.getElem_mem _
        have := kf.2 k hmem
        omega
      exact skLayoutLam2_cost P (by includes) fst hsf.1 hsf.2.1 k c hk66 (by omega))
  rw [List.length_zipIdx, kf.1] at c10
  rw [kf.1] at c9
  have : min rows.length tableLogFloors.length ≤ 6 := by
    rw [hfl]; simp only [List.length_cons, List.length_nil]; omega
  limbs_bound hW
  have : (2000 + 19) * min rows.length tableLogFloors.length ≤ 2019 * 6 := Nat.mul_le_mul_left _ this
  split_ifs
  omega

/-- The sizes from the announced values (`sizesOfL.c368`): `26` per value, `8` per bytecode word,
`2·10^9 + 1000`. -/
theorem skSizesOfL_cost (hP : Includes P sizesOfL.c368.costDeps) (bytecode : List K) (ann : List E)
    (hb : bytecode.length < 2 ^ 63) :
    machineCost P sizesOfL.c368.costIdx [encodeValue bytecode, encodeValue ann] ≤
      26 * ann.length + 8 * bytecode.length + 2000001000 := by
  have hk := skConsts
  rw [sizesOfL.c368.costEq P hP]
  have hall := all_cost P (by includes) (fun value : E ↦ decide (value.limb 1 = 0))
    (.closure sizesOfL.c368.lam0.costIdx [])
    (fun v ↦ RunsApp.of_spec (sizesOfL.c368.lam0.costSpec P (by includes) v)) 4 ann (fun v _ ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, sizesOfL.c368.lam0.costEq P (by includes)])
  have htl : (List.take nTables (List.drop 1 ann)).length ≤ 6 := by
    have := List.length_take_le nTables (List.drop 1 ann); omega
  have hm := map_cost P (by includes) (fun value : E ↦ kToNat (value.limb 0))
    (.closure sizesOfL.c368.lam1.costIdx [])
    (fun v ↦ RunsApp.of_spec (sizesOfL.c368.lam1.costSpec P (by includes) v)) 2
    (List.take nTables (List.drop 1 ann)) (fun v _ ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, sizesOfL.c368.lam1.costEq P (by includes)])
  have hrv := reverseAux_cost P (by includes) ann []
  have hbl := skBuildLayoutLite_cost P (by includes) bytecode (kToNat ((ann.headD 0).limb 0))
    (List.map (fun value ↦ kToNat (value.limb 0)) (List.take nTables (List.drop 1 ann))) hb
    (skKToNat_lt _) (fun r hr' ↦ by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hr'
      exact skKToNat_lt _) (by simp only [List.length_map]; omega)
  have hbd := bind_le P (by includes) _ (.closure sizesOfL.c368.lam2.costIdx
      [encodeValue (kToNat ((ann.getLastD 0).limb 0))])
    (fun L ↦ RunsApp.of_spec (sizesOfL.c368.lam2.costSpec P (by includes) _ L))
    (buildLayoutLite bytecode (kToNat ((ann.headD 0).limb 0))
      (List.map (fun value ↦ kToNat (value.limb 0)) (List.take nTables (List.drop 1 ann)))) 40
      (fun L hL ↦ by
      have := skBuildLayoutLite_stackLog hL
      have : Whir.minLogStack = 16 := rfl
      have : Whir.maxLogStack = 30 := rfl
      rw [appCost_fn, List.singleton_append, List.length_singleton,
        sizesOfL.c368.lam2.costEq P (by includes)]
      cost_calls []
      split_ifs <;> omega)
  have hk1 := skKToNat_lt ((ann.getLastD 0).limb 0)
  have c1 := listCases_le ann 5 3
  have c2 := listCases_le ann.reverse 5 3
  cost_calls []
  split_ifs <;> omega

/-- **The announced sizes** (`decSizesLC`) from `n` events: at most
`80·n + 8·|bytecode| + 10^10`. -/
theorem decSizesL_cost (hP : Includes P decSizesLC.costDeps) (bytecode : List K) (h : List EvP)
    (hb : bytecode.length < 2 ^ 63) (hn : h.length < 2 ^ 60) :
    machineCost P decSizesLC.costIdx [encodeValue bytecode, encodeValue h] ≤
      80 * h.length + 8 * bytecode.length + 10 ^ 10 := by
  rw [decSizesLC.costEq P hP]
  have h1 := mapMReads_cost P (by includes) (by includes) h
  have h2 := bind_le P (by includes) _ (.closure decSizesLC.lam0.costIdx [encodeValue bytecode])
    (fun a ↦ RunsApp.of_spec (decSizesLC.lam0.costSpec P (by includes) bytecode a))
    (List.mapM (fun p : EvP ↦ p.1) h) (26 * h.length + 8 * bytecode.length + 2000001004)
    (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, decSizesLC.lam0.costEq P (by includes)]
      have hl := skLength_of_mapM ha
      have := skSizesOfL_cost P (by includes) bytecode a hb
      rw [hl] at this
      simp only [List.length_singleton]
      omega)
  omega

end Front

end

end LeanVM.Cost.Bounds.AS
