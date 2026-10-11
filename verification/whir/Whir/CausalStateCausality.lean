import Whir.CausalExecution
import Whir.CausalPositions

/-! Prefix causality of total actual execution, including malformed replies. -/
namespace Whir.CausalStateCausality
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalRefinement
open CausalPositions

set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[simp] theorem challenge_folds_size (c : Config) (t : Tape c) (i : Fin c.folds.size) :
    (challenges c t).levels[i.val]!.folds.size = c.folds[i.val]! := by
  simp [challenges, _root_.getElem!_pos, i.isLt]

@[simp] theorem challenge_oods_size (c : Config) (t : Tape c) (i : Fin c.folds.size) :
    (challenges c t).levels[i.val]!.oodPoints.size = oodCount c i.val := by
  simp [challenges, _root_.getElem!_pos, i.isLt]

@[simp] theorem challenge_fold (c : Config) (t : Tape c) (i : Fin c.folds.size)
    (j : Fin c.folds[i.val]!) :
    (challenges c t).levels[i.val]!.folds[j.val]! = get (.fold i j) t := by
  have h := challengeBatch_eq (.fold i j) t
  exact Batch.fold.inj h |>.2.2

@[simp] theorem challenge_ood (c : Config) (t : Tape c) (i : Fin c.folds.size)
    (j : Fin (oodCount c i.val)) :
    (challenges c t).levels[i.val]!.oodPoints[j.val]! = Array.ofFn (get (.ood i j) t) := by
  have h := challengeBatch_eq (.ood i j) t
  exact Batch.ood.inj h |>.2.2

@[simp] theorem challenge_query (c : Config) (t : Tape c) (i : Fin c.folds.size) :
    (challenges c t).levels[i.val]!.querySqueezes = Array.ofFn (get (.query i) t).1 ∧
    (challenges c t).levels[i.val]!.lambda = (get (.query i) t).2 := by
  have h := challengeBatch_eq (.query i) t
  exact Batch.query.inj h |>.2

/-- Total decoding is a field projection even when tags are malformed. -/
theorem proof_level (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i : Fin input.config.folds.size) :
    (proof input strategy t).levels[i.val]! = decodedLevel input.config
      (challenges input.config t)
      (run strategy input [] (visibleBatches input.config t.1 (challenges input.config t))).toArray i := by
  simp [proof, CausalTerminal.proof, decodedOpening, _root_.getElem!_pos, i.isLt]

theorem proof_fold (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!) :
    (proof input strategy t).levels[i.val]!.afterFold[j.val]! =
      foldField (run strategy input []
        (visibleBatches input.config t.1 (challenges input.config t)))[levelStart
          (challenges input.config t) i.val + j.val]! := by
  rw [proof_level]
  dsimp only [decodedLevel]
  rw [_root_.getElem!_pos _ _ (by simpa using j.isLt)]
  simp

/-- Oracle replay consumes precisely the earlier fold scalars. -/
theorem rowAt_congr (a : Array E) (left right : Array E) (j : Nat)
    (h : ∀ k, k < j → left[k]! = right[k]!) :
    OracleReplay.rowAt left a j = OracleReplay.rowAt right a j := by
  unfold OracleReplay.rowAt
  apply List.foldl_ext
  intro b k hk
  exact congrArg (Concrete.foldLow b) (h k (List.mem_range.mp hk))

theorem oracleAt_congr (base : Bool) (k : Nat) (root : Oracle) (left right : Array E)
    (j : Nat) {N : Nat} (h : ∀ l, l < j → left[l]! = right[l]!) :
    OracleReplay.oracleAt base k root left j (N := N) =
      OracleReplay.oracleAt base k root right j := by
  funext lane q
  simp only [OracleReplay.oracleAt, rowAt_congr _ left right j h]

theorem decodedLevel_prefix (c : Config) (left right : Challenges)
    (i : Nat) (cs : left.levels[i]! = right.levels[i]!)
    (start : levelStart left i = levelStart right i)
    (strategy other : Strategy) (input : Public) (bs ds : List Batch)
    (past : ∀ n, n < levelStart left (i+1) →
      (run strategy input [] bs)[n]! = (run other input [] ds)[n]!) :
    decodedLevel c left (run strategy input [] bs).toArray i =
      decodedLevel c right (run other input [] ds).toArray i := by
  have bound := levelStart_succ left i
  have ans (n : Nat) (hn : n < levelStart left (i+1)) :
      (run strategy input [] bs).toArray[n]! =
        (run other input [] ds).toArray[n]! := by simpa using past n hn
  unfold decodedLevel
  dsimp only
  rw [← cs, ← start]
  congr 1
  · apply congrArg Array.ofFn
    funext j
    rw [ans _ (by omega)]
  · split_ifs with h
    · rw [ans _ (by omega)]
    · rfl
  · apply congrArg Array.ofFn
    funext j
    rw [ans _ (by omega)]
  · rw [ans _ (by omega)]
  · rw [ans _ (by omega)]

theorem levelAt_congr (input : Public) (strategy other : Strategy) (t u : Tape input.config)
    (i : Nat) (initial : CausalExecution.initial input strategy t =
      CausalExecution.initial input other u)
    (cs : ∀ k, k < i → (challenges input.config t).levels[k]! =
      (challenges input.config u).levels[k]!)
    (ps : ∀ k, k < i → (proof input strategy t).levels[k]! =
      (proof input other u).levels[k]!) :
    levelAt input strategy t i = levelAt input other u i := by
  induction i with
  | zero => exact initial
  | succ i ih =>
    rw [levelAt_succ, levelAt_succ, ih (fun k hk => cs k (by omega))
      (fun k hk => ps k (by omega))]
    simp only [next, cs i (by omega), ps i (by omega)]

theorem foldAt_congr (input : Public) (strategy other : Strategy) (t u : Tape input.config)
    (i j : Nat) (initial : levelAt input strategy t i = levelAt input other u i)
    (cs : ∀ k, k < j → (challenges input.config t).levels[i]!.folds[k]! =
      (challenges input.config u).levels[i]!.folds[k]!)
    (ps : ∀ k, k < j → (proof input strategy t).levels[i]!.afterFold[k]! =
      (proof input other u).levels[i]!.afterFold[k]!) :
    foldAt input strategy t i j = foldAt input other u i j := by
  induction j with
  | zero => exact initial
  | succ j ih =>
    rw [foldAt_succ, foldAt_succ, ih (fun k hk => cs k (by omega))
      (fun k hk => ps k (by omega))]
    simp only [foldStep, cs j (by omega), ps j (by omega)]

theorem levelStart_pos (ch : Challenges) (i : Nat) : 0 < levelStart ch i := by
  unfold levelStart
  omega

theorem levelStart_mono (ch : Challenges) {i k : Nat} (h : i ≤ k) :
    levelStart ch i ≤ levelStart ch k := by
  induction h with
  | refl => exact le_rfl
  | @step k h ih => rw [levelStart_succ]; omega

theorem initial_set (input : Public) (strategy : Strategy)
    (q : Coordinate input.config) (t : Tape input.config) (x : Sample q)
    (before : 0 < position q) :
    CausalExecution.initial input strategy (set q t x) =
      CausalExecution.initial input strategy t := by
  have hq : Coordinate.initial ≠ q := by
    intro h
    subst q
    simp [position, visibleCoordinates] at before
  have scalar : (set q t x).1 = t.1 := get_set_ne q .initial t x hq
  have sent := field_before q t x strategy input initialField 0 before
  simpa only [CausalExecution.initial, scalar, proof, CausalTerminal.proof,
    decodedOpening, List.getElem!_toArray] using
      congrArg (fun m => (⟨input.config.logN,
        ⟨(batchClaims (2 ^ input.config.logN) input.claims t.1).weight,
          (batchClaims (2 ^ input.config.logN) input.claims t.1).value, m⟩,
        liftRoot input.root⟩ : CheckedState)) sent

theorem challenge_level_set (c : Config) (q : Coordinate c) (t : Tape c) (x : Sample q)
    (i : Fin c.folds.size) (before : levelStart (challenges c t) (i.val+1) ≤ position q) :
    (challenges c (set q t x)).levels[i.val]! = (challenges c t).levels[i.val]! := by
  have limit : levelStart (challenges c t) i.val + c.folds[i.val]! + oodCount c i.val + 1 ≤
      position q := by simpa only [levelStart_succ, challenge_folds_size, challenge_oods_size] using before
  have hf : ((set q t x).2.1 i).1 = (t.2.1 i).1 := by
    funext j
    exact get_set_ne q (.fold i j) t x (by
      intro h
      have hp := congrArg position h
      rw [position_fold i j t] at hp
      omega)
  have ho : ((set q t x).2.1 i).2.1 = (t.2.1 i).2.1 := by
    funext j
    exact get_set_ne q (.ood i j) t x (by
      intro h
      have hp := congrArg position h
      rw [position_ood i j t] at hp
      omega)
  have hq : ((set q t x).2.1 i).2.2 = (t.2.1 i).2.2 :=
    get_set_ne q (.query i) t x (by
      intro h
      have hp := congrArg position h
      rw [position_query i t] at hp
      omega)
  have ht : (set q t x).2.1 i = t.2.1 i := Prod.ext hf (Prod.ext ho hq)
  simp [challenges, _root_.getElem!_pos, i.isLt, ht]

theorem proof_level_set (input : Public) (strategy : Strategy)
    (q : Coordinate input.config) (t : Tape input.config) (x : Sample q)
    (i : Fin input.config.folds.size)
    (before : levelStart (challenges input.config t) (i.val+1) ≤ position q) :
    (proof input strategy (set q t x)).levels[i.val]! = (proof input strategy t).levels[i.val]! := by
  rw [proof_level, proof_level]
  apply decodedLevel_prefix
  · exact challenge_level_set input.config q t x i before
  · exact levelStart_set q t x i.val
  · intro n hn
    apply field_before q t x strategy input id n
    rw [levelStart_set] at hn
    omega

theorem levelAt_set (input : Public) (strategy : Strategy)
    (q : Coordinate input.config) (t : Tape input.config) (x : Sample q)
    (i : Nat) (hi : i ≤ input.config.folds.size)
    (before : levelStart (challenges input.config t) i ≤ position q) :
    levelAt input strategy (set q t x) i = levelAt input strategy t i := by
  apply levelAt_congr
  · exact initial_set input strategy q t x (lt_of_lt_of_le (levelStart_pos _ i) before)
  · intro k hk
    exact challenge_level_set input.config q t x ⟨k, by omega⟩
      ((levelStart_mono _ (by omega : k+1 ≤ i)).trans before)
  · intro k hk
    exact proof_level_set input strategy q t x ⟨k, by omega⟩
      ((levelStart_mono _ (by omega : k+1 ≤ i)).trans before)

theorem foldAt_set (input : Public) (strategy : Strategy)
    (q : Coordinate input.config) (t : Tape input.config) (x : Sample q)
    (i : Fin input.config.folds.size) (j : Nat) (hj : j ≤ input.config.folds[i.val]!)
    (before : levelStart (challenges input.config t) i.val + j ≤ position q) :
    foldAt input strategy (set q t x) i.val j = foldAt input strategy t i.val j := by
  apply foldAt_congr
  · exact levelAt_set input strategy q t x i.val (by omega) (by omega)
  · intro k hk
    rw [challenge_fold input.config _ i ⟨k, by omega⟩,
      challenge_fold input.config _ i ⟨k, by omega⟩]
    apply get_set_ne
    intro h
    have hp := congrArg position h
    rw [position_fold _ _ t] at hp
    dsimp only [Fin.val_mk] at hp
    omega
  · intro k hk
    rw [proof_fold input strategy _ i ⟨k, by omega⟩,
      proof_fold input strategy _ i ⟨k, by omega⟩, levelStart_set]
    exact field_before q t x strategy input foldField
      (levelStart (challenges input.config t) i.val + k) (by omega)

theorem oracleAt_set (input : Public) (strategy : Strategy)
    (q : Coordinate input.config) (t : Tape input.config) (x : Sample q)
    (i : Fin input.config.folds.size) (j : Nat) (hj : j ≤ input.config.folds[i.val]!)
    (before : levelStart (challenges input.config t) i.val + j ≤ position q) {N : Nat} :
    OracleReplay.oracleAt (i.val == 0) input.config.folds[i.val]!
      (levelAt input strategy (set q t x) i.val).oracle
      (challenges input.config (set q t x)).levels[i.val]!.folds j (N := N) =
    OracleReplay.oracleAt (i.val == 0) input.config.folds[i.val]!
      (levelAt input strategy t i.val).oracle
      (challenges input.config t).levels[i.val]!.folds j := by
  rw [levelAt_set input strategy q t x i.val (by omega) (by omega)]
  apply oracleAt_congr
  intro k hk
  rw [challenge_fold input.config _ i ⟨k, by omega⟩,
    challenge_fold input.config _ i ⟨k, by omega⟩]
  apply get_set_ne
  intro h
  have hp := congrArg position h
  rw [position_fold _ _ t] at hp
  dsimp only [Fin.val_mk] at hp
  omega

theorem foldCandidates_set (input : Public) (strategy : Strategy)
    (q : Coordinate input.config) (t : Tape input.config) (x : Sample q)
    (i : Fin input.config.folds.size) (j : Nat) (hj : j ≤ input.config.folds[i.val]!)
    (before : levelStart (challenges input.config t) i.val + j ≤ position q) :
    foldCandidates input strategy (set q t x) i.val j =
      foldCandidates input strategy t i.val j := by
  unfold foldCandidates
  rw [oracleAt_set input strategy q t x i j hj before]

end Whir.CausalStateCausality
