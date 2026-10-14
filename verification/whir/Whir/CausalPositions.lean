import Whir.CausalProbability

namespace Whir.CausalPositions
open Concrete Protocol CausalGame CausalProbability
open Classical

private theorem idxOf_ofFn {A : Type*} [DecidableEq A] {n : Nat}
    (f : Fin n → A) (hf : Function.Injective f) (j : Fin n) :
    (List.ofFn f).idxOf (f j) = j.val := by
  have hm : f j ∈ List.ofFn f := List.mem_ofFn.mpr ⟨j, rfl⟩
  have hi := List.idxOf_lt_length_of_mem hm
  have he := List.getElem_idxOf hi
  simp only [List.getElem_ofFn] at he
  exact congrArg Fin.val (hf he)

def levelOf {c : Config} : Coordinate c → Option Nat
  | .fold i _ => some i.val
  | .ood i _ => some i.val
  | .query i => some i.val
  | _ => none

private theorem levelOf_mem {c : Config} (k : Nat) (q : Coordinate c)
    (h : q ∈ levelCoordinates c k) : levelOf q = some k := by
  unfold levelCoordinates at h
  split_ifs at h with hk
  · simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at h
    rcases h with (⟨j, rfl⟩ | ⟨j, rfl⟩) | rfl <;> rfl
  · simp at h

 theorem levelStart_eq (c : Config) (t u : Tape c) (i : Nat) :
    levelStart (challenges c t) i = levelStart (challenges c u) i := by
  simp only [levelStart, List.length_flatMap]
  congr 1
  congr 1
  apply List.map_congr_left
  intro k hk
  simp only [CausalRefinement.levelBatches_length]
  by_cases h : k < c.folds.size
  · simp [challenges, _root_.getElem!_pos, h]
  · simp [challenges, getElem!_neg, h]

 theorem levelStart_set {c : Config} (q : Coordinate c) (t : Tape c)
    (x : Sample q) (i : Nat) :
    levelStart (challenges c (set q t x)) i = levelStart (challenges c t) i :=
  levelStart_eq c _ _ i

private theorem position_level {c : Config} (i : Fin c.folds.size)
    (q : Coordinate c) (hq : q ∈ levelCoordinates c i.val) (t : Tape c) :
    position q = levelStart (challenges c t) i.val + (levelCoordinates c i.val).idxOf q := by
  have hr : List.range c.folds.size = List.range i.val ++ [i.val] ++
      (List.range (c.folds.size-(i.val+1))).map (fun x => i.val+1+x) := by
    calc
      List.range c.folds.size =
          List.range ((i.val+1)+(c.folds.size-(i.val+1))) := congrArg List.range (by omega)
      _ = _ := by rw [List.range_add, List.range_succ]
  have hl := levelOf_mem i.val q hq
  have hinit : q ∉ [Coordinate.initial] := by
    intro h
    have : q = .initial := by simpa using h
    simp [this, levelOf] at hl
  have hprior : q ∉ (List.range i.val).flatMap (levelCoordinates c) := by
    intro h
    obtain ⟨k, hk, hqk⟩ := List.mem_flatMap.mp h
    have he := levelOf_mem k q hqk
    have : i.val = k := Option.some.inj (hl.symm.trans he)
    have := List.mem_range.mp hk
    omega
  unfold position visibleCoordinates
  rw [hr]
  simp only [List.flatMap_append, List.flatMap_singleton, List.append_assoc]
  rw [List.idxOf_append_of_notMem hinit, List.idxOf_append_of_notMem hprior,
    List.idxOf_append_of_mem hq]
  have lengths : ((List.range i.val).flatMap (levelCoordinates c)).length =
      ((List.range i.val).flatMap (levelBatches (challenges c t))).length := by
    rw [← List.length_map (f := fun q => batch q (get q t))]
    simp only [List.map_flatMap]
    congr 1
    apply List.flatMap_congr
    intro k hk
    exact levelCoordinates_map c t k (lt_trans (List.mem_range.mp hk) i.isLt)
  simp only [List.length_singleton, lengths, levelStart]
  omega

@[simp] theorem position_initial (c : Config) : position (.initial : Coordinate c) = 0 := by
  simp [position, visibleCoordinates]

 theorem position_fold {c : Config} (i : Fin c.folds.size) (j : Fin c.folds[i.val]!)
    (t : Tape c) : position (.fold i j) = levelStart (challenges c t) i.val + j.val := by
  have hm : Coordinate.fold i j ∈ levelCoordinates c i.val := by
    unfold levelCoordinates
    rw [dite_eq_left i.isLt]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j, rfl⟩))
  rw [position_level i _ hm t]
  congr 1
  simp only [levelCoordinates, i.isLt, dite_true, List.append_assoc]
  rw [List.idxOf_append_of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩)]
  exact idxOf_ofFn _ (by intro a b h; cases h; rfl) j

 theorem position_ood {c : Config} (i : Fin c.folds.size) (j : Fin (oodCount c i.val))
    (t : Tape c) : position (.ood i j) =
      levelStart (challenges c t) i.val + c.folds[i.val]! + j.val := by
  have hm : Coordinate.ood i j ∈ levelCoordinates c i.val := by
    simp [levelCoordinates, i.isLt]
  rw [position_level i _ hm t]
  simp only [levelCoordinates, i.isLt, dite_true, List.append_assoc]
  rw [List.idxOf_append_of_notMem (by simp),
    List.idxOf_append_of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩),
    idxOf_ofFn _ (by intro a b h; cases h; rfl)]
  simp only [List.length_ofFn]
  omega

 theorem position_query {c : Config} (i : Fin c.folds.size) (t : Tape c) :
    position (.query i) =
      levelStart (challenges c t) i.val + c.folds[i.val]! + oodCount c i.val := by
  have hm : Coordinate.query i ∈ levelCoordinates c i.val := by
    simp [levelCoordinates, i.isLt]
  rw [position_level i _ hm t]
  simp only [levelCoordinates, i.isLt, dite_true, List.append_assoc]
  rw [List.idxOf_append_of_notMem (by simp), List.idxOf_append_of_notMem (by simp)]
  simp [Nat.add_assoc]

end Whir.CausalPositions
