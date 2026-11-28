module

public import NativeRustcVm.Whir.Rep

/-!
# The subspace roots as `whir.rs`'s `subspace_table` computes them

`subspace_table(μ)` keeps the layer in place: a 31-word array whose first `μ` words start as
`2^(i+1)` (`layer0`, set one word at a time, `initL`), and a start index `t`. Turn `t` squares and
shifts the words from `t` by the last root (`layerStep`, `sqStep`), then word `t` is the next
root. `layerAt μ t` is the layer after `t` turns; its first `t` words are the roots after `1`
(`tableAt`, with their inverses). `subspaceRoots_eq` and `subspaceTable_toList` connect them to
the model's `subspaceRoots` and `subspaceTable`. `innerL` is the layer during a turn, its words
before `j` updated.
-/

namespace NativeRustcVm.Whir

open NativeVm.Model

@[expose] public section

/-- A layer word's update by the last root: `v² + last·v`. -/
def sqStep (last v : UInt64) : UInt64 := kmul v v ^^^ kmul last v

/-- The layer's word `i` at the start: `2^(i+1)`. -/
def pow2 (i : Nat) : UInt64 := (2 ^ (i + 1) : Nat).toUInt64

/-- The layer at the start. -/
def layer0 (mu : Nat) : List UInt64 := (List.range mu).map pow2

/-- The last root after `t` turns: `1`, then word `t − 1` of the layer. -/
def lastAt (l : List UInt64) (t : Nat) : UInt64 := (1 :: l).getD t 0

/-- Turn `t`: the words from `t` updated by the last root. -/
def layerStep (l : List UInt64) (t : Nat) : List UInt64 :=
  l.take t ++ (l.drop t).map (sqStep (lastAt l t))

/-- The layer after `t` turns. -/
def layerAt (mu : Nat) : Nat → List UInt64
  | 0 => layer0 mu
  | t + 1 => layerStep (layerAt mu t) t

/-- A root with its inverse. -/
def rootPair (r : UInt64) : UInt64 × UInt64 := (r, kinv r)

/-- The table after `t` turns: `1`, then the layer's first `t` words, with their inverses. -/
def tableAt (mu t : Nat) : List (UInt64 × UInt64) := (1 :: (layerAt mu t).take t).map rootPair

/-- The layer during turn `t` of `l`: the words before `j` updated. -/
def innerL (l : List UInt64) (t j : Nat) : List UInt64 := (layerStep l t).take j ++ l.drop j

/-- The 31-word layer while it is initialized: its first `i` words set. -/
def initL (i : Nat) : List UInt64 := (List.range 31).map fun k ↦ if k < i then pow2 k else 0

end

public section

theorem layerStep_length (l : List UInt64) (t : Nat) : (layerStep l t).length = l.length := by
  simp only [layerStep, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem layerAt_length (mu : Nat) : ∀ t, (layerAt mu t).length = mu
  | 0 => by simp [layerAt, layer0]
  | t + 1 => by rw [layerAt, layerStep_length, layerAt_length mu t]

theorem layerStep_take {l : List UInt64} {t : Nat} (h : t ≤ l.length) :
    (layerStep l t).take t = l.take t := by
  rw [layerStep, List.take_append_of_le_length (by simp; omega)]
  simp

theorem layerStep_getElem {l : List UInt64} {t j : Nat} (htj : t ≤ j) (hj : j < l.length) :
    (layerStep l t)[j]'(by rw [layerStep_length]; exact hj) = sqStep (lastAt l t) l[j] := by
  simp only [layerStep]
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem_map, List.getElem_drop]
  congr 2
  omega

theorem innerL_length (l : List UInt64) (t j : Nat) (hj : j ≤ l.length) :
    (innerL l t j).length = l.length := by
  simp only [innerL, List.length_append, List.length_take, layerStep_length, List.length_drop]
  omega

theorem innerL_start {l : List UInt64} {t : Nat} (h : t ≤ l.length) : innerL l t t = l := by
  rw [innerL, layerStep_take h, List.take_append_drop]

theorem innerL_end (l : List UInt64) (t : Nat) : innerL l t l.length = layerStep l t := by
  rw [innerL, List.drop_length, List.append_nil, List.take_of_length_le (by rw [layerStep_length])]

theorem innerL_getElem {l : List UInt64} {t j : Nat} (hj : j < l.length) :
    (innerL l t j)[j]'(by rw [innerL_length _ _ _ hj.le]; exact hj) = l[j] := by
  simp only [innerL]
  rw [List.getElem_append_right (by simp [layerStep_length])]
  simp only [List.length_take, layerStep_length, List.getElem_drop]
  congr 1
  omega

theorem innerL_set {l : List UInt64} {t j : Nat} (htj : t ≤ j) (hj : j < l.length) :
    (innerL l t j).set j (sqStep (lastAt l t) l[j]) = innerL l t (j + 1) := by
  apply List.ext_getElem (by simp [innerL_length _ _ _ hj.le, innerL_length _ _ _ hj])
  intro i h1 h2
  rw [List.length_set, innerL_length _ _ _ hj.le] at h1
  rw [List.getElem_set]
  simp only [innerL]
  split
  · subst i
    rw [List.getElem_append_left (by simp [layerStep_length]; omega), List.getElem_take,
      layerStep_getElem htj hj]
  · by_cases hij : i < j
    · rw [List.getElem_append_left (by simp [layerStep_length]; omega),
        List.getElem_append_left (by simp [layerStep_length]; omega)]
      simp
    · rw [List.getElem_append_right (by simp [layerStep_length]; omega),
        List.getElem_append_right (by simp [layerStep_length]; omega)]
      simp only [List.length_take, layerStep_length, List.getElem_drop]
      congr 1
      omega

theorem lastAt_succ {l : List UInt64} {t : Nat} (h : t < l.length) :
    lastAt l (t + 1) = l[t] := by
  simp [lastAt, List.getD_eq_getElem?_getD, h]

theorem lastAt_zero (l : List UInt64) : lastAt l 0 = 1 := rfl

theorem layerAt_take {mu t : Nat} (h : t < mu) :
    (layerAt mu (t + 1)).take t = (layerAt mu t).take t := by
  rw [layerAt, layerStep_take (by rw [layerAt_length]; omega)]

theorem tableAt_succ {mu t : Nat} (h : t < mu) :
    tableAt mu (t + 1) = tableAt mu t ++
      [rootPair ((layerAt mu (t + 1))[t]'(by rw [layerAt_length]; exact h))] := by
  rw [tableAt, tableAt, List.take_add_one, layerAt_take h]
  simp [List.getElem?_eq_getElem (show t < (layerAt mu (t + 1)).length by
    rw [layerAt_length]; exact h)]

theorem tableAt_length {mu t : Nat} (h : t ≤ mu) : (tableAt mu t).length = t + 1 := by
  simp [tableAt, layerAt_length]
  omega

theorem tableAt_zero (mu : Nat) : tableAt mu 0 = [rootPair 1] := rfl

/-- The model's fold after `t` turns. -/
theorem roots_fold (mu : Nat) : ∀ t ≤ mu,
    (List.range t).foldl (fun (acc : Array UInt64 × UInt64 × Array UInt64) _ ↦
      let (roots, last, layer) := acc
      match (layer.map fun v ↦ kmul v v ^^^ kmul last v).toList with
      | [] => (roots, last, #[])
      | root :: rest => (roots.push root, root, rest.toArray))
      (#[1], 1, (Array.range mu).map fun i ↦ (2 ^ (i + 1) : Nat).toUInt64) =
    ((1 :: (layerAt mu t).take t).toArray, lastAt (layerAt mu t) t,
      ((layerAt mu t).drop t).toArray)
  | 0, _ => by
    simp only [List.range_zero, List.foldl_nil, layerAt, List.take_zero, List.drop_zero]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    apply Array.toList_inj.mp
    simp [layer0, pow2, Array.toList_range]
  | t + 1, h => by
    rw [List.range_succ, List.foldl_append, roots_fold mu t (by omega)]
    have hlen := layerAt_length mu t
    obtain ⟨x, rest, hx⟩ : ∃ x rest, (layerAt mu t).drop t = x :: rest := by
      cases hd : (layerAt mu t).drop t with
      | nil => have := congrArg List.length hd; simp at this; omega
      | cons x rest => exact ⟨x, rest, rfl⟩
    have hstep : layerAt mu (t + 1) = (layerAt mu t).take t ++
        (sqStep (lastAt (layerAt mu t) t) x :: rest.map (sqStep (lastAt (layerAt mu t) t))) := by
      rw [layerAt, layerStep, hx, List.map_cons]
    have htl : ((layerAt mu t).take t).length = t := by simp [hlen]; omega
    rw [hx]
    simp only [List.foldl_cons, List.foldl_nil, Array.toList_map, List.map_cons]
    rw [hstep]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply Array.toList_inj.mp
      simp [List.take_append, htl, sqStep]
    · simp [lastAt, List.getD_eq_getElem?_getD, htl, sqStep]
    · have hd : List.drop (t + 1) ((layerAt mu t).take t) = [] :=
        List.drop_eq_nil_of_le (by omega)
      rw [List.drop_append, hd, List.nil_append, htl, show t + 1 - t = 1 by omega]
      rfl

theorem subspaceRoots_eq (mu : Nat) : subspaceRoots mu = (1 :: layerAt mu mu).toArray := by
  have h := roots_fold mu mu le_rfl
  rw [List.take_of_length_le (by rw [layerAt_length])] at h
  exact congrArg Prod.fst h

theorem subspaceTable_toList (mu : Nat) : (subspaceTable mu).toList = tableAt mu mu := by
  rw [subspaceTable, subspaceRoots_eq, tableAt,
    List.take_of_length_le (by rw [layerAt_length])]
  simp [rootPair]

theorem initL_length (i : Nat) : (initL i).length = 31 := by simp [initL]

theorem initL_zero : initL 0 = List.replicate 31 0 :=
  List.ext_getElem (by simp [initL]) fun _ _ _ ↦ by simp [initL]

theorem initL_set (i : Nat) : (initL i).set i (pow2 i) = initL (i + 1) := by
  apply List.ext_getElem (by simp [initL])
  intro k h1 h2
  rw [List.getElem_set]
  simp only [initL, List.getElem_map, List.getElem_range]
  split
  · subst k; simp
  · by_cases hk : k < i
    · simp [hk, show k < i + 1 by omega]
    · simp [hk, show ¬k < i + 1 by omega]

theorem initL_take {mu : Nat} (h : mu ≤ 31) : (initL mu).take mu = layer0 mu := by
  apply List.ext_getElem (by simp [initL, layer0]; omega)
  intro k h1 h2
  have hk : k < mu := by simpa [layer0] using h2
  simp [initL, layer0, hk]

theorem pairWords_length' (ps : List (UInt64 × UInt64)) : (pairWords ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [pairWords] at ih ⊢; omega

theorem pairWords_concat (ps : List (UInt64 × UInt64)) (p : UInt64 × UInt64) :
    pairWords (ps ++ [p]) = pairWords ps ++ [p.1, p.2] := by
  simp [pairWords]

end

end NativeRustcVm.Whir
