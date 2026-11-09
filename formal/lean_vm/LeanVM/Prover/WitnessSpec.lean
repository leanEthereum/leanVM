/-
  LeanVM.Prover.WitnessSpec

  The columns of the stack of a witness, read off the instance, cell by cell: the specification's
  side of the executable columns.
-/

module

public import LeanVM.Protocol.LeanIsa.Complete
public import LeanVM.Protocol.EndToEnd.Complete.Claims

/-!
# The instance's columns of the stack of a witness

For a witness `w` at the sizes it carries (`witnessSizes w hp`), the instance's column `c` read
off `stackOf` is, cell by cell (`x < 2^τ`):

* a committed column: the witness's column (`column_toArray_committed`, from `column_stackOf`);
* a column of an opcode table that is no `KECCAK` output lane: the table's cells
  (`column_toArray_table`), the `KECCAK` input lanes and spare columns through `QKECCAK`'s slots
  (`keccakWitness_getElem`), a padding row zero;
* a `KECCAK` output lane: the last twelve rounds of the first twelve of the row's input lanes
  (`column_getElem_out`), as the instance derives it from `QKECCAK`.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.LeanIsa
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- A missing row's cells are zero. -/
theorem cellOf_of_le {t : Air.Flat.Table K} {x : ℕ} (h : t.table.length ≤ x) (i : ℕ) :
    cellOf t x i = 0 := by
  simp [cellOf, List.getElem?_eq_none h]

/-- The opcode table of a column of table `opIdx j`. -/
theorem opIdx_inj {j j' : Fin 6} (h : opIdx j = opIdx j') : j = j' := by
  have := congrArg Fin.val h
  simp only [opIdx] at this
  exact Fin.ext (by omega)

/-- A column of the `KECCAK` table that is a lane but no output lane is an input lane. -/
theorem eq_inCol {i : Fin (width (opIdx 5))} (h : 15 ≤ i.val) (h' : i.val < 40) :
    (⟨opIdx 5, i⟩ : Col) = inCol ⟨i.val - 15, by omega⟩ := by
  unfold inCol
  congr 1
  exact Fin.ext (by simp; omega)

/-- A column of the `KECCAK` table in `40 … 64` is an output lane. -/
theorem eq_outCol {i : Fin (width (opIdx 5))} (h : 40 ≤ i.val) (h' : i.val < 65) :
    (⟨opIdx 5, i⟩ : Col) = outCol ⟨i.val - 40, by omega⟩ := by
  unfold outCol
  congr 1
  exact Fin.ext (by simp; omega)

variable {prog : LeanIsaProgram} {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ))
  (hp : 0 < (imageOf w.data).1)

/-- An input lane of a witness, at the sizes it carries, is its cell, a padding row's zero. -/
theorem inLaneOf_eq (x : ℕ) (l : Fin 25) :
    inLaneOf prog (witnessSizes w hp) w x l = cellOf (tableAt w 5) x (15 + l) := by
  unfold inLaneOf
  split_ifs with hx
  · rfl
  · exact (cellOf_of_le (Nat.not_lt.mp hx) _).symm

/-- **A committed column of the stack is the witness's column.** -/
theorem column_toArray_committed (c : Col) (h : ¬ IsVirtual c) :
    ((leanIsaInstance prog (witnessSizes w hp)).column (stackOf prog (witnessSizes w hp) w)
        c).values.toArray = (witnessColumn prog (witnessSizes w hp) w c).toArray := by
  refine congrArg Vector.toArray (Vector.ext fun x hx ↦ ?_)
  exact column_stackOf prog (witnessSizes w hp) w c h ⟨x, hx⟩

/-- Cell `x` of input lane `l` of the stack is the row's cell. -/
theorem column_getElem_in (l : Fin 25) (x : ℕ) (hx : x < 2 ^ (witnessSizes w hp).τ 5) :
    ((leanIsaInstance prog (witnessSizes w hp)).column (stackOf prog (witnessSizes w hp) w)
        (inCol l)).values[x]'hx = cellOf (tableAt w 5) x (15 + l) := by
  have h1 := column_inCol prog (witnessSizes w hp) (stackOf prog (witnessSizes w hp) w) l ⟨x, hx⟩
  rw [word_stackOf prog (witnessSizes w hp) w l (by omega) ⟨x, hx⟩,
    keccakWitness_getElem prog (witnessSizes w hp) w l (by omega) x hx, dite_eq_left l.isLt,
    inLaneOf_eq w hp] at h1
  exact h1

/-- Cell `x` of a spare column of the stack is the row's cell. -/
theorem column_getElem_spare (c : Col) (h : IsSpare c) (x : ℕ)
    (hx : x < 2 ^ (witnessSizes w hp).τ 5) :
    ((leanIsaInstance prog (witnessSizes w hp)).column (stackOf prog (witnessSizes w hp) w)
        c).values[x]'(by
          show x < 2 ^ kappa prog (witnessSizes w hp) c
          rw [kappa_of_isVirtual prog _ h.isVirtual]; exact hx) =
      cellOf (tableAt w 5) x c.2 := by
  obtain ⟨h50, hcol⟩ := qSlot_spare h
  have h1 := column_spare prog (witnessSizes w hp) (stackOf prog (witnessSizes w hp) w) c h
    ⟨x, hx⟩
  rw [word_stackOf prog (witnessSizes w hp) w _ (qSlot c).isLt ⟨x, hx⟩,
    keccakWitness_getElem prog (witnessSizes w hp) w _ (qSlot c).isLt x hx,
    dite_eq_right (by omega), dite_eq_right (by omega), hcol] at h1
  exact h1

/-- The state after twelve rounds the stack of a witness commits at step `x`: the first twelve
rounds of the row's input lanes. -/
theorem state_mid_stackOf (x : Fin (2 ^ (witnessSizes w hp).τ 5)) :
    (keccakRegion prog (witnessSizes w hp)).state
        ((leanIsaInstance prog (witnessSizes w hp)).keccakColumn
          (keccakRegion prog (witnessSizes w hp)) (stackOf prog (witnessSizes w hp) w)) 25 x =
      keccakSegment 0 (laneState (inLaneOf prog (witnessSizes w hp) w x)) := by
  have hmid : (fun l : Fin 25 ↦ (keccakRegion prog (witnessSizes w hp)).word
      ((leanIsaInstance prog (witnessSizes w hp)).keccakColumn
        (keccakRegion prog (witnessSizes w hp)) (stackOf prog (witnessSizes w hp) w)) (25 + l)
        x) = stateLanes (keccakSegment 0 (laneState (inLaneOf prog (witnessSizes w hp) w x))) := by
    funext l
    refine (word_stackOf prog _ w (25 + l) (by omega) x).trans ?_
    rw [keccakWitness_getElem prog _ w (25 + l) (by omega) _ x.isLt,
      dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 1
    ext
    simp
  simp only [KeccakRegion.state]
  rw [hmid, laneState_stateLanes]

/-- **Cell `x` of output lane `l` of the stack**: the last twelve rounds of the first twelve of
the row's input lanes. -/
theorem column_getElem_out (l : Fin 25) (x : ℕ) (hx : x < 2 ^ (witnessSizes w hp).τ 5) :
    ((leanIsaInstance prog (witnessSizes w hp)).column (stackOf prog (witnessSizes w hp) w)
        (outCol l)).values[x]'hx =
      stateLanes (keccakSegment 1 (keccakSegment 0
        (laneState fun l' : Fin 25 ↦ cellOf (tableAt w 5) x (15 + l'.val)))) l := by
  have h1 := column_outCol prog (witnessSizes w hp) (stackOf prog (witnessSizes w hp) w) l
    ⟨x, hx⟩
  rw [state_mid_stackOf w hp] at h1
  have hin : inLaneOf prog (witnessSizes w hp) w x =
      fun l' : Fin 25 ↦ cellOf (tableAt w 5) x (15 + l'.val) :=
    funext fun l' ↦ inLaneOf_eq w hp x l'
  rw [hin] at h1
  exact h1

/-- **A column of an opcode table that is no output lane** is the table's cells, a padding row
zero. -/
theorem column_toArray_table (j : Fin 6) (i : Fin (width (opIdx j)))
    (hout : ¬ IsOut ⟨opIdx j, i⟩) :
    ((leanIsaInstance prog (witnessSizes w hp)).column (stackOf prog (witnessSizes w hp) w)
        ⟨opIdx j, i⟩).values.toArray =
      Array.ofFn (n := 2 ^ (witnessSizes w hp).τ j) fun x ↦
        cellOf (tableAt w ⟨j, by omega⟩) x i := by
  by_cases hv : IsVirtual ⟨opIdx j, i⟩
  · obtain rfl : j = 5 := opIdx_inj hv.1
    rcases hv.lane_or_spare with hl | hs
    · have h13 : 15 ≤ i.val := hl.2.1
      have h38 : i.val < 40 := Nat.lt_of_not_le fun h ↦ hout ⟨rfl, h, hl.2.2⟩
      refine (congrArg (fun c : Col ↦ ((leanIsaInstance prog (witnessSizes w hp)).column
        (stackOf prog (witnessSizes w hp) w) c).values.toArray) (eq_inCol h13 h38)).trans ?_
      refine Array.ext (by simp only [Vector.size_toArray, Array.size_ofFn]; rfl)
        fun x h1 h2 ↦ ?_
      have hx : x < 2 ^ (witnessSizes w hp).τ 5 := by simpa using h2
      rw [Array.getElem_ofFn, Vector.getElem_toArray]
      exact (column_getElem_in w hp ⟨i.val - 15, by omega⟩ x hx).trans
        (congrArg (cellOf (tableAt w 5) x) (by simp; omega))
    · refine Array.ext (by simp only [Vector.size_toArray, Array.size_ofFn]; rfl)
        fun x h1 h2 ↦ ?_
      have hx : x < 2 ^ (witnessSizes w hp).τ 5 := by simpa using h2
      rw [Array.getElem_ofFn, Vector.getElem_toArray]
      exact column_getElem_spare w hp _ hs x hx
  · exact (column_toArray_committed w hp _ hv).trans rfl

end

end LeanVM.Prover
