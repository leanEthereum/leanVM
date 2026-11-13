/-
  LeanVM.Prover.WitnessStack

  The executable stack is the specification's: each placed column written at its placement,
  zeros elsewhere, is the stack the columns are read off.
-/

module

public import LeanVM.Prover.WitnessColumns

/-!
# The stack

`stackArray_eq`: the stack the prover writes (`stackArray`: each column with a placement written
from its placement's index on, over zeros) is the stack `q` its columns are read off, given each
column's array is the instance's column of `q` and `q` is zero past the blocks: a committed
column sits at its block's offset (`placement_committed`, `column_committed`), a column with a
slot at its slot of `QKECCAK` (`placement_slot`, the cells `QKECCAK` holds), and every cell below
the blocks' total lies in a committed column's block (`exists_inWindow`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Verifier
open Air.Flat (EnsembleWitness)

@[expose] public section

/-! ## Writes -/

/-- Writing the first `n` cells of `col` from `idx` on keeps the size. -/
theorem size_write (col : Array K) (idx : ℕ) :
    ∀ n (hn : n ≤ col.size) (a : Array K),
      (Nat.fold n (fun i h stack ↦ stack.set! (idx + i) (col[i]'(by omega))) a).size = a.size
  | 0, _, a => by simp
  | n + 1, hn, a => by
    rw [Nat.fold_succ, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    exact size_write col idx n (by omega) a

/-- Writing the first `n` cells of `col` from `idx` on: cell `x` is `col`'s cell `x - idx` in the
window, the old cell elsewhere. -/
theorem getElem?_write (col : Array K) (idx : ℕ) :
    ∀ n (hn : n ≤ col.size) (a : Array K) (x : ℕ),
      (Nat.fold n (fun i h stack ↦ stack.set! (idx + i) (col[i]'(by omega))) a)[x]? =
        if idx ≤ x ∧ x < idx + n ∧ x < a.size then col[x - idx]? else a[x]?
  | 0, _, a, x => by
    simp only [Nat.fold_zero, Nat.add_zero]
    split <;> first | rfl | omega
  | n + 1, hn, a, x => by
    rw [Nat.fold_succ, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      size_write col idx n (by omega), getElem?_write col idx n (by omega) a x]
    split_ifs <;> first
      | rfl
      | omega
      | (subst_vars; rw [Nat.add_sub_cancel_left, Array.getElem?_eq_getElem (by omega)])
      | (subst_vars; rw [Array.getElem?_eq_none (by omega)])

/-- **Writes that agree with `T`, covering every cell of `T` the start does not hold, give `T`.**
Each step `f acc a` sets the cells of its window `win a` to `T`'s and keeps the others. -/
theorem foldl_eq_of_writes {α : Type} (T : Array K) (f : Array K → α → Array K)
    (win : α → ℕ → Prop) :
    ∀ (L : List α) (acc : Array K),
      (∀ a ∈ L, ∀ acc : Array K, acc.size = T.size → (f acc a).size = T.size ∧
        ∀ x, (win a x → (f acc a)[x]? = T[x]?) ∧ (¬ win a x → (f acc a)[x]? = acc[x]?)) →
      acc.size = T.size → (∀ x, acc[x]? = T[x]? ∨ ∃ a ∈ L, win a x) →
      L.foldl f acc = T
  | [], acc, _, _, hx => Array.ext_getElem? fun x ↦ (hx x).resolve_right (by simp)
  | a :: L, acc, hf, hs, hx => by
    rw [List.foldl_cons]
    obtain ⟨hs', hw⟩ := hf a List.mem_cons_self acc hs
    refine foldl_eq_of_writes T f win L _ (fun a' ha' ↦ hf a' (List.mem_cons_of_mem a ha')) hs'
      fun x ↦ ?_
    by_cases h : win a x
    · exact .inl ((hw x).1 h)
    · rw [(hw x).2 h]
      rcases hx x with e | ⟨a', ha', hwin⟩
      · exact .inl e
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · exact absurd hwin h
        · exact .inr ⟨a', ha', hwin⟩

/-! ## The placements -/

/-- The global numbers are distinct. -/
theorem nodup_columns : columns.Nodup := by decide +kernel

/-- The global number of the column at a global number is that number. -/
theorem refCol_getElem_columns (i : ℕ) (hi : i < columns.length) : refCol columns[i] = i :=
  nodup_columns.idxOf_getElem i hi

variable (prog : LeanIsaProgram) (s : Sizes)

/-- A column but an output lane has its placement. -/
theorem placements_getD_some (c : Col) (h : ¬ IsOut c) :
    (verifierLayout prog s).placements.getD (refCol c) none =
      some ((verifierLayout prog s).placement (refCol c)) := by
  have hno : refCol c ∉ keccakOutputColumns := (mem_keccakOutputColumns_pyCol c).not.mpr h
  unfold Verifier.Layout.placement
  rw [placements_getD, keccakSlot_pyCol]
  split_ifs <;> rfl

/-- A cell of a column read off the stack, as an entry of the stack's array. -/
theorem getElem?_column {q : Column (leanIsaμ prog s)} {c : Col} {i y : ℕ}
    (hi : i < 2 ^ kappa prog s c) (hy : y < 2 ^ leanIsaμ prog s)
    (e : ((inst prog s).column q c).values[i] = q.values[y]) :
    ((inst prog s).column q c).values.toArray[i]? = q.values.toArray[y]? := by
  rw [Array.getElem?_eq_getElem (by rw [Vector.size_toArray]; exact hi),
    Array.getElem?_eq_getElem (by rw [Vector.size_toArray]; exact hy), Vector.getElem_toArray,
    Vector.getElem_toArray]
  exact congrArg some e

/-- A column with a slot is the stack's cells at its slot of `QKECCAK`. -/
theorem column_slot (q : Column (leanIsaμ prog s)) (c : Col) (h : IsVirtual c ∧ ¬ IsOut c)
    (i : ℕ) (hi : i < 2 ^ s.τ 5) :
    i + 2 ^ s.τ 5 * (qSlot c).val + (blocks prog s).offset (keccakBlock prog s) <
        2 ^ leanIsaμ prog s ∧
      ((inst prog s).column q c).values.toArray[i]? =
        q.values.toArray[i + 2 ^ s.τ 5 * (qSlot c).val +
          (blocks prog s).offset (keccakBlock prog s)]? := by
  have hfit := blocks_fits prog s
  have hoff := (blocks prog s).offset_add_pow_le_total (keccakBlock prog s)
  rw [size_keccakBlock] at hoff
  have hcube : i + 2 ^ s.τ 5 * (qSlot c).val < 2 ^ (s.τ 5 + 6) :=
    slot_lt (⟨i, hi⟩ : Fin (2 ^ s.τ 5)) (qSlot c) (qSlot c).isLt
  have hx : i + 2 ^ s.τ 5 * (qSlot c).val + (blocks prog s).offset (keccakBlock prog s) <
      2 ^ leanIsaμ prog s := by omega
  refine ⟨hx, ?_⟩
  have hk : i < 2 ^ kappa prog s c := by rw [kappa_of_isVirtual prog s h.1]; exact hi
  refine getElem?_column prog s hk hx ?_
  rcases c with ⟨j, k⟩
  obtain ⟨hj, -⟩ := h.1
  subst hj
  by_cases hsp : IsSpare ⟨opIdx 5, k⟩
  · have e := column_spare prog s q _ hsp ⟨i, hi⟩
    rw [word_keccakColumn prog s q _ (qSlot _).isLt ⟨i, hi⟩] at e
    exact e
  · have hb : 15 ≤ k.val ∧ k.val < 40 := by
      have h1 : k.val < 65 := h.1.2.1
      have h1' : k.val ≠ 14 := h.1.2.2
      have h2 : ¬ (40 ≤ k.val ∧ k.val < 65) := fun hh ↦ h.2 ⟨rfl, hh⟩
      have h3 : ¬ (k.val < 14) := fun hh ↦ hsp ⟨rfl, hh⟩
      omega
    obtain ⟨l, rfl⟩ : ∃ l : Fin 25, k = (inCol l).2 :=
      ⟨⟨k.val - 15, by omega⟩, Fin.ext (by simp only [inCol]; omega)⟩
    have hq : (qSlot (⟨opIdx 5, (inCol l).2⟩ : Col)).val = l.val :=
      congrArg Fin.val (qSlot_inCol l)
    simp only [hq]
    exact column_inCol_stack prog s q l ⟨i, hi⟩

/-- **A column at its placement is the stack's cells there**: cell `i` of a column but an output
lane is the stack's cell `i` past its placement's index. -/
theorem column_at_placement (q : Column (leanIsaμ prog s)) (c : Col) (h : ¬ IsOut c) (i : ℕ)
    (hi : i < 2 ^ kappa prog s c) :
    ((verifierLayout prog s).placement (refCol c)).index + i < 2 ^ leanIsaμ prog s ∧
      ((inst prog s).column q c).values.toArray[i]? =
        q.values.toArray[((verifierLayout prog s).placement (refCol c)).index + i]? := by
  by_cases hv : IsVirtual c
  · rw [placement_slot prog s c ⟨hv, h⟩]
    have e := column_slot prog s q c ⟨hv, h⟩ i (kappa_of_isVirtual prog s hv ▸ hi)
    rwa [show (blocks prog s).offset (keccakBlock prog s) + (qSlot c).val * 2 ^ s.τ 5 + i =
      i + 2 ^ s.τ 5 * (qSlot c).val + (blocks prog s).offset (keccakBlock prog s) by ring]
  · rw [placement_committed prog s c hv]
    dsimp only
    have hfit := blocks_fits prog s
    have hoff := (blocks prog s).offset_add_pow_le_total (blockOf c hv)
    rw [size_blockOf] at hoff
    have hx : (blocks prog s).offset (blockOf c hv) + i < 2 ^ leanIsaμ prog s := by omega
    refine ⟨hx, ?_⟩
    rw [Nat.add_comm]
    exact getElem?_column prog s hi (by omega) (column_committed prog s q c hv ⟨i, hi⟩)

/-- The writes of the prover's stack: the placements of the instance's columns, with their
arrays. -/
theorem mem_zip_placements {cols : Array (Array K)} (hsize : cols.size = 158) :
    ∀ a, a ∈ (verifierLayout prog s).placements.zip cols.toList ↔ ∃ c : Col,
      a = ((verifierLayout prog s).placements.getD (refCol c) none, cols.getD (refCol c) #[]) := by
  have hlen : (verifierLayout prog s).placements.length = 158 := by
    show (placementsOf (refKappas prog s)).1.length = 158
    rw [placementsOf_pyKappas]
    simp [length_pyKappas]
  have hz : ((verifierLayout prog s).placements.zip cols.toList).length = 158 := by
    simp [hlen, hsize]
  have hget : ∀ i (hi : i < 158),
      ((verifierLayout prog s).placements.zip cols.toList)[i]'(hz ▸ hi) =
        ((verifierLayout prog s).placements.getD i none, cols.getD i #[]) := by
    intro i hi
    rw [List.getElem_zip, List.getD_eq_getElem _ _ (by omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega)]
    simp
  intro a
  constructor
  · intro ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    rw [hz] at hi
    refine ⟨columns[i]'(by rw [length_columns]; exact hi), ?_⟩
    rw [refCol_getElem_columns, hget i hi]
  · rintro ⟨c, rfl⟩
    rw [← hget _ (refCol_lt c)]
    exact List.getElem_mem _

/-- **The stack the prover writes is the stack its columns are read off**: given each column's
array is the instance's column of `q`, and `q` is zero past the blocks. -/
theorem stackArray_eq (q : Column (leanIsaμ prog s)) (cols : Array (Array K))
    (hsize : cols.size = 158)
    (hcols : ∀ c : Col, cols.getD (refCol c) #[] = ((inst prog s).column q c).values.toArray)
    (hzero : ∀ x (hx : x < 2 ^ leanIsaμ prog s), (blocks prog s).total ≤ x → q.values[x] = 0) :
    stackArray (verifierLayout prog s) cols = q.values.toArray := by
  have hmem := mem_zip_placements prog s hsize
  unfold stackArray
  rw [stackLog_verifierLayout]
  refine foldl_eq_of_writes _ _
    (fun a x ↦ ∃ pl, a.1 = some pl ∧ pl.index ≤ x ∧ x < pl.index + a.2.size) _ _ ?_
    (by simp) ?_
  · intro a ha acc hacc
    obtain ⟨c, rfl⟩ := (hmem a).mp ha
    have hcs : (cols.getD (refCol c) #[]).size = 2 ^ kappa prog s c := by
      rw [hcols, Vector.size_toArray]; rfl
    have hT : q.values.toArray.size = 2 ^ leanIsaμ prog s := Vector.size_toArray _
    by_cases ho : IsOut c
    · rw [placements_outLane prog s c ho]
      dsimp only
      refine ⟨hacc, fun x ↦ ⟨?_, fun _ ↦ rfl⟩⟩
      rintro ⟨_, hpl, -⟩
      exact absurd hpl (by simp)
    · rw [placements_getD_some prog s c ho]
      dsimp only
      refine ⟨(size_write _ _ _ le_rfl acc).trans hacc, fun x ↦ ⟨?_, ?_⟩⟩
      · rintro ⟨pl, hpl, h1, h2⟩
        cases hpl
        rw [hcs] at h2
        obtain ⟨hx, e⟩ := column_at_placement prog s q c ho
          (x - ((verifierLayout prog s).placement (refCol c)).index) (by omega)
        rw [getElem?_write _ _ _ le_rfl, ite_eq_left ⟨h1, by rw [hcs]; exact h2, by omega⟩,
          hcols, e, Nat.add_sub_cancel' h1]
      · intro hw
        rw [getElem?_write _ _ _ le_rfl, ite_eq_right fun h' ↦ hw ⟨_, rfl, h'.1, h'.2.1⟩]
  · intro x
    by_cases hx : x < 2 ^ leanIsaμ prog s
    · by_cases ht : x < (blocks prog s).total
      · right
        obtain ⟨b, hb⟩ := (blocks prog s).exists_inWindow ht
        have hc : (stackOrder prog s)[b.val] ∈ committedColumns :=
          List.mem_mergeSort.mp (List.getElem_mem _)
        have hv : ¬ IsVirtual (stackOrder prog s)[b.val] := by
          simp only [committedColumns, List.mem_filter, Bool.not_eq_true',
            decide_eq_false_iff_not] at hc
          exact hc.2
        have hnd : (stackOrder prog s).Nodup :=
          (List.mergeSort_perm _ _).nodup_iff.mpr nodup_committedColumns
        have hbo : blockOf (prog := prog) (s := s) _ hv = b := Fin.ext (hnd.idxOf_getElem _ _)
        refine ⟨_, (hmem _).mpr ⟨_, rfl⟩, _,
          placements_getD_some prog s _ fun ho ↦ hv ho.isVirtual, ?_⟩
        rw [placement_committed prog s _ hv, hbo, hcols]
        simp only [Vector.size_toArray]
        have := hb.2
        exact ⟨hb.1, this⟩
      · left
        rw [Array.getElem?_eq_getElem (by simpa using hx),
          Array.getElem?_eq_getElem (by simpa using hx), Array.getElem_replicate,
          Vector.getElem_toArray, hzero x hx (Nat.le_of_not_lt ht)]
    · left
      rw [Array.getElem?_eq_none (by simpa using hx), Array.getElem?_eq_none (by simpa using hx)]

end

end LeanVM.Prover
