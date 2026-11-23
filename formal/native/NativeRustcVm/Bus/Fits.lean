module

public import NativeVm.Model.Bus
public import NativeVm.Math.Bus

/-!
# The bus's forms fit their `FormBuf`s

A form's monomials (`colsL`) do not depend on the coefficients: `addTerm` appends a monomial that
is new (`colsL_addTerm`), `addScaled` merges another form's (`colsL_addScaled`), `blockForm` starts
from the constant's (`colsL_blockForm`). So each block's form, and each table's form of a side
after `accumulateSide`, has the monomials of a fold over the tuples only (`blockCols`,
`slotCols`), computed from the statement's tables, where `decide` counts them: at most `formCap =
148` (`blockCols_le`, `slotCols_le`; `KECCAK`'s push side has exactly `148`).
-/

namespace NativeRustcVm.Bus

open NativeVm.Model LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Monomials -/

/-- A form's monomials, in order. -/
def colsL (f : FormW) : List (List Nat) := f.toList.map (·.cols.toList)

/-- A monomial merged in: appended when new. -/
def mergeOne (L : List (List Nat)) (m : List Nat) : List (List Nat) :=
  if m ∈ L then L else L ++ [m]

/-- Monomials merged in, in order. -/
def mergeAll (L M : List (List Nat)) : List (List Nat) := M.foldl mergeOne L

/-- A tuple's block form's monomials: the constant's, then each coordinate's. -/
def blockCols (coords : List (List (List Nat))) : List (List Nat) :=
  coords.foldl mergeAll [[]]

/-- A side's slot of table `o`: its blocks' forms merged, from none. -/
def slotCols (blocks : List (Nat × List (List (List Nat)))) (o : Nat) : List (List Nat) :=
  (blocks.filter (·.1 == o)).foldl (fun L x ↦ mergeAll L (blockCols x.2)) []

/-- The statement's tuples of a side: each table's pushes, pulls or count columns, with its opcode,
as monomials. -/
def sideTuples (side : Nat) : List (Nat × List (List (List Nat))) :=
  tables.flatMap fun t ↦
    (if side = 0 then t.flushes.push.map (·.map fun f ↦ f.terms.map (·.1))
      else if side = 1 then t.flushes.pull.map (·.map fun f ↦ f.terms.map (·.1))
      else t.countColumns.map fun l ↦ [(Form.col l).terms.map (·.1)]).map (t.opcode, ·)

/-- `FORM_CAP`. -/
def formCapW : Nat := 148

/-! ## The counts -/

theorem blockCols_le01 : ((List.range 2).all fun s ↦ (sideTuples s).all fun x ↦
    decide ((blockCols x.2).length ≤ formCapW)) = true := by
  decide +kernel

theorem slotCols_le01 : ((List.range 2).all fun s ↦ (List.range 6).all fun o ↦
    decide ((slotCols (sideTuples s) o).length ≤ formCapW)) = true := by
  decide +kernel

/-! ## Lengths -/

theorem mergeOne_length_le (L : List (List Nat)) (m : List Nat) :
    (mergeOne L m).length ≤ L.length + 1 := by
  unfold mergeOne; split <;> simp

theorem mergeAll_length_le (L M : List (List Nat)) :
    (mergeAll L M).length ≤ L.length + M.length := by
  induction M generalizing L with
  | nil => simp [mergeAll]
  | cons m M ih =>
    have h1 := ih (mergeOne L m)
    have h2 := mergeOne_length_le L m
    simp only [mergeAll, List.foldl_cons, List.length_cons] at *
    omega

theorem slotCols_length_le (blocks : List (Nat × List (List (List Nat)))) (o c : Nat)
    (hb : ∀ x ∈ blocks, (blockCols x.2).length ≤ c) :
    (slotCols blocks o).length ≤ c * blocks.length := by
  unfold slotCols
  have key : ∀ (bs : List (Nat × List (List (List Nat)))) (L : List (List Nat)),
      (∀ x ∈ bs, (blockCols x.2).length ≤ c) →
      (bs.foldl (fun L x ↦ mergeAll L (blockCols x.2)) L).length ≤ L.length + c * bs.length := by
    intro bs
    induction bs with
    | nil => intro L _; simp
    | cons x bs ih =>
      intro L h
      have h1 := ih (mergeAll L (blockCols x.2)) fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
      have h2 := mergeAll_length_le L (blockCols x.2)
      have h3 := h x List.mem_cons_self
      simp only [List.foldl_cons, List.length_cons] at *
      rw [Nat.mul_succ]
      omega
  have := key (blocks.filter (·.1 == o)) [] fun x hx ↦ hb x (List.mem_of_mem_filter hx)
  have hf := List.length_filter_le (·.1 == o) blocks
  simp only [List.length_nil, Nat.zero_add] at this
  exact this.trans (Nat.mul_le_mul_left _ hf)

/-! ## The count side -/

theorem sideTuples_two :
    sideTuples 2 = tables.flatMap fun t ↦ t.countColumns.map fun l ↦ (t.opcode, [[[l]]]) := by
  simp only [sideTuples, show (2 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 1 from by decide,
    ↓reduceIte, List.map_map]
  rfl

theorem sideTuples_two_length : (sideTuples 2).length = 45 := by
  have h := congrArg (fun l ↦ (l.map Prod.snd).sum) NativeVm.Math.Bus.tables_count
  simp only [List.map_map, Function.comp_def] at h
  rw [sideTuples_two, List.length_flatMap]
  simp only [List.length_map]
  rw [h]
  rfl

theorem blockCols_two {x : Nat × List (List (List Nat))} (hx : x ∈ sideTuples 2) :
    (blockCols x.2).length ≤ 2 := by
  rw [sideTuples_two] at hx
  simp only [List.mem_flatMap, List.mem_map] at hx
  obtain ⟨t, -, l, -, rfl⟩ := hx
  exact (mergeAll_length_le [[]] [[l]]).trans (by simp)

/-! ## Every side -/

theorem blockCols_le {s : Nat} (hs : s < 3) {x : Nat × List (List (List Nat))}
    (hx : x ∈ sideTuples s) : (blockCols x.2).length ≤ formCapW := by
  match s, hs with
  | 2, _ => exact (blockCols_two hx).trans (by decide)
  | 0, _ | 1, _ =>
    have h := blockCols_le01
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h _ (by omega) x hx

theorem tables_opcode_lt : (tables.all fun t ↦ decide (t.opcode < 6)) = true := by decide +kernel

theorem sideTuples_owner_lt {s : Nat} {x : Nat × List (List (List Nat))} (hx : x ∈ sideTuples s) :
    x.1 < 6 := by
  have h := tables_opcode_lt
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  simp only [sideTuples, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨t, ht, y, -, rfl⟩ := hx
  exact h t ht

theorem slotCols_le {s : Nat} (hs : s < 3) (o : Nat) :
    (slotCols (sideTuples s) o).length ≤ formCapW := by
  by_cases ho : o < 6
  · obtain rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 := by omega
    all_goals first
      | (have := slotCols_length_le (sideTuples 2) o 2 fun x hx ↦ blockCols_two hx
         rw [sideTuples_two_length] at this
         exact this.trans (by decide))
      | (have h := slotCols_le01
         simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
         exact h _ (by omega) o ho)
  · have hnil : (sideTuples s).filter (·.1 == o) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := sideTuples_owner_lt hx
      simp only [beq_iff_eq]
      omega
    rw [slotCols, hnil]
    simp [formCapW]

end

end NativeRustcVm.Bus
