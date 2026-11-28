module

public import NativeRustcVm.Whir.Basis
public import NativeRustcVm.Whir.Sample

/-!
# `verify_stacked_opening`'s model, claim by claim

The stack claims (`stackClaims`) are the ring-switched one, the placed column claims (the first `i`
of them `placedOf … i`), the out-of-domain one; their count is `placedOf … cs.size + 2`
(`size_stackClaims`). The batched target `dot scales values` is a sum built claim by claim
(`dotL`, `dotL_take_succ`), the `j`th value the `i`th column claim's when that claim is the
`j`th placed (`vals_placed`). `vso_run`: the model's run, the batching challenge squeezed, then
the ladder and `whirLevels`.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeVm.Model NativeRustcVm.Whir LeanVM.Parameters

@[expose] public section

/-- The placed column claims among the first `i`. -/
def placedOf (layout : LayoutW) (cs : Array ColumnClaimW) (i : Nat) : Nat :=
  ((cs.toList.take i).filterMap (·.onStack layout)).length

/-- `Σ l[j]·r[j]` over the common length, from `0`. -/
def dotL (l r : List EW) : EW := (List.zipWith (· * ·) l r).foldl (· + ·) 0

/-- The stack claims' values. -/
def valsOf (layout : LayoutW) (target : EW) (cs : Array ColumnClaimW) (value : EW) : List EW :=
  target :: ((cs.toList.filterMap (·.onStack layout)).map (·.value) ++ [value])

end

public section

variable {layout : LayoutW} {cs : Array ColumnClaimW}

theorem ew_add_comm' (a b : EW) : a + b = b + a := by
  show (⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1⟩ : EW) = ⟨b.c0 ^^^ a.c0, b.c1 ^^^ a.c1⟩
  rw [UInt64.xor_comm a.c0, UInt64.xor_comm a.c1]

theorem ew_zero_add (a : EW) : 0 + a = a := by
  show (⟨0 ^^^ a.c0, 0 ^^^ a.c1⟩ : EW) = a
  simp

theorem size_stackClaims (target : EW) (point coefficients : Array EW) (z : Array EW)
    (value : EW) :
    (stackClaims layout target point coefficients cs z value).size =
      placedOf layout cs cs.size + 2 := by
  rw [← Array.length_toList]
  simp [stackClaims, placedOf, List.take_of_length_le]

theorem vals_stackClaims (target : EW) (point coefficients : Array EW) (z : Array EW)
    (value : EW) :
    ((stackClaims layout target point coefficients cs z value).map (·.value)).toList =
      valsOf layout target cs value := by
  simp [stackClaims, valsOf, ringSwitchClaim]

theorem length_valsOf (target : EW) (value : EW) :
    (valsOf layout target cs value).length = placedOf layout cs cs.size + 2 := by
  simp [valsOf, placedOf, List.take_of_length_le]

theorem placedOf_succ {i : Nat} (hi : i < cs.size) :
    placedOf layout cs (i + 1) =
      placedOf layout cs i + (if (cs[i].onStack layout).isSome then 1 else 0) := by
  unfold placedOf
  rw [List.take_add_one, List.filterMap_append, List.length_append,
    List.getElem?_eq_getElem (by simp; omega), Array.getElem_toList]
  cases h : cs[i].onStack layout <;> simp [h]

theorem placedOf_le (i : Nat) : placedOf layout cs i ≤ placedOf layout cs cs.size := by
  unfold placedOf
  rw [show cs.toList.take cs.size = cs.toList by simp]
  have := List.take_append_drop i cs.toList
  conv => rhs; rw [← this]
  rw [List.filterMap_append, List.length_append]
  omega

theorem placedOf_le_self (i : Nat) : placedOf layout cs i ≤ i := by
  unfold placedOf
  exact (List.length_filterMap_le _ _).trans (List.length_take_le _ _)

/-- **The `j`th placed value** is the `i`th column claim's, `i` placed and `j = placedOf … i`. -/
theorem vals_placed {i : Nat} (hi : i < cs.size) (h : (cs[i].onStack layout).isSome)
    (target value : EW) :
    (valsOf layout target cs value)[placedOf layout cs i + 1]? = some cs[i].value := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  have hval : x.value = cs[i].value := by
    unfold ColumnClaimW.onStack at hx
    cases hp : (layout.placements[cs[i].column]?).getD none <;> rw [hp] at hx <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hx
    rw [← hx]
  have hsplit : cs.toList.filterMap (·.onStack layout) =
      (cs.toList.take i).filterMap (·.onStack layout) ++
        x :: (cs.toList.drop (i + 1)).filterMap (·.onStack layout) := by
    conv_lhs => rw [← List.take_append_drop (i + 1) cs.toList]
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega), Array.getElem_toList,
      List.filterMap_append, List.filterMap_append]
    simp [hx]
  simp only [valsOf, hsplit, placedOf, List.getElem?_cons_succ, List.map_append, List.map_cons,
    List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp [hval]

theorem dot_eq (a b : Array EW) : dot a b = dotL a.toList b.toList := by
  unfold dot dotL
  rw [← Array.foldl_toList, Array.toList_zipWith]

theorem dotL_take_succ {l r : List EW} {j : Nat} (hl : j < l.length) (hr : j < r.length) :
    dotL (l.take (j + 1)) (r.take (j + 1)) = dotL (l.take j) (r.take j) + l[j] * r[j] := by
  unfold dotL
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hl,
    List.getElem?_eq_getElem hr,
    List.zipWith_append (by simp; omega)]
  simp [List.foldl_append]

theorem dotL_take_one {l r : List EW} (hl : 0 < l.length) (hr : 0 < r.length) :
    dotL (l.take 1) (r.take 1) = l[0] * r[0] := by
  rw [dotL_take_succ hl hr]
  exact ew_zero_add _

/-- **The model's run**: the challenge squeezed, then the ladder and `whirLevels`. -/
theorem vso_run (L R : Nat) (claims : Array StackClaimW) (h : claims.size ≤ 512) (s : TState) :
    (verifyStackedOpening L R claims).run s = (Whir.ladder L R).bind fun cfg ↦
      (whirLevels L ((cfg.head?.map (·.fold)).getD 0) ⟨powers (sq s).1 claims.size, claims⟩ 0
        cfg ⟨dot (powers (sq s).1 claims.size) (claims.map (·.value)), #[], #[]⟩).run (sq s).2 := by
  have h' : decide (claims.size ≤ LeanVM.Protocol.Verifier.maxStackedClaims) = true :=
    decide_eq_true h
  unfold verifyStackedOpening verifyWhir require
  rw [h']
  cases hl : Whir.ladder L R <;> rfl

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
