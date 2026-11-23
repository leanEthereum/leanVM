module

public import NativeRustcVm.Whir.Basis
public import NativeVm.Equiv.Field

/-!
# `BasisW.eval` as `BasisW::eval` runs it

`BasisW::eval` takes the scales one by one, `0` once they run out (`sAt`), and sums each scale
times its claim's weight: the ring-switched claim's, each column claim's with a placement
(`colWs`), the out-of-domain claim's (`basis_eval`). `dot` stops at the shorter array, the code's
extra products are `0` (`dot_push`).
-/

namespace NativeRustcVm.Whir

open NativeVm.Model LeanVM.Parameters
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- Scale `k`, `0` past the end. -/
def sAt (sc : Array EW) (k : Nat) : EW := sc[k]?.getD 0

/-- The weights at `x` of the column claims with a placement among the first `i`. -/
def colWs (layout : LayoutW) (x : Array EW) (cs : Array ColumnClaimW) (i : Nat) : List EW :=
  ((cs.toList.take i).filterMap (·.onStack layout)).map (·.weight.eval x)

end

public section

theorem ew_zero_mul (x : EW) : (0 : EW) * x = 0 :=
  NativeVm.Equiv.EW.toE_injective (by
    rw [NativeVm.Equiv.EW.toE_mul, NativeVm.Equiv.EW.toE_zero, zero_mul])

theorem ew_zero_add (x : EW) : (0 : EW) + x = x :=
  NativeVm.Equiv.EW.toE_injective (by
    rw [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_zero, zero_add])

theorem ew_add_zero (x : EW) : x + (0 : EW) = x :=
  NativeVm.Equiv.EW.toE_injective (by
    rw [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_zero, add_zero])

theorem zipWith_snoc {f : EW → EW → EW} :
    ∀ (l r : List EW) (w : EW), List.zipWith f l (r ++ [w]) =
      List.zipWith f l r ++ (match l[r.length]? with | some a => [f a w] | none => [])
  | [], r, w => by simp
  | a :: l, [], w => by simp
  | a :: l, b :: r, w => by
    simp only [List.cons_append, List.zipWith_cons_cons, List.length_cons,
      List.getElem?_cons_succ, List.cons_append]
    rw [zipWith_snoc l r w]

/-- **A weight more**: its scale (or `0`) times it, added. -/
theorem dot_push (sc ws : Array EW) (w : EW) :
    dot sc (ws.push w) = dot sc ws + sAt sc ws.size * w := by
  unfold dot sAt
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_zipWith, Array.toList_zipWith,
    Array.toList_push, zipWith_snoc, List.foldl_append, ← Array.length_toList,
    ← Array.getElem?_toList]
  cases sc.toList[ws.toList.length]? with
  | none => simp [ew_zero_mul, ew_add_zero]
  | some a => simp

theorem dot_empty (sc : Array EW) : dot sc #[] = 0 := by
  unfold dot
  rw [← Array.foldl_toList, Array.toList_zipWith]
  simp

theorem colWs_succ (layout : LayoutW) (x : Array EW) (cs : Array ColumnClaimW) {i : Nat}
    (hi : i < cs.size) :
    colWs layout x cs (i + 1) = colWs layout x cs i ++
      (((layout.placements[cs[i].column]?).getD none).map fun pl ↦
        eqEval (stackPoint pl cs[i].point layout.stackLog) x).toList := by
  simp only [colWs, List.take_add_one, List.filterMap_append, List.map_append]
  rw [List.getElem?_eq_getElem (by simpa using hi), Array.getElem_toList]
  simp only [Option.toList_some, List.filterMap_cons, List.filterMap_nil, ColumnClaimW.onStack]
  cases (layout.placements[cs[i].column]?).getD none <;> simp [StackWeight.eval]

theorem colWs_zero (layout : LayoutW) (x : Array EW) (cs : Array ColumnClaimW) :
    colWs layout x cs 0 = [] := by simp [colWs]

/-- **`BasisW.eval` of the stack claims**: the scales against the ring-switched claim's weight,
the column claims', the out-of-domain claim's. -/
theorem basis_eval (sc : Array EW) (layout : LayoutW) (target : EW) (point coeffs : Array EW)
    (cs : Array ColumnClaimW) (z : Array EW) (value : EW) (x : Array EW) :
    BasisW.eval ⟨sc, stackClaims layout target point coeffs cs z value⟩ x =
      dot sc ((StackWeight.eval (.ring (layout.placement qkeccak) point coeffs) x ::
        colWs layout x cs cs.size) ++ [eqEval z x]).toArray := by
  simp only [BasisW.eval]
  congr 1
  apply Array.ext'
  simp [stackClaims, colWs, ringSwitchClaim, List.take_of_length_le, StackWeight.eval]

end

end NativeRustcVm.Whir
