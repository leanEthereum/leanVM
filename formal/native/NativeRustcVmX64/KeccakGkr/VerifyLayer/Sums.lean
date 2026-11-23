module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Model
public import NativeVm.Equiv.KeccakRmfe

/-!
# `verify_layer`'s first check as the loops sum it

The sums of the first check in the native code's order: `xs f n` the sum of `f 0`, …, `f (n - 1)`
from `0`; `sel b x` the term a test keeps. The instance weights' masked sum (`masked_eq`), the
product's projection (`projected_eq`), the round constant's bit weights (`bits_eq`) and ι
(`iota_eq`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- `f 0 + … + f (n - 1)`, from `0`. -/
def xs (f : Nat → EW) (n : Nat) : EW := (List.range n).foldl (fun acc i ↦ acc + f i) 0

/-- The term a test keeps. -/
def sel (b : Bool) (x : EW) : EW := if b then x else 0

/-- The masked sum's term `i` at bit `j`. -/
def muSel (mu : Array EW) (j i : Nat) : EW :=
  sel (testBitW (rmfeProjectW.getD i 0) j) (mu.getD i 0)

/-- The projection's term `j`. -/
def projTerm (mu p : Array EW) (j : Nat) : EW := maskedOf mu j * p.getD j 0

/-- The bit weight `z` a round constant `k` keeps. -/
def bitSel (w : Array EW) (k : UInt64) (z : Nat) : EW := sel (testBitW k z) (w.getD z 0)

end

public section

theorem ew_add_zero' (x : EW) : x + 0 = x := by
  show (⟨x.c0 ^^^ 0, x.c1 ^^^ 0⟩ : EW) = x
  simp

theorem ew_zero_add' (x : EW) : 0 + x = x := by
  show (⟨0 ^^^ x.c0, 0 ^^^ x.c1⟩ : EW) = x
  simp

theorem ew_add_comm' (x y : EW) : x + y = y + x := by
  show (⟨x.c0 ^^^ y.c0, x.c1 ^^^ y.c1⟩ : EW) = ⟨y.c0 ^^^ x.c0, y.c1 ^^^ x.c1⟩
  rw [UInt64.xor_comm x.c0, UInt64.xor_comm x.c1]

theorem xs_zero (f : Nat → EW) : xs f 0 = 0 := rfl

theorem xs_succ (f : Nat → EW) (n : Nat) : xs f (n + 1) = xs f n + f n := by
  simp only [xs, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem getD_toList {α : Type} (a : Array α) (i : Nat) (d : α) : a.getD i d = a.toList.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem foldl_filterMap {α : Type} (g : α → Option EW) : ∀ (l : List α) (acc : EW),
    (l.filterMap g).foldl (· + ·) acc = l.foldl (fun acc x ↦ acc + (g x).getD 0) acc
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.filterMap_cons, List.foldl_cons]
    cases h : g x with
    | none =>
      simp only [Option.getD_none, ew_add_zero']
      exact foldl_filterMap g l acc
    | some v =>
      simp only [List.foldl_cons, Option.getD_some]
      exact foldl_filterMap g l (acc + v)

theorem foldl_range_shift (f : Nat → EW) (n : Nat) (acc : EW) :
    (List.range (n + 1)).foldl (fun acc i ↦ acc + f i) acc =
      (List.range n).foldl (fun acc i ↦ acc + f (i + 1)) (acc + f 0) := by
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

theorem foldl_zip (H : EW → UInt64 → EW) : ∀ (a : List EW) (b : List UInt64) (acc : EW),
    a.length ≤ b.length →
    (a.zip b).foldl (fun acc x ↦ acc + H x.1 x.2) acc =
      (List.range a.length).foldl (fun acc i ↦ acc + H (a.getD i 0) (b.getD i 0)) acc
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => absurd h (by simp)
  | x :: a, y :: b, acc, h => by
    rw [List.zip_cons_cons, List.foldl_cons, List.length_cons, foldl_range_shift]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact foldl_zip H a b _ (by simp only [List.length_cons] at h; omega)

/-- A sum over a range. -/
theorem sumE_map_range (f : Nat → EW) (n : Nat) : sumE ((Array.range n).map f) = xs f n := by
  unfold NativeVm.Model.sumE xs
  rw [← Array.foldl_toList, Array.toList_map, Array.toList_range, List.foldl_map]

/-- A masked sum over a range. -/
theorem sumE_filterMap_range (P : Nat → Bool) (g : Nat → EW) (n : Nat) :
    sumE ((Array.range n).filterMap fun z ↦ if P z then some (g z) else none) =
      xs (fun z ↦ sel (P z) (g z)) n := by
  unfold NativeVm.Model.sumE xs
  rw [← Array.foldl_toList, Array.toList_filterMap, Array.toList_range, foldl_filterMap]
  congr 1
  funext acc z
  unfold sel
  by_cases hP : P z <;> simp [hP]

theorem rmfeProjectW_size : rmfeProjectW.size = 16 := by
  rw [NativeVm.Equiv.rmfeProjectW_eq]
  rfl

/-- **The masked sum at bit `j`**, term by term. -/
theorem masked_eq (mu : Array EW) (j : Nat) (h : mu.size ≤ 16) :
    maskedOf mu j = xs (muSel mu j) mu.size := by
  unfold maskedOf NativeVm.Model.sumE
  rw [← Array.foldl_toList, Array.toList_filterMap, Array.toList_zip, foldl_filterMap]
  have e : (fun acc (x : EW × UInt64) ↦ acc +
      ((fun x : EW × UInt64 ↦ match x with
        | (m, mask) => if testBitW mask j then some m else none) x).getD 0) =
      fun acc x ↦ acc + sel (testBitW x.2 j) x.1 := by
    funext acc x
    obtain ⟨m, mask⟩ := x
    unfold sel
    by_cases hb : testBitW mask j <;> simp [hb]
  rw [e, foldl_zip (fun m mask ↦ sel (testBitW mask j) m) _ _ _
    (by rw [Array.length_toList, Array.length_toList, rmfeProjectW_size]; exact h),
    Array.length_toList]
  unfold xs muSel
  simp only [getD_toList]

/-- **The projection**, term by term. -/
theorem projected_eq (mu p : Array EW) : projectedOf mu p = xs (projTerm mu p) 47 := by
  unfold projectedOf
  rw [sumE_map_range, show productBits = 47 by decide]
  rfl

/-- **A round constant's bit weights**, bit by bit. -/
theorem bits_eq (w : Array EW) (k : UInt64) : bitsOf w k = xs (bitSel w k) 64 := by
  unfold bitsOf
  exact sumE_filterMap_range _ _ _

/-- **ι**: the two segments' terms. -/
theorem iota_eq (logSteps step : Nat) (c : KeccakClaimW) :
    iotaOf logSteps step c =
      (eqKernel (c.point.extract (logSteps - 4) c.point.size)).getD 0 0 *
          bitsOf c.weights (keccakRCW.getD (11 - step) 0) +
        (eqKernel (c.point.extract (logSteps - 4) c.point.size)).getD 1 0 *
          bitsOf c.weights (keccakRCW.getD (23 - step) 0) := by
  unfold iotaOf
  rw [sumE_map_range, show keccakSegments = 2 by decide, xs_succ, xs_succ, xs_zero,
    ew_zero_add']
  simp only [show keccakDepth = 12 from rfl, show 12 * (0 + 1) - step - 1 = 11 - step by omega,
    show 12 * (1 + 1) - step - 1 = 23 - step by omega]

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
