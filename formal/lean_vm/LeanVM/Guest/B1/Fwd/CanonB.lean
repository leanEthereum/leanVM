/-
  LeanVM.Guest.B1.Fwd.CanonB

  `canonChk` with the known values as a bit mask (`canonGoB`): the same walk, each membership
  test one bit of a `Nat`, so that a kernel evaluation over thousands of atoms stays small.
-/

module

public import LeanVM.Guest.B1.Fwd.Canon

/-!
# The canonical-input checker on a bit mask

`mAdd M v`: the mask `M` with bit `v` set. `canonGoB M atoms`: `canonGo` with the values known
canonical the set bits of `M`. `canonGoB_eq`: on a mask whose bits are a list's members, it is
`canonGo` on that list; `canonChk_of_canonGoB`: `canonChk A atoms` from `canonGoB (maskOf A) atoms`. `canonGo_filter`:
dropping atoms the walk passes over (`canonSkip`: no `KECCAK`, `XOR`, copy, `SET`) changes nothing.
-/

namespace LeanVM.Guest.B1.Fwd

open LeanVM.Guest.Core

@[expose] public section

/-- The mask `M` with bit `v` set. -/
def mAdd (M v : Nat) : Nat := M ||| 2 ^ v

/-- **The walk on a mask**: `canonGo`, the values known canonical the set bits of `M`. -/
def canonGoB : Nat → List Atom → Bool
  | _, [] => true
  | M, .keccak ins outs _ _ :: as =>
    ins.all (fun v => M.testBit v.idx) && canonGoB (outs.foldr (fun o M => mAdd M o.idx) M) as
  | M, .add d x y :: as =>
    canonGoB (if M.testBit x.idx && M.testBit y.idx then mAdd M d.idx else M) as
  | M, .copy d s :: as => canonGoB (if M.testBit s.idx then mAdd M d.idx else M) as
  | M, .const d e :: as => canonGoB (if decide (e.limb 2 = 0) then mAdd M d.idx else M) as
  | M, _ :: as => canonGoB M as

/-- The mask of a list's members. -/
def maskOf (A : List Nat) : Nat := A.foldr (fun v M => mAdd M v) 0

theorem testBit_mAdd (M v w : Nat) : (mAdd M v).testBit w = (M.testBit w || w == v) := by
  rw [mAdd, Nat.testBit_or, Nat.testBit_two_pow]
  congr 1
  by_cases h : w = v
  · subst h; simp
  · simp [h, Ne.symm h]

theorem testBit_foldr (outs : List V) (M w : Nat) :
    (outs.foldr (fun o M => mAdd M o.idx) M).testBit w = ((outs.map V.idx).contains w || M.testBit w) := by
  induction outs with
  | nil => simp
  | cons o os ih =>
    rw [List.foldr_cons, testBit_mAdd, ih, List.map_cons, List.contains_cons]
    cases (os.map V.idx).contains w <;> cases M.testBit w <;> cases w == o.idx <;> simp [Bool.or_comm]

theorem testBit_maskOf (A : List Nat) (w : Nat) : (maskOf A).testBit w = A.contains w := by
  induction A with
  | nil => simp [maskOf]
  | cons a as ih =>
    rw [maskOf, List.foldr_cons, testBit_mAdd, ← maskOf, ih, List.contains_cons, Bool.or_comm]

theorem canonGoB_eq : ∀ (as : List Atom) (K : List Nat) (M : Nat),
    (∀ w, M.testBit w = K.contains w) → canonGoB M as = canonGo K as
  | [], _, _, _ => rfl
  | .keccak ins outs _ _ :: as, K, M, h => by
    simp only [canonGoB, canonGo, h]
    congr 1
    refine canonGoB_eq as _ _ fun w => ?_
    rw [testBit_foldr, h, List.contains_append]
  | .add d x y :: as, K, M, h => by
    simp only [canonGoB, canonGo, h]
    refine canonGoB_eq as _ _ fun w => ?_
    split
    · rw [testBit_mAdd, h, List.contains_cons, Bool.or_comm]
    · exact h w
  | .copy d s :: as, K, M, h => by
    simp only [canonGoB, canonGo, h]
    refine canonGoB_eq as _ _ fun w => ?_
    split
    · rw [testBit_mAdd, h, List.contains_cons, Bool.or_comm]
    · exact h w
  | .const d e :: as, K, M, h => by
    simp only [canonGoB, canonGo]
    refine canonGoB_eq as _ _ fun w => ?_
    split
    · rw [testBit_mAdd, h, List.contains_cons, Bool.or_comm]
    · exact h w
  | .mul .. :: as, K, M, h => canonGoB_eq as K M h
  | .load .. :: as, K, M, h => canonGoB_eq as K M h
  | .assertEq .. :: as, K, M, h => canonGoB_eq as K M h
  | .assertNe .. :: as, K, M, h => canonGoB_eq as K M h
  | .rangeCheck .. :: as, K, M, h => canonGoB_eq as K M h
  | .hint .. :: as, K, M, h => canonGoB_eq as K M h
  | .assertInK .. :: as, K, M, h => canonGoB_eq as K M h
  | .frameAddr .. :: as, K, M, h => canonGoB_eq as K M h
  | .touch .. :: as, K, M, h => canonGoB_eq as K M h

/-- **`canonChk` from the walk on the inputs' mask.** -/
theorem canonChk_of_canonGoB {A : List Nat} {atoms : List Atom}
    (h : canonGoB (maskOf A) atoms = true) : canonChk A atoms = true := by
  rw [canonChk, ← canonGoB_eq atoms A (maskOf A) (testBit_maskOf A)]
  exact h

/-- An atom the walk passes over. -/
def canonSkip : Atom → Bool
  | .keccak .. | .add .. | .copy .. | .const .. => false
  | _ => true

/-- **Dropping atoms the walk passes over does not change it**: so a check need not filter
(a filter by `∉ S` on atoms is a costly kernel evaluation). -/
theorem canonGo_filter (p : Atom → Bool) : ∀ (A : List Atom) (K : List Nat),
    (∀ a ∈ A, p a = false → canonSkip a = true) → canonGo K (A.filter p) = canonGo K A
  | [], _, _ => rfl
  | a :: as, K, h => by
    have ih : ∀ K', canonGo K' (as.filter p) = canonGo K' as := fun K' =>
      canonGo_filter p as K' fun b hb => h b (List.mem_cons_of_mem _ hb)
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp]
      cases a <;> simp only [canonGo, ih]
    · have hs := h a List.mem_cons_self (by simpa using hp)
      rw [List.filter_cons_of_neg hp, ih]
      cases a <;> simp_all [canonSkip, canonGo]

end
end LeanVM.Guest.B1.Fwd
