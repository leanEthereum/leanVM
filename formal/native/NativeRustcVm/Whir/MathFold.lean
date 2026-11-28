module

public import NativeVm.Model.Whir

/-!
# `fold_row` as rustc compiled it

rustc unrolled `fold_row`'s rounds (at most six, its callers' `Buf<FoldRoundW, 6>`) and runs
round `r`'s turns `i < n >>> r` (not `min n 64 >>> r`), a turn writing lane `i` only for
`i < 32` (`values.get` in bounds). The lanes in memory after `r` rounds are `foldMem r`
(`foldPart` a round's first `i` turns, in place: turn `i` reads lanes `2i`, `2i + 1`, not yet
written). Their first `min n 64 >>> r` are the model's (`foldMem_eq`), so the result, lane `0`
when `n >>> R ≠ 0`, is `foldRow` (`foldRow_eq`).
-/

namespace NativeRustcVm.Whir

open NativeVm.Model

@[expose] public section

/-- A round's factor `α + β·x`. -/
def foldFactor (x : UInt64) (rd : FoldRoundW) : EW := rd.alpha + EW.scale x rd.beta

/-- The lanes after a round's first `i` turns. -/
def foldPart (x : UInt64) (rd : FoldRoundW) (i : Nat) (old : Nat → EW) : Nat → EW :=
  fun j ↦ if j < min i 32 then old (2 * j + 1) + foldFactor x rd * old (2 * j) else old j

/-- The lanes after `r` rounds, `v0` at first. -/
def foldMem (x : UInt64) (rounds : Array FoldRoundW) (n : Nat) (v0 : Nat → EW) : Nat → Nat → EW
  | 0 => v0
  | r + 1 => foldPart x (rounds.getD r default) (n >>> (r + 1)) (foldMem x rounds n v0 r)

end

public section

theorem foldPart_zero (x : UInt64) (rd : FoldRoundW) (old : Nat → EW) :
    foldPart x rd 0 old = old := by
  funext j
  simp [foldPart]

/-- A turn past lane `31` writes nothing. -/
theorem foldPart_succ_of_le (x : UInt64) (rd : FoldRoundW) (old : Nat → EW) {i : Nat}
    (h : 32 ≤ i) : foldPart x rd (i + 1) old = foldPart x rd i old := by
  funext j
  simp only [foldPart, show min (i + 1) 32 = 32 by omega, show min i 32 = 32 by omega]

/-- Turn `i < 32` writes lane `i`. -/
theorem foldPart_succ (x : UInt64) (rd : FoldRoundW) (old : Nat → EW) {i : Nat} (h : i < 32) :
    foldPart x rd (i + 1) old = Function.update (foldPart x rd i old) i
      (old (2 * i + 1) + foldFactor x rd * old (2 * i)) := by
  funext j
  simp only [foldPart, Function.update]
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp only [hj, dite_false]
    by_cases hji : j < i
    · simp [show j < min (i + 1) 32 by omega, show j < min i 32 by omega]
    · simp [show ¬j < min (i + 1) 32 by omega, show ¬j < min i 32 by omega]

/-- Turn `i` reads lanes `2i`, `2i + 1`: not yet written. -/
theorem foldPart_old (x : UInt64) (rd : FoldRoundW) (old : Nat → EW) {i j : Nat} (h : i ≤ j) :
    foldPart x rd i old j = old j := by
  simp [foldPart, show ¬j < min i 32 by omega]

theorem shiftRight_succ' (n r : Nat) : n >>> (r + 1) = (n >>> r) / 2 := by
  rw [Nat.shiftRight_succ]

theorem min_shiftRight_le (n r : Nat) : min n 64 >>> (r + 1) ≤ min (n >>> (r + 1)) 32 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  refine le_min (Nat.div_le_div_right (Nat.min_le_left _ _)) ?_
  calc min n 64 / 2 ^ (r + 1) ≤ 64 / 2 ^ (r + 1) := Nat.div_le_div_right (Nat.min_le_right _ _)
    _ ≤ 64 / 2 ^ 1 := Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) (by omega))
        (by decide)
    _ = 32 := by decide

/-- **The model's lanes are the memory's**, round by round. -/
theorem foldMem_eq (x : UInt64) (rounds : Array FoldRoundW) (n : Nat) (v0 : Nat → EW)
    (values : Array EW) (hsz : values.size = min n 64)
    (hv : ∀ j (h : j < values.size), values[j] = v0 j) :
    ∀ r, r ≤ rounds.size →
      ((rounds.toList.take r).foldl (fun v rd ↦ foldLanes x rd v) values).size = min n 64 >>> r ∧
      ∀ j (h : j < ((rounds.toList.take r).foldl (fun v rd ↦ foldLanes x rd v) values).size),
        ((rounds.toList.take r).foldl (fun v rd ↦ foldLanes x rd v) values)[j] =
          foldMem x rounds n v0 r j
  | 0, _ => by simp [hsz, foldMem, hv]
  | r + 1, hr => by
    obtain ⟨ih1, ih2⟩ := foldMem_eq x rounds n v0 values hsz hv r (by omega)
    have ht : rounds.toList.take (r + 1) = rounds.toList.take r ++ [rounds[r]] := by
      rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem (by omega)]
      rfl
    rw [ht, List.foldl_append]
    generalize hA : (rounds.toList.take r).foldl (fun v rd ↦ foldLanes x rd v) values = A at ih1 ih2
    simp only [List.foldl_cons, List.foldl_nil]
    have hsz' : (foldLanes x rounds[r] A).size = min n 64 >>> (r + 1) := by
      simp [foldLanes, ih1, shiftRight_succ']
    refine ⟨hsz', fun j hj ↦ ?_⟩
    have hj' : j < min n 64 >>> (r + 1) := hsz' ▸ hj
    have hlt := min_shiftRight_le n r
    have h2 : 2 * j + 1 < A.size := by rw [ih1]; rw [shiftRight_succ'] at hj'; omega
    simp only [foldLanes, Array.getElem_map, Array.getElem_range]
    have hjc : j < min (n >>> (r + 1)) 32 := by omega
    rw [foldMem, foldPart]
    simp only [hjc, ↓reduceIte]
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem h2, Option.getD_some, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega), Option.getD_some, ih2 _ h2, ih2 _ (by omega)]
    simp [foldFactor, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show r < rounds.size by omega)]

/-- **`fold_row`'s result**: lane `0` after the rounds, or `0` once no lane is left. -/
theorem foldRow_eq (x : UInt64) (rounds : Array FoldRoundW) (n : Nat) (v0 : Nat → EW)
    (values : Array EW) (hsz : values.size = min n 64)
    (hv : ∀ j (h : j < values.size), values[j] = v0 j) (hR : rounds.size ≤ 6) :
    foldRow values x rounds =
      if n >>> rounds.size = 0 then 0 else foldMem x rounds n v0 rounds.size 0 := by
  have key := foldMem_eq x rounds n v0 values hsz hv rounds.size le_rfl
  rw [List.take_of_length_le (by simp), Array.foldl_toList] at key
  obtain ⟨h1, h2⟩ := key
  have hp : 2 ^ rounds.size ≤ 64 :=
    (Nat.pow_le_pow_right (by decide) hR).trans (by decide)
  have hiff : min n 64 >>> rounds.size = 0 ↔ n >>> rounds.size = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff,
      Nat.div_eq_zero_iff]
    have := Nat.two_pow_pos rounds.size
    omega
  rw [foldRow, Array.getD_eq_getD_getElem?]
  by_cases h0 : n >>> rounds.size = 0
  · simp only [h0, ↓reduceIte]
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  · simp only [h0, ↓reduceIte]
    rw [Array.getElem?_eq_getElem (by omega), Option.getD_some, h2]

end

end NativeRustcVm.Whir
