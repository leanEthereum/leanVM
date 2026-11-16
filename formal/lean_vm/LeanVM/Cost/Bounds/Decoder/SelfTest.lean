module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.FieldLib
public import LeanVM.Cost.Bounds.Decoder.GuestPlacesOk
public import LeanVM.Cost.Bounds.Decoder.GuestTablesBounds
public import LeanVM.Cost.Decoder.EntryTable

/-!
# Bound: a frame's words and the decoder's self test, compiled

The prices of the words the decoder reads off a frame, a memory read (the reader closure `rdVal`)
at most `R`:

* the guest's tables' maxima (`argCount_le`, `retCount_le`, `registered_le`) and every place code's
  cell below `2^13` and shift below `g^8` (`place_ok`, from `GuestPlacesOk.lean`);
* `powSqW_cost`: a power `g^o`, `o < 2^W`, by squaring, at most `psAt W = 5 + 73·W`;
  `powSqE_cost`: a power in `E` by squaring;
* `wordWith_cost`: a frame cell's word, its offset below `2^W`, at most `psAt W + R + 43`;
* **`placeWord_cost`**: the word a place code names (`placeWordC`, `Decoder/Witness.lean`), its
  cell below `2^13` and its shift below `g^8` (every code of the guest's table:
  `GuestPlacesOk.lean`), at most `R + 1320`;
* **`selfTest_cost`**: the self test the decoder files a state under (`selfTestC`,
  `Located.selfTest`: a callee, and a registered loop helper's own pointer past its at most `56`
  arguments), at most `2·R + 1104`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Located

public section

/-- A power `g^o` by squaring, `o < 2^W` (`powSq_cost`). -/
@[expose] def psAt (W : ℕ) : ℕ := 5 + 73 * W

/-! ## The guest's tables -/

theorem toArray_getD_le_of_all {l : List ℕ} {B : ℕ} (h : l.all (· ≤ B) = true) (j : ℕ) :
    l.toArray.getD j 0 ≤ B := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rw [List.all_eq_true] at h
  cases hj : l[j]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (h x (List.mem_of_getElem? hj))

theorem argCount_le (j : ℕ) : guestArgCounts.getD j 0 ≤ 56 :=
  toArray_getD_le_of_all guestArgCountsList_le j

theorem retCount_le (j : ℕ) : guestRetCounts.getD j 0 ≤ 10 :=
  toArray_getD_le_of_all guestRetCountsList_le j

/-- Every registered flag is `0` or `1`. -/
theorem guestRegisteredList_le : guestRegisteredList.all (· ≤ 1) = true := by decide +kernel

theorem registered_le (j : ℕ) : guestRegistered.getD j 0 ≤ 1 :=
  toArray_getD_le_of_all guestRegisteredList_le j

/-- An entry of a table of rows, `0` past the rows, has a property `0` has and every entry has. -/
theorem getD_getD_of (A : Array (Array ℕ)) (p : ℕ → Prop) (h0 : p 0)
    (h : ∀ a ∈ A, ∀ x ∈ a, p x) (j i : ℕ) : p ((A.getD j #[]).getD i 0) := by
  by_cases h1 : j < A.size
  · have e : A.getD j #[] = A[j] := by simp [Array.getD, h1]
    rw [e]
    by_cases h2 : i < A[j].size
    · have e2 : A[j].getD i 0 = A[j][i] := by simp [Array.getD, h2]
      rw [e2]
      exact h _ (Array.getElem_mem h1) _ (Array.getElem_mem h2)
    · have e2 : A[j].getD i 0 = 0 := by simp [Array.getD, h2]
      rw [e2]
      exact h0
  · have e : A.getD j #[] = #[] := by simp [Array.getD, h1]
    rw [e]
    simpa using h0

/-- **Every place code of the guest's table** names a cell below `2^13`, shifted by at most `g^7`. -/
theorem place_ok (j i : ℕ) :
    (guestPlaces.getD j #[]).getD i 0 % 2 ^ 20 < 2 ^ 13 ∧ (guestPlaces.getD j #[]).getD i 0 < 9 * 2 ^ 20 := by
  refine getD_getD_of _ (fun c ↦ c % 2 ^ 20 < 2 ^ 13 ∧ c < 9 * 2 ^ 20) (by norm_num)
    (fun a ha x hx ↦ ?_) j i
  have h := guestPlacesList_ok
  rw [List.all_eq_true] at h
  rw [show guestPlaces = (guestPlacesList.map List.toArray).toArray from rfl, List.mem_toArray,
    List.mem_map] at ha
  obtain ⟨l, hl, rfl⟩ := ha
  have hl' := h l hl
  rw [List.all_eq_true] at hl'
  have := hl' x (by simpa using hx)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

variable (P : LeanVM.Cost.MachineProgram)

/-! ## Powers -/

/-- A power `g^o` by squaring, `o < 2^W`: at most `psAt W`. -/
theorem powSqW_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c101.costDeps) {W o : ℕ}
    (hW : 0 < W) (hW64 : W < 64) (ho : o < 2 ^ W) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c101.costIdx [encodeValue LeanVM.Parameters.g, encodeValue o] ≤
      psAt W := by
  have h64 : 2 ^ W ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hW64.le
  have h1 := powSq_cost P hP LeanVM.Parameters.g o (by omega)
  have h2 := log2_lt_of hW ho
  unfold psAt
  omega

/-- A power in `E` by squaring (`powSqEC`): at most `11 + 606·(log₂ n + 1)`. -/
theorem powSqE_cost (hP : Includes P powSqEC.costDeps) (a : E) (n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P powSqEC.costIdx [encodeValue a, encodeValue n] ≤
      11 + 606 * (Nat.log2 n + 1) := by
  have := le_of_halving (fun x : E × ℕ ↦ x.2 < 2 ^ 64) (fun x ↦ x.2)
    (fun x ↦ machineCost P powSqEC.costIdx
      [encodeValue x.1, encodeValue x.2]) 606 11
    (fun x hx h0 ↦ by
      rw [powSqEC.costEq P hP, h0]
      simp)
    (fun x hx hpos ↦ by
      right
      refine ⟨(x.1 * x.1, x.2 / 2), by dsimp only; omega, le_refl _, ?_⟩
      rw [powSqEC.costEq P hP, limbs_of_lt hx,
        limbs_of_lt (by omega : x.2 % 2 < 2 ^ 64)]
      simp only [show x.2 ≠ 0 by omega, ↓reduceIte]
      split_ifs <;> omega)
    (a, n) hn
  simpa using this

/-! ## A frame's words -/

section Reads

variable (rd : Reader) (rdVal : MachineValue)
  (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
  (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
  {W : ℕ} (hW : 0 < W) (hW64 : W < 64)

include hrd

include hR hW hW64 in
/-- A frame cell's word (`wordWithC`): a power, a read and `43`. -/
theorem wordWith_cost (hP : Includes P wordWithC.costDeps) (fp : K)
    (o : ℕ) (ho : o < 2 ^ W) :
    machineCost P wordWithC.costIdx
      [rdVal, encodeValue fp, encodeValue o] ≤ psAt W + R + 43 := by
  rw [wordWithC.costEq P hP rd rdVal hrd]
  have := powSqW_cost P (by includes) hW hW64 ho
  have := hR (fp * addressOfIndex o)
  generalize rd (fp * addressOfIndex o) = r
  cases r <;> dsimp only <;> omega

include hR in
/-- **The word a place code names** (`placeWordC`), its cell below `2^13` and its shift below
`g^8`: at most `R + 1320` (a cell's word, and for a shifted place a power `g^e` by squaring and a
product limb by limb). -/
theorem placeWord_cost (hP : Includes P placeWordC.costDeps) (fp : K) (c : ℕ)
    (h1 : c % 2 ^ 20 < 2 ^ 13) (h2 : c < 9 * 2 ^ 20) :
    machineCost P placeWordC.costIdx [rdVal, encodeValue fp, encodeValue c] ≤ R + 1320 := by
  rw [placeWordC.costEq P hP rd rdVal hrd]
  have hc : c < 2 ^ 64 := by omega
  rw [limbs_of_lt hc, limbs_of_lt (by norm_num : (1 : ℕ) <<< 20 < 2 ^ 64),
    limbs_of_lt (by norm_num : (2 : ℕ) ^ 20 < 2 ^ 64),
    limbs_of_lt (by omega : c / 2 ^ 20 < 2 ^ 64)]
  split_ifs with h0 h20
  · omega
  · have hc' : c < 2 ^ 13 := by rw [Nat.mod_eq_of_lt h20] at h1; exact h1
    have := wordWith_cost P rd rdVal hrd R hR (W := 13) (by norm_num) (by norm_num) (by includes)
      fp c hc'
    unfold psAt at this
    omega
  · have hw := wordWith_cost P rd rdVal hrd R hR (W := 13) (by norm_num) (by norm_num)
      (by includes) fp (c % 2 ^ 20) h1
    have he := powSqW_cost P (by includes) (W := 3) (o := c / 2 ^ 20 - 1) (by norm_num)
      (by norm_num) (by omega)
    have hm : machineCost P mulKC.costIdx [encodeValue (wordWith rd fp (c % 2 ^ 20)),
        encodeValue (addressOfIndex (c / 2 ^ 20 - 1))] = 63 :=
      (mulKC.costEq P (by includes) _ _).trans (by norm_num)
    unfold psAt at hw he
    omega

include hR in
/-- **The self test** (`selfTestC`, `Located.selfTest`): at most `2·R + 1104` (a registered loop
helper's own pointer, past its at most `56` arguments, read and compared limb by limb). -/
theorem selfTest_cost (hP : Includes P selfTestC.costDeps) (j : ℕ) (hj : j < 2 ^ 64) (fp : K) :
    machineCost P selfTestC.costIdx [rdVal, encodeValue j, encodeValue fp] ≤ 2 * R + 1104 := by
  rw [selfTestC.costEq P hP rd rdVal hrd]
  have ha := argCount_le j
  have hreg : guestRegistered.getD j 0 < 2 ^ 64 := by have := registered_le j; omega
  have hw := wordWith_cost P rd rdVal hrd R hR (W := 6) (by norm_num) (by norm_num) (by includes)
    fp (2 + guestArgCounts.getD j 0) (by omega)
  unfold psAt at hw
  rw [limbs_of_lt hj, limbs_of_lt (by unfold LeanVM.Guest.nFns; norm_num : LeanVM.Guest.nFns < 2 ^ 64),
    limbs_of_lt hreg, limbs_of_lt (by omega : 2 + guestArgCounts.getD j 0 < 2 ^ 64),
    limbs_of_lt (by omega : guestArgCounts.getD j 0 < 2 ^ 64)]
  split_ifs <;> (try simp only [max_self]) <;> omega

end Reads

end

end LeanVM.Cost.Bounds
