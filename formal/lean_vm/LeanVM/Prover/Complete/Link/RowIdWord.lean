/-
  LeanVM.Prover.Complete.Link.RowIdWord

  `Functionals.new`'s tables read at a one-hot pointer word.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdStep

/-!
# The functionals at a one-hot word

`Functionals.new c r maxShift` lists `D_i` (`eqKernel` of chunk `i`'s part of `r`), `D̄_i` (the same
reversed) and chunk `0`'s window reads `T_s`. At the one-hot word of `σ < 2^W`:

* `evalChunk_D`: `D_i` reads `eq(r_i, σ_i)`;
* `cert_zero`: `D_i·D̄_i + π_i = 0`;
* `prod_D`: `D_0·Π_{i ≥ 1} D_i = eq(r, σ)`;
* `window_rest`: `T_s·Π_{i ≥ 1} D_i = shEq σ s`, the equality weight at `σ + s` inside the window,
  zero past it (`Chunks.shifted`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset
open LeanVM.Protocol.KeccakGkr (eqAt eqKernel_getD eqKernel_length)

/-- The equality weight at the pointer `σ` read `s` cells further, zero past its window. -/
def shEq (c : Chunks) (r : List E) (σ s : ℕ) : E :=
  match c.shifted σ s with
  | some j => eqAt r j
  | none => 0

theorem shEq_zero (c : Chunks) (r : List E) (σ : ℕ) : shEq c r σ 0 = eqAt r σ := by
  simp [shEq, Chunks.shifted, Nat.mod_lt _ (Nat.two_pow_pos _)]

/-- The index a pointer word names, its first. -/
def ptrOf (c : Chunks) (w : K) : ℕ := (c.indices (kToNat w)).headD 0

section Tables

variable (c : Chunks) (r : List E) (ms : ℕ)

theorem fn_D {i : ℕ} (hi : i < c.d) :
    (Functionals.new c r ms).tables.getD i (0, []) = (i, eqKernel (c.part r i)) := by
  simp [Functionals.new, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi]

theorem fn_Dbar {i : ℕ} (hi : i < c.d) :
    (Functionals.new c r ms).tables.getD (c.d + i) (0, []) =
      (i, (eqKernel (c.part r i)).reverse) := by
  simp [Functionals.new, List.getD_eq_getElem?_getD, List.getElem?_append_left,
    List.getElem?_append_right, hi]

theorem fn_T {s : ℕ} (hs : 1 ≤ s) (hs' : s ≤ ms) (hd : 1 ≤ c.d) :
    (Functionals.new c r ms).tables.getD (2 * c.d + s - 1) (0, []) =
      (0, linkWindowShift (eqKernel (c.part r 0)) s) := by
  have h1 : 2 * c.d + s - 1 = (c.d + c.d) + (s - 1) := by omega
  simp only [Functionals.new, List.getD_eq_getElem?_getD, h1]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_append, List.length_map, List.length_zip, List.length_range, min_self,
    Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range (show s - 1 < ms by omega),
    Option.map_some, Option.getD_some, Prod.mk.injEq, true_and]
  rw [show s - 1 + 1 = s by omega]
  congr 2
  obtain ⟨d', hd'⟩ : ∃ d', c.d = d' + 1 := ⟨c.d - 1, by omega⟩
  rw [hd', List.range_succ_eq_map]
  simp

theorem fn_mirror {i : ℕ} (hi : i < c.d) :
    (Functionals.new c r ms).mirrors.getD i 0 = prodE ((c.part r i).map fun x ↦ x * (1 + x)) := by
  simp [Functionals.new, List.getD_eq_getElem?_getD, hi]

end Tables

/-! ## At a one-hot word -/

section OneHot

variable {c : Chunks} (hc : ChunkFacts c) (r : List E) (hr : r.length = c.width)
include hc hr

theorem digit_lt_part {i : ℕ} (hi : i < c.d) (σ : ℕ) : c.digit σ i < 2 ^ (c.part r i).length := by
  rw [length_part hc r hr hi]; exact digit_lt c σ i

theorem evalChunk_D (σ : ℕ) {i : ℕ} (hi : i < c.d) :
    evalChunk c (eqKernel (c.part r i)) (c.encode σ) i = eqAt (c.part r i) (c.digit σ i) := by
  have hl := digit_lt_part hc r hr hi σ
  rw [evalChunk_pow c _ _ i _ (fun j hj ↦ hc.bits σ i hi j (by
      rwa [eqKernel_length, length_part hc r hr hi] at hj)) (by rw [eqKernel_length]; exact hl),
    eqKernel_getD, ite_eq_left hl]

theorem evalChunk_Dbar (σ : ℕ) {i : ℕ} (hi : i < c.d) :
    evalChunk c (eqKernel (c.part r i)).reverse (c.encode σ) i =
      (eqKernel (c.part r i)).reverse.getD (c.digit σ i) 0 := by
  have hl := digit_lt_part hc r hr hi σ
  exact evalChunk_pow c _ _ i _ (fun j hj ↦ hc.bits σ i hi j (by
      rwa [List.length_reverse, eqKernel_length, length_part hc r hr hi] at hj)) (by
    rw [List.length_reverse, eqKernel_length]; exact hl)

/-- **The mirror term vanishes at a one-hot chunk.** -/
theorem cert_zero (σ : ℕ) {i : ℕ} (hi : i < c.d) :
    evalChunk c (eqKernel (c.part r i)) (c.encode σ) i *
        evalChunk c (eqKernel (c.part r i)).reverse (c.encode σ) i +
      prodE ((c.part r i).map fun x ↦ x * (1 + x)) = 0 := by
  have hl := digit_lt_part hc r hr hi σ
  rw [evalChunk_D hc r hr σ hi, evalChunk_Dbar hc r hr σ hi]
  have := mirror_cancel _ hl
  rwa [eqKernel_getD, ite_eq_left hl] at this

/-- The weights of the chunks past the first. -/
def restProd (c : Chunks) (r : List E) (σ : ℕ) : E :=
  ((List.range (c.d - 1)).map fun i ↦ eqAt (c.part r (i + 1)) (c.digit σ (i + 1))).prod

/-- **The chunks' product** at a one-hot word: `D_0·Π_{i ≥ 1} D_i = eq(r, σ)`. -/
theorem prod_D (σ : ℕ) : eqAt (c.part r 0) (c.digit σ 0) * restProd c r σ = eqAt r σ := by
  rw [← prod_eqAt_digit hc r hr σ, restProd]
  obtain ⟨d', hd'⟩ : ∃ d', c.d = d' + 1 := ⟨c.d - 1, by have := hc.pos; omega⟩
  rw [hd', List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map,
    Nat.add_sub_cancel]
  rfl

omit hr in
theorem indexShift_zero : c.indexShifts.getD 0 0 = 0 := by
  rw [hc.shifts]
  obtain ⟨d', hd'⟩ : ∃ d', c.d = d' + 1 := ⟨c.d - 1, by have := hc.pos; omega⟩
  unfold Chunks.d at hd'
  obtain ⟨w, ws, hw⟩ : ∃ w ws, c.widths = w :: ws := by
    cases h : c.widths with
    | nil => rw [h] at hd'; simp at hd'
    | cons w ws => exact ⟨w, ws, rfl⟩
  rw [hw, exclusivePrefix_cons]
  rfl

omit hr in
theorem le_indexShift_succ {i : ℕ} (hi : i + 1 < c.d) :
    c.widths.getD 0 0 ≤ c.indexShifts.getD (i + 1) 0 := by
  rw [hc.shifts]
  unfold Chunks.d at hi
  obtain ⟨w, ws, hw⟩ : ∃ w ws, c.widths = w :: ws := by
    cases h : c.widths with
    | nil => rw [h] at hi; simp at hi
    | cons w ws => exact ⟨w, ws, rfl⟩
  rw [hw] at hi ⊢
  rw [exclusivePrefix_cons]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  have hi' : i < ws.length := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simp [length_exclusivePrefix, hi']), List.getElem_map]
  omega

omit hr in
theorem digit_zero (σ : ℕ) : c.digit σ 0 = σ % 2 ^ c.widths.getD 0 0 := by
  unfold Chunks.digit
  rw [indexShift_zero hc, Nat.shiftRight_zero]

/-- **A window read** at a one-hot word: `T_s·Π_{i ≥ 1} D_i` is `shEq σ s`. -/
theorem window_rest (σ s : ℕ) :
    (eqKernel (c.part r 0)).getD (c.digit σ 0 + s) 0 * restProd c r σ = shEq c r σ s := by
  have hd := hc.pos
  have hl0 : (c.part r 0).length = c.widths.getD 0 0 := length_part hc r hr hd
  rw [eqKernel_getD, hl0, digit_zero hc]
  unfold shEq Chunks.shifted
  by_cases hw : σ % 2 ^ c.widths.getD 0 0 + s < 2 ^ c.widths.getD 0 0
  · rw [ite_eq_left hw]
    simp only [hw, ↓reduceIte]
    have hrest : restProd c r σ = restProd c r (σ + s) := by
      unfold restProd
      refine congrArg _ (List.map_congr_left fun i hi ↦ ?_)
      have hi' : i + 1 < c.d := by have := List.mem_range.mp hi; omega
      simp only [Chunks.digit, Nat.shiftRight_eq_div_pow]
      rw [div_shift_add (le_indexShift_succ hc hi') hw]
    have h0 : (σ + s) % 2 ^ c.widths.getD 0 0 = σ % 2 ^ c.widths.getD 0 0 + s := by
      have := Nat.mod_add_div σ (2 ^ c.widths.getD 0 0)
      have e : σ + s = (σ % 2 ^ c.widths.getD 0 0 + s) + 2 ^ c.widths.getD 0 0 * (σ / 2 ^ c.widths.getD 0 0) := by
        omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]
    rw [hrest, ← h0, ← digit_zero hc, prod_D hc r hr]
  · rw [ite_eq_right hw]
    simp only [hw, ↓reduceIte, zero_mul]

end OneHot

end LeanVM.Prover.Complete.RowId

end
