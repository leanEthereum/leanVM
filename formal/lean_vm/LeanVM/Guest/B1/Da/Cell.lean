/-
  LeanVM.Guest.B1.Da.Cell

  `da_verify_cell`'s core IR gives its meaning (TRIAGE G #92).
-/

module

public import LeanVM.Guest.B1.Da.RowShape

/-!
# `da_verify_cell` (G:4386-4398)

`da_verify_cell(lvals)` (`core30`): `256` hinted symbols `.n 1 … .n 256`; pair `e`'s atoms
(`blkA e`, the template `tmplA`, compared atom by atom) assert both in `K`, pack them into the cell
`sym[2e] + y·sym[2e + 1]` (`packV e`) and add `lvals[2e]·sym[2e] + lvals[2e + 1]·sym[2e + 1]` to the
running sum (`accV e`, `acc_sum`); the `128` cells are hashed (`keccak_cells`, a `ChainSpec` from the
zero state, checked on the block after the template). The returned words are the digest's two
cells and the sum (`CellSound`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader} {σ : Val} {atoms : List Atom}

/-! ## The template of the packing and the dot product -/

/-- The running sum after pair `e`. -/
def accV (e : ℕ) : ℕ := if e = 0 then 264 else 256 + 9 * e + 8

/-- The packed cell of pair `e`. -/
def packV (e : ℕ) : ℕ := if e = 0 then 259 else 256 + 9 * e + 2

/-- **Pair `e`'s atoms**: `assert_in_k(sym[2e], sym[2e + 1])`, the packed cell
`sym[2e] + y·sym[2e + 1]`, and the two products `lvals[j]·sym[j]` added to the running sum. -/
def blkA (e : ℕ) : List Atom :=
  if e = 0 then
    [.assertInK (.n 1) (.n 2), .const (.n 257) (word 0 1), .mul (.n 258) (.n 257) (.n 2),
      .add (.n 259) (.n 1) (.n 258), .load (.n 260) (.n 0) 0, .mul (.n 261) (.n 260) (.n 1),
      .load (.n 262) (.n 0) 1, .mul (.n 263) (.n 262) (.n 2), .add (.n 264) (.n 261) (.n 263)]
  else
    [.assertInK (.n (2 * e + 1)) (.n (2 * e + 2)), .const (.n (256 + 9 * e)) (word 0 1),
      .mul (.n (256 + 9 * e + 1)) (.n (256 + 9 * e)) (.n (2 * e + 2)),
      .add (.n (256 + 9 * e + 2)) (.n (2 * e + 1)) (.n (256 + 9 * e + 1)),
      .load (.n (256 + 9 * e + 3)) (.n 0) (2 * e),
      .mul (.n (256 + 9 * e + 4)) (.n (256 + 9 * e + 3)) (.n (2 * e + 1)),
      .add (.n (256 + 9 * e + 5)) (.n (accV (e - 1))) (.n (256 + 9 * e + 4)),
      .load (.n (256 + 9 * e + 6)) (.n 0) (2 * e + 1),
      .mul (.n (256 + 9 * e + 7)) (.n (256 + 9 * e + 6)) (.n (2 * e + 2)),
      .add (.n (256 + 9 * e + 8)) (.n (256 + 9 * e + 5)) (.n (256 + 9 * e + 7))]

/-- The packing and the dot product: the `128` pairs' atoms. -/
def tmplA : List Atom := (List.range 128).flatMap blkA

/-- **Pair `e`'s facts.** -/
theorem blk_sound {e : ℕ} (he : e < 128) (hat : ∀ a ∈ tmplA, a.Holds rd σ) :
    IsInK (σ (.n (2 * e + 1))) ∧ IsInK (σ (.n (2 * e + 2))) ∧
    σ (.n (packV e)) = E.ofLimbs ((σ (.n (2 * e + 1))).limb 0) ((σ (.n (2 * e + 2))).limb 0) ∧
    LoadHolds rd (σ (.n 0)) (2 * e) (memAt rd (σ (.n 0)) (2 * e)) ∧
    LoadHolds rd (σ (.n 0)) (2 * e + 1) (memAt rd (σ (.n 0)) (2 * e + 1)) ∧
    σ (.n (accV e)) = (if e = 0 then 0 else σ (.n (accV (e - 1)))) +
      memAt rd (σ (.n 0)) (2 * e) * σ (.n (2 * e + 1)) +
      memAt rd (σ (.n 0)) (2 * e + 1) * σ (.n (2 * e + 2)) := by
  have hb : ∀ a ∈ blkA e, a.Holds rd σ := fun a ha =>
    hat a (List.mem_flatMap.mpr ⟨e, List.mem_range.mpr he, ha⟩)
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · have h := fun a (h : a ∈ blkA 0) => hb a h
    simp only [blkA, ite_true, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at h
    obtain ⟨⟨k1, k2⟩, c, m1, a1, l0, m2, l1, m3, a2⟩ := h
    have e0 := memAt_of_load l0
    have e1 := memAt_of_load l1
    refine ⟨k1, k2, ?_, by rw [e0]; exact l0, by rw [e1]; exact l1, ?_⟩
    · show σ (.n 259) = _
      rw [show σ (.n 259) = _ from a1, show σ (.n 258) = _ from m1, show σ (.n 257) = _ from c,
        word_y, pack64x2_eq k1 k2]
    · show σ (.n 264) = _
      rw [show σ (.n 264) = _ from a2, show σ (.n 261) = _ from m2, show σ (.n 263) = _ from m3,
        e0, e1]
      simp
  · have h := fun a (h : a ∈ blkA e) => hb a h
    simp only [blkA, show e ≠ 0 by omega, ite_false, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq] at h
    obtain ⟨⟨k1, k2⟩, c, m1, a1, l0, m2, a2, l1, m3, a3⟩ := h
    have e0 := memAt_of_load l0
    have e1 := memAt_of_load l1
    refine ⟨k1, k2, ?_, by rw [e0]; exact l0, by rw [e1]; exact l1, ?_⟩
    · rw [packV, ite_neg' (show ¬ e = 0 by omega), show σ (.n (256 + 9 * e + 2)) = _ from a1,
        show σ (.n (256 + 9 * e + 1)) = _ from m1, show σ (.n (256 + 9 * e)) = _ from c, word_y,
        pack64x2_eq k1 k2]
    · rw [accV, ite_neg' (show ¬ e = 0 by omega), ite_neg' (show ¬ e = 0 by omega),
        show σ (.n (256 + 9 * e + 8)) = _ from a3, show σ (.n (256 + 9 * e + 5)) = _ from a2,
        show σ (.n (256 + 9 * e + 4)) = _ from m2, show σ (.n (256 + 9 * e + 7)) = _ from m3,
        e0, e1]

/-- **The running sum**: after pair `e`, the sum of the first `2e + 2` products. -/
theorem acc_sum (hat : ∀ a ∈ tmplA, a.Holds rd σ) : ∀ e < 128,
    σ (.n (accV e)) = ((List.range (2 * e + 2)).map fun j =>
      memAt rd (σ (.n 0)) j * σ (.n (j + 1))).sum
  | 0, _ => by
    rw [(blk_sound (by omega) hat).2.2.2.2.2]
    simp [List.range_succ]
  | e + 1, he => by
    rw [(blk_sound he hat).2.2.2.2.2, ite_neg' (by omega), show e + 1 - 1 = e from rfl,
      acc_sum hat e (by omega), show 2 * (e + 1) + 2 = (2 * e + 2) + 2 by ring,
      @List.range_add (2 * e + 2) 2,
      List.map_append, List.sum_append, show List.range 2 = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring_nf

/-- Atom lists compared, words limb by limb. -/
def atomsEqb : List Atom → List Atom → Bool
  | [], [] => true
  | x :: xs, y :: ys => atomEqb x y && atomsEqb xs ys
  | _, _ => false

theorem atomsEqb_sound : ∀ {xs ys : List Atom}, atomsEqb xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [atomsEqb] at h
  | _ :: _, [], h => by simp [atomsEqb] at h
  | x :: xs, y :: ys, h => by
    simp only [atomsEqb, Bool.and_eq_true] at h
    rw [atomEqb_sound h.1, atomsEqb_sound h.2]

/-! ## The check -/

/-- The digest's chain: the `128` packed cells, `2048` bytes, from the zero state. -/
def cellSpec (atoms : List Atom) : ChainSpec :=
  ⟨(List.range 128).map fun e => some (.n (packV e)), 2048, true, none, keccakBlocks atoms⟩

/-- **`da_verify_cell`'s body, checked**: the hint, the template's atoms, then the chain, the
copies and `ret`. -/
def cellOk (fn : Fn) : Bool :=
  decide (fn.params = [.n 0]) &&
  match splitBody fn.body with
  | some (A, vs) =>
    decide (vs = [.n 1740, .n 1741, .n 1742]) && decide (1280 ≤ A.length) &&
    atomsEqb ((A.drop 1).take 1279) tmplA &&
    (cellSpec (A.drop 1280)).check (A.drop 1280) &&
    retOk (A.drop 1280) (cellSpec (A.drop 1280)) (.n 1740) (.n 1741) &&
    (A.drop 1280).any (isCopyAt (.n 1742) (.n 1407))
  | none => false

/-! ## Bytes -/

theorem flatMap_pairs {α : Type} (f : ℕ → α) (g : α → List UInt8) : ∀ n,
    ((List.range (2 * n)).map f).flatMap g =
      (List.range n).flatMap fun e => g (f (2 * e)) ++ g (f (2 * e + 1))
  | 0 => rfl
  | n + 1 => by
    have e : List.range (2 * (n + 1)) = List.range (2 * n) ++ [2 * n, 2 * n + 1] := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ]
      simp
    rw [e, List.map_append, List.flatMap_append, flatMap_pairs f g n, List.range_succ,
      List.flatMap_append]
    simp

end
end LeanVM.Guest.B1.Da
