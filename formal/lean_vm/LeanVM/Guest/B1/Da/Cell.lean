/-
  LeanVM.Guest.B1.Da.Cell

  `da_verify_cell`'s core IR gives its meaning (TRIAGE G #92).
-/

module

public import LeanVM.Guest.B1.Da.Padding

/-!
# `da_verify_cell`

`da_verify_cell(lvals)`: `128` hinted symbols `.n 1 … .n 128`, each a word of `E`; symbol `e`'s
atoms (`blkA e`, the template `tmplA`, compared atom by atom) load the weight `lvals[e]` and add
its product with the symbol to the running sum (`accV e`, `acc_sum`); the symbols are hashed as
they are (`keccak_cells`, a `ChainSpec` from the zero state, checked on the block after the
template). The returned words are the digest's two cells and the sum (`CellSound`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader} {σ : Val} {atoms : List Atom}

/-! ## The template of the dot product -/

/-- The running sum after symbol `e`. -/
def accV (e : ℕ) : ℕ := 130 + 3 * e

/-- **Symbol `e`'s atoms**: the weight `lvals[e]` loaded, its product with the symbol, added to the
running sum (the first product is the sum). -/
def blkA (e : ℕ) : List Atom :=
  if e = 0 then
    [.load (.n 129) (.n 0) 0, .mul (.n 130) (.n 129) (.n 1)]
  else
    [.load (.n (128 + 3 * e)) (.n 0) e, .mul (.n (129 + 3 * e)) (.n (128 + 3 * e)) (.n (e + 1)),
      .add (.n (130 + 3 * e)) (.n (accV (e - 1))) (.n (129 + 3 * e))]

/-- The dot product: the `128` symbols' atoms. -/
def tmplA : List Atom := (List.range 128).flatMap blkA

/-- **Symbol `e`'s facts.** -/
theorem blk_sound {e : ℕ} (he : e < 128) (hat : ∀ a ∈ tmplA, a.Holds rd σ) :
    LoadHolds rd (σ (.n 0)) e (memAt rd (σ (.n 0)) e) ∧
    σ (.n (accV e)) = (if e = 0 then 0 else σ (.n (accV (e - 1)))) +
      memAt rd (σ (.n 0)) e * σ (.n (e + 1)) := by
  have hb : ∀ a ∈ blkA e, a.Holds rd σ := fun a ha =>
    hat a (List.mem_flatMap.mpr ⟨e, List.mem_range.mpr he, ha⟩)
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · have h := fun a (h : a ∈ blkA 0) => hb a h
    simp only [blkA, ite_true, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at h
    obtain ⟨l0, m⟩ := h
    have e0 := memAt_of_load l0
    refine ⟨by rw [e0]; exact l0, ?_⟩
    show σ (.n 130) = _
    rw [show σ (.n 130) = _ from m, e0]
    simp
  · have h := fun a (h : a ∈ blkA e) => hb a h
    simp only [blkA, show e ≠ 0 by omega, ite_false, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq] at h
    obtain ⟨l0, m, a⟩ := h
    have e0 := memAt_of_load l0
    refine ⟨by rw [e0]; exact l0, ?_⟩
    rw [accV, ite_neg' (show ¬ e = 0 by omega), show σ (.n (130 + 3 * e)) = _ from a,
      show σ (.n (129 + 3 * e)) = _ from m, e0]

/-- **The running sum**: after symbol `e`, the sum of the first `e + 1` products. -/
theorem acc_sum (hat : ∀ a ∈ tmplA, a.Holds rd σ) : ∀ e < 128,
    σ (.n (accV e)) = ((List.range (e + 1)).map fun j =>
      memAt rd (σ (.n 0)) j * σ (.n (j + 1))).sum
  | 0, _ => by
    rw [(blk_sound (by omega) hat).2]
    simp
  | e + 1, he => by
    rw [(blk_sound he hat).2, ite_neg' (by omega), show e + 1 - 1 = e from rfl,
      acc_sum hat e (by omega), List.range_succ (n := e + 1), List.map_append, List.sum_append]
    simp

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

/-- A cell's bytes are its symbols', sixteen a symbol. -/
theorem cellsBytes_eq_eBytes (cs : List E) : cellsBytes cs = cs.flatMap E.toBytes := rfl

/-! ## The check -/

/-- The digest's chain: the `128` symbols, `2048` bytes, from the zero state. -/
def cellSpec (atoms : List Atom) : ChainSpec :=
  ⟨(List.range 128).map fun e => some (.n (e + 1)), 2048, true, none, keccakBlocks atoms⟩

/-- **`da_verify_cell`'s body, checked**: the hint, the template's atoms, then the chain, the
copies and `ret`. -/
def cellOk (fn : Fn) : Bool :=
  decide (fn.params = [.n 0]) &&
  match splitBody fn.body with
  | some (A, vs) =>
    decide (vs = [.n 844, .n 845, .n 846]) && decide (384 ≤ A.length) &&
    atomsEqb ((A.drop 1).take 383) tmplA &&
    (cellSpec (A.drop 384)).check (A.drop 384) &&
    retOk (A.drop 384) (cellSpec (A.drop 384)) (.n 844) (.n 845) &&
    (A.drop 384).any (isCopyAt (.n 846) (.n 511))
  | none => false

end
end LeanVM.Guest.B1.Da
