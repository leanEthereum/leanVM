module

public import LeanVM.Guest.Complete.Agg.W0

/-!
# `aggregate_claims`' second run, its atoms

The window `aW2` (statements `43 ..< 476`) as `w2A`, its parts:

* `w2Ptr`: the last absorbing row's pointer `absorb·g^(13m)`; `w2Row`: its thirteen words read;
* `w2Perm`: its permutation (`fs_perm_pending`); `w2Non`: the nonce read from `bc_msgs`, its
  permutation;
* `aggGrindA`: `grind_check` inlined on the nonce permutation's cell `1`;
* `w2Sq`: `λ²`, `col`'s `HeapBuf(6)` and the six column challenges squeezed and stored;
* `w2Tree`: `eq_col_tree`'s `HeapBuf(126)`, its level `0` and its levels `1 ..< 6` (`trL`);
* `w2Tail`: `fresh_val`'s `HeapBuf(m)`, the guard of `aggregate_claims_loop1`, `eq_col`'s pointer.

The kernel checks `atomsOf` of the statements is `w2A` (`w2_eq`), its atoms are the body's
(`w2_mem`), the fresh loads are no stores (`w2_fresh`), and the parts' shapes.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- The last absorbing row's pointer `absorb·g^(13m)`. -/
def w2Ptr : List Atom :=
  [.mul (.n 34) (.n 0) (.n 0), .mul (.n 35) (.n 34) (.n 0), .mul (.n 36) (.n 35) (.n 35),
    .mul (.n 37) (.n 36) (.n 36), .mul (.n 38) (.n 37) (.n 0), .mul (.n 39) (.n 30) (.n 38)]

/-- The last absorbing row's words. -/
def w2Row : List Atom := (List.range 13).map fun i => .load (.n (40 + i)) (.n 39) i

/-- The row's permutation's inputs: its rate cells, then its capacity cells. -/
def w2Kin : List V :=
  [.n 45, .n 46, .n 47, .n 48, .n 53, .n 54, .n 55, .n 56, .n 40, .n 41, .n 42, .n 43, .n 44]

/-- The row's permutation. -/
def w2Perm : List Atom :=
  [.copy (.n 53) (.n 49), .copy (.n 54) (.n 50), .copy (.n 55) (.n 51), .copy (.n 56) (.n 52),
    .keccak w2Kin ((List.range 13).map fun i => .n (57 + i)) false false]

/-- The nonce permutation's inputs: the nonce's two cells, six zeros, the row permutation's capacity. -/
def w2Nin : List V :=
  [.n 71, .n 72, .n 74, .n 74, .n 74, .n 75, .n 76, .n 77, .n 65, .n 66, .n 67, .n 68, .n 69]

/-- The nonce read and permuted. -/
def w2Non : List Atom :=
  [.load (.n 70) (.n 6) 0, .copy (.n 71) (.n 70), .const (.n 72) (word 0 4), .const (.n 73) (word 1 0),
    .const (.n 74) (word 0 0), .const (.n 75) (word 0 0), .const (.n 76) (word 0 0), .const (.n 77) (word 0 0),
    .keccak w2Nin ((List.range 13).map fun i => .n (78 + i)) false false]

/-- The squeezes' zero rate cells. -/
def w2Zs : List V := [.n 74, .n 74, .n 74, .n 74, .n 74, .n 75, .n 76, .n 77]

/-- The first squeeze's capacity: the nonce permutation's. -/
def w2Cap0 : List V := [.n 86, .n 87, .n 88, .n 89, .n 90]

/-- `λ²`, `col`, the six squeezes, each block's cell `0` stored at `col[k]`. -/
def w2Sq : List Atom :=
  [.mul (.n 155) (.n 78) (.n 78), .hint (.alloc (.n 156) 6)] ++
    (List.range 6).flatMap fun k =>
      [.keccak (sqIns w2Zs w2Cap0 157 k) (sqOuts 157 k) false false, .load (.n (157 + 13 * k)) (.n 156) k]

/-- `eqtree`'s level `t ≥ 1` starts at `trB t`. -/
def trB (t : ℕ) : ℕ := 239 + 3 * (t - 1) + 3 * (2 ^ t - 2)

/-- Level `t`'s entry `i`: the previous level's word, its two products stored. -/
def trE (t i : ℕ) : List Atom :=
  [.load (.n (trB t + 3 + 3 * i)) (.n 235) (2 ^ t - 2 + i),
    .mul (.n (trB t + 4 + 3 * i)) (.n (trB t + 3 + 3 * i)) (.n (trB t + 2)),
    .load (.n (trB t + 4 + 3 * i)) (.n 235) (2 ^ (t + 1) - 2 + i),
    .mul (.n (trB t + 5 + 3 * i)) (.n (trB t + 3 + 3 * i)) (.n (trB t)),
    .load (.n (trB t + 5 + 3 * i)) (.n 235) (2 ^ (t + 1) - 2 + 2 ^ t + i)]

/-- Level `t ≥ 1`: `col[t]`, `1 + col[t]`, then its entries. -/
def trL (t : ℕ) : List Atom :=
  [.load (.n (trB t)) (.n 156) t, .const (.n (trB t + 1)) (word 1 0), .add (.n (trB t + 2)) (.n (trB t + 1)) (.n (trB t))] ++
    (List.range (2 ^ t)).flatMap (trE t)

/-- `eq_col_tree` and its levels. -/
def w2Tree : List Atom :=
  [.hint (.alloc (.n 235) 126), .load (.n 236) (.n 156) 0, .const (.n 237) (word 1 0),
    .add (.n 238) (.n 237) (.n 236), .load (.n 238) (.n 235) 0, .load (.n 236) (.n 235) 1] ++
    (List.range 5).flatMap fun t => trL (t + 1)

/-- `fresh_val`, the guard, `eq_col`'s pointer. -/
def w2Tail : List Atom :=
  [.hint (.allocDyn (.n 440) (.n 0)), .const (.n 441) (word 1 0), .add (.n 442) (.n 441) (.n 0),
    .const (.n 443) (word 1 0), .const (.n 444) (word 4611686018427387904 0), .mul (.n 445) (.n 235) (.n 444)]

/-- `aW2`'s atoms. -/
def w2A : List Atom := w2Ptr ++ w2Row ++ w2Perm ++ w2Non ++ aggGrindA ++ w2Sq ++ w2Tree ++ w2Tail

set_option maxRecDepth 400000 in
theorem w2_eq : atomsOf ((aggP.drop 43).take 433) = w2A := by decide +kernel

set_option maxRecDepth 400000 in
theorem w2_mem : ∀ x ∈ w2A, x ∈ atomsOf aggP := by decide +kernel

theorem w2_grind : aggGrindA.map Stmt.atom = gcInlineT 3 91 (.n 79) (.n 5) := aggGrindA_eq

/-- A load through the pointer `.n p` at an offset below `n`. -/
def ldIn (p n : ℕ) : Atom → Bool
  | .load _ q off => decide (q = .n p) && decide (off < n)
  | _ => false

theorem ldIn_spec {p n : ℕ} {x : Atom} (h : ldIn p n x = true) : ∃ d off, x = .load d (.n p) off ∧ off < n := by
  cases x with
  | load d q off =>
    simp only [ldIn, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨d, off, by rw [h.1], h.2⟩
  | _ => simp [ldIn] at h

set_option maxRecDepth 400000 in
/-- **The parts' shapes**: no backward product or assertion outside the grind; loads only through
the row's, `bc_msgs`', `col`'s and `eq_col_tree`'s pointers. -/
theorem w2_shape :
    (w2Ptr ++ w2Row ++ w2Perm ++ w2Non ++ w2Sq ++ w2Tree ++ w2Tail).all pureB = true ∧
    w2A.all noHeapB = true ∧
    allocDsts (w2A.map Ev.atom) = [.n 156, .n 235, .n 440] ∧
    w2A.filterMap allocK = [.inl 6, .inl 126, .inr (.n 0)] ∧
    (w2Ptr ++ w2Perm ++ w2Tail).all isNL = true ∧
    w2Non.all (fun x => isNL x || decide (x = .load (.n 70) (.n 6) 0)) = true ∧
    w2Sq.all (fun x => isNL x || ldIn 156 6 x) = true ∧
    w2Tree.all (fun x => isNL x || ldIn 156 6 x || ldIn 235 126 x) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
/-- **The fresh loads**: the row's words, the nonce, `col`'s words and the previous levels' words
the tree reads. -/
theorem w2_fresh : (∀ i < 13, Atom.load (.n (40 + i)) (.n 39) i ∉ storesOf 6 aggP) ∧
    Atom.load (.n 70) (.n 6) 0 ∉ storesOf 6 aggP ∧ Atom.load (.n 236) (.n 156) 0 ∉ storesOf 6 aggP ∧
    (∀ t < 5, Atom.load (.n (trB (t + 1))) (.n 156) (t + 1) ∉ storesOf 6 aggP) ∧
    (∀ t < 5, ∀ i < 2 ^ (t + 1),
      Atom.load (.n (trB (t + 1) + 3 + 3 * i)) (.n 235) (2 ^ (t + 1) - 2 + i) ∉ storesOf 6 aggP) := by
  decide +kernel

end
end LeanVM.Guest.Complete.Agg
