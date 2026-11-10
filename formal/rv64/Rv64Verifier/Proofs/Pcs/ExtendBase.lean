import Rv64Verifier.Proofs.Pcs.Contracts
import Rv64Verifier.Blocks.F37

/-!
# `Vec<StackClaim>::extend_desugared`: the claims as memory holds them

```rust
stack_claims.extend(claims.iter().filter_map(|claim| claim.on_stack(&layout)));
```

compiled at `0x80009b94` (`Blocks/F37.lean`), `S` the entry's `sp` and `F = S - 240` the frame:
the prologue saves `ra`, `s0`..`s11`, keeps the `Vec` in `s1`, the iterator in `s0`, its end in
`s3`, the layout in `s4` and the claim in `s9`. A claim whose placement is `Some` is pushed:
`selector_point(F + 80, index >> variables, stack_log - variables)`, `concat(F + 56, [point,
selector])` (the slices at `F + 104`), the value to `F + 32`, `grow_amortized` when the `Vec` is
full, then the 88-byte `StackClaim` at its end.

This file: `ClaimRegions`, the regions a `StackClaim` read reads, and `claim_move`, which reads
it off its words and buffers.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs

/-- The regions the `StackClaim` at `e` reads, each meeting `P`: its 88 bytes and its weight's
buffers. -/
def ClaimRegions (P : Word → Nat → Prop) (u : MachineState) (e : Word) : Prop :=
  P e 88 ∧
    if u.getMem e = eqTag then P (vecPtr u (e + 8)) (24 * (vecLen u (e + 8)).toNat)
    else if u.getMem e = ringTag then
      P (vecPtr u (e + 8)) (24 * (vecLen u (e + 8)).toNat) ∧
        P (vecPtr u (e + 32)) (24 * (vecLen u (e + 32)).toNat)
    else P (vecPtr u e) (24 * (vecLen u e).toNat) ∧
      P (vecPtr u (e + 24)) (24 * (vecLen u (e + 24)).toNat)

theorem add_lit (x a b c : Word) (h : a + b = c) : x + a + b = x + c := by
  rw [BitVec.add_assoc, h]

/-- The `StackClaim` at `e'` in `v`, its eleven words `u`'s at `e` and its buffers kept, is `u`'s
at `e`. -/
theorem claim_move {u v : MachineState} {e e' : Word} {P Q : Word → Nat → Prop}
    (hw : ∀ k < 11, v.getMem (e' + BitVec.ofNat 64 (8 * k)) = u.getMem (e + BitVec.ofNat 64 (8 * k)))
    (hok : ClaimRegions P u e) (hbuf : ∀ a m, P a (24 * m) → eListAt v a m = eListAt u a m)
    (hPQ : ∀ a n, P a n → Q a n) (hQ : Q e' 88) :
    stackClaimAt v e' = stackClaimAt u e ∧ ClaimRegions Q v e' := by
  have w0 : v.getMem e' = u.getMem e := by
    have := hw 0 (by decide); simpa only [Nat.mul_zero, add_ofNat_zero] using this
  have w1 : v.getMem (e' + 8) = u.getMem (e + 8) := hw 1 (by decide)
  have w2 : v.getMem (e' + 16) = u.getMem (e + 16) := hw 2 (by decide)
  have w3 : v.getMem (e' + 24) = u.getMem (e + 24) := hw 3 (by decide)
  have w4 : v.getMem (e' + 32) = u.getMem (e + 32) := hw 4 (by decide)
  have w5 : v.getMem (e' + 40) = u.getMem (e + 40) := hw 5 (by decide)
  have w6 : v.getMem (e' + 48) = u.getMem (e + 48) := hw 6 (by decide)
  have w7 : v.getMem (e' + 56) = u.getMem (e + 56) := hw 7 (by decide)
  have w8 : v.getMem (e' + 64) = u.getMem (e + 64) := hw 8 (by decide)
  have w9 : v.getMem (e' + 72) = u.getMem (e + 72) := hw 9 (by decide)
  have w10 : v.getMem (e' + 80) = u.getMem (e + 80) := hw 10 (by decide)
  have n1 (x : Word) : x + 8 + 8 = x + 16 := add_lit _ _ _ _ rfl
  have n2 (x : Word) : x + 8 + 16 = x + 24 := add_lit _ _ _ _ rfl
  have n3 (x : Word) : x + 8 + 24 = x + 32 := add_lit _ _ _ _ rfl
  have n4 (x : Word) : x + 32 + 8 = x + 40 := add_lit _ _ _ _ rfl
  have n5 (x : Word) : x + 32 + 16 = x + 48 := add_lit _ _ _ _ rfl
  have n6 (x : Word) : x + 24 + 8 = x + 32 := add_lit _ _ _ _ rfl
  have n7 (x : Word) : x + 24 + 16 = x + 40 := add_lit _ _ _ _ rfl
  have n8 (x : Word) : x + 64 + 8 = x + 72 := add_lit _ _ _ _ rfl
  have n9 (x : Word) : x + 64 + 16 = x + 80 := add_lit _ _ _ _ rfl
  have he : eAt v (e' + 64) = eAt u (e + 64) := by
    simp only [eAt, n8, n9, w8, w9, w10]
  simp only [ClaimRegions, vecPtr, vecLen, n1, n2, n4, n5, n6, n7] at hok ⊢
  simp only [stackClaimAt, stackWeightAt, ringWeightAt, vecEs, vecPtr, vecLen, n1, n2, n3, n4,
    n5, n6, n7, he, w0, w1, w2, w3, w4, w5, w6, w7]
  refine ⟨?_, hQ, ?_⟩
  · by_cases h1 : u.getMem e = eqTag
    · simp only [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hok ⊢
      rw [hbuf _ _ hok.2]
    · by_cases h2 : u.getMem e = ringTag
      · simp only [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)] at hok ⊢
        rw [hbuf _ _ hok.2.1, hbuf _ _ hok.2.2]
      · simp only [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)] at hok ⊢
        rw [hbuf _ _ hok.2.1, hbuf _ _ hok.2.2]
  · by_cases h1 : u.getMem e = eqTag
    · simp only [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hok ⊢
      exact hPQ _ _ hok.2
    · by_cases h2 : u.getMem e = ringTag
      · simp only [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)] at hok ⊢
        exact ⟨hPQ _ _ hok.2.1, hPQ _ _ hok.2.2⟩
      · simp only [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)] at hok ⊢
        exact ⟨hPQ _ _ hok.2.1, hPQ _ _ hok.2.2⟩

theorem claimsAt_succ (s : MachineState) (p : Word) (n : Nat) :
    claimsAt s p (n + 1) = claimsAt s p n ++ [stackClaimAt s (p + BitVec.ofNat 64 (88 * n))] := by
  simp only [claimsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem claimsAt_congr {u v : MachineState} {p q : Word} {n : Nat}
    (h : ∀ i < n, stackClaimAt v (q + BitVec.ofNat 64 (88 * i)) =
      stackClaimAt u (p + BitVec.ofNat 64 (88 * i))) : claimsAt v q n = claimsAt u p n := by
  unfold claimsAt
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem columnClaimsAt_succ (s : MachineState) (p : Word) (n : Nat) :
    columnClaimsAt s p (n + 1) =
      columnClaimsAt s p n ++ [columnClaimAt s (p + BitVec.ofNat 64 (56 * n))] := by
  simp only [columnClaimsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

end Rv64Verifier.Proofs.Pcs.Extend
