/-
  LeanVM.Guest.B1.Exact.GPower

  `g_power_of_word` is exact on every valid tree: its six bits are Boolean and rebuild its word.
-/

module

public import LeanVM.Guest.Exact.Ok
public import LeanVM.Guest.B1.Bits.GPower

/-!
# `g_power_of_word`, exact

`g_power_of_word` hints the six bits of its word, pins each by booleanity and asserts that they rebuild the word
(`GPowerP.lean`). So on every path that holds, the bits are the word's (`bits_of_reconstruct`): its one computed hint is
exact (`gpw_pathExact`), and `g_power_of_word` is in `ExactOk`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-- `g_power_of_word`'s computed hint: the six bits of its word. -/
def gpwHint : Atom := .hint (.bits (.n 0) 0 6 (.stack [.n 1, .n 2, .n 3, .n 4, .n 5, .n 6]))

theorem gpw_sites : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ [gpwHint])) pinsInverse
    (fn% «g_power_of_word»).body = true := by
  decide +kernel

/-- **Every path of `g_power_of_word` that holds is exact.** -/
theorem gpw_pathExact : PathExactFn fn% «g_power_of_word» := by
  refine pathExact_of_sites gpw_sites fun rd σ es vs hw hes a ha _ => ?_
  rw [List.mem_singleton.mp ha]
  have h : Stmt.HoldsList (fun _ _ _ => True) rd σ (fn% «g_power_of_word»).body False (fun _ => True) :=
    holdsList_of_walk _ (by rw [hw]; exact ⟨fun e he => ⟨hes e he, fun _ _ _ _ => trivial⟩, trivial⟩)
  simp only [show (fn% «g_power_of_word»).body = Fn.«g_power_of_word».core.body from rfl,
    Fn.«g_power_of_word».core.body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨b0, e7, e8, e9, e10, b1, e11, e12, e13, e14, e15, e16, e17, e18, b2, e19, e20,
      e21, e22, e23, e24, e25, e26, b3, e27, e28, e29, e30, e31, e32, e33, e34, b4, e35, e36, e37,
      e38, e39, e40, e41, e42, b5, e43, e44, e45, e46, e47, e48, e49, e50, ha, -⟩ := h
  have hb : ∀ j < 6, σ (.n (1 + j)) * σ (.n (1 + j)) = σ (.n (1 + j)) := by
    intro j hj
    interval_cases j
    exacts [b0.symm, b1.symm, b2.symm, b3.symm, b4.symm, b5.symm]
  have hword : ∑ j ∈ Finset.range 6, σ (.n (1 + j)) * coordBasis (0 + j) = σ (.n 0) := by
    rw [← (e_add_eq_zero_iff.mp ha)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [e45, e44, e43, e37, e36, e35, e29, e28, e27, e21, e20, e19, e13, e12, e11]
    simp [word_eOfNat, eOfNat_one, coordBasis, eOfNat128_of_lt]
  obtain ⟨N, hN, hv, hbits⟩ := bits_of_reconstruct hb hword
  have hN64 : N < 2 ^ 64 := lt_of_lt_of_le hN (by norm_num)
  rw [Nat.pow_zero, Nat.one_mul, eOfNat128_of_lt hN64] at hv
  refine bits_exact_of_eq hN64 hv ?_
  simp only [List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append, List.cons_append]
  rw [← hbits 0 (by omega), ← hbits 1 (by omega), ← hbits 2 (by omega), ← hbits 3 (by omega), ← hbits 4 (by omega),
    ← hbits 5 (by omega)]

/-- **`g_power_of_word` is exact on every valid tree.** -/
theorem gpw_exactOk : ExactOk "g_power_of_word" :=
  .node find_g_power_of_word gpw_pathExact fun g hg => absurd hg (by
    rw [show Stmt.blockCallees (fn% «g_power_of_word»).body = [] by decide +kernel]
    exact List.not_mem_nil)

end
end LeanVM.Guest.B1
