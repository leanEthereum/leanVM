/-
  LeanVM.Guest.B1.Digest.Range

  Range checks on a memory image, the compile-time powers of `g` the guest bounds them by, and B1
  for `list_split` (TRIAGE #87).
-/

module

public import LeanVM.Guest.B1.Digest.Lists
import LeanVM.Guest.B1.Common.Vc

/-!
# Range checks; `list_split`

On a memory image of `2^κ` words, `16 ≤ κ ≤ 32` (`MemOk`), a word read through a pointer at
offset `0` is a power of `g` below `2^32` (`load_gpow`), so a range check
`rangeCheck x y t1 t2 k` makes `x = g^e`, `k = g^(e + e')` (`rc_sound`): against a compile-time
`g^c` it bounds `e ≤ c` (`rc_const`), against a runtime bound `b · g⁻¹` it gives `BelowLog b e`
(`rc_below`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Range checks on a memory image -/

/-- A word read at offset `0` through a pointer of the memory is a power of `g` below `2^32`. -/
theorem load_gpow {rd : Reader} (hm : MemOk rd) {x t : E} (h : LoadHolds rd x 0 t) :
    ∃ e < 2 ^ 32, x = gen ^ e := by
  obtain ⟨κ, -, hκ, L, rfl⟩ := hm
  obtain ⟨hx, hr⟩ := h
  rw [Parameters.addressOfIndex, pow_zero, mul_one] at hr
  obtain ⟨i, hi, -⟩ := (read_some_iff (by omega) L _ _).mp hr
  refine ⟨i, lt_of_lt_of_le i.2 (Nat.pow_le_pow_right (by decide) hκ), ?_⟩
  rw [eq_ofK_limb hx, hi, gen_pow_eq_ofK]

theorem gen_pow_inj' {a b : ℕ} (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) (h : gen ^ a = gen ^ b) :
    a = b :=
  gen_pow_inj (by omega) (by omega) h

/-- A range check: its two reads make `x`, `y` powers of `g` below `2^32`, `k` their product. -/
theorem rc_sound {rd : Reader} (hm : MemOk rd) {x y t1 t2 k : E}
    (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ x = gen ^ e ∧ k = gen ^ (e + e') := by
  obtain ⟨e, he, rfl⟩ := load_gpow hm h.1
  obtain ⟨e', he', rfl⟩ := load_gpow hm h.2.2
  exact ⟨e, e', he, he', rfl, by rw [h.2.1, pow_add]⟩

/-- **A range check against `g^c`**: `x = g^e` with `e ≤ c`. -/
theorem rc_const {rd : Reader} (hm : MemOk rd) {x y t1 t2 k : E} {c : ℕ} (hc : c < 2 ^ 33)
    (hk : k = gen ^ c) (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e ≤ c, x = gen ^ e := by
  obtain ⟨e, e', he, he', hx, hk'⟩ := rc_sound hm h
  have := gen_pow_inj' (by omega) (by omega) (hk.symm.trans hk')
  exact ⟨e, by omega, hx⟩

set_option maxRecDepth 100000 in
theorem ginvW_mul_gen : ginvW * gen = 1 := by
  unfold ginvW
  rw [word_eOfNat, gen, eOfNat, eOfNat, ← ofK_mul, ← ofK_one]
  congr 1

/-- **A range check against a runtime bound** `b` (`assert log x < log b`, its `k` the product
`b · g⁻¹`): `x = g^e` with `BelowLog b e`. -/
theorem rc_below {rd : Reader} (hm : MemOk rd) {x y t1 t2 k b : E} (hk : k = b * ginvW)
    (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e, x = gen ^ e ∧ BelowLog b e := by
  obtain ⟨e, e', he, he', hx, hk'⟩ := rc_sound hm h
  refine ⟨e, hx, he, e', he', ?_⟩
  rw [show b = b * (ginvW * gen) by rw [ginvW_mul_gen, mul_one], ← mul_assoc, ← hk, hk', pow_succ]

/-- `BelowLog` against a known power: the exponent is below. -/
theorem belowLog_lt {b : E} {e M : ℕ} (hM : M < 2 ^ 33) (hb : b = gen ^ M) (h : BelowLog b e) :
    e < M := by
  obtain ⟨he, e', he', hb'⟩ := h
  have := gen_pow_inj' (by omega) (by omega) (hb.symm.trans hb')
  omega

/-! ## Compile-time powers of `g` -/

theorem word_g16 : word 65536 0 = gen ^ 16 := word_two_pow (a := 16) (by decide)

/-! ## `list_split` (TRIAGE #87) -/

theorem word_g7 : word 128 0 = gen ^ 7 := word_two_pow (a := 7) (by decide)

/-- **`list_split`'s condition**: the hinted rest `c` and groups `b` range-checked against `g^16`
and `g^7`, the hinted big frames `a` a word of the memory, `a^136 · b^17 · c = n_g`, and
`[a, b, c]` returned. -/
def LsCond (rd : Reader) (ng : E) (rets : List E) : Prop :=
  ∃ c y t1, LoadHolds rd c 0 t1 ∧ gen ^ 16 = c * y ∧ ∃ t2, LoadHolds rd y 0 t2 ∧
    ∃ b y' t3, LoadHolds rd b 0 t3 ∧ gen ^ 7 = b * y' ∧ ∃ t4, LoadHolds rd y' 0 t4 ∧
      ∃ a t5, LoadHolds rd a 0 t5 ∧ a ^ 136 * b ^ 17 * c + ng = 0 ∧ [a, b, c] = rets

/-- **`list_split` is its condition** (`vc`). -/
theorem list_split_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "list_split" args rets ↔ ∃ ng, [ng] = args ∧ LsCond rd ng rets := by
  rw [rel_iff_fnSem find_list_split]
  vc [word_g16, word_g7, ← pow_two]
  simp only [← pow_mul, ← pow_succ, Nat.reduceMul, Nat.reduceAdd]
  exact Iff.rfl

/-- **`list_split` splits a count into big frames, whole claim groups and a rest.** -/
theorem list_split_sound : list_split_sound_Spec := by
  intro rd hm args rets h
  obtain ⟨ng, rfl, c, y, t1, h1, e1, t2, h2, b, y', t3, h3, e2, t4, h4, a, t5, h5, hid, rfl⟩ :=
    (list_split_iff rd args rets).mp h
  obtain ⟨c', hc, rfl⟩ := rc_const hm (c := 16) (by norm_num) rfl ⟨h1, e1, h2⟩
  obtain ⟨b', hb, rfl⟩ := rc_const hm (c := 7) (by norm_num) rfl ⟨h3, e2, h4⟩
  obtain ⟨a', ha, rfl⟩ := load_gpow hm h5
  refine ⟨a', ha, b', by simp only [bigGroups]; omega, c', by simp only [claimGroup]; omega, ?_, rfl⟩
  rw [← e_add_eq_zero_iff.mp hid, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  simp only [claimGroup, claimBig]
  ring

end
end LeanVM.Guest.B1.Digest
