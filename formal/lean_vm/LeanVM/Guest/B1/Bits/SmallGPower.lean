/-
  LeanVM.Guest.B1.Bits.SmallGPower

  B1 for `assert_small_g_power`: a g-power with an exponent below `2^36`, by nine hinted nibbles.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning

/-!
# `assert_small_g_power`

`assert_small_g_power(x, g_squares)` hints nine digits `d_j` (`hint_decompose_digits_exponent`),
range checks each below `16` (`log(d) < 16`, against `g^15`), reads the share
`g_squares[g^(34 + 16 j) · d_j]` and multiplies the shares; the product must be `x`. On the
exponent table (`ExpTables`) the share of `d_j = g^n` is `g^(n·16^j)`, so `x = g^e` with
`e = Σ n_j 16^j < 2^36`, and conversely every such `x` passes with the digits of `e`
(`assert_small_g_power_holds`).

The expansion is `asgHead` (the hint and digit `0`), `asgBlk j` per digit `j + 1` (values
`17 + 7j ..`, its share multiplied into the running product `asgAcc j`), the check.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Range checks against a power of `g` -/

/-- A range check against `g^(K-1)` (the word `2^(K-1)`), on a memory of `2^κ ≤ 2^32` words:
`x = g^e`, `e < K`, for some complement and touched words. -/
theorem rangeCheck_gen_iff {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemoryImage κ) (x : E) {K : ℕ}
    (hK1 : 1 ≤ K) (hK : K ≤ 2 ^ κ) (hK64 : K ≤ 64) :
    (∃ y t1 t2 : E, LoadHolds Lm.read x 0 t1 ∧ word (2 ^ (K - 1)) 0 = x * y ∧
      LoadHolds Lm.read y 0 t2) ↔ ∃ e < K, x = gen ^ e := by
  rw [word_two_pow (by omega), gen_pow_eq_ofK]
  simp only [gen_pow_eq_ofK]
  exact rangeCheck_iff hκ Lm x hK1 hK

/-! ## The template -/

/-- The hint and digit `0`: its range check and share. -/
def asgHead : List Stmt :=
  [.atom (.hint (.digitsExp (.n 0) 36 9 4 0 none
      (.stack [.n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10]))),
    .atom (.const (.n 11) (word 32768 0)),
    .atom (.rangeCheck (.n 2) (.n 12) (.n 13) (.n 14) (.n 11)),
    .atom (.mul (.n 15) (.n 1) (.n 2)), .atom (.load (.n 16) (.n 15) 34)]

/-- The running product after digit `j`. -/
def asgAcc : ℕ → ℕ
  | 0 => 16
  | j + 1 => 23 + 7 * j

/-- The pointer into the shares of digit `j`. -/
def asgPtr : ℕ → ℕ
  | 0 => 15
  | j + 1 => 21 + 7 * j

/-- Digit `j + 1`: its range check, its share, the product. -/
def asgBlk (j : ℕ) : List Stmt :=
  [.atom (.const (.n (17 + 7 * j)) (word 32768 0)),
    .atom (.rangeCheck (.n (3 + j)) (.n (18 + 7 * j)) (.n (19 + 7 * j)) (.n (20 + 7 * j))
      (.n (17 + 7 * j))),
    .atom (.mul (.n (21 + 7 * j)) (.n 1) (.n (3 + j))),
    .atom (.load (.n (22 + 7 * j)) (.n (21 + 7 * j)) (50 + 16 * j)),
    .atom (.mul (.n (23 + 7 * j)) (.n (asgAcc j)) (.n (22 + 7 * j)))]

/-- The expansion of `assert_small_g_power`. -/
def asgBody : List Stmt :=
  asgHead ++ ((List.range 8).map asgBlk).flatten ++ [.atom (.assertEq (.n 72) (.n 0)), .ret []]

theorem core3_body : Fn.body Data.core3 = asgBody := stmtsEqb_sound (by decide +kernel)

theorem find_assert_small_g_power : coreProgram.find? "assert_small_g_power" = some Data.core3 :=
  Program.find?_of_indexOf? (j := 3) (by decide +kernel) rfl

/-- Digit `j + 1`'s conditions. -/
def AsgOk (rd : Reader) (σ : Val) (j : ℕ) : Prop :=
  σ (.n (17 + 7 * j)) = word 32768 0 ∧
    (LoadHolds rd (σ (.n (3 + j))) 0 (σ (.n (19 + 7 * j))) ∧
      σ (.n (17 + 7 * j)) = σ (.n (3 + j)) * σ (.n (18 + 7 * j)) ∧
      LoadHolds rd (σ (.n (18 + 7 * j))) 0 (σ (.n (20 + 7 * j)))) ∧
    σ (.n (21 + 7 * j)) = σ (.n 1) * σ (.n (3 + j)) ∧
    LoadHolds rd (σ (.n (21 + 7 * j))) (50 + 16 * j) (σ (.n (22 + 7 * j))) ∧
    σ (.n (23 + 7 * j)) = σ (.n (asgAcc j)) * σ (.n (22 + 7 * j))

theorem holds_asgBlk {C : CallRel} {rd : Reader} {σ : Val} (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (asgBlk j) True kret ↔ AsgOk rd σ j := by
  simp only [asgBlk, AsgOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The body under any call relation, valuation and continuation, unfolded to its conditions. -/
theorem asg_holds_iff (C : CallRel) (rd : Reader) (σ : Val) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ asgBody False kret ↔
      σ (.n 11) = word 32768 0 ∧
      (LoadHolds rd (σ (.n 2)) 0 (σ (.n 13)) ∧ σ (.n 11) = σ (.n 2) * σ (.n 12) ∧
        LoadHolds rd (σ (.n 12)) 0 (σ (.n 14))) ∧
      σ (.n 15) = σ (.n 1) * σ (.n 2) ∧ LoadHolds rd (σ (.n 15)) 34 (σ (.n 16)) ∧
      (∀ j < 8, AsgOk rd σ j) ∧ σ (.n 72) + σ (.n 0) = 0 ∧ kret [] := by
  rw [asgBody, asgHead]
  simp only [holdsList_append, holdsList_range_flatten 8 asgBlk (fun _ => rfl), holds_asgBlk,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_nil, true_and]

/-- The body, unfolded to its conditions. -/
theorem asg_unfold (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "assert_small_g_power" args rets ↔ ∃ σ : Val,
      [σ (.n 0), σ (.n 1)] = args ∧ σ (.n 11) = word 32768 0 ∧
      (LoadHolds rd (σ (.n 2)) 0 (σ (.n 13)) ∧ σ (.n 11) = σ (.n 2) * σ (.n 12) ∧
        LoadHolds rd (σ (.n 12)) 0 (σ (.n 14))) ∧
      σ (.n 15) = σ (.n 1) * σ (.n 2) ∧ LoadHolds rd (σ (.n 15)) 34 (σ (.n 16)) ∧
      (∀ j < 8, AsgOk rd σ j) ∧ σ (.n 72) + σ (.n 0) = 0 ∧ [] = rets := by
  rw [rel_iff_sem find_assert_small_g_power, core3_body,
    show Fn.params Data.core3 = [.n 0, .n 1] from rfl]
  simp only [asg_holds_iff, List.map_cons, List.map_nil]

/-! ## Soundness -/

/-- The share of digit `j` read through `q·g^n` at `34 + 16 j`: `g^(n·16^j)`. -/
theorem asg_share {rd : Reader} {q s : E} (ht : ExpTables rd q) {j n : ℕ} (hj : j < 9)
    (hn : n < 16) (h : LoadHolds rd (q * gen ^ n) (34 + 16 * j) s) : s = gen ^ (n * 16 ^ j) := by
  rw [loadHolds_mul_gen_pow] at h
  exact loadHolds_unique h (by
    have := ht.2.1 j hj n hn
    rwa [show sizeBits + 16 * j + n = n + (34 + 16 * j) by simp only [sizeBits]; omega] at this)

theorem asg_sound {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemoryImage κ) {q : E}
    (ht : ExpTables Lm.read q) {σ : Val} (h1 : σ (.n 1) = q)
    (h11 : σ (.n 11) = word 32768 0)
    (r0 : LoadHolds Lm.read (σ (.n 2)) 0 (σ (.n 13)) ∧ σ (.n 11) = σ (.n 2) * σ (.n 12) ∧
      LoadHolds Lm.read (σ (.n 12)) 0 (σ (.n 14)))
    (h15 : σ (.n 15) = σ (.n 1) * σ (.n 2)) (l16 : LoadHolds Lm.read (σ (.n 15)) 34 (σ (.n 16)))
    (hb : ∀ j < 8, AsgOk Lm.read σ j) :
    ∀ j < 9, ∃ e < 16 ^ (j + 1), σ (.n (asgAcc j)) = gen ^ e := by
  have hK : (16 : ℕ) ≤ 2 ^ κ := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6)
  have digit : ∀ {d t1 y t2 c : E}, c = word 32768 0 → LoadHolds Lm.read d 0 t1 →
      c = d * y → LoadHolds Lm.read y 0 t2 → ∃ n < 16, d = gen ^ n := by
    intro d t1 y t2 c hc a b c'
    exact (rangeCheck_gen_iff hκ Lm d (K := 16) (by decide) hK (by decide)).1
      ⟨y, t1, t2, a, by rw [← b, hc]; norm_num, c'⟩
  intro j hj
  induction j with
  | zero =>
    obtain ⟨n, hn, hd⟩ := digit h11 r0.1 r0.2.1 r0.2.2
    rw [h15, h1, hd] at l16
    refine ⟨n, by omega, ?_⟩
    rw [asgAcc, asg_share ht (j := 0) (by decide) hn l16, pow_zero, mul_one]
  | succ j ih =>
    obtain ⟨e, he, hA⟩ := ih (by omega)
    obtain ⟨c, ⟨a, b, c'⟩, m, l, p⟩ := hb j (by omega)
    obtain ⟨n, hn, hd⟩ := digit c a b c'
    rw [m, h1, hd] at l
    have hs := asg_share ht (j := j + 1) (by omega) hn (by
      rwa [show 50 + 16 * j = 34 + 16 * (j + 1) by omega] at l)
    refine ⟨e + n * 16 ^ (j + 1), ?_, ?_⟩
    · have : n * 16 ^ (j + 1) ≤ 15 * 16 ^ (j + 1) := Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ 16 (j + 1)]
      omega
    · rw [show asgAcc (j + 1) = 23 + 7 * j from rfl, p, hA, hs, ← pow_add]

/-! ## Completeness -/

/-- The honest values: the arguments, the nine digits `g^(n_j)`, each block's constant, range
check words, pointer, share and product (`n_j = e / 16^j % 16`). -/
def asgVals (x q : E) (e : ℕ) (y t1 t2 : ℕ → E) (k : ℕ) : E :=
  let n := fun j ↦ e / 16 ^ j % 16
  if k = 0 then x else if k = 1 then q else if k < 11 then gen ^ n (k - 2)
  else if k < 17 then
    [word 32768 0, y 0, t1 0, t2 0, q * gen ^ n 0, gen ^ n 0].getD (k - 11) 0
  else
    let j := (k - 17) / 7 + 1
    [word 32768 0, y j, t1 j, t2 j, q * gen ^ n j, gen ^ (n j * 16 ^ j),
      gen ^ (e % 16 ^ (j + 1))].getD ((k - 17) % 7) 0

theorem asgVals_x (x q : E) (e : ℕ) (y t1 t2 : ℕ → E) : asgVals x q e y t1 t2 0 = x := rfl

theorem asgVals_q (x q : E) (e : ℕ) (y t1 t2 : ℕ → E) : asgVals x q e y t1 t2 1 = q := rfl

theorem asgVals_d (x q : E) (e : ℕ) (y t1 t2 : ℕ → E) (j : ℕ) (hj : j < 9) :
    asgVals x q e y t1 t2 (j + 2) = gen ^ (e / 16 ^ j % 16) := by
  simp only [asgVals]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel]

theorem asgVals_head (x q : E) (e : ℕ) (y t1 t2 : ℕ → E) (i : ℕ) (hi : i < 6) :
    asgVals x q e y t1 t2 (11 + i) =
      [word 32768 0, y 0, t1 0, t2 0, q * gen ^ (e / 16 ^ 0 % 16), gen ^ (e / 16 ^ 0 % 16)].getD
        i 0 := by
  simp only [asgVals]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    Nat.add_sub_cancel_left]

theorem asgVals_blk (x q : E) (e : ℕ) (y t1 t2 : ℕ → E) (j i : ℕ) (hi : i < 7) :
    asgVals x q e y t1 t2 (17 + 7 * j + i) =
      [word 32768 0, y (j + 1), t1 (j + 1), t2 (j + 1), q * gen ^ (e / 16 ^ (j + 1) % 16),
        gen ^ (e / 16 ^ (j + 1) % 16 * 16 ^ (j + 1)), gen ^ (e % 16 ^ (j + 2))].getD i 0 := by
  have h1 : (17 + 7 * j + i - 17) / 7 = j := by omega
  have h2 : (17 + 7 * j + i - 17) % 7 = i := by omega
  simp only [asgVals, h1, h2]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega)]

/-- `e mod 16^(j+1)` adds digit `j` to `e mod 16^j`. -/
theorem mod_sixteen_succ (e j : ℕ) : e % 16 ^ (j + 1) = e % 16 ^ j + e / 16 ^ j % 16 * 16 ^ j := by
  rw [Nat.mod_pow_succ, Nat.mul_comm]

/-- **The honest valuation** of `assert_small_g_power` at `g^e`, `e < 16^9`, on any reader where
each digit's range check reads its words (`hrc`) and the table at `q` holds the shares (`hshare`). -/
theorem asg_holds_of {C : CallRel} {rd : Reader} {q : E} {e : ℕ} (he : e < 16 ^ 9)
    (hrc : ∀ j, ∃ y t1 t2 : E, LoadHolds rd (gen ^ (e / 16 ^ j % 16)) 0 t1 ∧
      word (2 ^ (16 - 1)) 0 = gen ^ (e / 16 ^ j % 16) * y ∧ LoadHolds rd y 0 t2)
    (hshare : ∀ j < 9, LoadHolds rd (q * gen ^ (e / 16 ^ j % 16)) (34 + 16 * j)
      (gen ^ (e / 16 ^ j % 16 * 16 ^ j))) :
    ∃ σ : Val, σ (.n 0) = gen ^ e ∧ σ (.n 1) = q ∧
      (∀ j < 9, σ (.n (asgPtr j)) = q * gen ^ (e / 16 ^ j % 16)) ∧
      Stmt.HoldsList C rd σ asgBody False (fun rs ↦ rs = []) := by
  choose y t1 t2 hrc using hrc
  let σ : Val := fun v ↦ asgVals (gen ^ e) q e y t1 t2 v.idx
  have ev : ∀ k, σ (.n k) = asgVals (gen ^ e) q e y t1 t2 k := fun _ ↦ rfl
  have eb : ∀ j i, i < 7 → σ (.n (17 + 7 * j + i)) = _ := fun j i hi ↦
    (ev _).trans (asgVals_blk (gen ^ e) q e y t1 t2 j i hi)
  have w15 : word (2 ^ (16 - 1)) 0 = word 32768 0 := rfl
  have ed : ∀ j < 9, σ (.n (j + 2)) = gen ^ (e / 16 ^ j % 16) := fun j hj ↦
    (ev _).trans (asgVals_d _ q e y t1 t2 j hj)
  have eh : ∀ i < 6, σ (.n (11 + i)) = _ := fun i hi ↦
    (ev _).trans (asgVals_head (gen ^ e) q e y t1 t2 i hi)
  have e1 : σ (.n 1) = q := rfl
  have e0 : σ (.n 0) = gen ^ e := rfl
  have hacc : ∀ j < 8, σ (.n (asgAcc j)) = gen ^ (e % 16 ^ (j + 1)) := fun j hj ↦ by
    cases j with
    | zero =>
      rw [show asgAcc 0 = 11 + 5 from rfl, eh 5 (by omega)]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, Nat.div_one, zero_add,
        pow_one]
    | succ j =>
      rw [show asgAcc (j + 1) = 17 + 7 * j + 6 by simp only [asgAcc]; omega, eb j 6 (by omega)]
      rfl
  have d0 := ed 0 (by omega)
  simp only [pow_zero, Nat.div_one, zero_add] at d0
  have ep : ∀ j < 9, σ (.n (asgPtr j)) = q * gen ^ (e / 16 ^ j % 16) := fun j hj ↦ by
    cases j with
    | zero =>
      rw [show asgPtr 0 = 11 + 4 from rfl, eh 4 (by omega)]
      rfl
    | succ j =>
      rw [show asgPtr (j + 1) = 17 + 7 * j + 4 by simp only [asgPtr]; omega, eb j 4 (by omega)]
      rfl
  refine ⟨σ, rfl, rfl, ep, (asg_holds_iff C rd σ _).2
    ⟨eh 0 (by omega), ⟨?_, ?_, ?_⟩, ?_, ?_, fun j hj ↦ ?_, ?_, rfl⟩⟩
  · rw [d0, show 13 = 11 + 2 from rfl, eh 2 (by omega)]
    simpa using (hrc 0).1
  · rw [d0, show 11 = 11 + 0 from rfl, eh 0 (by omega), show 12 = 11 + 1 from rfl,
      eh 1 (by omega)]
    simpa [w15] using (hrc 0).2.1
  · rw [show 12 = 11 + 1 from rfl, eh 1 (by omega), show 14 = 11 + 3 from rfl, eh 3 (by omega)]
    simpa using (hrc 0).2.2
  · rw [show 15 = 11 + 4 from rfl, eh 4 (by omega), e1, d0]
    simp
  · rw [show 15 = 11 + 4 from rfl, eh 4 (by omega), show 16 = 11 + 5 from rfl, eh 5 (by omega)]
    simpa using hshare 0 (by decide)
  · have dj := ed (j + 1) (by omega)
    rw [show j + 1 + 2 = 3 + j by omega] at dj
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [show 17 + 7 * j = 17 + 7 * j + 0 from rfl, eb j 0 (by omega)]; rfl
    · rw [show 19 + 7 * j = 17 + 7 * j + 2 by omega, eb j 2 (by omega), dj]
      exact (hrc (j + 1)).1
    · rw [show 17 + 7 * j = 17 + 7 * j + 0 from rfl, eb j 0 (by omega),
        show 18 + 7 * j = 17 + 7 * j + 1 by omega, eb j 1 (by omega), dj]
      have := (hrc (j + 1)).2.1
      rw [w15] at this
      exact this
    · rw [show 18 + 7 * j = 17 + 7 * j + 1 by omega, eb j 1 (by omega),
        show 20 + 7 * j = 17 + 7 * j + 3 by omega, eb j 3 (by omega)]
      exact (hrc (j + 1)).2.2
    · rw [show 21 + 7 * j = 17 + 7 * j + 4 by omega, eb j 4 (by omega), e1, dj]
      rfl
    · rw [show 21 + 7 * j = 17 + 7 * j + 4 by omega, eb j 4 (by omega),
        show 22 + 7 * j = 17 + 7 * j + 5 by omega, eb j 5 (by omega)]
      have := hshare (j + 1) (by omega)
      rwa [show 34 + 16 * (j + 1) = 50 + 16 * j by omega] at this
    · rw [show 23 + 7 * j = 17 + 7 * j + 6 by omega, eb j 6 (by omega),
        show 22 + 7 * j = 17 + 7 * j + 5 by omega, eb j 5 (by omega), hacc j hj]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [mod_sixteen_succ e (j + 1), pow_add]
  · rw [show 72 = 17 + 7 * 7 + 6 from rfl, eb 7 6 (by omega), e0]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [Nat.mod_eq_of_lt (by simpa using he)]
    exact e_add_eq_zero_iff.mpr rfl

/-- **`assert_small_g_power`'s core IR is its meaning.** -/
theorem assert_small_g_power_holds : assert_small_g_power_Spec := by
  intro κ hκ hκ6 Lm x q ht rets
  rw [asg_unfold]
  have hK : (16 : ℕ) ≤ 2 ^ κ := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6)
  constructor
  · rintro ⟨σ, hp, h11, r0, h15, l16, hb, ha, hret⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨e, he, hA⟩ := asg_sound hκ hκ6 Lm ht rfl h11 r0 h15 l16 hb 8 (by omega)
    refine ⟨⟨e, by simpa using he, ?_⟩, hret.symm⟩
    rw [← hA]
    exact (e_add_eq_zero_iff.mp ha).symm
  · rintro ⟨⟨e, he, rfl⟩, rfl⟩
    -- the range checks' words for each digit
    have hrc : ∀ j, ∃ y t1 t2 : E, LoadHolds Lm.read (gen ^ (e / 16 ^ j % 16)) 0 t1 ∧
        word (2 ^ (16 - 1)) 0 = gen ^ (e / 16 ^ j % 16) * y ∧ LoadHolds Lm.read y 0 t2 :=
      fun j ↦ (rangeCheck_gen_iff hκ Lm _ (K := 16) (by decide) hK (by decide)).2
        ⟨_, Nat.mod_lt _ (by decide), rfl⟩
    have hshare : ∀ j < 9, LoadHolds Lm.read (q * gen ^ (e / 16 ^ j % 16)) (34 + 16 * j)
        (gen ^ (e / 16 ^ j % 16 * 16 ^ j)) := fun j hj ↦ by
      rw [loadHolds_mul_gen_pow]
      have := ht.2.1 j hj (e / 16 ^ j % 16) (Nat.mod_lt _ (by decide))
      rwa [show sizeBits + 16 * j + e / 16 ^ j % 16 = e / 16 ^ j % 16 + (34 + 16 * j) by
        simp only [sizeBits]; omega] at this
    obtain ⟨σ, e0, e1, -, hh⟩ :=
      asg_holds_of (C := coreProgram.Rel Lm.read) (by simpa using he) hrc hshare
    obtain ⟨a, b, c, d, f, g, -⟩ := (asg_holds_iff _ _ _ _).1 hh
    exact ⟨σ, by rw [e0, e1], a, b, c, d, f, g, rfl⟩

end
end LeanVM.Guest.B1
