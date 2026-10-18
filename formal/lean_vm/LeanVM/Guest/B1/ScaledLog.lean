/-
  LeanVM.Guest.B1.ScaledLog

  B1 for `scaled_log`: `2^shift · log x` as a bit pattern, at both of its shifts.
-/

module

public import LeanVM.Guest.B1.Log2

/-!
# `scaled_log` (TRIAGE #59)

`scaled_log(x, g_squares, shift)` (G:2706-2723) hints the 16 exponent bits of `x` into frame
cells, pins each by booleanity, weighs them over `COORD_BASIS` into the exponent's word, ties
them back by the g-power product over `g_squares`, and returns the word times
`COORD_BASIS[shift]`. Over the exponent tables its relation is exactly: `x = g^N` with
`N < 2^16`, and the return is `E(2^shift · N)` (`Value.scaled_log_spec`). The expansion is
`slBlk j` per bit; `slBody shift` is equal to both specializations (`__L6`, `__L11`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The running word after bit `j`. -/
def slV : ℕ → ℕ
  | 0 => 2
  | j + 1 => 26 + 10 * j

/-- The running product after bit `j`. -/
def slR : ℕ → ℕ
  | 0 => 23
  | j + 1 => 33 + 10 * j

/-- The table word of bit `j`. -/
def slS : ℕ → ℕ
  | 0 => 19
  | j + 1 => 28 + 10 * j

/-- Bit `j`. -/
def slBlk : ℕ → List Stmt
  | 0 => [.atom (.mul (.n 2) (.n 2) (.n 2)), .atom (.const (.n 18) (word 1 0 0)),
      .atom (.load (.n 19) (.n 1) 0), .atom (.const (.n 20) (word 1 0 0)),
      .atom (.add (.n 21) (.n 19) (.n 20)), .atom (.mul (.n 22) (.n 2) (.n 21)),
      .atom (.add (.n 23) (.n 18) (.n 22))]
  | j + 1 => [.atom (.mul (.n (3 + j)) (.n (3 + j)) (.n (3 + j))),
      .atom (.const (.n (24 + 10 * j)) (word (2 ^ (j + 1)) 0 0)),
      .atom (.mul (.n (25 + 10 * j)) (.n (3 + j)) (.n (24 + 10 * j))),
      .atom (.add (.n (26 + 10 * j)) (.n (slV j)) (.n (25 + 10 * j))),
      .atom (.const (.n (27 + 10 * j)) (word 1 0 0)),
      .atom (.load (.n (28 + 10 * j)) (.n 1) (j + 1)),
      .atom (.const (.n (29 + 10 * j)) (word 1 0 0)),
      .atom (.add (.n (30 + 10 * j)) (.n (28 + 10 * j)) (.n (29 + 10 * j))),
      .atom (.mul (.n (31 + 10 * j)) (.n (3 + j)) (.n (30 + 10 * j))),
      .atom (.add (.n (32 + 10 * j)) (.n (27 + 10 * j)) (.n (31 + 10 * j))),
      .atom (.mul (.n (33 + 10 * j)) (.n (slR j)) (.n (32 + 10 * j)))]

/-- The 16 frame cells of the bits. -/
def slRun : List V := (List.range 16).map fun i => .n (2 + i)

/-- The expansion of `scaled_log` at `shift`. -/
def slBody (shift : ℕ) : List Stmt :=
  [.atom (.hint (.bitsExp (.n 0) 16 (.stack slRun)))] ++ ((List.range 16).map slBlk).flatten ++
  [.atom (.assertEq (.n 173) (.n 0)), .atom (.const (.n 174) (word (2 ^ shift) 0 0)),
    .atom (.mul (.n 175) (.n 166) (.n 174)), .ret [.n 175]]

theorem core495_body : Fn.body Data.core495 = slBody 6 := stmtsEqb_sound (by decide +kernel)

theorem core461_body : Fn.body Data.core461 = slBody 11 := stmtsEqb_sound (by decide +kernel)

/-- What bit `j` asks of a valuation. -/
def SlOk (rd : Reader) (σ : Val) : ℕ → Prop
  | 0 => σ (.n 2) = σ (.n 2) * σ (.n 2) ∧ σ (.n 18) = 1 ∧ LoadHolds rd (σ (.n 1)) 0 (σ (.n 19)) ∧
      σ (.n 20) = 1 ∧ σ (.n 21) = σ (.n 19) + σ (.n 20) ∧ σ (.n 22) = σ (.n 2) * σ (.n 21) ∧
      σ (.n 23) = σ (.n 18) + σ (.n 22)
  | j + 1 => σ (.n (3 + j)) = σ (.n (3 + j)) * σ (.n (3 + j)) ∧
      σ (.n (24 + 10 * j)) = word (2 ^ (j + 1)) 0 0 ∧
      σ (.n (25 + 10 * j)) = σ (.n (3 + j)) * σ (.n (24 + 10 * j)) ∧
      σ (.n (26 + 10 * j)) = σ (.n (slV j)) + σ (.n (25 + 10 * j)) ∧ σ (.n (27 + 10 * j)) = 1 ∧
      LoadHolds rd (σ (.n 1)) (j + 1) (σ (.n (28 + 10 * j))) ∧ σ (.n (29 + 10 * j)) = 1 ∧
      σ (.n (30 + 10 * j)) = σ (.n (28 + 10 * j)) + σ (.n (29 + 10 * j)) ∧
      σ (.n (31 + 10 * j)) = σ (.n (3 + j)) * σ (.n (30 + 10 * j)) ∧
      σ (.n (32 + 10 * j)) = σ (.n (27 + 10 * j)) + σ (.n (31 + 10 * j)) ∧
      σ (.n (33 + 10 * j)) = σ (.n (slR j)) * σ (.n (32 + 10 * j))

theorem holds_slBlk {C : CallRel} {rd : Reader} {σ : Val} (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (slBlk j) True kret ↔ SlOk rd σ j := by
  cases j <;> simp only [slBlk, SlOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one]

theorem sl_chain {rd : Reader} {σ : Val} : ∀ n, n < 63 → (∀ j < n + 1, SlOk rd σ j) →
    σ (.n (slV n)) = ∑ j ∈ Finset.range (n + 1), σ (.n (2 + j)) * coordBasis j ∧
      σ (.n (slR n)) = gpwProd (fun j => σ (.n (2 + j))) (fun j => σ (.n (slS j))) (n + 1)
  | 0, _, h => by
    obtain ⟨-, e18, -, e20, e21, e22, e23⟩ := h 0 (by omega)
    refine ⟨?_, ?_⟩
    · rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
        eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
      rfl
    · rw [gpwProd, show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_one]
      show σ (.n 23) = 1 + σ (.n 2) * (σ (.n 19) + 1)
      rw [e23, e18, e22, e21, e20]
  | n + 1, hn, h => by
    obtain ⟨ih1, ih2⟩ := sl_chain n (by omega) (fun j hj => h j (by omega))
    obtain ⟨-, e24, e25, e26, e27, -, e29, e30, e31, e32, e33⟩ := h (n + 1) (by omega)
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ (n := n + 1), ← ih1]
      show σ (.n (26 + 10 * n)) = _
      rw [e26, e25, e24, word_coordBasis (by omega), show 2 + (n + 1) = 3 + n by omega]
    · rw [gpwProd, Finset.prod_range_succ (n := n + 1), ← gpwProd, ← ih2]
      show σ (.n (33 + 10 * n)) = _
      rw [e33, e32, e31, e30, e29, e27, show 2 + (n + 1) = 3 + n by omega]
      rfl

/-- **`scaled_log(x, g_squares, shift)`** (G:2706-2723; TRIAGE #59), over the exponent tables:
`x = g^N` with `N < 2^16`, and the function returns `E(2^shift · N)`. -/
def MeaningScaledLog (shift : ℕ) : List E → List E → Prop
  | [x, _], rets => ∃ N < 2 ^ 16, x = gen ^ N ∧ rets = [eOfNat (2 ^ shift * N)]
  | _, _ => False

/-- The honest values from `.n 18`, through bit `j`. -/
def slVals (b s : ℕ → E) : ℕ → ℕ → E
  | 0, i => [1, s 0, 1, s 0 + 1, b 0 * (s 0 + 1), 1 + b 0 * (s 0 + 1)].getD i 0
  | j + 1, i => if i < 6 + 10 * j then slVals b s j i else
      [word (2 ^ (j + 1)) 0 0, b (j + 1) * word (2 ^ (j + 1)) 0 0,
        ∑ t ∈ Finset.range (j + 2), b t * coordBasis t, 1, s (j + 1), 1, s (j + 1) + 1,
        b (j + 1) * (s (j + 1) + 1), 1 + b (j + 1) * (s (j + 1) + 1), gpwProd b s (j + 2)].getD
        (i - (6 + 10 * j)) 0

theorem slVals_lt (b s : ℕ → E) : ∀ m j i, j ≤ m → i < 6 + 10 * j → slVals b s m i = slVals b s j i
  | 0, j, i, h, _ => by rw [show j = 0 by omega]
  | m + 1, j, i, h, hi => by
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · rw [slVals, ite_pos' (by omega)]; exact slVals_lt b s m j i (by omega) hi
    · rw [show j = m + 1 by omega]

/-- **`scaled_log` at `shift ≤ 48`**, for a compiled function whose body is `slBody shift`, over
the exponent tables. -/
theorem scaled_log_iff {name : String} {f : Fn} (shift : ℕ) (hs : shift ≤ 48)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = slBody shift) (rd : Reader) {x lp sq : E} (ht : ExpTables rd lp sq)
    (rets : List E) :
    coreProgram.Rel rd name [x, sq] rets ↔ MeaningScaledLog shift [x, sq] rets := by
  rw [rel_iff_sem hfind, hbody, hparams, slBody]
  simp only [holdsList_append, holdsList_range_flatten 16 slBlk (fun j => by cases j <;> rfl),
    holds_slBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  have hsq : ∀ j < 16, LoadHolds rd sq j (gen ^ 2 ^ j) := fun j hj => (ht j (by show j < 34; omega)).2
  constructor
  · rintro ⟨σ, hp, hblk, a173, h174, h175, hret⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, -⟩ := hp
    obtain ⟨hsum, hprod⟩ := sl_chain 15 (by omega) hblk
    have hbool : ∀ j < 16, σ (.n (2 + j)) * σ (.n (2 + j)) = σ (.n (2 + j)) := fun j hj => by
      cases j with
      | zero => exact (hblk 0 hj).1.symm
      | succ j =>
        rw [show 2 + (j + 1) = 3 + j by omega]; exact (hblk (j + 1) hj).1.symm
    have hs16 : ∀ j < 16, σ (.n (slS j)) = gen ^ 2 ^ j := fun j hj => by
      cases j with
      | zero => exact loadHolds_unique (hblk 0 hj).2.2.1 (hsq 0 hj)
      | succ j => exact loadHolds_unique (hblk (j + 1) hj).2.2.2.2.2.1 (hsq (j + 1) hj)
    set c := fun j => decide (σ (.n (2 + j)) = 1)
    set N := bitsVal c 16
    have hN : N < 2 ^ 16 := bitsVal_lt c 16
    have hb : ∀ j < 16, σ (.n (2 + j)) = bitE (N.testBit j) := fun j hj => by
      rw [bitE_of_mul_self (hbool j hj), testBit_bitsVal]; simp [hj, c]
    have hx : σ (.n 0) = gen ^ N := by
      rw [← e_add_eq_zero_iff.mp a173, show (173 : ℕ) = slR 15 from rfl, hprod, gpwProd,
        Finset.prod_congr rfl fun j hj => by rw [hs16 j (Finset.mem_range.mp hj)]]
      exact prod_gen_pow_of_bool hbool
    have hv : σ (.n 166) = eOfNat N := by
      rw [show (166 : ℕ) = slV 15 from rfl, hsum, ← Nat.mod_eq_of_lt hN,
        ← sum_bits_mod N 16 (by omega)]
      exact Finset.sum_congr rfl fun j hj => by rw [hb j (Finset.mem_range.mp hj)]
    refine ⟨N, hN, hx, ?_⟩
    rw [← hret, h175, hv, h174, word_two_pow (by omega), gen_pow_eq_eOfNat (by omega), mul_comm,
      eOfNat_two_pow_mul (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hN (Nat.two_pow_pos _))
        (by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)))]
  · rintro ⟨N, hN, rfl, rfl⟩
    set b := fun j => bitE (N.testBit j)
    set sv := fun j => (gen ^ 2 ^ j : E)
    set τ := setl (setv (setv (Val.ofArgs [gen ^ N, sq]) 2 16 b) 18 156 (slVals b sv 15)) 174
      [word (2 ^ shift) 0 0, (∑ t ∈ Finset.range 16, b t * coordBasis t) * word (2 ^ shift) 0 0]
    have tb : ∀ j < 16, τ (.n (2 + j)) = b j := fun j hj => by
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by omega),
        Nat.add_sub_cancel_left]
    have tv : ∀ i < 156, τ (.n (18 + i)) = slVals b sv 15 i := fun i hi => by
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
    have t0 : ∀ i < 6, τ (.n (18 + i)) = [1, sv 0, 1, sv 0 + 1, b 0 * (sv 0 + 1),
        1 + b 0 * (sv 0 + 1)].getD i 0 := fun i hi => by
      rw [tv i (by omega), slVals_lt b sv 15 0 i (by omega) (by omega), slVals]
    have ts : ∀ j c, j + 1 ≤ 15 → c < 10 → τ (.n (24 + 10 * j + c)) = [word (2 ^ (j + 1)) 0 0,
        b (j + 1) * word (2 ^ (j + 1)) 0 0, ∑ t ∈ Finset.range (j + 2), b t * coordBasis t, 1,
        sv (j + 1), 1, sv (j + 1) + 1, b (j + 1) * (sv (j + 1) + 1),
        1 + b (j + 1) * (sv (j + 1) + 1), gpwProd b sv (j + 2)].getD c 0 := fun j c hj hc => by
      rw [show 24 + 10 * j + c = 18 + (6 + 10 * j + c) by omega, tv _ (by omega),
        slVals_lt b sv 15 (j + 1) _ hj (by omega), slVals, ite_neg' (by omega),
        show 6 + 10 * j + c - (6 + 10 * j) = c by omega]
    have hacc : ∀ j < 16, τ (.n (slV j)) = ∑ t ∈ Finset.range (j + 1), b t * coordBasis t ∧
        τ (.n (slR j)) = gpwProd b sv (j + 1) := fun j hj => by
      cases j with
      | zero =>
        refine ⟨?_, ?_⟩
        · have := tb 0 (by omega)
          rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
            eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
          exact this
        · have := t0 5 (by omega)
          rw [gpwProd, show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_one]
          exact this
      | succ j =>
        rw [show slV (j + 1) = 24 + 10 * j + 2 by simp only [slV]; omega,
          show slR (j + 1) = 24 + 10 * j + 9 by simp only [slR]; omega]
        exact ⟨ts j 2 (by omega) (by omega), ts j 9 (by omega) (by omega)⟩
    have e1 : τ (.n 1) = sq := by simp only [τ]; b1_look
    have e0 : τ (.n 0) = gen ^ N := by simp only [τ]; b1_look
    have hall := (hacc 15 (by omega))
    have x174 : τ (.n 174) = word (2 ^ shift) 0 0 := by simp only [τ]; b1_look
    have x175 : τ (.n 175) = (∑ t ∈ Finset.range 16, b t * coordBasis t) * word (2 ^ shift) 0 0 := by
      simp only [τ]; b1_look
    refine ⟨τ, by rw [e0, e1], fun j hj => ?_, ?_, x174, ?_, ?_⟩
    · cases j with
      | zero =>
        have f18 := t0 0 (by omega); have f19 := t0 1 (by omega); have f20 := t0 2 (by omega)
        have f21 := t0 3 (by omega); have f22 := t0 4 (by omega); have f23 := t0 5 (by omega)
        have f2 := tb 0 (by omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd]
          at f18 f19 f20 f21 f22 f23 f2
        refine ⟨by rw [f2]; exact (bitE_mul_self _).symm, f18, ?_, f20, by rw [f21, f19, f20],
          by rw [f22, f2, f21], by rw [f23, f18, f22]⟩
        rw [e1, f19]; exact hsq 0 hj
      | succ j =>
        have e := fun c (hc : c < 10) => ts j c (by omega) hc
        have f0 := e 0 (by omega); have f1 := e 1 (by omega); have f2 := e 2 (by omega)
        have f3 := e 3 (by omega); have f4 := e 4 (by omega); have f5 := e 5 (by omega)
        have f6 := e 6 (by omega); have f7 := e 7 (by omega); have f8 := e 8 (by omega)
        have f9 := e 9 (by omega)
        have fb := tb (j + 1) hj
        simp only [List.getD_cons_zero, List.getD_cons_succ,
          show ∀ k, 24 + 10 * j + k = k + 24 + 10 * j from fun k => by ring,
          show 2 + (j + 1) = 3 + j by omega] at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fb
        obtain ⟨ha, hg⟩ := hacc j (by omega)
        refine ⟨by rw [fb]; exact (bitE_mul_self _).symm, f0, by rw [f1, fb, f0], ?_, f3, ?_, f5,
          by rw [f6, f4, f5], by rw [f7, fb, f6], by rw [f8, f3, f7], ?_⟩
        · rw [f2, ha, f1, Finset.sum_range_succ (n := j + 1), word_coordBasis (by omega)]
        · rw [e1, f4]; exact hsq (j + 1) hj
        · rw [f9, hg, f8, gpwProd, gpwProd, Finset.prod_range_succ (n := j + 1)]
    · rw [show (173 : ℕ) = slR 15 from rfl, hall.2, e0, ← gpwProd_pow (n := 16) (s := sv)
        (fun _ _ => rfl) hN]
      exact e_add_self _
    · rw [x175, x174, show (166 : ℕ) = slV 15 from rfl, hall.1]
    · rw [x175, sum_bits_mod N 16 (by omega), Nat.mod_eq_of_lt hN, word_two_pow (by omega),
        gen_pow_eq_eOfNat (by omega), mul_comm,
        eOfNat_two_pow_mul (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hN (Nat.two_pow_pos _))
          (by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)))]

set_option maxRecDepth 100000 in
theorem scaled_log_L6_iff (rd : Reader) {x lp sq : E} (ht : ExpTables rd lp sq) (rets : List E) :
    coreProgram.Rel rd "scaled_log__L6" [x, sq] rets ↔ MeaningScaledLog 6 [x, sq] rets :=
  scaled_log_iff 6 (by decide) (Program.find?_of_indexOf? (j := 495) (by decide +kernel) rfl) rfl
    core495_body rd ht rets

set_option maxRecDepth 100000 in
theorem scaled_log_L11_iff (rd : Reader) {x lp sq : E} (ht : ExpTables rd lp sq) (rets : List E) :
    coreProgram.Rel rd "scaled_log__L11" [x, sq] rets ↔ MeaningScaledLog 11 [x, sq] rets :=
  scaled_log_iff 11 (by decide) (Program.find?_of_indexOf? (j := 461) (by decide +kernel) rfl) rfl
    core461_body rd ht rets

end
end LeanVM.Guest.B1
