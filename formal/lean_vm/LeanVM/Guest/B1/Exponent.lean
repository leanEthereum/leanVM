/-
  LeanVM.Guest.B1.Exponent

  B1 for the exponent gadgets: `g_power_of_word`, raising an integer word to its g-power.
-/

module

public import LeanVM.Guest.B1.Tables

/-!
# `g_power_of_word` (TRIAGE #14)

`g_power_of_word(value, g_squares, n)` (G:590-603) hints the `n` bits of `value` into a fresh
heap run, pins each by booleanity, reconstructs `value = Σ b_j·2^j`, and multiplies the factors
`1 + b_j·(g_squares[g^j] + 1)`. Its relation is exactly that: `value` an integer word below `2^n`,
its bits in the run, and the product over the table's words (`gpwProd`); over the exponent
tables (`ExpTables`, `exponent_tables`' postcondition) the product is `g^value`
(`g_power_of_word_L6_pow`). The expansion is `gpwBlk j` per bit, from value `4` then
`12 + 12·j`, with `gpwAcc`, `gpwG` the running word and product.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- Bit `j`'s value number. -/
def gpwB : ℕ → ℕ
  | 0 => 4
  | j + 1 => 12 + 12 * j

/-- The running word after bit `j`. -/
def gpwAcc : ℕ → ℕ
  | 0 => 4
  | j + 1 => 16 + 12 * j

/-- The running product after bit `j`. -/
def gpwG : ℕ → ℕ
  | 0 => 11
  | j + 1 => 23 + 12 * j

/-- Bit `j`: read, booleanity, add `b·2^j` to the word, multiply the product by
`1 + b·(g_squares[g^j] + 1)`; the first term of each is folded. -/
def gpwBlk : ℕ → List Stmt
  | 0 => [.atom (.load (.n 4) (.n 3) 0), .atom (.mul (.n 5) (.n 4) (.n 4)),
      .atom (.assertEq (.n 5) (.n 4)), .atom (.const (.n 6) (word 1 0 0)),
      .atom (.load (.n 7) (.n 1) 0), .atom (.const (.n 8) (word 1 0 0)),
      .atom (.add (.n 9) (.n 7) (.n 8)), .atom (.mul (.n 10) (.n 4) (.n 9)),
      .atom (.add (.n 11) (.n 6) (.n 10))]
  | j + 1 => [.atom (.load (.n (12 + 12 * j)) (.n 3) (j + 1)),
      .atom (.mul (.n (13 + 12 * j)) (.n (12 + 12 * j)) (.n (12 + 12 * j))),
      .atom (.assertEq (.n (13 + 12 * j)) (.n (12 + 12 * j))),
      .atom (.const (.n (14 + 12 * j)) (word (2 ^ (j + 1)) 0 0)),
      .atom (.mul (.n (15 + 12 * j)) (.n (12 + 12 * j)) (.n (14 + 12 * j))),
      .atom (.add (.n (16 + 12 * j)) (.n (gpwAcc j)) (.n (15 + 12 * j))),
      .atom (.const (.n (17 + 12 * j)) (word 1 0 0)),
      .atom (.load (.n (18 + 12 * j)) (.n 1) (j + 1)),
      .atom (.const (.n (19 + 12 * j)) (word 1 0 0)),
      .atom (.add (.n (20 + 12 * j)) (.n (18 + 12 * j)) (.n (19 + 12 * j))),
      .atom (.mul (.n (21 + 12 * j)) (.n (12 + 12 * j)) (.n (20 + 12 * j))),
      .atom (.add (.n (22 + 12 * j)) (.n (17 + 12 * j)) (.n (21 + 12 * j))),
      .atom (.mul (.n (23 + 12 * j)) (.n (gpwG j)) (.n (22 + 12 * j)))]

/-- The expansion of `g_power_of_word` at `n + 1` bits. -/
def gpwBody (n : ℕ) : List Stmt :=
  [.atom (.const (.n 2) (word (2 ^ (n + 1)) 0 0)), .atom (.hint (.allocDyn (.n 3) (.n 2))),
    .atom (.hint (.bits (.n 0) 0 (n + 1) (.heap (.n 3) 0 (n + 1))))] ++
  ((List.range (n + 1)).map gpwBlk).flatten ++
  [.atom (.assertEq (.n (gpwAcc n)) (.n 0)), .atom (.copy (.n (12 + 12 * n)) (.n (gpwG n))),
    .ret [.n (12 + 12 * n)]]

theorem core172_body : Fn.body Data.core172 = gpwBody 5 := stmtsEqb_sound (by decide +kernel)

/-- What bit `j` asks of a valuation. -/
def GpwOk (rd : Reader) (σ : Val) : ℕ → Prop
  | 0 => LoadHolds rd (σ (.n 3)) 0 (σ (.n 4)) ∧ σ (.n 5) = σ (.n 4) * σ (.n 4) ∧
      σ (.n 5) + σ (.n 4) = 0 ∧ σ (.n 6) = 1 ∧ LoadHolds rd (σ (.n 1)) 0 (σ (.n 7)) ∧
      σ (.n 8) = 1 ∧ σ (.n 9) = σ (.n 7) + σ (.n 8) ∧ σ (.n 10) = σ (.n 4) * σ (.n 9) ∧
      σ (.n 11) = σ (.n 6) + σ (.n 10)
  | j + 1 => LoadHolds rd (σ (.n 3)) (j + 1) (σ (.n (12 + 12 * j))) ∧
      σ (.n (13 + 12 * j)) = σ (.n (12 + 12 * j)) * σ (.n (12 + 12 * j)) ∧
      σ (.n (13 + 12 * j)) + σ (.n (12 + 12 * j)) = 0 ∧
      σ (.n (14 + 12 * j)) = word (2 ^ (j + 1)) 0 0 ∧
      σ (.n (15 + 12 * j)) = σ (.n (12 + 12 * j)) * σ (.n (14 + 12 * j)) ∧
      σ (.n (16 + 12 * j)) = σ (.n (gpwAcc j)) + σ (.n (15 + 12 * j)) ∧
      σ (.n (17 + 12 * j)) = 1 ∧ LoadHolds rd (σ (.n 1)) (j + 1) (σ (.n (18 + 12 * j))) ∧
      σ (.n (19 + 12 * j)) = 1 ∧ σ (.n (20 + 12 * j)) = σ (.n (18 + 12 * j)) + σ (.n (19 + 12 * j)) ∧
      σ (.n (21 + 12 * j)) = σ (.n (12 + 12 * j)) * σ (.n (20 + 12 * j)) ∧
      σ (.n (22 + 12 * j)) = σ (.n (17 + 12 * j)) + σ (.n (21 + 12 * j)) ∧
      σ (.n (23 + 12 * j)) = σ (.n (gpwG j)) * σ (.n (22 + 12 * j))

theorem holds_gpwBlk {C : CallRel} {rd : Reader} {σ : Val} (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gpwBlk j) True kret ↔ GpwOk rd σ j := by
  cases j <;> simp only [gpwBlk, GpwOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
    word_one]

/-! ## The running word and product -/

/-- The product of the factors over the table words `s`. -/
def gpwProd (b s : ℕ → E) (n : ℕ) : E := ∏ j ∈ Finset.range n, (1 + b j * (s j + 1))

/-- Bit `j`'s table word's value number. -/
def gpwS : ℕ → ℕ
  | 0 => 7
  | j + 1 => 18 + 12 * j

theorem gpw_chain {rd : Reader} {σ : Val} : ∀ n, n < 63 → (∀ j < n + 1, GpwOk rd σ j) →
    σ (.n (gpwAcc n)) = ∑ j ∈ Finset.range (n + 1), σ (.n (gpwB j)) * coordBasis j ∧
      σ (.n (gpwG n)) = gpwProd (fun j => σ (.n (gpwB j))) (fun j => σ (.n (gpwS j))) (n + 1)
  | 0, _, h => by
    obtain ⟨-, -, -, e6, -, e8, e9, e10, e11⟩ := h 0 (by omega)
    refine ⟨?_, ?_⟩
    · rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
        eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
      rfl
    · rw [gpwProd, show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_one]
      show σ (.n 11) = 1 + σ (.n 4) * (σ (.n 7) + 1)
      rw [e11, e6, e10, e9, e8]
  | n + 1, hn, h => by
    obtain ⟨ih1, ih2⟩ := gpw_chain n (by omega) (fun j hj => h j (by omega))
    obtain ⟨-, -, -, e14, e15, e16, e17, -, e19, e20, e21, e22, e23⟩ := h (n + 1) (by omega)
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ (n := n + 1), ← ih1]
      show σ (.n (16 + 12 * n)) = _
      rw [e16, e15, e14, word_coordBasis (by omega)]
      rfl
    · rw [gpwProd, Finset.prod_range_succ (n := n + 1), ← gpwProd, ← ih2]
      show σ (.n (23 + 12 * n)) = _
      rw [e23, e22, e21, e20, e19, e17]
      rfl

/-! ## The meaning -/

/-- **`g_power_of_word(value, g_squares, n)`** (G:590-603; TRIAGE #14): `value` is an integer
word `N < 2^n`, its bits are in a run `p`, and the function returns the product of
`1 + bit_j·(s_j + 1)` over the words `s` the table holds (`g^N` over the exponent tables:
`gpw_pow`). -/
def MeaningGPowerOfWord (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [value, sq], [r] =>
      IsInK value ∧ kToNat (value.limb 0) < 2 ^ n ∧
        (∃ p, ∀ j < n, LoadHolds rd p j (bitE ((kToNat (value.limb 0)).testBit j))) ∧
        ∃ s : List E, s.length = n ∧ ReadsAt rd sq s ∧
          r = gpwProd (fun j => bitE ((kToNat (value.limb 0)).testBit j)) (fun j => s.getD j 0) n
  | _, _ => False

/-- Over the exponent tables, the product is `g^N`. -/
theorem gpw_pow {rd : Reader} {lp sq : E} (ht : ExpTables rd lp sq) {n N : ℕ} (hn : n ≤ sizeBits)
    {s : List E} (hs : s.length = n) (hr : ReadsAt rd sq s) (hN : N < 2 ^ n) :
    gpwProd (fun j => bitE (N.testBit j)) (fun j => s.getD j 0) n = gen ^ N := by
  have hsj : ∀ j < n, s.getD j 0 = gen ^ 2 ^ j := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact loadHolds_unique (hr j (by omega)) (ht j (by omega)).2
  rw [gpwProd, Finset.prod_congr rfl fun j hj => by rw [hsj j (Finset.mem_range.mp hj),
    add_comm (gen ^ 2 ^ j) 1, add_comm 1 (gen ^ 2 ^ j)], prod_bitE_gen_pow, bitsVal_testBit hN]

/-- The honest values of `g_power_of_word`, from `.n 4`. -/
def gpwVals (b s : ℕ → E) : ℕ → ℕ → E
  | 0, i => [b 0, b 0 * b 0, 1, s 0, 1, s 0 + 1, b 0 * (s 0 + 1), 1 + b 0 * (s 0 + 1)].getD i 0
  | j + 1, i => if i < 8 + 12 * j then gpwVals b s j i else
      [b (j + 1), b (j + 1) * b (j + 1), word (2 ^ (j + 1)) 0 0,
        b (j + 1) * word (2 ^ (j + 1)) 0 0,
        ∑ t ∈ Finset.range (j + 2), b t * coordBasis t, 1, s (j + 1), 1, s (j + 1) + 1,
        b (j + 1) * (s (j + 1) + 1), 1 + b (j + 1) * (s (j + 1) + 1), gpwProd b s (j + 2)].getD
        (i - (8 + 12 * j)) 0

theorem gpwVals_lt (b s : ℕ → E) : ∀ m j i, j ≤ m → i < 8 + 12 * j → gpwVals b s m i = gpwVals b s j i
  | 0, j, i, h, _ => by rw [show j = 0 by omega]
  | m + 1, j, i, h, hi => by
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · rw [gpwVals, ite_pos' (by omega)]; exact gpwVals_lt b s m j i (by omega) hi
    · rw [show j = m + 1 by omega]

theorem gpwVals_zero (b s : ℕ → E) (m i : ℕ) (hi : i < 8) :
    gpwVals b s m i = [b 0, b 0 * b 0, 1, s 0, 1, s 0 + 1, b 0 * (s 0 + 1),
      1 + b 0 * (s 0 + 1)].getD i 0 := by
  rw [gpwVals_lt b s m 0 i (by omega) (by omega), gpwVals]

theorem gpwVals_succ (b s : ℕ → E) (m j c : ℕ) (hj : j + 1 ≤ m) (hc : c < 12) :
    gpwVals b s m (8 + 12 * j + c) = [b (j + 1), b (j + 1) * b (j + 1), word (2 ^ (j + 1)) 0 0,
        b (j + 1) * word (2 ^ (j + 1)) 0 0,
        ∑ t ∈ Finset.range (j + 2), b t * coordBasis t, 1, s (j + 1), 1, s (j + 1) + 1,
        b (j + 1) * (s (j + 1) + 1), 1 + b (j + 1) * (s (j + 1) + 1), gpwProd b s (j + 2)].getD c 0 := by
  rw [gpwVals_lt b s m (j + 1) _ hj (by omega), gpwVals, ite_neg' (by omega),
    show 8 + 12 * j + c - (8 + 12 * j) = c by omega]

/-- **`g_power_of_word` at `n + 1 ≤ 34` bits**, for a compiled function whose body is
`gpwBody n`. -/
theorem g_power_of_word_iff {name : String} {f : Fn} (n : ℕ) (hn : n < 34)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = gpwBody n) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningGPowerOfWord (n + 1) rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, gpwBody]
  simp only [holdsList_append, holdsList_range_flatten (n + 1) gpwBlk (fun j => by cases j <;> rfl),
    holds_gpwBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  constructor
  · rintro ⟨σ, hp, h2, hblk, a0, hc, hret⟩
    subst hp hret
    obtain ⟨hsum, hprod⟩ := gpw_chain n (by omega) hblk
    have hbool : ∀ j < n + 1, σ (.n (gpwB j)) * σ (.n (gpwB j)) = σ (.n (gpwB j)) := fun j hj => by
      cases j with
      | zero =>
        obtain ⟨-, e5, a5, -⟩ := hblk 0 hj
        show σ (.n 4) * σ (.n 4) = σ (.n 4)
        rw [← e5]; exact e_add_eq_zero_iff.mp a5
      | succ j =>
        obtain ⟨-, e13, a13, -⟩ := hblk (j + 1) hj
        show σ (.n (12 + 12 * j)) * σ (.n (12 + 12 * j)) = σ (.n (12 + 12 * j))
        rw [← e13]; exact e_add_eq_zero_iff.mp a13
    rw [e_add_eq_zero_iff.mp a0] at hsum
    obtain ⟨N, hN, hv, hb⟩ := bits_of_reconstruct (s := 0) hbool
      (by simpa only [Nat.zero_add] using hsum.symm)
    have hN64 : N < 2 ^ 64 := lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.pow_zero, Nat.one_mul, eOfNat192_of_lt hN64] at hv
    have hk : kToNat ((σ (.n 0)).limb 0) = N := by
      rw [hv, eOfNat_eq_ofLimbs, ofLimbs_limb0, kToNat_ofBits, Nat.mod_eq_of_lt hN64]
    simp only [MeaningGPowerOfWord]
    rw [hk]
    refine ⟨by rw [hv]; exact eOfNat_isInK N, hN, ⟨σ (.n 3), fun j hj => ?_⟩,
      (List.range (n + 1)).map (fun j => σ (.n (gpwS j))), by simp, fun j hj => ?_, ?_⟩
    · rw [← hb j hj]
      cases j with
      | zero => exact (hblk 0 hj).1
      | succ j => exact (hblk (j + 1) hj).1
    · simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range]
      cases j with
      | zero => exact (hblk 0 hj).2.2.2.2.1
      | succ j => exact (hblk (j + 1) hj).2.2.2.2.2.2.2.1
    · rw [hc, hprod, gpwProd, gpwProd]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [hb j hj', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj'),
        Option.getD_some]
      simp
  · intro hm
    obtain ⟨value, sq, r, rfl, rfl⟩ : ∃ value sq r, args = [value, sq] ∧ rets = [r] := by
      match args, rets, hm with
      | [a, b], [c], _ => exact ⟨a, b, c, rfl, rfl⟩
    obtain ⟨hvK, hN, ⟨p, hp⟩, s, hs, hrs, rfl⟩ := hm
    set N := kToNat (value.limb 0)
    set b := fun j => bitE (N.testBit j)
    set sv := fun j => s.getD j 0
    set τ := setl (setv (setl (Val.ofArgs [value, sq]) 2 [word (2 ^ (n + 1)) 0 0, p]) 4
      (12 * n + 8) (gpwVals b sv n)) (12 + 12 * n) [gpwProd b sv (n + 1)]
    have gv : ∀ i < 12 * n + 8, τ (.n (4 + i)) = gpwVals b sv n i := fun i hi => by
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
    have g0 : ∀ i < 8, τ (.n (4 + i)) = [b 0, b 0 * b 0, 1, sv 0, 1, sv 0 + 1, b 0 * (sv 0 + 1),
        1 + b 0 * (sv 0 + 1)].getD i 0 := fun i hi => by
      rw [gv i (by omega), gpwVals_zero _ _ _ _ hi]
    have gs : ∀ j c, j + 1 ≤ n → c < 12 → τ (.n (12 + 12 * j + c)) = [b (j + 1),
        b (j + 1) * b (j + 1), word (2 ^ (j + 1)) 0 0, b (j + 1) * word (2 ^ (j + 1)) 0 0,
        ∑ t ∈ Finset.range (j + 2), b t * coordBasis t, 1, sv (j + 1), 1, sv (j + 1) + 1,
        b (j + 1) * (sv (j + 1) + 1), 1 + b (j + 1) * (sv (j + 1) + 1), gpwProd b sv (j + 2)].getD
        c 0 := fun j c hj hc => by
      rw [show 12 + 12 * j + c = 4 + (8 + 12 * j + c) by omega, gv _ (by omega),
        gpwVals_succ _ _ _ _ _ hj hc]
    have hv : value = eOfNat N := by
      rw [eOfNat, ofBits_kToNat]; exact eq_ofK_limb hvK
    have hsv : ∀ j < n + 1, LoadHolds rd sq j (sv j) := fun j hj => by
      have := hrs j (by omega)
      simp only [sv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < s.length by omega),
        Option.getD_some]
      exact this
    have hacc : ∀ j < n + 1, τ (.n (gpwAcc j)) = ∑ t ∈ Finset.range (j + 1), b t * coordBasis t ∧
        τ (.n (gpwG j)) = gpwProd b sv (j + 1) := fun j hj => by
      cases j with
      | zero =>
        refine ⟨?_, ?_⟩
        · have := g0 0 (by omega)
          rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
            eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
          exact this
        · have := g0 7 (by omega)
          rw [gpwProd, show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_one]
          exact this
      | succ j =>
        rw [show gpwAcc (j + 1) = 12 + 12 * j + 4 by simp only [gpwAcc]; omega,
          show gpwG (j + 1) = 12 + 12 * j + 11 by simp only [gpwG]; omega]
        exact ⟨gs j 4 (by omega) (by omega), gs j 11 (by omega) (by omega)⟩
    refine ⟨τ, ?_, ?_, fun j hj => ?_, ?_, ?_, ?_⟩
    · simp only [τ]; b1_look
    · simp only [τ]; b1_look
    · cases j with
      | zero =>
        have e4 := g0 0 (by omega); have e5 := g0 1 (by omega); have e6 := g0 2 (by omega)
        have e7 := g0 3 (by omega); have e8 := g0 4 (by omega); have e9 := g0 5 (by omega)
        have e10 := g0 6 (by omega); have e11 := g0 7 (by omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd]
          at e4 e5 e6 e7 e8 e9 e10 e11
        have t3 : τ (.n 3) = p := by simp only [τ]; b1_look
        have t1 : τ (.n 1) = sq := by simp only [τ]; b1_look
        refine ⟨?_, by rw [e5, e4], by rw [e5, e4, bitE_mul_self]; exact e_add_self _, e6, ?_, e8,
          by rw [e9, e7, e8], by rw [e10, e4, e9], by rw [e11, e6, e10]⟩
        · rw [t3, e4]; exact hp 0 (by omega)
        · rw [t1, e7]; exact hsv 0 (by omega)
      | succ j =>
        have e := fun c (hc : c < 12) => gs j c (by omega) hc
        have f0 := e 0 (by omega); have f1 := e 1 (by omega); have f2 := e 2 (by omega)
        have f3 := e 3 (by omega); have f4 := e 4 (by omega); have f5 := e 5 (by omega)
        have f6 := e 6 (by omega); have f7 := e 7 (by omega); have f8 := e 8 (by omega)
        have f9 := e 9 (by omega); have f10 := e 10 (by omega); have f11 := e 11 (by omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ,
          show ∀ k, 12 + 12 * j + k = k + 12 + 12 * j from fun k => by ring]
          at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
        have t3 : τ (.n 3) = p := by simp only [τ]; b1_look
        have t1 : τ (.n 1) = sq := by simp only [τ]; b1_look
        obtain ⟨ha, hg⟩ := hacc j (by omega)
        refine ⟨?_, by rw [f1, f0], ?_, f2, by rw [f3, f0, f2], ?_, f5, ?_, f7, by rw [f8, f6, f7],
          by rw [f9, f0, f8], by rw [f10, f5, f9], ?_⟩
        · rw [t3, f0]; exact hp (j + 1) hj
        · rw [f1, f0]; simp only [b, bitE_mul_self]; exact e_add_self _
        · rw [f4, ha, f3, Finset.sum_range_succ (n := j + 1), word_coordBasis (by omega)]
        · rw [t1, f6]; exact hsv (j + 1) hj
        · rw [f11, hg, f10, gpwProd, gpwProd, Finset.prod_range_succ (n := j + 1)]
    · obtain ⟨ha, -⟩ := hacc n (by omega)
      have hr := reconstruct_bits 0 hN
      simp only [Nat.zero_add, pow_zero, one_mul] at hr
      have t0 : τ (.n 0) = value := by simp only [τ]; b1_look
      rw [ha, t0, hr, eOfNat192_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide)
        (by omega))), ← hv]
      exact e_add_self _
    · obtain ⟨-, hg⟩ := hacc n (by omega)
      rw [hg]
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_in (by omega) (by omega), Nat.sub_self]
      rfl
    · simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_in (by omega) (by omega), Nat.sub_self]
      rfl

set_option maxRecDepth 100000 in
theorem g_power_of_word_L6_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "g_power_of_word__L6" args rets ↔ MeaningGPowerOfWord 6 rd args rets :=
  g_power_of_word_iff 5 (by decide) (Program.find?_of_indexOf? (j := 172) (by decide +kernel) rfl)
    rfl core172_body rd args rets

/-! ## Completeness at a given buffer -/

/-- `MeaningGPowerOfWord` at the bit buffer `p` (a `HeapBuf` the caller's allocator names). -/
def MeaningGPowerOfWordAt (n : ℕ) (rd : Reader) (p : E) : List E → List E → Prop
  | [value, sq], [r] =>
      IsInK value ∧ kToNat (value.limb 0) < 2 ^ n ∧
        (∀ j < n, LoadHolds rd p j (bitE ((kToNat (value.limb 0)).testBit j))) ∧
        ∃ s : List E, s.length = n ∧ ReadsAt rd sq s ∧
          r = gpwProd (fun j => bitE ((kToNat (value.limb 0)).testBit j)) (fun j => s.getD j 0) n
  | _, _ => False

theorem meaningGPowerOfWord_of_at {n : ℕ} {rd : Reader} {p : E} {args rets : List E}
    (h : MeaningGPowerOfWordAt n rd p args rets) : MeaningGPowerOfWord n rd args rets := by
  match args, rets, h with
  | [_, _], [_], ⟨hK, hlt, hb, hs⟩ => exact ⟨hK, hlt, ⟨p, hb⟩, hs⟩

theorem g_power_of_word_L6_complete (rd : Reader) (p : E) (args rets : List E)
    (h : MeaningGPowerOfWordAt 6 rd p args rets) :
    coreProgram.Rel rd "g_power_of_word__L6" args rets :=
  (g_power_of_word_L6_iff rd args rets).mpr (meaningGPowerOfWord_of_at h)

end
end LeanVM.Guest.B1
