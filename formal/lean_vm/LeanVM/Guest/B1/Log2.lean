/-
  LeanVM.Guest.B1.Log2

  B1 for `verify_log2_ceil` and `log2_ceil_in_the_exponent`: the hinted `log2Ceil`, pinned by
  its two bounds, at both floors the guest compiles.
-/

module

public import LeanVM.Guest.B1.Exponent

/-!
# `verify_log2_ceil`, `log2_ceil_in_the_exponent` (TRIAGE #15, #16)

`verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, 34)` (G:606-640) reads 34 Boolean bits of a
word `W`, multiplies `g^W` over `g_squares`, stores the prefix sums `W mod 2^j` in a fresh run,
and pins the hinted `g^L` by two range checks (`L < 34`, `L - floor < 34`), `high·(W + 2^L) = 0`
and, unless `L` is the floor or zero, `(W mod 2^(L-1) + W)·(W + 2^(L-1)) ≠ 0`: that is
`L = max floor (log2Ceil W)` (`Value.verify_log2_ceil_sound`). The range checks read the memory,
so the theorems are stated on a memory image of `2^κ` words, `6 ≤ κ ≤ 32`, and over the exponent
tables (`ExpTables`, `exponent_tables`' postcondition). The expansion is `vlBlk j` per bit, from
value `5` then `13 + 12·j`, and `vlTail floor`; `vlBody floor` is equal to both specializations
(`__L0_L34`, `__L15_L34`) by kernel evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- Bit `j`'s value number. -/
def vlB : ℕ → ℕ
  | 0 => 5
  | j + 1 => 13 + 12 * j

/-- The running product `g^(W mod 2^(j+1))` after bit `j`. -/
def vlE : ℕ → ℕ
  | 0 => 12
  | j + 1 => 21 + 12 * j

/-- The running word `W mod 2^(j+1)` after bit `j`. -/
def vlW : ℕ → ℕ
  | 0 => 5
  | j + 1 => 24 + 12 * j

/-- Bit `j`: read, booleanity, the product's factor, the word's term, the prefix sum stored. -/
def vlBlk : ℕ → List Stmt
  | 0 => [.atom (.load (.n 5) (.n 0) 0), .atom (.mul (.n 6) (.n 5) (.n 5)),
      .atom (.assertEq (.n 6) (.n 5)), .atom (.const (.n 7) (word 1 0 0)),
      .atom (.load (.n 8) (.n 2) 0), .atom (.const (.n 9) (word 1 0 0)),
      .atom (.add (.n 10) (.n 8) (.n 9)), .atom (.mul (.n 11) (.n 5) (.n 10)),
      .atom (.add (.n 12) (.n 7) (.n 11)), .atom (.load (.n 5) (.n 3) 1)]
  | j + 1 => [.atom (.load (.n (13 + 12 * j)) (.n 0) (j + 1)),
      .atom (.mul (.n (14 + 12 * j)) (.n (13 + 12 * j)) (.n (13 + 12 * j))),
      .atom (.assertEq (.n (14 + 12 * j)) (.n (13 + 12 * j))),
      .atom (.const (.n (15 + 12 * j)) (word 1 0 0)),
      .atom (.load (.n (16 + 12 * j)) (.n 2) (j + 1)),
      .atom (.const (.n (17 + 12 * j)) (word 1 0 0)),
      .atom (.add (.n (18 + 12 * j)) (.n (16 + 12 * j)) (.n (17 + 12 * j))),
      .atom (.mul (.n (19 + 12 * j)) (.n (13 + 12 * j)) (.n (18 + 12 * j))),
      .atom (.add (.n (20 + 12 * j)) (.n (15 + 12 * j)) (.n (19 + 12 * j))),
      .atom (.mul (.n (21 + 12 * j)) (.n (vlE j)) (.n (20 + 12 * j))),
      .atom (.const (.n (22 + 12 * j)) (word (2 ^ (j + 1)) 0 0)),
      .atom (.mul (.n (23 + 12 * j)) (.n (13 + 12 * j)) (.n (22 + 12 * j))),
      .atom (.add (.n (24 + 12 * j)) (.n (vlW j)) (.n (23 + 12 * j))),
      .atom (.load (.n (24 + 12 * j)) (.n 3) (j + 2))]

/-- `g⁻¹`, the guest's `INV_GEN`, as the data writes it. -/
abbrev invGenWord : E := word 9223372036854775821 0 0

/-- The minimality check proper, at `L ≠ 0`. -/
def vlMinIn : List Stmt :=
  [.atom (.const (.n 434) invGenWord), .atom (.mul (.n 435) (.n 409) (.n 434)),
      .atom (.mul (.n 436) (.n 3) (.n 435)), .atom (.load (.n 437) (.n 436) 0),
      .atom (.const (.n 438) invGenWord), .atom (.mul (.n 439) (.n 409) (.n 438)),
      .atom (.mul (.n 440) (.n 1) (.n 439)), .atom (.load (.n 441) (.n 440) 0),
      .atom (.add (.n 442) (.n 408) (.n 441)), .atom (.add (.n 443) (.n 437) (.n 408)),
      .atom (.mul (.n 444) (.n 443) (.n 442)), .atom (.const (.n 445) (word 0 0 0)),
      .atom (.add (.n 446) (.n 444) (.n 445)), .atom (.hint (.inverse (.n 446) (.n 447))),
      .atom (.assertNe (.n 446) (.n 447) (.n 448))]

/-- The minimality check, at `L ≠ floor`. -/
def vlMin : List Stmt :=
  [.atom (.const (.n 432) (word 1 0 0)), .atom (.add (.n 433) (.n 409) (.n 432)),
    .ite (.n 433) [] vlMinIn]

/-- The hinted log and its checks. -/
def vlTail (fl : ℕ) : List Stmt :=
  [.atom (.hint (.log2Ceil (.heap (.n 0) 0 34) 34 fl (.n 409))),
    .atom (.const (.n 410) (word (2 ^ 33) 0 0)), .atom (.rangeCheck (.n 409) (.n 411) (.n 412) (.n 413) (.n 410)),
    .atom (.const (.n 414) (word (2 ^ 33) 0 0)), .atom (.const (.n 415) (word (2 ^ fl) 0 0)),
    .atom (.mul (.n 409) (.n 416) (.n 415)),
    .atom (.rangeCheck (.n 416) (.n 417) (.n 418) (.n 419) (.n 414)),
    .atom (.mul (.n 420) (.n 3) (.n 409)), .atom (.load (.n 421) (.n 420) 0),
    .atom (.add (.n 422) (.n 421) (.n 408)), .atom (.mul (.n 423) (.n 422) (.n 421)),
    .atom (.const (.n 424) (word 0 0 0)), .atom (.assertEq (.n 423) (.n 424)),
    .atom (.mul (.n 425) (.n 1) (.n 409)), .atom (.load (.n 426) (.n 425) 0),
    .atom (.add (.n 427) (.n 408) (.n 426)), .atom (.mul (.n 428) (.n 422) (.n 427)),
    .atom (.const (.n 429) (word 0 0 0)), .atom (.assertEq (.n 428) (.n 429)),
    .atom (.const (.n 430) (word (2 ^ fl) 0 0)), .atom (.add (.n 431) (.n 409) (.n 430)),
    .ite (.n 431) [] vlMin,
    .atom (.copy (.n 449) (.n 409)), .atom (.copy (.n 450) (.n 405)), .ret [.n 449, .n 450]]

/-- The expansion of `verify_log2_ceil` at the floor `fl`, 34 bits. -/
def vlBody (fl : ℕ) : List Stmt :=
  [.atom (.hint (.alloc (.n 3) 35)), .atom (.const (.n 4) (word 0 0 0)),
    .atom (.load (.n 4) (.n 3) 0)] ++ ((List.range 34).map vlBlk).flatten ++ vlTail fl

theorem core575_body : Fn.body Data.core575 = vlBody 0 := stmtsEqb_sound (by decide +kernel)

theorem core576_body : Fn.body Data.core576 = vlBody 15 := stmtsEqb_sound (by decide +kernel)

/-! ## The bits, the prefix sums, the product -/

/-- Bit `j`'s table word's value number. -/
def vlS : ℕ → ℕ
  | 0 => 8
  | j + 1 => 16 + 12 * j

/-- What bit `j` asks of a valuation. -/
def VlOk (rd : Reader) (σ : Val) : ℕ → Prop
  | 0 => LoadHolds rd (σ (.n 0)) 0 (σ (.n 5)) ∧ σ (.n 6) = σ (.n 5) * σ (.n 5) ∧
      σ (.n 6) + σ (.n 5) = 0 ∧ σ (.n 7) = 1 ∧ LoadHolds rd (σ (.n 2)) 0 (σ (.n 8)) ∧
      σ (.n 9) = 1 ∧ σ (.n 10) = σ (.n 8) + σ (.n 9) ∧ σ (.n 11) = σ (.n 5) * σ (.n 10) ∧
      σ (.n 12) = σ (.n 7) + σ (.n 11) ∧ LoadHolds rd (σ (.n 3)) 1 (σ (.n 5))
  | j + 1 => LoadHolds rd (σ (.n 0)) (j + 1) (σ (.n (13 + 12 * j))) ∧
      σ (.n (14 + 12 * j)) = σ (.n (13 + 12 * j)) * σ (.n (13 + 12 * j)) ∧
      σ (.n (14 + 12 * j)) + σ (.n (13 + 12 * j)) = 0 ∧ σ (.n (15 + 12 * j)) = 1 ∧
      LoadHolds rd (σ (.n 2)) (j + 1) (σ (.n (16 + 12 * j))) ∧ σ (.n (17 + 12 * j)) = 1 ∧
      σ (.n (18 + 12 * j)) = σ (.n (16 + 12 * j)) + σ (.n (17 + 12 * j)) ∧
      σ (.n (19 + 12 * j)) = σ (.n (13 + 12 * j)) * σ (.n (18 + 12 * j)) ∧
      σ (.n (20 + 12 * j)) = σ (.n (15 + 12 * j)) + σ (.n (19 + 12 * j)) ∧
      σ (.n (21 + 12 * j)) = σ (.n (vlE j)) * σ (.n (20 + 12 * j)) ∧
      σ (.n (22 + 12 * j)) = word (2 ^ (j + 1)) 0 0 ∧
      σ (.n (23 + 12 * j)) = σ (.n (13 + 12 * j)) * σ (.n (22 + 12 * j)) ∧
      σ (.n (24 + 12 * j)) = σ (.n (vlW j)) + σ (.n (23 + 12 * j)) ∧
      LoadHolds rd (σ (.n 3)) (j + 2) (σ (.n (24 + 12 * j)))

theorem holds_vlBlk {C : CallRel} {rd : Reader} {σ : Val} (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (vlBlk j) True kret ↔ VlOk rd σ j := by
  cases j <;> simp only [vlBlk, VlOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one]

theorem vl_chain {rd : Reader} {σ : Val} : ∀ n, n < 63 → (∀ j < n + 1, VlOk rd σ j) →
    σ (.n (vlW n)) = ∑ j ∈ Finset.range (n + 1), σ (.n (vlB j)) * coordBasis j ∧
      σ (.n (vlE n)) = gpwProd (fun j => σ (.n (vlB j))) (fun j => σ (.n (vlS j))) (n + 1)
  | 0, _, h => by
    obtain ⟨-, -, -, e7, -, e9, e10, e11, e12, -⟩ := h 0 (by omega)
    refine ⟨?_, ?_⟩
    · rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
        eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
      rfl
    · rw [gpwProd, show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_one]
      show σ (.n 12) = 1 + σ (.n 5) * (σ (.n 8) + 1)
      rw [e12, e7, e11, e10, e9]
  | n + 1, hn, h => by
    obtain ⟨ih1, ih2⟩ := vl_chain n (by omega) (fun j hj => h j (by omega))
    obtain ⟨-, -, -, e15, -, e17, e18, e19, e20, e21, e22, e23, e24, -⟩ := h (n + 1) (by omega)
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ (n := n + 1), ← ih1]
      show σ (.n (24 + 12 * n)) = _
      rw [e24, e23, e22, word_coordBasis (by omega)]
      rfl
    · rw [gpwProd, Finset.prod_range_succ (n := n + 1), ← gpwProd, ← ih2]
      show σ (.n (21 + 12 * n)) = _
      rw [e21, e20, e19, e18, e17, e15]
      rfl

/-- A prefix of the bits of `N` reconstructs `N mod 2^j`. -/
theorem sum_bits_mod (N j : ℕ) (hj : j ≤ 64) :
    ∑ t ∈ Finset.range j, bitE (N.testBit t) * coordBasis t = eOfNat (N % 2 ^ j) := by
  have h := sum_bitE_coordBasis N.testBit 0 j
  simp only [Nat.zero_add, pow_zero, one_mul] at h
  have hb : bitsVal N.testBit j = N % 2 ^ j := by
    rw [bitsVal_congr (f' := (N % 2 ^ j).testBit) fun t ht => by
      rw [Nat.testBit_mod_two_pow]; simp [ht], bitsVal_testBit (Nat.mod_lt _ (Nat.two_pow_pos j))]
  rw [h, hb, eOfNat192_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos j))
    (Nat.pow_le_pow_right (by decide) hj))]

/-- Over the table of squares, the product of the factors of `N`'s bits is `g^N`. -/
theorem gpwProd_pow {n N : ℕ} {s : ℕ → E} (hs : ∀ j < n, s j = gen ^ 2 ^ j) (hN : N < 2 ^ n) :
    gpwProd (fun j => bitE (N.testBit j)) s n = gen ^ N := by
  rw [gpwProd, Finset.prod_congr rfl fun j hj => by rw [hs j (Finset.mem_range.mp hj),
    add_comm (gen ^ 2 ^ j) 1, add_comm 1 (gen ^ 2 ^ j)], prod_bitE_gen_pow, bitsVal_testBit hN]

/-- `INV_GEN` is `g⁻¹`. -/
theorem gen_mul_invGenWord : gen * invGenWord = 1 := by
  rw [show gen = ofK (K.ofBits 2) from rfl, show invGenWord = ofK (K.ofBits 9223372036854775821)
    from word_eOfNat _, ← ofK_mul, show K.ofBits 2 * K.ofBits 9223372036854775821 = 1 by
      decide +kernel, ofK_one]

theorem gen_pow_mul_invGen (L : ℕ) : gen ^ (L + 1) * invGenWord = gen ^ L := by
  rw [pow_succ, mul_assoc, gen_mul_invGenWord, mul_one]

/-! ## The meaning -/

/-- **`verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, 34)`** (G:606-640; TRIAGE #15): the
34 words at `bits` are the bits of `W < 2^34`, the prefix sums `W mod 2^j` are in a run, the
floored log `max floor (log2Ceil W)` (V:695) is below 34, and the function returns its g-power
and `g^W`. -/
def MeaningVerifyLog2Ceil (fl : ℕ) (rd : Reader) : List E → List E → Prop
  | [bits, _, _], rets =>
      ∃ W < 2 ^ 34, (∀ j < 34, LoadHolds rd bits j (bitE (W.testBit j))) ∧
        max fl (log2Ceil W) < 34 ∧ (∃ ps, ∀ j ≤ 34, LoadHolds rd ps j (eOfNat (W % 2 ^ j))) ∧
        rets = [gen ^ max fl (log2Ceil W), gen ^ W]
  | _, _ => False

/-! ## Soundness -/

theorem word_two_pow_33 : word (2 ^ 33) 0 0 = ofK (Parameters.gpow 33) := by
  rw [word_two_pow (by decide), gen_pow_eq_ofK]

/-- The function's body, simplified to its conditions. -/
theorem vl_unfold {name : String} {f : Fn} (fl : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = vlBody fl) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2)] = args ∧
      σ (.n 4) = 0 ∧ LoadHolds rd (σ (.n 3)) 0 (σ (.n 4)) ∧ (∀ j < 34, VlOk rd σ j) ∧
      σ (.n 410) = word (2 ^ 33) 0 0 ∧
      (LoadHolds rd (σ (.n 409)) 0 (σ (.n 412)) ∧ σ (.n 410) = σ (.n 409) * σ (.n 411) ∧
        LoadHolds rd (σ (.n 411)) 0 (σ (.n 413))) ∧
      σ (.n 414) = word (2 ^ 33) 0 0 ∧ σ (.n 415) = word (2 ^ fl) 0 0 ∧
      σ (.n 409) = σ (.n 416) * σ (.n 415) ∧
      (LoadHolds rd (σ (.n 416)) 0 (σ (.n 418)) ∧ σ (.n 414) = σ (.n 416) * σ (.n 417) ∧
        LoadHolds rd (σ (.n 417)) 0 (σ (.n 419))) ∧
      σ (.n 420) = σ (.n 3) * σ (.n 409) ∧ LoadHolds rd (σ (.n 420)) 0 (σ (.n 421)) ∧
      σ (.n 422) = σ (.n 421) + σ (.n 408) ∧ σ (.n 423) = σ (.n 422) * σ (.n 421) ∧
      σ (.n 424) = 0 ∧ σ (.n 423) + σ (.n 424) = 0 ∧
      σ (.n 425) = σ (.n 1) * σ (.n 409) ∧ LoadHolds rd (σ (.n 425)) 0 (σ (.n 426)) ∧
      σ (.n 427) = σ (.n 408) + σ (.n 426) ∧ σ (.n 428) = σ (.n 422) * σ (.n 427) ∧
      σ (.n 429) = 0 ∧ σ (.n 428) + σ (.n 429) = 0 ∧
      σ (.n 430) = word (2 ^ fl) 0 0 ∧ σ (.n 431) = σ (.n 409) + σ (.n 430) ∧
      (IsInK (σ (.n 431)) ∧ (σ (.n 431) ≠ 0 →
        σ (.n 432) = 1 ∧ σ (.n 433) = σ (.n 409) + σ (.n 432) ∧ IsInK (σ (.n 433)) ∧
        (σ (.n 433) ≠ 0 → σ (.n 434) = invGenWord ∧ σ (.n 435) = σ (.n 409) * σ (.n 434) ∧
          σ (.n 436) = σ (.n 3) * σ (.n 435) ∧ LoadHolds rd (σ (.n 436)) 0 (σ (.n 437)) ∧
          σ (.n 438) = invGenWord ∧ σ (.n 439) = σ (.n 409) * σ (.n 438) ∧
          σ (.n 440) = σ (.n 1) * σ (.n 439) ∧ LoadHolds rd (σ (.n 440)) 0 (σ (.n 441)) ∧
          σ (.n 442) = σ (.n 408) + σ (.n 441) ∧ σ (.n 443) = σ (.n 437) + σ (.n 408) ∧
          σ (.n 444) = σ (.n 443) * σ (.n 442) ∧ σ (.n 445) = 0 ∧
          σ (.n 446) = σ (.n 444) + σ (.n 445) ∧ σ (.n 448) = σ (.n 446) * σ (.n 447) ∧
          σ (.n 448) = 1))) ∧
      σ (.n 449) = σ (.n 409) ∧ σ (.n 450) = σ (.n 405) ∧ [σ (.n 449), σ (.n 450)] = rets := by
  rw [rel_iff_sem hfind, hbody, hparams, vlBody, vlTail]
  simp only [holdsList_append, Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 431) [] vlMin rfl rfl]
  simp only [vlMin, Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 433) [] vlMinIn rfl rfl]
  simp only [vlMinIn]
  simp only [holdsList_range_flatten 34 vlBlk (fun j => by cases j <;> rfl), holds_vlBlk,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and, and_true,
    word_zero, word_one, implies_true]

/-- A range check against `g^33` on a memory of `2^κ ≥ 34` words: `x = g^e`, `e < 34`. -/
theorem rangeCheck34 {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {x y t1 t2 k : E}
    (hk : k = word (2 ^ 33) 0 0) (h1 : LoadHolds Lm.read x 0 t1) (h2 : k = x * y)
    (h3 : LoadHolds Lm.read y 0 t2) : ∃ e < 34, x = gen ^ e := by
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ Lm x (K := 34) (by omega)
    (le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6))).mp
    ⟨y, t1, t2, h1, by rw [← h2, hk, word_two_pow_33], h3⟩
  exact ⟨e, he, by rw [hx, gen_pow_eq_ofK]⟩

theorem vl_bool {rd : Reader} {σ : Val} (hblk : ∀ j < 34, VlOk rd σ j) :
    ∀ j < 34, σ (.n (vlB j)) * σ (.n (vlB j)) = σ (.n (vlB j)) := fun j hj => by
  cases j with
  | zero =>
    obtain ⟨-, e6, a6, -⟩ := hblk 0 hj
    show σ (.n 5) * σ (.n 5) = σ (.n 5)
    rw [← e6]; exact e_add_eq_zero_iff.mp a6
  | succ j =>
    obtain ⟨-, e14, a14, -⟩ := hblk (j + 1) hj
    show σ (.n (13 + 12 * j)) * σ (.n (13 + 12 * j)) = σ (.n (13 + 12 * j))
    rw [← e14]; exact e_add_eq_zero_iff.mp a14

/-- The prefix sums stored in the run. -/
theorem vl_psum {rd : Reader} {σ : Val} {N : ℕ} (hblk : ∀ j < 34, VlOk rd σ j)
    (h4 : σ (.n 4) = 0) (l4 : LoadHolds rd (σ (.n 3)) 0 (σ (.n 4)))
    (hb : ∀ j < 34, σ (.n (vlB j)) = bitE (N.testBit j)) :
    ∀ j ≤ 34, LoadHolds rd (σ (.n 3)) j (eOfNat (N % 2 ^ j)) := fun j hj => by
  cases j with
  | zero => rw [pow_zero, Nat.mod_one, eOfNat_zero, ← h4]; exact l4
  | succ j =>
    have hw : σ (.n (vlW j)) = eOfNat (N % 2 ^ (j + 1)) := by
      rw [(vl_chain j (by omega) fun i hi => hblk i (by omega)).1, ← sum_bits_mod N (j + 1) (by omega)]
      exact Finset.sum_congr rfl fun i hi => by rw [hb i (by have := Finset.mem_range.mp hi; omega)]
    rw [← hw]
    cases j with
    | zero => exact (hblk 0 (by omega)).2.2.2.2.2.2.2.2.2
    | succ j => exact (hblk (j + 1) (by omega)).2.2.2.2.2.2.2.2.2.2.2.2.2

theorem vl_mul_gen_pow {rd : Reader} {p w : E} {L : ℕ} (h : LoadHolds rd (p * gen ^ L) 0 w) :
    LoadHolds rd p L w := by rwa [loadHolds_mul_gen_pow, Nat.add_zero] at h

theorem verify_log2_ceil_sound_aux {name : String} {f : Fn} (fl : ℕ) (hfl : fl < 34)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = vlBody fl) {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    {bits lp sq : E} (ht : ExpTables Lm.read lp sq) (rets : List E)
    (h : coreProgram.Rel Lm.read name [bits, lp, sq] rets) :
    MeaningVerifyLog2Ceil fl Lm.read [bits, lp, sq] rets := by
  rw [vl_unfold fl hfind hparams hbody] at h
  obtain ⟨σ, hp, h4, l4, hblk, h410, ⟨r1a, r1b, r1c⟩, h414, h415, m409, ⟨r2a, r2b, r2c⟩, h420,
    l421, h422, -, -, -, h425, l426, h427, h428, h429, a428, h430, h431, ⟨-, hmin⟩, h449, h450,
    hret⟩ := h
  simp only [List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, -⟩ := hp
  obtain ⟨hsum, hprod⟩ := vl_chain 33 (by omega) hblk
  obtain ⟨N, hN, hX, hb⟩ := bits_of_reconstruct (s := 0) (vl_bool hblk)
    (by simpa only [Nat.zero_add] using hsum.symm)
  rw [Nat.pow_zero, Nat.one_mul, eOfNat192_of_lt (lt_of_lt_of_le hN (by decide))] at hX
  change σ (.n 408) = _ at hX
  have hps := vl_psum hblk h4 l4 hb
  obtain ⟨L, hL, hxL⟩ := rangeCheck34 hκ hκ6 Lm h410 r1a r1b r1c
  obtain ⟨c, hc, hxc⟩ := rangeCheck34 hκ hκ6 Lm h414 r2a r2b r2c
  have hLc : L = c + fl := by
    rw [hxL, hxc, h415, word_two_pow (by omega), ← pow_add] at m409
    exact gen_pow_inj (by omega) (by omega) m409
  have hlow : σ (.n 421) = eOfNat (N % 2 ^ L) := by
    rw [h420, hxL] at l421
    exact loadHolds_unique (vl_mul_gen_pow l421) (hps L (by omega))
  have hlp : σ (.n 426) = eOfNat (2 ^ L) := by
    rw [h425, hxL] at l426
    exact loadHolds_unique (vl_mul_gen_pow l426) (ht L (by show _ < 34; omega)).1
  have h2 : (eOfNat (N % 2 ^ L) + eOfNat N) * (eOfNat N + eOfNat (2 ^ L)) = 0 := by
    rw [h429, add_zero, h428, h427, h422, hlow, hlp, hX] at a428
    exact a428
  have h3 : L ≠ fl → L ≠ 0 →
      (eOfNat (N % 2 ^ (L - 1)) + eOfNat N) * (eOfNat N + eOfNat (2 ^ (L - 1))) ≠ 0 := by
    intro hne h0
    have h431' : σ (.n 431) ≠ 0 := by
      rw [h431, h430, hxL, word_two_pow (by omega)]
      intro he
      exact hne (gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp he))
    obtain ⟨h432, h433, -, hin⟩ := hmin h431'
    have h433' : σ (.n 433) ≠ 0 := by
      rw [h433, h432, hxL, ← pow_zero gen]
      intro he
      exact h0 (gen_pow_inj (by omega) (by decide) (e_add_eq_zero_iff.mp he))
    obtain ⟨h434, h435, h436, l437, h438, h439, h440, l441, h442, h443, h444, h445, h446, h448a,
      h448b⟩ := hin h433'
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hg : σ (.n 435) = gen ^ L' := by rw [h435, h434, hxL, gen_pow_mul_invGen]
    have hg' : σ (.n 439) = gen ^ L' := by rw [h439, h438, hxL, gen_pow_mul_invGen]
    rw [h436, hg] at l437
    rw [h440, hg'] at l441
    have e437 := loadHolds_unique (vl_mul_gen_pow l437) (hps L' (by omega))
    have e441 := loadHolds_unique (vl_mul_gen_pow l441) (ht L' (by show _ < 34; omega)).1
    have hne0 : σ (.n 446) ≠ 0 := fun h0' => by
      rw [h0', zero_mul] at h448a; rw [h448a] at h448b; exact zero_ne_one h448b
    rw [h446, h445, add_zero, h444, h443, h442, e437, e441, hX] at hne0
    simpa using hne0
  have hLmax := verify_log2_ceil_sound (lt_of_lt_of_le hN (by decide)) (by omega) (by omega) h2 h3
  have hsq : ∀ j < 34, σ (.n (vlS j)) = gen ^ 2 ^ j := fun j hj => by
    cases j with
    | zero => exact loadHolds_unique (hblk 0 hj).2.2.2.2.1 (ht 0 (by show 0 < 34; omega)).2
    | succ j => exact loadHolds_unique (hblk (j + 1) hj).2.2.2.2.1 (ht (j + 1) (by show _ < 34; omega)).2
  have hE : σ (.n 405) = gen ^ N := by
    change σ (.n (vlE 33)) = _
    rw [hprod, ← gpwProd_pow (n := 34) (s := fun j => σ (.n (vlS j))) hsq hN, gpwProd, gpwProd]
    exact Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.mem_range.mp hj)]
  refine ⟨N, hN, fun j hj => ?_, by rw [← hLmax]; exact hL, ⟨σ (.n 3), hps⟩, ?_⟩
  · rw [← hb j hj]
    cases j with
    | zero => exact (hblk 0 hj).1
    | succ j => exact (hblk (j + 1) hj).1
  · rw [← hret, h449, h450, hxL, ← hLmax]
    exact congrArg (fun z => [gen ^ L, z]) hE

/-! ## Completeness -/

/-- The honest values of the bits' blocks, from `.n 5`, through bit `j`. -/
def vlVals (b s : ℕ → E) : ℕ → ℕ → E
  | 0, i => [b 0, b 0 * b 0, 1, s 0, 1, s 0 + 1, b 0 * (s 0 + 1), 1 + b 0 * (s 0 + 1)].getD i 0
  | j + 1, i => if i < 8 + 12 * j then vlVals b s j i else
      [b (j + 1), b (j + 1) * b (j + 1), 1, s (j + 1), 1, s (j + 1) + 1,
        b (j + 1) * (s (j + 1) + 1), 1 + b (j + 1) * (s (j + 1) + 1), gpwProd b s (j + 2),
        word (2 ^ (j + 1)) 0 0, b (j + 1) * word (2 ^ (j + 1)) 0 0,
        ∑ t ∈ Finset.range (j + 2), b t * coordBasis t].getD (i - (8 + 12 * j)) 0

theorem vlVals_lt (b s : ℕ → E) : ∀ m j i, j ≤ m → i < 8 + 12 * j → vlVals b s m i = vlVals b s j i
  | 0, j, i, h, _ => by rw [show j = 0 by omega]
  | m + 1, j, i, h, hi => by
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · rw [vlVals, ite_pos' (by omega)]; exact vlVals_lt b s m j i (by omega) hi
    · rw [show j = m + 1 by omega]

theorem vlVals_zero (b s : ℕ → E) (m i : ℕ) (hi : i < 8) :
    vlVals b s m i = [b 0, b 0 * b 0, 1, s 0, 1, s 0 + 1, b 0 * (s 0 + 1),
      1 + b 0 * (s 0 + 1)].getD i 0 := by
  rw [vlVals_lt b s m 0 i (by omega) (by omega), vlVals]

theorem vlVals_succ (b s : ℕ → E) (m j c : ℕ) (hj : j + 1 ≤ m) (hc : c < 12) :
    vlVals b s m (8 + 12 * j + c) = [b (j + 1), b (j + 1) * b (j + 1), 1, s (j + 1), 1,
        s (j + 1) + 1, b (j + 1) * (s (j + 1) + 1), 1 + b (j + 1) * (s (j + 1) + 1),
        gpwProd b s (j + 2), word (2 ^ (j + 1)) 0 0, b (j + 1) * word (2 ^ (j + 1)) 0 0,
        ∑ t ∈ Finset.range (j + 2), b t * coordBasis t].getD c 0 := by
  rw [vlVals_lt b s m (j + 1) _ hj (by omega), vlVals, ite_neg' (by omega),
    show 8 + 12 * j + c - (8 + 12 * j) = c by omega]

theorem verify_log2_ceil_complete_aux {name : String} {f : Fn} (fl : ℕ) (hfl : fl < 34)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = vlBody fl) {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    {bits lp sq : E} (ht : ExpTables Lm.read lp sq) (rets : List E)
    (h : MeaningVerifyLog2Ceil fl Lm.read [bits, lp, sq] rets) :
    coreProgram.Rel Lm.read name [bits, lp, sq] rets := by
  obtain ⟨W, hW, hbits, hL, ⟨ps, hps⟩, rfl⟩ := h
  rw [vl_unfold fl hfind hparams hbody]
  set L := max fl (log2Ceil W)
  have hW64 : W < 2 ^ 64 := lt_of_lt_of_le hW (by decide)
  obtain ⟨c1, c2, c3⟩ := verify_log2_ceil_complete (floor := fl) hW64 (by omega)
  have hK34 : 34 ≤ 2 ^ κ := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6)
  obtain ⟨y1, t1, t2, r1a, r1b, r1c⟩ := (rangeCheck_iff hκ Lm (ofK (Parameters.gpow L)) (K := 34)
    (by omega) hK34).mpr ⟨L, hL, rfl⟩
  obtain ⟨y2, u1, u2, r2a, r2b, r2c⟩ := (rangeCheck_iff hκ Lm (ofK (Parameters.gpow (L - fl)))
    (K := 34) (by omega) hK34).mpr ⟨L - fl, by omega, rfl⟩
  set b := fun j => bitE (W.testBit j)
  set sv := fun j => (gen ^ 2 ^ j : E)
  set lo := eOfNat (W % 2 ^ L)
  set hi := lo + eOfNat W
  set lo' := eOfNat (W % 2 ^ (L - 1))
  set x := (lo' + eOfNat W) * (eOfNat W + eOfNat (2 ^ (L - 1)))
  set τ := setl (setv (setl (Val.ofArgs [bits, lp, sq]) 3 [ps, 0]) 5 404 (vlVals b sv 33)) 409
    [gen ^ L, word (2 ^ 33) 0 0, y1, t1, t2, word (2 ^ 33) 0 0, word (2 ^ fl) 0 0, gen ^ (L - fl),
      y2, u1, u2, ps * gen ^ L, lo, hi, hi * lo, 0, lp * gen ^ L, eOfNat (2 ^ L),
      eOfNat W + eOfNat (2 ^ L), hi * (eOfNat W + eOfNat (2 ^ L)), 0, word (2 ^ fl) 0 0,
      gen ^ L + word (2 ^ fl) 0 0, 1, gen ^ L + 1, invGenWord, gen ^ L * invGenWord,
      ps * (gen ^ L * invGenWord), lo', invGenWord, gen ^ L * invGenWord,
      lp * (gen ^ L * invGenWord), eOfNat (2 ^ (L - 1)), eOfNat W + eOfNat (2 ^ (L - 1)),
      lo' + eOfNat W, x, 0, x + 0, (x + 0)⁻¹, (x + 0) * (x + 0)⁻¹, gen ^ L, gen ^ W]
  have tv : ∀ i < 404, τ (.n (5 + i)) = vlVals b sv 33 i := fun i hi => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have t0 : ∀ i < 8, τ (.n (5 + i)) = [b 0, b 0 * b 0, 1, sv 0, 1, sv 0 + 1, b 0 * (sv 0 + 1),
      1 + b 0 * (sv 0 + 1)].getD i 0 := fun i hi => by rw [tv i (by omega), vlVals_zero _ _ _ _ hi]
  have ts : ∀ j c, j + 1 ≤ 33 → c < 12 → τ (.n (13 + 12 * j + c)) = [b (j + 1),
      b (j + 1) * b (j + 1), 1, sv (j + 1), 1, sv (j + 1) + 1, b (j + 1) * (sv (j + 1) + 1),
      1 + b (j + 1) * (sv (j + 1) + 1), gpwProd b sv (j + 2), word (2 ^ (j + 1)) 0 0,
      b (j + 1) * word (2 ^ (j + 1)) 0 0, ∑ t ∈ Finset.range (j + 2), b t * coordBasis t].getD c 0 :=
    fun j c hj hc => by
      rw [show 13 + 12 * j + c = 5 + (8 + 12 * j + c) by omega, tv _ (by omega),
        vlVals_succ _ _ _ _ _ hj hc]
  have tl : ∀ i < 42, τ (.n (409 + i)) = [gen ^ L, word (2 ^ 33) 0 0, y1, t1, t2, word (2 ^ 33) 0 0,
      word (2 ^ fl) 0 0, gen ^ (L - fl), y2, u1, u2, ps * gen ^ L, lo, hi, hi * lo, 0, lp * gen ^ L,
      eOfNat (2 ^ L), eOfNat W + eOfNat (2 ^ L), hi * (eOfNat W + eOfNat (2 ^ L)), 0,
      word (2 ^ fl) 0 0, gen ^ L + word (2 ^ fl) 0 0, 1, gen ^ L + 1, invGenWord,
      gen ^ L * invGenWord, ps * (gen ^ L * invGenWord), lo', invGenWord, gen ^ L * invGenWord,
      lp * (gen ^ L * invGenWord), eOfNat (2 ^ (L - 1)), eOfNat W + eOfNat (2 ^ (L - 1)),
      lo' + eOfNat W, x, 0, x + 0, (x + 0)⁻¹, (x + 0) * (x + 0)⁻¹, gen ^ L, gen ^ W].getD i 0 :=
    fun i hi => by
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hacc : ∀ j < 34, τ (.n (vlW j)) = ∑ t ∈ Finset.range (j + 1), b t * coordBasis t ∧
      τ (.n (vlE j)) = gpwProd b sv (j + 1) := fun j hj => by
    cases j with
    | zero =>
      refine ⟨?_, ?_⟩
      · have := t0 0 (by omega)
        rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
          eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
        exact this
      · have := t0 7 (by omega)
        rw [gpwProd, show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_one]
        exact this
    | succ j =>
      rw [show vlW (j + 1) = 13 + 12 * j + 11 by simp only [vlW]; omega,
        show vlE (j + 1) = 13 + 12 * j + 8 by simp only [vlE]; omega]
      exact ⟨ts j 11 (by omega) (by omega), ts j 8 (by omega) (by omega)⟩
  have hbits' : ∀ j < 34, LoadHolds Lm.read bits j (b j) := hbits
  have hsq : ∀ j < 34, LoadHolds Lm.read sq j (sv j) := fun j hj => (ht j (by show j < 34; omega)).2
  have hX : τ (.n 408) = eOfNat W := by
    rw [show (408 : ℕ) = vlW 33 from rfl, (hacc 33 (by omega)).1, sum_bits_mod W 34 (by omega),
      Nat.mod_eq_of_lt hW]
  have hE : τ (.n 405) = gen ^ W := by
    rw [show (405 : ℕ) = vlE 33 from rfl, (hacc 33 (by omega)).2]
    exact gpwProd_pow (fun j _ => rfl) hW
  have e1 : τ (.n 1) = lp := by simp only [τ]; b1_look
  have e3 : τ (.n 3) = ps := by simp only [τ]; b1_look
  have x409 : τ (.n 409) = gen ^ L := tl 0 (by omega)
  have x410 : τ (.n 410) = word (2 ^ 33) 0 0 := tl 1 (by omega)
  have x411 : τ (.n 411) = y1 := tl 2 (by omega)
  have x412 : τ (.n 412) = t1 := tl 3 (by omega)
  have x413 : τ (.n 413) = t2 := tl 4 (by omega)
  have x414 : τ (.n 414) = word (2 ^ 33) 0 0 := tl 5 (by omega)
  have x415 : τ (.n 415) = word (2 ^ fl) 0 0 := tl 6 (by omega)
  have x416 : τ (.n 416) = gen ^ (L - fl) := tl 7 (by omega)
  have x417 : τ (.n 417) = y2 := tl 8 (by omega)
  have x418 : τ (.n 418) = u1 := tl 9 (by omega)
  have x419 : τ (.n 419) = u2 := tl 10 (by omega)
  have x420 : τ (.n 420) = ps * gen ^ L := tl 11 (by omega)
  have x421 : τ (.n 421) = lo := tl 12 (by omega)
  have x422 : τ (.n 422) = hi := tl 13 (by omega)
  have x423 : τ (.n 423) = hi * lo := tl 14 (by omega)
  have x424 : τ (.n 424) = 0 := tl 15 (by omega)
  have x425 : τ (.n 425) = lp * gen ^ L := tl 16 (by omega)
  have x426 : τ (.n 426) = eOfNat (2 ^ L) := tl 17 (by omega)
  have x427 : τ (.n 427) = eOfNat W + eOfNat (2 ^ L) := tl 18 (by omega)
  have x428 : τ (.n 428) = hi * (eOfNat W + eOfNat (2 ^ L)) := tl 19 (by omega)
  have x429 : τ (.n 429) = 0 := tl 20 (by omega)
  have x430 : τ (.n 430) = word (2 ^ fl) 0 0 := tl 21 (by omega)
  have x431 : τ (.n 431) = gen ^ L + word (2 ^ fl) 0 0 := tl 22 (by omega)
  have x432 : τ (.n 432) = 1 := tl 23 (by omega)
  have x433 : τ (.n 433) = gen ^ L + 1 := tl 24 (by omega)
  have x434 : τ (.n 434) = invGenWord := tl 25 (by omega)
  have x435 : τ (.n 435) = gen ^ L * invGenWord := tl 26 (by omega)
  have x436 : τ (.n 436) = ps * (gen ^ L * invGenWord) := tl 27 (by omega)
  have x437 : τ (.n 437) = lo' := tl 28 (by omega)
  have x438 : τ (.n 438) = invGenWord := tl 29 (by omega)
  have x439 : τ (.n 439) = gen ^ L * invGenWord := tl 30 (by omega)
  have x440 : τ (.n 440) = lp * (gen ^ L * invGenWord) := tl 31 (by omega)
  have x441 : τ (.n 441) = eOfNat (2 ^ (L - 1)) := tl 32 (by omega)
  have x442 : τ (.n 442) = eOfNat W + eOfNat (2 ^ (L - 1)) := tl 33 (by omega)
  have x443 : τ (.n 443) = lo' + eOfNat W := tl 34 (by omega)
  have x444 : τ (.n 444) = x := tl 35 (by omega)
  have x445 : τ (.n 445) = 0 := tl 36 (by omega)
  have x446 : τ (.n 446) = x + 0 := tl 37 (by omega)
  have x447 : τ (.n 447) = (x + 0)⁻¹ := tl 38 (by omega)
  have x448 : τ (.n 448) = (x + 0) * (x + 0)⁻¹ := tl 39 (by omega)
  have x449 : τ (.n 449) = gen ^ L := tl 40 (by omega)
  have x450 : τ (.n 450) = gen ^ W := tl 41 (by omega)
  have e0 : τ (.n 0) = bits := by simp only [τ]; b1_look
  have e2 : τ (.n 2) = sq := by simp only [τ]; b1_look
  have e4 : τ (.n 4) = 0 := by simp only [τ]; b1_look
  refine ⟨τ, by rw [e0, e1, e2], e4, by
      rw [e3, e4]; have := hps 0 (by omega); rwa [pow_zero, Nat.mod_one, eOfNat_zero] at this,
    fun j hj => ?_,
    x410, ⟨?_, ?_, ?_⟩, x414, x415, ?_, ⟨?_, ?_, ?_⟩, by rw [x420, e3, x409], ?_,
    by rw [x422, x421, hX], by rw [x423, x422, x421], x424, ?_, by rw [x425, e1, x409], ?_,
    by rw [x427, hX, x426], by rw [x428, x422, x427], x429, ?_, x430, by rw [x431, x409, x430],
    ⟨?_, fun h431 => ?_⟩, by rw [x449, x409], by rw [x450, hE], by rw [x449, x450]⟩
  · cases j with
    | zero =>
      have f5 := t0 0 (by omega); have f6 := t0 1 (by omega); have f7 := t0 2 (by omega)
      have f8 := t0 3 (by omega); have f9 := t0 4 (by omega); have f10 := t0 5 (by omega)
      have f11 := t0 6 (by omega); have f12 := t0 7 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd]
        at f5 f6 f7 f8 f9 f10 f11 f12
      refine ⟨?_, by rw [f6, f5], ?_, f7, ?_, f9, by rw [f10, f8, f9], by rw [f11, f5, f10],
        by rw [f12, f7, f11], ?_⟩
      · rw [e0, f5]; exact hbits' 0 hj
      · rw [f6, f5]; simp only [b, bitE_mul_self]; exact e_add_self _
      · rw [e2, f8]; exact hsq 0 hj
      rw [e3, f5]
      have := hps 1 (by omega)
      rwa [show eOfNat (W % 2 ^ 1) = b 0 by
        rw [← sum_bits_mod W 1 (by omega), Finset.sum_range_one, coordBasis, pow_zero,
          eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]] at this
    | succ j =>
      have e := fun c (hc : c < 12) => ts j c (by omega) hc
      have f0 := e 0 (by omega); have f1 := e 1 (by omega); have f2 := e 2 (by omega)
      have f3 := e 3 (by omega); have f4 := e 4 (by omega); have f5 := e 5 (by omega)
      have f6 := e 6 (by omega); have f7 := e 7 (by omega); have f8 := e 8 (by omega)
      have f9 := e 9 (by omega); have f10 := e 10 (by omega); have f11 := e 11 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ,
        show ∀ k, 13 + 12 * j + k = k + 13 + 12 * j from fun k => by ring]
        at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
      obtain ⟨ha, hg⟩ := hacc j (by omega)
      refine ⟨?_, by rw [f1, f0], ?_, f2, ?_, f4, by rw [f5, f3, f4], by rw [f6, f0, f5],
        by rw [f7, f2, f6], ?_, f9, by rw [f10, f0, f9], ?_, ?_⟩
      · rw [e0, f0]; exact hbits' (j + 1) hj
      · rw [f1, f0]; simp only [b, bitE_mul_self]; exact e_add_self _
      · rw [e2, f3]; exact hsq (j + 1) hj
      · rw [f8, hg, f7, gpwProd, gpwProd, Finset.prod_range_succ (n := j + 1)]
      · rw [f11, ha, f10, Finset.sum_range_succ (n := j + 1), word_coordBasis (by omega)]
      · rw [e3, f11, sum_bits_mod W (j + 2) (by omega)]
        exact hps (j + 2) (by omega)
  · rw [x409, x412, gen_pow_eq_ofK]; exact r1a
  · rw [x410, x409, x411, word_two_pow_33, gen_pow_eq_ofK]; exact r1b
  · rw [x411, x413]; exact r1c
  · rw [x409, x416, x415, word_two_pow (by omega), ← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
  · rw [x416, x418, gen_pow_eq_ofK]; exact r2a
  · rw [x414, x416, x417, word_two_pow_33, gen_pow_eq_ofK]; exact r2b
  · rw [x417, x419]; exact r2c
  · rw [x420, x421]
    rw [loadHolds_mul_gen_pow, Nat.add_zero]
    exact hps L (by omega)
  · rw [x423, x424, add_zero]; exact c1
  · rw [x425, x426, loadHolds_mul_gen_pow, Nat.add_zero]
    exact (ht L (by show L < 34; omega)).1
  · rw [x428, x429, add_zero]; exact c2
  · rw [x431, word_two_pow (by omega)]
    exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · have hne : L ≠ fl := fun he => by
      rw [x431, he, word_two_pow (by omega)] at h431
      exact h431 (e_add_self _)
    refine ⟨x432, by rw [x433, x409, x432], ?_, fun h433 => ?_⟩
    · rw [x433]
      exact isInK_add (gen_pow_isInK _) (by rw [← pow_zero gen]; exact gen_pow_isInK 0)
    have h0 : L ≠ 0 := fun he => by
      rw [x433, he, pow_zero] at h433
      exact h433 (e_add_self _)
    obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hinv : gen ^ L * invGenWord = gen ^ L' := by rw [hL', gen_pow_mul_invGen]
    have hxne : x + 0 ≠ 0 := by rw [add_zero]; exact c3 hne h0
    have hm : (x + 0) * (x + 0)⁻¹ = 1 := e_mul_inv_cancel hxne
    refine ⟨x434, by rw [x435, x409, x434], by rw [x436, e3, x435], ?_, x438,
      by rw [x439, x409, x438], by rw [x440, e1, x439], ?_, by rw [x442, hX, x441],
      by rw [x443, x437, hX], by rw [x444, x443, x442], x445, by rw [x446, x444, x445],
      by rw [x448, x446, x447], by rw [x448]; exact hm⟩
    · rw [x436, x437, hinv, loadHolds_mul_gen_pow, Nat.add_zero]
      have := hps (L - 1) (by omega)
      rw [show L' = L - 1 by omega]
      exact this
    · rw [x440, x441, hinv, loadHolds_mul_gen_pow, Nat.add_zero, show L - 1 = L' by omega]
      exact (ht L' (by show L' < 34; omega)).1

/-! ## The theorems -/

/-- **`verify_log2_ceil` at the floor `fl`**, for a compiled function whose body is `vlBody fl`,
on a memory of `2^κ` words, `6 ≤ κ ≤ 32`, over the exponent tables at `lp`, `sq`. -/
theorem verify_log2_ceil_iff {name : String} {f : Fn} (fl : ℕ) (hfl : fl < 34)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = vlBody fl) {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    {bits lp sq : E} (ht : ExpTables Lm.read lp sq) (rets : List E) :
    coreProgram.Rel Lm.read name [bits, lp, sq] rets ↔
      MeaningVerifyLog2Ceil fl Lm.read [bits, lp, sq] rets :=
  ⟨verify_log2_ceil_sound_aux fl hfl hfind hparams hbody hκ hκ6 Lm ht rets,
    verify_log2_ceil_complete_aux fl hfl hfind hparams hbody hκ hκ6 Lm ht rets⟩

set_option maxRecDepth 100000 in
theorem find_verify_log2_ceil_L0_L34 :
    coreProgram.find? "verify_log2_ceil__L0_L34" = some Data.core575 :=
  Program.find?_of_indexOf? (j := 575) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_verify_log2_ceil_L15_L34 :
    coreProgram.find? "verify_log2_ceil__L15_L34" = some Data.core576 :=
  Program.find?_of_indexOf? (j := 576) (by decide +kernel) rfl

theorem verify_log2_ceil_L0_L34_iff {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    {bits lp sq : E} (ht : ExpTables Lm.read lp sq) (rets : List E) :
    coreProgram.Rel Lm.read "verify_log2_ceil__L0_L34" [bits, lp, sq] rets ↔
      MeaningVerifyLog2Ceil 0 Lm.read [bits, lp, sq] rets :=
  verify_log2_ceil_iff 0 (by decide) find_verify_log2_ceil_L0_L34 rfl core575_body hκ hκ6 Lm ht rets

theorem verify_log2_ceil_L15_L34_iff {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    {bits lp sq : E} (ht : ExpTables Lm.read lp sq) (rets : List E) :
    coreProgram.Rel Lm.read "verify_log2_ceil__L15_L34" [bits, lp, sq] rets ↔
      MeaningVerifyLog2Ceil 15 Lm.read [bits, lp, sq] rets :=
  verify_log2_ceil_iff 15 (by decide) find_verify_log2_ceil_L15_L34 rfl core576_body hκ hκ6 Lm ht
    rets

/-! ## `log2_ceil_in_the_exponent` -/

/-- **`log2_ceil_in_the_exponent(g^N, g_logs_pow2, g_squares, floor, 34)`** (G:643-651; TRIAGE
#16): `g^N` for `N < 2^34` (its bits hinted into a run and checked by `verify_log2_ceil`), the
floored log below 34 (for the floor 0, `N ≤ 2^33`), and the function returns
`g^max floor (log2Ceil N)`. -/
def MeaningLog2CeilExp (fl : ℕ) (rd : Reader) : List E → List E → Prop
  | [gN, _, _], rets =>
      ∃ N < 2 ^ 34, gN = gen ^ N ∧ max fl (log2Ceil N) < 34 ∧
        (∃ bp, ∀ j < 34, LoadHolds rd bp j (bitE (N.testBit j))) ∧
        (∃ ps, ∀ j ≤ 34, LoadHolds rd ps j (eOfNat (N % 2 ^ j))) ∧
        rets = [gen ^ max fl (log2Ceil N)]
  | _, _ => False

/-- The expansion of `log2_ceil_in_the_exponent`, calling `callee`. -/
def lcBody (callee : String) : List Stmt :=
  [.atom (.const (.n 3) (word (2 ^ 34) 0 0)), .atom (.hint (.allocDyn (.n 4) (.n 3))),
    .atom (.hint (.bitsExp (.n 0) 34 (.heap (.n 4) 0 34))),
    .call callee [.n 4, .n 1, .n 2] [.n 5, .n 6], .atom (.assertEq (.n 6) (.n 0)),
    .atom (.copy (.n 7) (.n 5)), .ret [.n 7]]

theorem log2_ceil_in_the_exponent_iff {name callee : String} {f : Fn} (fl : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = lcBody callee) {κ : ℕ}
    (Lm : MemImage κ) {gN lp sq : E}
    (hcallee : ∀ bits rets, coreProgram.Rel Lm.read callee [bits, lp, sq] rets ↔
      MeaningVerifyLog2Ceil fl Lm.read [bits, lp, sq] rets) (rets : List E) :
    coreProgram.Rel Lm.read name [gN, lp, sq] rets ↔
      MeaningLog2CeilExp fl Lm.read [gN, lp, sq] rets := by
  rw [rel_iff_sem hfind, hbody, hparams, lcBody]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  constructor
  · rintro ⟨σ, hp, h3, hcall, a6, h7, hret⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, -⟩ := hp
    obtain ⟨W, hW, hbits, hL, hps, hr⟩ := (hcallee _ _).mp hcall
    simp only [List.cons.injEq] at hr
    obtain ⟨h5, h6, -⟩ := hr
    refine ⟨W, hW, ?_, hL, ⟨σ (.n 4), hbits⟩, hps, ?_⟩
    · rw [← e_add_eq_zero_iff.mp a6, h6]
    · rw [← hret, h7, h5]
  · rintro ⟨N, hN, rfl, hL, ⟨bp, hbp⟩, hps, rfl⟩
    refine ⟨setl (Val.ofArgs [gen ^ N, lp, sq]) 3 [word (2 ^ 34) 0 0, bp, gen ^ max fl (log2Ceil N),
      gen ^ N, gen ^ max fl (log2Ceil N)], ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try b1_look)
    · exact (hcallee _ _).mpr ⟨N, hN, hbp, hL, hps, rfl⟩
    · exact e_add_self _

set_option maxRecDepth 100000 in
theorem log2_ceil_in_the_exponent_L0_L34_iff {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ)
    (Lm : MemImage κ) {gN lp sq : E} (ht : ExpTables Lm.read lp sq) (rets : List E) :
    coreProgram.Rel Lm.read "log2_ceil_in_the_exponent__L0_L34" [gN, lp, sq] rets ↔
      MeaningLog2CeilExp 0 Lm.read [gN, lp, sq] rets :=
  log2_ceil_in_the_exponent_iff 0 (Program.find?_of_indexOf? (j := 173) (by decide +kernel) rfl)
    rfl rfl Lm (fun _ rets => verify_log2_ceil_L0_L34_iff hκ hκ6 Lm ht rets) rets

set_option maxRecDepth 100000 in
theorem log2_ceil_in_the_exponent_L15_L34_iff {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ)
    (Lm : MemImage κ) {gN lp sq : E} (ht : ExpTables Lm.read lp sq) (rets : List E) :
    coreProgram.Rel Lm.read "log2_ceil_in_the_exponent__L15_L34" [gN, lp, sq] rets ↔
      MeaningLog2CeilExp 15 Lm.read [gN, lp, sq] rets :=
  log2_ceil_in_the_exponent_iff 15 (Program.find?_of_indexOf? (j := 176) (by decide +kernel) rfl)
    rfl rfl Lm (fun _ rets => verify_log2_ceil_L15_L34_iff hκ hκ6 Lm ht rets) rets

/-! ## Completeness at given buffers

The `HeapBuf`s the functions allocate are the caller's: for every pointer holding the honest
words, the meaning with that pointer gives the relation. -/

/-- `MeaningVerifyLog2Ceil` at the prefix-sum buffer `ps`. -/
def MeaningVerifyLog2CeilAt (fl : ℕ) (rd : Reader) (ps : E) : List E → List E → Prop
  | [bits, _, _], rets =>
      ∃ W < 2 ^ 34, (∀ j < 34, LoadHolds rd bits j (bitE (W.testBit j))) ∧
        max fl (log2Ceil W) < 34 ∧ (∀ j ≤ 34, LoadHolds rd ps j (eOfNat (W % 2 ^ j))) ∧
        rets = [gen ^ max fl (log2Ceil W), gen ^ W]
  | _, _ => False

theorem meaningVerifyLog2Ceil_of_at {fl : ℕ} {rd : Reader} {ps : E} {args rets : List E}
    (h : MeaningVerifyLog2CeilAt fl rd ps args rets) : MeaningVerifyLog2Ceil fl rd args rets := by
  match args, h with
  | [_, _, _], ⟨W, hW, hb, hL, hps, hr⟩ => exact ⟨W, hW, hb, hL, ⟨ps, hps⟩, hr⟩

theorem verify_log2_ceil_L0_L34_complete {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    {bits lp sq : E} (ht : ExpTables Lm.read lp sq) (ps : E) (rets : List E)
    (h : MeaningVerifyLog2CeilAt 0 Lm.read ps [bits, lp, sq] rets) :
    coreProgram.Rel Lm.read "verify_log2_ceil__L0_L34" [bits, lp, sq] rets :=
  (verify_log2_ceil_L0_L34_iff hκ hκ6 Lm ht rets).mpr (meaningVerifyLog2Ceil_of_at h)

theorem verify_log2_ceil_L15_L34_complete {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    {bits lp sq : E} (ht : ExpTables Lm.read lp sq) (ps : E) (rets : List E)
    (h : MeaningVerifyLog2CeilAt 15 Lm.read ps [bits, lp, sq] rets) :
    coreProgram.Rel Lm.read "verify_log2_ceil__L15_L34" [bits, lp, sq] rets :=
  (verify_log2_ceil_L15_L34_iff hκ hκ6 Lm ht rets).mpr (meaningVerifyLog2Ceil_of_at h)

/-- `MeaningLog2CeilExp` at the bit buffer `bp` and the callee's prefix-sum buffer `ps`. -/
def MeaningLog2CeilExpAt (fl : ℕ) (rd : Reader) (bp ps : E) : List E → List E → Prop
  | [gN, _, _], rets =>
      ∃ N < 2 ^ 34, gN = gen ^ N ∧ max fl (log2Ceil N) < 34 ∧
        (∀ j < 34, LoadHolds rd bp j (bitE (N.testBit j))) ∧
        (∀ j ≤ 34, LoadHolds rd ps j (eOfNat (N % 2 ^ j))) ∧
        rets = [gen ^ max fl (log2Ceil N)]
  | _, _ => False

theorem meaningLog2CeilExp_of_at {fl : ℕ} {rd : Reader} {bp ps : E} {args rets : List E}
    (h : MeaningLog2CeilExpAt fl rd bp ps args rets) : MeaningLog2CeilExp fl rd args rets := by
  match args, h with
  | [_, _, _], ⟨N, hN, hg, hL, hb, hps, hr⟩ => exact ⟨N, hN, hg, hL, ⟨bp, hb⟩, ⟨ps, hps⟩, hr⟩

theorem log2_ceil_in_the_exponent_L0_L34_complete {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ)
    (Lm : MemImage κ) {gN lp sq : E} (ht : ExpTables Lm.read lp sq) (bp ps : E) (rets : List E)
    (h : MeaningLog2CeilExpAt 0 Lm.read bp ps [gN, lp, sq] rets) :
    coreProgram.Rel Lm.read "log2_ceil_in_the_exponent__L0_L34" [gN, lp, sq] rets :=
  (log2_ceil_in_the_exponent_L0_L34_iff hκ hκ6 Lm ht rets).mpr (meaningLog2CeilExp_of_at h)

theorem log2_ceil_in_the_exponent_L15_L34_complete {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ)
    (Lm : MemImage κ) {gN lp sq : E} (ht : ExpTables Lm.read lp sq) (bp ps : E) (rets : List E)
    (h : MeaningLog2CeilExpAt 15 Lm.read bp ps [gN, lp, sq] rets) :
    coreProgram.Rel Lm.read "log2_ceil_in_the_exponent__L15_L34" [gN, lp, sq] rets :=
  (log2_ceil_in_the_exponent_L15_L34_iff hκ hκ6 Lm ht rets).mpr (meaningLog2CeilExp_of_at h)

end
end LeanVM.Guest.B1
