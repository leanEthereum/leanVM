/-
  LeanVM.Guest.B1.Selectors.ColumnSelector

  B1 for `column_selector`: its 33 specializations rebuild a column's offset from hinted
  base-16 digits below `2^32` and return the eq weight of its bits above `κ`, a nibble at a time
  off the opening point's tables.
-/

module

public import LeanVM.Guest.B1.Selectors.TableLemmas
public import LeanVM.Guest.B1.Placement.Common
public import LeanVM.Guest.CoreData

/-!
# `column_selector` (TRIAGE G #68)

`column_selector(offset, sel_eq, sel_g, κ)` (G:3357-3384) hints the `g`-power digits `g^u_k` of
`offset`'s exponent's nibbles `κ / 4 .. 7` (`hint_decompose_digits_exponent`) and, for each
(`j = κ / 4 + k`, the first `4j + 4 - κ` wide, the others four), range-checks `u_k < 16`, reads
the nibble's eq weight at `sel_eq·g^u` (offset `64j + 16(w - 1)`, the strided level-`w - 1`
table) and its share `g^(u·16^j)` at `sel_g·g^u` (offset `16j`), and multiplies them up; then
asserts the rebuilt power is `offset`. So `offset = g^o`, `o = Σ u_k 16^j` (`csDig`), below
`2^32` and a multiple of `16^(κ / 4)`; once `o` is a multiple of `2^κ` (the placement), the lowest
digit's bits below `κ` are zero and the strided table holds it, and the selector is the eq weight
of `o`'s bits `κ .. 31`.

The specialization `column_selector__L{κ}` is the template `csPre κ` (`csFound`, by kernel
evaluation for all `κ < 31`): the hint, nibble `k` from value `csC κ k` (`csNibT`), the assertion
and the copy of the selector.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## General lemmas -/

/-- The factor of bit `t` of an index: `1 + b·(1 + g^(2^t))`. -/
def csFactor (b : E) (t : ℕ) : E := 1 + b * (1 + gen ^ 2 ^ t)

theorem prod_range_four_blocks {M : Type} [CommMonoid M] (F : ℕ → M) (B : ℕ) : ∀ m : ℕ,
    ∏ k ∈ Finset.range m, ∏ s ∈ Finset.range 4, F (B + 4 * k + s) =
      ∏ i ∈ Finset.range (4 * m), F (B + i)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.prod_range_succ, prod_range_four_blocks F B m, show 4 * (m + 1) = 4 * m + 4 by ring,
      Finset.prod_range_add]
    refine congrArg _ (Finset.prod_congr rfl fun s _ => ?_)
    rw [Nat.add_assoc]

/-- `g` to the bits `κ, κ + 1, …` of `h`. -/
theorem prod_gen_pow_bits (κ : ℕ) (h : ℕ → Bool) : ∀ m : ℕ,
    ∏ i ∈ Finset.range m, gen ^ (2 ^ (κ + i) * (h i).toNat) = gen ^ (2 ^ κ * bitsVal h m)
  | 0 => by simp [bitsVal]
  | m + 1 => by
    rw [Finset.prod_range_succ, prod_gen_pow_bits κ h m, ← pow_add, bitsVal, Nat.mul_add,
      pow_add 2 κ m, Nat.mul_assoc]

/-- `bitsEq` as a product over the positions. -/
theorem bitsEq_eq_prod : ∀ {m : ℕ} {bs : List Bool} {zs zs1 : List E}, bs.length = m →
    zs.length = m → zs1.length = m →
    bitsEq bs zs zs1 = ∏ i ∈ Finset.range m,
      (if bs.getD i false then zs.getD i 0 else zs1.getD i 0)
  | 0, bs, zs, zs1, h1, _, _ => by rw [List.length_eq_zero_iff] at h1; subst h1; rfl
  | m + 1, b :: bs, z :: zs, z1 :: zs1, h1, h2, h3 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2 h3
    rw [bitsEq, List.zip_cons_cons, List.zip_cons_cons, List.map_cons, List.prod_cons, ← bitsEq,
      bitsEq_eq_prod h1 h2 h3, Finset.prod_range_succ', mul_comm]
    simp


theorem eqLevels_length {zs zs1 : List E} {n : ℕ} (h : zs.length = n) (h1 : zs1.length = n) :
    (eqLevels zs zs1).length = 2 ^ (n + 1) - 2 := by
  rw [eqLevels, h]
  have key : ∀ m ≤ n, ((List.range m).flatMap fun t ↦ eqTable (zs.take (t + 1))
      (zs1.take (t + 1))).length = 2 ^ (m + 1) - 2 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.flatMap_append, List.length_append, ih (by omega),
        List.flatMap_singleton, eqTable_length (n := m + 1) (by simp; omega) (by simp; omega),
        pow_succ 2 (m + 1)]
      have : 2 ≤ 2 ^ (m + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  exact key n le_rfl

theorem two_le_two_pow {w : ℕ} (hw : 1 ≤ w) : 2 ≤ 2 ^ w :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

theorem tbReadsAt_getD {rd : Reader} {p : E} {xs : List E} (h : TbReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-! ## Digits -/

/-- The base-16 number of digits `u 0, …, u (N - 1)`, low first. -/
def csDig (u : ℕ → ℕ) (N : ℕ) : ℕ := ∑ k ∈ Finset.range N, u k * 16 ^ k

theorem csDig_lt {u : ℕ → ℕ} : ∀ {N : ℕ}, (∀ k < N, u k < 16) → csDig u N < 2 ^ (4 * N)
  | 0, _ => by simp [csDig]
  | N + 1, h => by
    have ih := csDig_lt (N := N) fun k hk => h k (by omega)
    have hN := h N (by omega)
    rw [csDig, Finset.sum_range_succ, ← csDig, show 4 * (N + 1) = 4 * N + 4 by ring, pow_add,
      show 16 ^ N = 2 ^ (4 * N) by rw [pow_mul]; norm_num]
    nlinarith

/-- **The digits are the nibbles**: bit `4k + t` of the number is bit `t` of digit `k`. -/
theorem testBit_csDig {u : ℕ → ℕ} : ∀ {N : ℕ}, (∀ k < N, u k < 16) → ∀ k t, t < 4 →
    (csDig u N).testBit (4 * k + t) = (decide (k < N) && (u k).testBit t)
  | 0, _, k, t, _ => by simp [csDig]
  | N + 1, h, k, t, ht => by
    have hlt := csDig_lt (N := N) fun k hk => h k (by omega)
    rw [csDig, Finset.sum_range_succ, ← csDig, add_comm,
      show u N * 16 ^ N = 2 ^ (4 * N) * u N by rw [pow_mul]; norm_num; ring,
      Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hk : k < N
    · rw [ite_eq_left (by omega), testBit_csDig (fun k hk => h k (by omega)) k t ht]
      simp [hk, show k < N + 1 by omega]
    · rw [ite_eq_right (by omega)]
      by_cases hkN : k = N
      · subst hkN; simp
      · have hu := h N (by omega)
        have : (u N).testBit (4 * k + t - 4 * N) = false := by
          apply Nat.testBit_lt_two_pow
          calc u N < 2 ^ 4 := by omega
            _ ≤ 2 ^ (4 * k + t - 4 * N) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [this]; simp; omega

/-- The digits' shares multiply to `g` to the number. -/
theorem prod_gen_pow_csDig (u : ℕ → ℕ) (b : ℕ) : ∀ N : ℕ,
    ∏ k ∈ Finset.range N, gen ^ (u k * 16 ^ (b + k)) = gen ^ (16 ^ b * csDig u N)
  | 0 => by simp [csDig]
  | N + 1 => by
    rw [Finset.prod_range_succ, prod_gen_pow_csDig u b N, ← pow_add]
    congr 1
    simp only [csDig, Finset.sum_range_succ, pow_add]; ring

/-! ## The template -/

/-- The number of digits of `column_selector__L{κ}`. -/
def csN (κ : ℕ) : ℕ := 8 - κ / 4

/-- The width of nibble `k`. -/
def csW (κ k : ℕ) : ℕ := if k = 0 then 4 * (κ / 4) + 4 - κ else 4

/-- The first value of nibble `k`, past the digits `3 .. 3 + csN κ - 1`. -/
def csC (κ k : ℕ) : ℕ := if k = 0 then 3 + csN κ else 3 + csN κ + 8 + 10 * (k - 1)

/-- The selector product after nibble `k`. -/
def csSel (κ k : ℕ) : ℕ := if k = 0 then csC κ 0 + 5 else csC κ k + 6

/-- The rebuilt product after nibble `k`. -/
def csRb (κ k : ℕ) : ℕ := if k = 0 then csC κ 0 + 7 else csC κ k + 9

/-- `g^15`, the digits' range check (`assert log(d) < 16`). -/
abbrev w15 : E := word 32768 0

theorem word_g15 : w15 = ofK (Parameters.addressOfIndex 15) := by
  rw [w15, tb_word_eOfNat]
  show ofK (K.ofBits 32768) = ofK (Parameters.addressOfIndex 15)
  rw [show K.ofBits 32768 = Parameters.addressOfIndex 15 by decide +kernel]

/-- Nibble `k` of `column_selector__L{κ}`: the digit's range check, the eq weight at
`sel_eq·g^u`, the share at `sel_g·g^u`, the running products. -/
def csNibT (κ k : ℕ) : List Stmt :=
  let j := κ / 4 + k
  let w := csW κ k
  let c := csC κ k
  let d := 3 + k
  [.atom (.const (.n c) w15), .atom (.rangeCheck (.n d) (.n (c + 1)) (.n (c + 2)) (.n (c + 3)) (.n c)),
    .atom (.mul (.n (c + 4)) (.n 1) (.n d)),
    .atom (.load (.n (c + 5)) (.n (c + 4)) (64 * j + 16 * (w - 1)))] ++
  if k = 0 then
    [.atom (.mul (.n (c + 6)) (.n 2) (.n d)), .atom (.load (.n (c + 7)) (.n (c + 6)) (16 * j))]
  else
    [.atom (.mul (.n (c + 6)) (.n (csSel κ (k - 1))) (.n (c + 5))),
      .atom (.mul (.n (c + 7)) (.n 2) (.n d)), .atom (.load (.n (c + 8)) (.n (c + 7)) (16 * j)),
      .atom (.mul (.n (c + 9)) (.n (csRb κ (k - 1))) (.n (c + 8)))]

/-- The hint of the digits, at values `3 .. 3 + csN κ - 1`. -/
def csHint (κ : ℕ) : Stmt :=
  .atom (.hint (.digitsExp (.n 0) 32 (csN κ) 4 (4 * (κ / 4)) none
    (.stack ((List.range (csN κ)).map fun k ↦ .n (3 + k)))))

/-- `column_selector__L{κ}`'s statements before its `ret`, the hint first. -/
def csPre (κ : ℕ) : List Stmt :=
  csHint κ :: if κ = 32 then
    [.atom (.const (.n 3) (word 1 0)), .atom (.assertEq (.n 3) (.n 0)),
      .atom (.const (.n 4) (word 1 0))]
  else ((List.range (csN κ)).map (csNibT κ)).flatten ++
    [.atom (.assertEq (.n (csRb κ (csN κ - 1))) (.n 0)),
      .atom (.copy (.n (csC κ (csN κ))) (.n (csSel κ (csN κ - 1))))]

/-- The value `column_selector__L{κ}` returns. -/
def csRet (κ : ℕ) : ℕ := if κ = 32 then 4 else csC κ (csN κ)

/-- The function found by name is the template. -/
noncomputable def csCheck (κ : ℕ) : Bool :=
  match coreProgram.find? (lName "column_selector" κ) with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2]) &&
      tbStmtsEqb fn.body (csPre κ ++ [.ret [.n (csRet κ)]])
  | none => false

theorem csCheck_all : (List.range 31).all csCheck = true := by decide +kernel

theorem csFound {κ : ℕ} (hκ : κ < 31) : ∃ fn : Fn,
    coreProgram.find? (lName "column_selector" κ) = some fn ∧ fn.params = [.n 0, .n 1, .n 2] ∧
      fn.body = csPre κ ++ [.ret [.n (csRet κ)]] := by
  have h := List.all_eq_true.mp csCheck_all κ (List.mem_range.mpr hκ)
  unfold csCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem csNibT_noRet (κ k : ℕ) : Stmt.noRetList (csNibT κ k) = true := by
  unfold csNibT; split <;> rfl

theorem csPre_noRet (κ : ℕ) : Stmt.noRetList (csPre κ) = true := by
  unfold csPre
  split
  · rfl
  · show Stmt.noRetList (_ ++ _) = true
    rw [tb_noRetList_append, tb_noRetList_flatten_range _ _ (csNibT_noRet κ)]; rfl

theorem csW_bounds (κ k : ℕ) : 1 ≤ csW κ k ∧ csW κ k ≤ 4 := by
  unfold csW; split <;> omega

/-! ## A nibble -/

section Sem

variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
variable {C : CallRel} {σ : Val} {kret : List E → Prop}

include hμ in
/-- **A nibble**: its digit `g^u`, `u < 16`; the eq weight and the share it reads, at `g^u` past
the tables' offsets; the running products. -/
theorem holds_csNib {κ k : ℕ} (h : Stmt.HoldsList C Lm.read σ (csNibT κ k) True kret) :
    ∃ u < 16, σ (.n (3 + k)) = gen ^ u ∧
      ∃ xe xg, LoadHolds Lm.read (σ (.n 1)) (u + (64 * (κ / 4 + k) + 16 * (csW κ k - 1))) xe ∧
        LoadHolds Lm.read (σ (.n 2)) (u + 16 * (κ / 4 + k)) xg ∧
        σ (.n (csSel κ k)) = (if k = 0 then 1 else σ (.n (csSel κ (k - 1)))) * xe ∧
        σ (.n (csRb κ k)) = (if k = 0 then 1 else σ (.n (csRb κ (k - 1)))) * xg := by
  unfold csNibT at h
  rw [tb_holdsList_append_noRet rfl] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  obtain ⟨hc, ⟨r1, r2, r3⟩, hm, hl⟩ := h1
  obtain ⟨u, hu, hd⟩ := tb_rc_sound' hμ Lm (K := 16) (by omega) (by norm_num)
    (by rw [hc, word_g15]) r1 r2 r3
  refine ⟨u, hu, hd, ?_⟩
  rw [hm, hd, tb_loadHolds_mul_gen_pow] at hl
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h2
    obtain ⟨hm2, hl2⟩ := h2
    rw [hm2, hd, tb_loadHolds_mul_gen_pow] at hl2
    refine ⟨_, _, hl, hl2, ?_, ?_⟩ <;> simp [csSel, csRb]
  · simp only [hk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h2
    obtain ⟨hs, hm2, hl2, hr⟩ := h2
    rw [hm2, hd, tb_loadHolds_mul_gen_pow] at hl2
    exact ⟨_, _, hl, hl2, by simp only [csSel, hk, ↓reduceIte]; exact hs,
      by simp only [csRb, hk, ↓reduceIte]; exact hr⟩

end Sem

/-! ## The selector's product -/

/-- A product over `Ico a 4` as one over `range 4`. -/
theorem prod_Ico_four {M : Type} [CommMonoid M] (F : ℕ → M) (a : ℕ) :
    ∏ t ∈ Finset.Ico a 4, F t = ∏ t ∈ Finset.range 4, if a ≤ t then F t else 1 := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  congr 1
  ext t; simp [Finset.mem_Ico, Finset.mem_filter]; omega

/-- The nibbles cover the coordinates `κ .. 31`: with `H` trivial below `κ`, the product over the
nibbles from `κ / 4` is the one over `κ .. 31`. -/
theorem cs_cover {M : Type} [CommMonoid M] (G : ℕ → M) {κ : ℕ} (hκ : κ < 32) :
    ∏ k ∈ Finset.range (csN κ), ∏ t ∈ Finset.range 4,
        (if κ ≤ 4 * (κ / 4) + 4 * k + t then G (4 * (κ / 4) + 4 * k + t) else 1) =
      ∏ i ∈ Finset.range (32 - κ), G (κ + i) := by
  rw [prod_range_four_blocks (fun i ↦ if κ ≤ i then G i else 1) (4 * (κ / 4)) (csN κ),
    show 4 * csN κ = (κ - 4 * (κ / 4)) + (32 - κ) by unfold csN; omega, Finset.prod_range_add]
  rw [Finset.prod_eq_one fun i hi => by
    have := Finset.mem_range.mp hi; rw [ite_eq_right (by omega)], one_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ite_eq_left (by omega)]; congr 1; omega

/-! ## The number of the digits and its selector -/

section Math

variable {κ : ℕ} (hκ : κ < 32) {u : ℕ → ℕ} (hu : ∀ k < csN κ, u k < 16)
include hκ hu

omit hκ in
/-- Bit `4(κ/4 + k) + t` of the digits' number is bit `t` of digit `k`. -/
theorem cs_bit {k : ℕ} (hk : k < csN κ) {t : ℕ} (ht : t < 4) :
    (16 ^ (κ / 4) * csDig u (csN κ)).testBit (4 * (κ / 4) + 4 * k + t) = (u k).testBit t := by
  rw [show 16 ^ (κ / 4) = 2 ^ (4 * (κ / 4)) by rw [pow_mul]; norm_num, Nat.testBit_two_pow_mul,
    show 4 * (κ / 4) + 4 * k + t - 4 * (κ / 4) = 4 * k + t by omega, testBit_csDig hu k t ht]
  simp only [hk, decide_true, Bool.true_and, ge_iff_le,
    show 4 * (κ / 4) ≤ 4 * (κ / 4) + 4 * k + t by omega]

omit hκ in
/-- **The strided table holds every digit**: digit `k` is a multiple of `2^(3 - (w_k - 1))`, the
lowest one's bits below `κ` being zero once the number is a multiple of `2^κ`. -/
theorem cs_dvd (hal : 2 ^ κ ∣ 16 ^ (κ / 4) * csDig u (csN κ)) (k : ℕ) (hk : k < csN κ) :
    2 ^ (3 - (csW κ k - 1)) ∣ u k := by
  have hlev : 3 - (csW κ k - 1) = if k = 0 then κ - 4 * (κ / 4) else 0 := by
    unfold csW; split <;> omega
  rw [hlev]
  split
  · rename_i hk0
    subst hk0
    apply Nat.dvd_of_mod_eq_zero
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < κ - 4 * (κ / 4)
    · simp only [hi, decide_true, Bool.true_and]
      rw [← cs_bit hu hk (show i < 4 by omega), Nat.mul_zero, Nat.add_zero]
      obtain ⟨m, hm⟩ := hal
      rw [hm, Nat.testBit_two_pow_mul]
      simp only [ge_iff_le, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
      exact Or.inl (by omega)
    · simp [hi]
  · simp

/-- **The selector**: the digits' eq weights off the strided tables multiply to the eq weight of
the number's bits `κ .. 31`. -/
theorem cs_sel_prod {p p1 : List E}
    (hp : p.length = 32) (hp1 : p1.length = 32) :
    ∏ k ∈ Finset.range (csN κ), selEqEntry p p1 (κ / 4 + k) (csW κ k - 1) (u k) =
      bitsEq ((List.range (32 - κ)).map fun i ↦ (16 ^ (κ / 4) * csDig u (csN κ)).testBit (κ + i))
        (p.drop κ) (p1.drop κ) := by
  let G : ℕ → E := fun i ↦
    if (16 ^ (κ / 4) * csDig u (csN κ)).testBit i then p.getD i 0 else p1.getD i 0
  have hxe : ∀ k < csN κ, selEqEntry p p1 (κ / 4 + k) (csW κ k - 1) (u k) =
      ∏ t ∈ Finset.range 4, (if κ ≤ 4 * (κ / 4) + 4 * k + t then G (4 * (κ / 4) + 4 * k + t)
        else 1) := by
    intro k hk
    have hlev : 3 - (csW κ k - 1) = if k = 0 then κ - 4 * (κ / 4) else 0 := by
      unfold csW; split <;> omega
    rw [selEqEntry, prod_Ico_four, hlev]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    have hc : ((if k = 0 then κ - 4 * (κ / 4) else 0) ≤ t) ↔ κ ≤ 4 * (κ / 4) + 4 * k + t := by
      split <;> omega
    by_cases hct : κ ≤ 4 * (κ / 4) + 4 * k + t
    · rw [ite_eq_left (hc.mpr hct), ite_eq_left hct]
      simp only [G]
      rw [cs_bit hu hk ht', show 4 * (κ / 4 + k) + t = 4 * (κ / 4) + 4 * k + t by ring]
    · rw [ite_eq_right (fun h => hct (hc.mp h)), ite_eq_right hct]
  rw [Finset.prod_congr rfl (fun k hk => hxe k (Finset.mem_range.mp hk)), cs_cover G hκ,
    bitsEq_eq_prod (m := 32 - κ) (by simp) (by simp [hp]) (by simp [hp1])]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have e1 : ((List.range (32 - κ)).map fun i ↦
      (16 ^ (κ / 4) * csDig u (csN κ)).testBit (κ + i)).getD i false =
      (16 ^ (κ / 4) * csDig u (csN κ)).testBit (κ + i) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range]
  have e2 : ∀ q : List E, (q.drop κ).getD i 0 = q.getD (κ + i) 0 := fun q => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  rw [e1, e2, e2]

end Math

/-- **`column_selector` is sound**. -/
theorem column_selector_sound {κ : ℕ} (hκ : κ < 31) {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
    {args rets : List E} (h : coreProgram.Rel Lm.read (lName "column_selector" κ) args rets) :
    ColSelOut κ Lm.read args rets := by
  obtain ⟨fn, hf, hp, hb⟩ := csFound hκ
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb (csPre_noRet κ) args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar hret
  subst hpar hret
  simp only [ColSelOut]
  intro hG
  by_cases h32 : κ = 32
  · subst h32
    simp only [csPre, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
      true_and] at hpre
    obtain ⟨h1, h2, h3⟩ := hpre
    refine ⟨0, by norm_num, dvd_zero _, ?_, fun _ p p1 _ _ _ => ?_⟩
    · rw [pow_zero]; rw [h1, tb_word_one] at h2; exact (e_add_eq_zero_iff.mp h2).symm
    · simp only [csRet, ↓reduceIte, h3, tb_word_one]; rfl
  have hκ' : κ < 32 := by omega
  simp only [csPre, h32, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    true_and] at hpre
  rw [holdsList_append, holdsList_flatten _ (fun b hb => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact csNibT_noRet κ t)] at hpre
  obtain ⟨hnibs, htail⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
  obtain ⟨hassert, hcopy⟩ := htail
  set N := csN κ with hNdef
  set b := κ / 4 with hbdef
  have hN1 : 1 ≤ N := by simp only [hNdef, csN]; omega
  have hNb : b + N = 8 := by simp only [hNdef, hbdef, csN]; omega
  have hNib : ∀ k < N, _ := fun k hk => holds_csNib hμ Lm (C := coreProgram.Rel Lm.read)
    (σ := σ) (kret := fun rs => rs = [σ (.n (csRet κ))]) (κ := κ) (k := k)
    (hnibs _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
  choose u hu hd xe xg hxe hxg hsel hrb using hNib
  let u' : ℕ → ℕ := fun k ↦ if hk : k < N then u k hk else 0
  have hu' : ∀ k < N, u' k < 16 := fun k hk => by simp only [u', hk, ↓reduceDIte]; exact hu k hk
  let xe' : ℕ → E := fun k ↦ if hk : k < N then xe k hk else 1
  let xg' : ℕ → E := fun k ↦ if hk : k < N then xg k hk else 1
  have hS : ∀ k < N, σ (.n (csSel κ k)) = ∏ m ∈ Finset.range (k + 1), xe' m := by
    intro k hk
    induction k with
    | zero => rw [hsel 0 hk]; simp [xe', hk]
    | succ k ih =>
      rw [hsel (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xe', hk]
  have hR : ∀ k < N, σ (.n (csRb κ k)) = ∏ m ∈ Finset.range (k + 1), xg' m := by
    intro k hk
    induction k with
    | zero => rw [hrb 0 hk]; simp [xg', hk]
    | succ k ih =>
      rw [hrb (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xg', hk]
  -- the shares
  have hxg' : ∀ k < N, xg' k = gen ^ (u' k * 16 ^ (b + k)) := by
    intro k hk
    have h1 := hG (b + k) (show b + k < 8 by omega) (u k hk) (hu k hk)
    have h2 := hxg k hk
    rw [show u k hk + 16 * (b + k) = 16 * (b + k) + u k hk by omega] at h2
    simp only [xg', u', hk, ↓reduceDIte]
    exact tb_loadHolds_unique h2 h1
  let o := 16 ^ b * csDig u' N
  have hob : o = 2 ^ (4 * b) * csDig u' N := by
    simp only [o, pow_mul]; norm_num
  refine ⟨o, ?_, ?_, ?_, fun hal p p1 hp hp1 hE => ?_⟩
  · have := csDig_lt hu'
    rw [hob]
    calc 2 ^ (4 * b) * csDig u' N < 2 ^ (4 * b) * 2 ^ (4 * N) :=
          Nat.mul_lt_mul_of_pos_left this (Nat.two_pow_pos _)
      _ = 2 ^ 32 := by rw [← pow_add, show 4 * b + 4 * N = 32 by omega]
  · rw [hob]; exact Dvd.intro _ rfl
  · have e0 := e_add_eq_zero_iff.mp hassert
    rw [← e0, hR (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxg' k (Finset.mem_range.mp hk)),
      prod_gen_pow_csDig]
  · -- the selector
    have hxe' : ∀ k < N, xe' k = selEqEntry p p1 (b + k) (csW κ k - 1) (u' k) := by
      intro k hk
      obtain ⟨hw1, hw4⟩ := csW_bounds κ k
      have h1 := hE (b + k) (show b + k < 8 by omega) (csW κ k - 1) (by omega) (u' k) (hu' k hk)
        (cs_dvd hu' hal k hk)
      have h2 := hxe k hk
      rw [show u k hk + (64 * (κ / 4 + k) + 16 * (csW κ k - 1)) =
        64 * (b + k) + 16 * (csW κ k - 1) + u' k by simp only [u', hk, ↓reduceDIte, hbdef]; omega]
        at h2
      simp only [xe', hk, ↓reduceDIte]
      exact tb_loadHolds_unique h2 h1
    rw [show csRet κ = csC κ N by simp only [csRet, h32, ↓reduceIte, hNdef], hcopy,
      hS (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxe' k (Finset.mem_range.mp hk))]
    exact cs_sel_prod hκ' hu' hp hp1

theorem column_selector_holds : column_selector_Spec :=
  fun _ hκ _ hμ Lm _ _ h => column_selector_sound hκ hμ Lm h

end
end LeanVM.Guest.B1.Tables
