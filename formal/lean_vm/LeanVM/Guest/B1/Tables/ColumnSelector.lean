/-
  LeanVM.Guest.B1.Tables.ColumnSelector

  B1 for `column_selector`: a committed column's selector at the opening point, and the
  certificate that its offset is aligned to its size, at each of its 29 specializations.
-/

module

public import LeanVM.Guest.B1.Tables.Padding

/-!
# `column_selector` (TRIAGE #42)

`column_selector(offset, point, κ)` (G:2002-2017) hints the 28 bits of the exponent of
`offset = g^off`, pins those from `κ` on Boolean, rebuilds `g^off` from them alone (so `off` is
below `2^28` and a multiple of `2^κ`) and returns `Π_{κ ≤ k < 28} (1 + bit_k + point[k])`, the
column's `Placement.eqAbove` (V:870) on a point padded to 28 coordinates.

The expansion at `κ ≤ 27` is `csBody κ`: the hint, the first factor pair, `27 - κ` later pairs,
the check and the return; it is equal to each specialization `__L0` .. `__L27` by kernel
evaluation. `__L28` reads nothing and returns `1`, after checking `offset = 1`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- `1 + g^(2^k)`, folded. -/
def csC (k : ℕ) : E := word (gSquaresBits.getD k 0 ^^^ 1) 0 0

theorem csC_eq {k : ℕ} (hk : k < 34) : csC k = gen ^ 2 ^ k + 1 := by
  rw [csC, word_eOfNat, eOfNat_xor, eOfNat_gSquaresBits k hk, eOfNat_one]

/-- The hint: the 28 bits of `off`, at values `2 .. 29`. -/
def csHint : Stmt :=
  .atom (.hint (.bitsExp (.n 0) 28 (.stack ((List.range 28).map fun k => .n (2 + k)))))

/-- The first pair, at `k = κ`, from value `30`. -/
def csFirst (κ : ℕ) : List Stmt :=
  [.atom (.mul (.n (2 + κ)) (.n (2 + κ)) (.n (2 + κ))), .atom (.const (.n 30) (word 1 0 0)),
    .atom (.const (.n 31) (csC κ)), .atom (.mul (.n 32) (.n (2 + κ)) (.n 31)),
    .atom (.add (.n 33) (.n 30) (.n 32)), .atom (.const (.n 34) (word 1 0 0)),
    .atom (.add (.n 35) (.n 34) (.n (2 + κ))), .atom (.load (.n 36) (.n 1) κ),
    .atom (.add (.n 37) (.n 35) (.n 36))]

/-- The rebuilt offset after pair `i`, by its value number. -/
def csReb (i : ℕ) : ℕ := if i = 0 then 33 else 32 + 10 * i

/-- Pair `i ≥ 1`, at `k = κ + i`, from value `28 + 10·i`. -/
def csIter (κ i : ℕ) : List Stmt :=
  [.atom (.mul (.n (2 + κ + i)) (.n (2 + κ + i)) (.n (2 + κ + i))),
    .atom (.const (.n (28 + 10 * i)) (word 1 0 0)),
    .atom (.const (.n (29 + 10 * i)) (csC (κ + i))),
    .atom (.mul (.n (30 + 10 * i)) (.n (2 + κ + i)) (.n (29 + 10 * i))),
    .atom (.add (.n (31 + 10 * i)) (.n (28 + 10 * i)) (.n (30 + 10 * i))),
    .atom (.mul (.n (32 + 10 * i)) (.n (csReb (i - 1))) (.n (31 + 10 * i))),
    .atom (.const (.n (33 + 10 * i)) (word 1 0 0)),
    .atom (.add (.n (34 + 10 * i)) (.n (33 + 10 * i)) (.n (2 + κ + i))),
    .atom (.load (.n (35 + 10 * i)) (.n 1) (κ + i)),
    .atom (.add (.n (36 + 10 * i)) (.n (34 + 10 * i)) (.n (35 + 10 * i))),
    .atom (.mul (.n (37 + 10 * i)) (.n (27 + 10 * i)) (.n (36 + 10 * i)))]

/-- The expansion of `column_selector` at `κ ≤ 27`. -/
def csBody (κ : ℕ) : List Stmt :=
  [csHint] ++ csFirst κ ++ ((List.range (27 - κ)).map fun i => csIter κ (i + 1)).flatten ++
    [.atom (.assertEq (.n (csReb (27 - κ))) (.n 0)),
      .atom (.copy (.n (38 + 10 * (27 - κ))) (.n (37 + 10 * (27 - κ)))),
      .ret [.n (38 + 10 * (27 - κ))]]

/-- The expansion at `κ = 28`. -/
def csBody28 : List Stmt :=
  [csHint, .atom (.const (.n 30) (word 1 0 0)), .atom (.assertEq (.n 30) (.n 0)),
    .atom (.const (.n 31) (word 1 0 0)), .ret [.n 31]]

theorem core143_body : Fn.body Data.core143 = csBody 0 := stmtsEqb_sound (by decide +kernel)
theorem core144_body : Fn.body Data.core144 = csBody 1 := stmtsEqb_sound (by decide +kernel)
theorem core145_body : Fn.body Data.core145 = csBody 2 := stmtsEqb_sound (by decide +kernel)
theorem core146_body : Fn.body Data.core146 = csBody 3 := stmtsEqb_sound (by decide +kernel)
theorem core147_body : Fn.body Data.core147 = csBody 4 := stmtsEqb_sound (by decide +kernel)
theorem core148_body : Fn.body Data.core148 = csBody 5 := stmtsEqb_sound (by decide +kernel)
theorem core149_body : Fn.body Data.core149 = csBody 6 := stmtsEqb_sound (by decide +kernel)
theorem core150_body : Fn.body Data.core150 = csBody 7 := stmtsEqb_sound (by decide +kernel)
theorem core151_body : Fn.body Data.core151 = csBody 8 := stmtsEqb_sound (by decide +kernel)
theorem core152_body : Fn.body Data.core152 = csBody 9 := stmtsEqb_sound (by decide +kernel)
theorem core153_body : Fn.body Data.core153 = csBody 10 := stmtsEqb_sound (by decide +kernel)
theorem core154_body : Fn.body Data.core154 = csBody 11 := stmtsEqb_sound (by decide +kernel)
theorem core155_body : Fn.body Data.core155 = csBody 12 := stmtsEqb_sound (by decide +kernel)
theorem core156_body : Fn.body Data.core156 = csBody 13 := stmtsEqb_sound (by decide +kernel)
theorem core157_body : Fn.body Data.core157 = csBody 14 := stmtsEqb_sound (by decide +kernel)
theorem core158_body : Fn.body Data.core158 = csBody 15 := stmtsEqb_sound (by decide +kernel)
theorem core159_body : Fn.body Data.core159 = csBody 16 := stmtsEqb_sound (by decide +kernel)
theorem core160_body : Fn.body Data.core160 = csBody 17 := stmtsEqb_sound (by decide +kernel)
theorem core161_body : Fn.body Data.core161 = csBody 18 := stmtsEqb_sound (by decide +kernel)
theorem core162_body : Fn.body Data.core162 = csBody 19 := stmtsEqb_sound (by decide +kernel)
theorem core163_body : Fn.body Data.core163 = csBody 20 := stmtsEqb_sound (by decide +kernel)
theorem core164_body : Fn.body Data.core164 = csBody 21 := stmtsEqb_sound (by decide +kernel)
theorem core165_body : Fn.body Data.core165 = csBody 22 := stmtsEqb_sound (by decide +kernel)
theorem core166_body : Fn.body Data.core166 = csBody 23 := stmtsEqb_sound (by decide +kernel)
theorem core167_body : Fn.body Data.core167 = csBody 24 := stmtsEqb_sound (by decide +kernel)
theorem core168_body : Fn.body Data.core168 = csBody 25 := stmtsEqb_sound (by decide +kernel)
theorem core169_body : Fn.body Data.core169 = csBody 26 := stmtsEqb_sound (by decide +kernel)
theorem core170_body : Fn.body Data.core170 = csBody 27 := stmtsEqb_sound (by decide +kernel)

theorem core171_body : Fn.body Data.core171 = csBody28 := stmtsEqb_sound (by decide +kernel)

/-! ## The meaning -/

/-- **`column_selector(offset, point, κ)`** (G:2002-2017; TRIAGE #42): `offset = g^off` for an
`off < 2^28` aligned to `2^κ`, the point's words `zs[k]` lie at `point` for `κ ≤ k < 28`, and the
function returns the column's selector `eqAbove` (V:870) at `zs`. -/
def MeaningColumnSelector (κ : ℕ) (rd : Reader) : List E → List E → Prop
  | [offset, point], rets => ∃ off zs, off < 2 ^ 28 ∧ 2 ^ κ ∣ off ∧ offset = gen ^ off ∧
      zs.length = 28 ∧ (∀ k (hk : k < zs.length), κ ≤ k → LoadHolds rd point k zs[k]) ∧
      rets = [({ vars := κ, index := off } : Placement).eqAbove zs]
  | _, _ => False

/-! ## Products -/

theorem eqEval_take (as bs : List E) :
    ∀ j ≤ as.length, j ≤ bs.length →
      eqEval (as.take j) (bs.take j) = ∏ i ∈ Finset.range j, (1 + as.getD i 0 + bs.getD i 0)
  | 0, _, _ => rfl
  | j + 1, ha, hb => by
    rw [eqEval_take_succ as bs j (by omega) (by omega), eqEval_take as bs j (by omega) (by omega),
      Finset.prod_range_succ, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)]

/-- **`eqAbove` as a product** over the coordinates from `κ`, for a point of 28. -/
theorem eqAbove_eq_prod {κ off : ℕ} (zs : List E) (hzs : zs.length = 28) :
    ({ vars := κ, index := off } : Placement).eqAbove zs =
      ∏ t ∈ Finset.range (28 - κ), (1 + bitE (off.testBit (κ + t)) + zs.getD (κ + t) 0) := by
  simp only [Placement.eqAbove, Nat.zero_add, Nat.sub_zero, hzs]
  have hl : (selectorPoint (off >>> κ) (28 - κ)).length = 28 - κ := by simp [selectorPoint]
  have hr : (zs.drop κ).length = 28 - κ := by simp [hzs]
  have h := eqEval_take (selectorPoint (off >>> κ) (28 - κ)) (zs.drop κ) (28 - κ) (by omega)
    (by omega)
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at h
  rw [h]
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  have h2 : (List.drop κ zs).getD t 0 = zs.getD (κ + t) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [h2]
  congr 2
  simp only [selectorPoint, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht',
    Option.map_some, Option.getD_some, eOfNat_shift_mod, Nat.testBit_shiftRight]

/-- The rebuilt offset of bits Boolean from `κ`: a power of `g` aligned to `2^κ`. -/
theorem cs_rebuild {κ : ℕ} (hκ : κ ≤ 28) {b : ℕ → E}
    (hb : ∀ t < 28 - κ, b (κ + t) * b (κ + t) = b (κ + t)) :
    ∃ off < 2 ^ 28, 2 ^ κ ∣ off ∧
      ∏ t ∈ Finset.range (28 - κ), (1 + b (κ + t) * (gen ^ 2 ^ (κ + t) + 1)) = gen ^ off ∧
      ∀ t < 28 - κ, b (κ + t) = bitE (off.testBit (κ + t)) := by
  set b' : ℕ → E := fun k => if k < κ then 0 else b k
  have hb' : ∀ j < 28, b' j * b' j = b' j := fun j hj => by
    simp only [b']
    split
    · simp
    · have := hb (j - κ) (by omega); rwa [show κ + (j - κ) = j by omega] at this
  have hprod := prod_gen_pow_of_bool hb'
  have hsplit : ∏ j ∈ Finset.range 28, (1 + b' j * (gen ^ 2 ^ j + 1)) =
      ∏ t ∈ Finset.range (28 - κ), (1 + b' (κ + t) * (gen ^ 2 ^ (κ + t) + 1)) := by
    conv_lhs => rw [show (28 : ℕ) = κ + (28 - κ) by omega]
    rw [Finset.prod_range_add, Finset.prod_eq_one (fun j hj => by
      simp [b', Finset.mem_range.mp hj]), one_mul]
  rw [hsplit] at hprod
  set off := bitsVal (fun j => decide (b' j = 1)) 28
  have hoff : off < 2 ^ 28 := bitsVal_lt _ _
  have htb : ∀ k, off.testBit k = (decide (k < 28) && decide (b' k = 1)) := fun k => by
    simp only [off, testBit_bitsVal]
  refine ⟨off, hoff, ?_, ?_, fun t ht => ?_⟩
  · refine Nat.dvd_of_mod_eq_zero (Nat.eq_of_testBit_eq fun i => ?_)
    rw [Nat.testBit_mod_two_pow, htb, Nat.zero_testBit]
    by_cases hi : i < κ <;> simp [hi, b']
  · rw [← hprod]
    exact Finset.prod_congr rfl fun t ht => by
      simp [b', show ¬ κ + t < κ by omega]
  · rw [htb]
    simp only [b', show ¬ κ + t < κ by omega, ↓reduceIte, show κ + t < 28 by omega, decide_true,
      Bool.true_and]
    exact bitE_of_mul_self (hb t ht)

/-- **Completeness of the rebuild**: an aligned `off < 2^28` is the product over its bits from
`κ`. -/
theorem cs_rebuild_complete {κ off : ℕ} (hoff : off < 2 ^ 28) (hdvd : 2 ^ κ ∣ off) :
    ∏ t ∈ Finset.range (28 - κ), (1 + bitE (off.testBit (κ + t)) * (gen ^ 2 ^ (κ + t) + 1)) =
      gen ^ off := by
  have hlow : ∀ j < κ, off.testBit j = false := fun j hj => by
    obtain ⟨q, rfl⟩ := hdvd
    rw [mul_comm, Nat.testBit_mul_two_pow]; simp [show ¬ κ ≤ j by omega]
  rcases Nat.lt_or_ge 28 κ with h | h
  · have : off = 0 := by
      obtain ⟨q, rfl⟩ := hdvd
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · rfl
      · have : 2 ^ 28 < 2 ^ κ * q :=
          lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) h) (Nat.le_mul_of_pos_right _ hq)
        omega
    simp [this, show 28 - κ = 0 by omega]
  have := prod_bitE_gen_pow off.testBit 28
  rw [bitsVal_testBit hoff] at this
  have hsplit : ∏ j ∈ Finset.range 28, (1 + bitE (off.testBit j) * (gen ^ 2 ^ j + 1)) =
      ∏ t ∈ Finset.range (28 - κ), (1 + bitE (off.testBit (κ + t)) * (gen ^ 2 ^ (κ + t) + 1)) := by
    conv_lhs => rw [show (28 : ℕ) = κ + (28 - κ) by omega]
    rw [Finset.prod_range_add, Finset.prod_eq_one (fun j hj => by
      simp [hlow j (Finset.mem_range.mp hj), bitE]), one_mul]
  rw [← hsplit, this]

/-! ## The template's conditions -/

/-- The running rebuilt offset, factor by factor. -/
def csRebP (b : ℕ → E) (κ : ℕ) : ℕ → E
  | 0 => word 1 0 0 + b κ * csC κ
  | i + 1 => csRebP b κ i * (word 1 0 0 + b (κ + (i + 1)) * csC (κ + (i + 1)))

/-- The running selector, factor by factor. -/
def csSelP (b z : ℕ → E) (κ : ℕ) : ℕ → E
  | 0 => word 1 0 0 + b κ + z κ
  | i + 1 => csSelP b z κ i * (word 1 0 0 + b (κ + (i + 1)) + z (κ + (i + 1)))

theorem csRebP_eq (b : ℕ → E) (κ : ℕ) :
    ∀ i, κ + i < 34 →
      csRebP b κ i = ∏ t ∈ Finset.range (i + 1), (1 + b (κ + t) * (gen ^ 2 ^ (κ + t) + 1))
  | 0, h => by simp [csRebP, word_one, csC_eq (show κ < 34 by omega)]
  | i + 1, h => by
    rw [csRebP, csRebP_eq b κ i (by omega), Finset.prod_range_succ (n := i + 1), word_one,
      csC_eq (by omega)]

theorem csSelP_eq (b z : ℕ → E) (κ : ℕ) :
    ∀ i, csSelP b z κ i = ∏ t ∈ Finset.range (i + 1), (1 + b (κ + t) + z (κ + t))
  | 0 => by simp [csSelP, word_one]
  | i + 1 => by rw [csSelP, csSelP_eq b z κ i, Finset.prod_range_succ (n := i + 1), word_one]

section
variable {C : CallRel} {rd : Reader} {σ : Val}

/-- What pair `i ≥ 1` asks of a valuation. -/
def CsIterOk (rd : Reader) (σ : Val) (κ i : ℕ) : Prop :=
  σ (.n (2 + κ + i)) = σ (.n (2 + κ + i)) * σ (.n (2 + κ + i)) ∧
    σ (.n (28 + 10 * i)) = word 1 0 0 ∧ σ (.n (29 + 10 * i)) = csC (κ + i) ∧
    σ (.n (30 + 10 * i)) = σ (.n (2 + κ + i)) * σ (.n (29 + 10 * i)) ∧
    σ (.n (31 + 10 * i)) = σ (.n (28 + 10 * i)) + σ (.n (30 + 10 * i)) ∧
    σ (.n (32 + 10 * i)) = σ (.n (csReb (i - 1))) * σ (.n (31 + 10 * i)) ∧
    σ (.n (33 + 10 * i)) = word 1 0 0 ∧
    σ (.n (34 + 10 * i)) = σ (.n (33 + 10 * i)) + σ (.n (2 + κ + i)) ∧
    LoadHolds rd (σ (.n 1)) (κ + i) (σ (.n (35 + 10 * i))) ∧
    σ (.n (36 + 10 * i)) = σ (.n (34 + 10 * i)) + σ (.n (35 + 10 * i)) ∧
    σ (.n (37 + 10 * i)) = σ (.n (27 + 10 * i)) * σ (.n (36 + 10 * i))

theorem holds_csIter (κ i : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (csIter κ i) True kret ↔ CsIterOk rd σ κ i := by
  simp only [csIter, CsIterOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The function's body, simplified to its conditions. -/
theorem cs_unfold {name : String} {f : Fn} (κ : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = csBody κ) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ ∃ σ : Val, [σ (.n 0), σ (.n 1)] = args ∧
      σ (.n (2 + κ)) = σ (.n (2 + κ)) * σ (.n (2 + κ)) ∧ σ (.n 30) = word 1 0 0 ∧
      σ (.n 31) = csC κ ∧ σ (.n 32) = σ (.n (2 + κ)) * σ (.n 31) ∧
      σ (.n 33) = σ (.n 30) + σ (.n 32) ∧ σ (.n 34) = word 1 0 0 ∧
      σ (.n 35) = σ (.n 34) + σ (.n (2 + κ)) ∧ LoadHolds rd (σ (.n 1)) κ (σ (.n 36)) ∧
      σ (.n 37) = σ (.n 35) + σ (.n 36) ∧ (∀ i < 27 - κ, CsIterOk rd σ κ (i + 1)) ∧
      σ (.n (csReb (27 - κ))) + σ (.n 0) = 0 ∧
      σ (.n (38 + 10 * (27 - κ))) = σ (.n (37 + 10 * (27 - κ))) ∧
      [σ (.n (38 + 10 * (27 - κ)))] = rets := by
  rw [rel_iff_sem hfind, hbody, hparams, csBody]
  simp only [holdsList_append, holdsList_range_flatten (27 - κ) (fun i => csIter κ (i + 1))
    (fun _ => rfl), holds_csIter, csHint, csFirst, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, true_and]

end

/-! ## Soundness -/

/-- The value number of the word read at pair `i`. -/
def csZ (i : ℕ) : ℕ := if i = 0 then 36 else 35 + 10 * i

theorem cs_sound {name : String} {f : Fn} (κ : ℕ) (hκ : κ ≤ 27)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = csBody κ) (rd : Reader) (offset point : E) (rets : List E)
    (h : coreProgram.Rel rd name [offset, point] rets) :
    MeaningColumnSelector κ rd [offset, point] rets := by
  rw [cs_unfold κ hfind hparams hbody] at h
  obtain ⟨σ, hp, f0, f30, f31, f32, f33, f34, f35, l36, f37, hit, hreb, hcp, hret⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1⟩ := hp
  set b : ℕ → E := fun k => σ (.n (2 + k))
  set z : ℕ → E := fun k => σ (.n (csZ (k - κ)))
  have hb : ∀ t < 28 - κ, b (κ + t) * b (κ + t) = b (κ + t) := fun t ht => by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact f0.symm
    · obtain ⟨e, -⟩ := hit (t - 1) (by omega)
      simp only [b]
      rw [show 2 + (κ + t) = 2 + κ + (t - 1 + 1) by omega]
      exact e.symm
  have hz : ∀ t < 28 - κ, LoadHolds rd point (κ + t) (z (κ + t)) := fun t ht => by
    rw [← h1]
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simpa [z, csZ] using l36
    · obtain ⟨-, -, -, -, -, -, -, -, e, -⟩ := hit (t - 1) (by omega)
      simp only [z, csZ, show κ + t - κ = t by omega, Nat.ne_of_gt ht0, ↓reduceIte]
      rw [show t - 1 + 1 = t by omega] at e
      exact e
  have hrebc : ∀ i ≤ 27 - κ, σ (.n (csReb i)) = csRebP b κ i := fun i hi => by
    induction i with
    | zero => simp only [csReb, ↓reduceIte, csRebP]; rw [f33, f30, f32, f31]
    | succ i ih =>
      obtain ⟨-, e28, e29, e30, e31, e32, -⟩ := hit i (by omega)
      simp only [csReb, Nat.succ_ne_zero, ↓reduceIte, csRebP]
      rw [e32, e31, e30, e29, e28, show i + 1 - 1 = i by omega, ih (by omega)]
      simp only [b]; rw [show 2 + κ + (i + 1) = 2 + (κ + (i + 1)) by omega]
  have hselc : ∀ i ≤ 27 - κ, σ (.n (37 + 10 * i)) = csSelP b z κ i := fun i hi => by
    induction i with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, csSelP]
      rw [f37, f35, f34]; simp [z, csZ, b]
    | succ i ih =>
      obtain ⟨-, -, -, -, -, -, e33, e34, -, e36, e37⟩ := hit i (by omega)
      rw [csSelP, e37, e36, e34, e33, show 27 + 10 * (i + 1) = 37 + 10 * i by ring, ih (by omega)]
      simp only [b, z, csZ, show κ + (i + 1) - κ = i + 1 by omega, Nat.succ_ne_zero, ↓reduceIte,
        show 2 + κ + (i + 1) = 2 + (κ + (i + 1)) by omega]
  obtain ⟨off, hoff, hdvd, hprod, hbits⟩ := cs_rebuild (by omega) hb
  have hoffset : offset = gen ^ off := by
    rw [← h0, ← e_add_eq_zero_iff.mp hreb, hrebc _ le_rfl, csRebP_eq b κ _ (by omega),
      show 27 - κ + 1 = 28 - κ by omega, hprod]
  set zs := (List.range 28).map fun k => if k < κ then 0 else z k
  have hlen : zs.length = 28 := by simp [zs]
  have hzs : ∀ t < 28 - κ, zs.getD (κ + t) 0 = z (κ + t) := fun t ht => by
    simp [zs, List.getD_eq_getElem?_getD, show κ + t < 28 by omega]
  refine ⟨off, zs, hoff, hdvd, hoffset, hlen, fun k hk hκk => ?_, ?_⟩
  · have := hz (k - κ) (by omega)
    rw [show κ + (k - κ) = k by omega] at this
    have e := hzs (k - κ) (by omega)
    rw [show κ + (k - κ) = k by omega, List.getD_eq_getElem _ _ hk] at e
    rwa [e]
  · rw [← hret, hcp, hselc _ le_rfl, csSelP_eq, eqAbove_eq_prod zs hlen,
      show 27 - κ + 1 = 28 - κ by omega]
    exact congrArg (fun x => [x]) (Finset.prod_congr rfl fun t ht => by
      rw [hbits t (Finset.mem_range.mp ht), hzs t (Finset.mem_range.mp ht)])

/-! ## Completeness -/

/-- The honest value of value number `i`, at `κ ≤ 27`. -/
def csF (κ : ℕ) (offset point : E) (b z : ℕ → E) (i : ℕ) : E :=
  if i < 2 then [offset, point].getD i 0
  else if i < 30 then b (i - 2)
  else if i < 38 then
    [word 1 0 0, csC κ, b κ * csC κ, word 1 0 0 + b κ * csC κ, word 1 0 0, word 1 0 0 + b κ,
      z κ, word 1 0 0 + b κ + z κ].getD (i - 30) 0
  else if i < 38 + 10 * (27 - κ) then
    let j := (i - 28) / 10
    [word 1 0 0, csC (κ + j), b (κ + j) * csC (κ + j), word 1 0 0 + b (κ + j) * csC (κ + j),
      csRebP b κ (j - 1) * (word 1 0 0 + b (κ + j) * csC (κ + j)), word 1 0 0,
      word 1 0 0 + b (κ + j), z (κ + j), word 1 0 0 + b (κ + j) + z (κ + j),
      csSelP b z κ (j - 1) * (word 1 0 0 + b (κ + j) + z (κ + j))].getD ((i - 28) % 10) 0
  else csSelP b z κ (27 - κ)

section
variable {κ : ℕ} {offset point : E} {b z : ℕ → E}

theorem csF_lt2 {i : ℕ} (hi : i < 2) : csF κ offset point b z i = [offset, point].getD i 0 := by
  rw [csF, ite_pos' hi]

theorem csF_bit {i k : ℕ} (hi : i = 2 + k) (hk : k < 28) : csF κ offset point b z i = b k := by
  subst hi; rw [csF, ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel_left]

theorem csF_first {i r : ℕ} (hi : i = 30 + r) (hr : r < 8) :
    csF κ offset point b z i = [word 1 0 0, csC κ, b κ * csC κ, word 1 0 0 + b κ * csC κ,
      word 1 0 0, word 1 0 0 + b κ, z κ, word 1 0 0 + b κ + z κ].getD r 0 := by
  subst hi; rw [csF, ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    Nat.add_sub_cancel_left]

theorem csF_iter {i j r : ℕ} (hi : i = 28 + 10 * j + r) (hj1 : 1 ≤ j) (hj : j ≤ 27 - κ)
    (hr : r < 10) :
    csF κ offset point b z i = [word 1 0 0, csC (κ + j), b (κ + j) * csC (κ + j),
      word 1 0 0 + b (κ + j) * csC (κ + j),
      csRebP b κ (j - 1) * (word 1 0 0 + b (κ + j) * csC (κ + j)), word 1 0 0,
      word 1 0 0 + b (κ + j), z (κ + j), word 1 0 0 + b (κ + j) + z (κ + j),
      csSelP b z κ (j - 1) * (word 1 0 0 + b (κ + j) + z (κ + j))].getD r 0 := by
  subst hi
  rw [csF, ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
  simp only
  rw [show (28 + 10 * j + r - 28) / 10 = j by omega, show (28 + 10 * j + r - 28) % 10 = r by omega]

theorem csF_last {i : ℕ} (hi : i = 38 + 10 * (27 - κ)) :
    csF κ offset point b z i = csSelP b z κ (27 - κ) := by
  subst hi
  rw [csF, ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega)]

/-- The rebuilt offset after pair `i`. -/
theorem csF_reb {i : ℕ} (hi : i ≤ 27 - κ) : csF κ offset point b z (csReb i) = csRebP b κ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp only [csReb, ↓reduceIte]
    rw [csF_first (r := 3) rfl (by omega)]; rfl
  · simp only [csReb, Nat.ne_of_gt hi0, ↓reduceIte]
    rw [csF_iter (j := i) (r := 4) (by omega) (by omega) hi (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [csRebP, Nat.add_sub_cancel]

/-- The selector after pair `i`. -/
theorem csF_sel {i : ℕ} (hi : i ≤ 27 - κ) :
    csF κ offset point b z (37 + 10 * i) = csSelP b z κ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [csF_first (r := 7) rfl (by omega)]; rfl
  · rw [csF_iter (j := i) (r := 9) (by omega) (by omega) hi (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [csSelP, Nat.add_sub_cancel]

end

theorem cs_complete {name : String} {f : Fn} (κ : ℕ) (hκ : κ ≤ 27)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = csBody κ) (rd : Reader) (offset point : E) (rets : List E)
    (h : MeaningColumnSelector κ rd [offset, point] rets) :
    coreProgram.Rel rd name [offset, point] rets := by
  obtain ⟨off, zs, hoff, hdvd, hoffset, hlen, hread, hret⟩ := h
  rw [cs_unfold κ hfind hparams hbody]
  set b : ℕ → E := fun k => bitE (off.testBit k)
  set z : ℕ → E := fun k => zs.getD k 0
  set F := csF κ offset point b z
  have hz : ∀ k, κ ≤ k → k < 28 → LoadHolds rd point k (z k) := fun k h1 h2 => by
    have := hread k (by omega) h1
    simpa [z, List.getD_eq_getElem?_getD, show k < zs.length by omega] using this
  have hbool : ∀ k, b k = b k * b k := fun k => (bitE_mul_self _).symm
  have fb : ∀ k < 28, F (2 + k) = b k := fun k hk => csF_bit rfl hk
  have f1 : F 1 = point := csF_lt2 (by omega)
  have q : ∀ r < 8, F (30 + r) = [word 1 0 0, csC κ, b κ * csC κ, word 1 0 0 + b κ * csC κ,
      word 1 0 0, word 1 0 0 + b κ, z κ, word 1 0 0 + b κ + z κ].getD r 0 :=
    fun r hr => csF_first rfl hr
  refine ⟨fun v => F v.idx, ?_, ?_, q 0 (by omega), q 1 (by omega), ?_, ?_, q 4 (by omega), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have f0 : F 0 = offset := csF_lt2 (by omega)
    show [F 0, F 1] = [offset, point]; rw [f0, f1]
  · show F (2 + κ) = F (2 + κ) * F (2 + κ); rw [fb κ (by omega)]; exact hbool _
  · show F 32 = F (2 + κ) * F 31; rw [q 2 (by omega), q 1 (by omega), fb κ (by omega)]; rfl
  · show F 33 = F 30 + F 32; rw [q 3 (by omega), q 0 (by omega), q 2 (by omega)]; rfl
  · show F 35 = F 34 + F (2 + κ); rw [q 5 (by omega), q 4 (by omega), fb κ (by omega)]; rfl
  · show LoadHolds rd (F 1) κ (F 36); rw [f1, q 6 (by omega)]; exact hz κ le_rfl (by omega)
  · show F 37 = F 35 + F 36; rw [q 7 (by omega), q 5 (by omega), q 6 (by omega)]; rfl
  · intro i hi
    have hj1 : 1 ≤ i + 1 := by omega
    have hj : i + 1 ≤ 27 - κ := by omega
    have p := fun (m r : ℕ) (hm : m = 28 + 10 * (i + 1) + r) (hr : r < 10) =>
      csF_iter (κ := κ) (offset := offset) (point := point) (b := b) (z := z) hm hj1 hj hr
    simp only [Nat.add_sub_cancel] at p
    have v28 : F (28 + 10 * (i + 1)) = word 1 0 0 := p _ 0 (by omega) (by omega)
    have v29 : F (29 + 10 * (i + 1)) = csC (κ + (i + 1)) := p _ 1 (by omega) (by omega)
    have v30 : F (30 + 10 * (i + 1)) = b (κ + (i + 1)) * csC (κ + (i + 1)) := p _ 2 (by omega) (by omega)
    have v31 : F (31 + 10 * (i + 1)) = word 1 0 0 + b (κ + (i + 1)) * csC (κ + (i + 1)) :=
      p _ 3 (by omega) (by omega)
    have v32 : F (32 + 10 * (i + 1)) =
        csRebP b κ i * (word 1 0 0 + b (κ + (i + 1)) * csC (κ + (i + 1))) := p _ 4 (by omega) (by omega)
    have v33 : F (33 + 10 * (i + 1)) = word 1 0 0 := p _ 5 (by omega) (by omega)
    have v34 : F (34 + 10 * (i + 1)) = word 1 0 0 + b (κ + (i + 1)) := p _ 6 (by omega) (by omega)
    have v35 : F (35 + 10 * (i + 1)) = z (κ + (i + 1)) := p _ 7 (by omega) (by omega)
    have v36 : F (36 + 10 * (i + 1)) = word 1 0 0 + b (κ + (i + 1)) + z (κ + (i + 1)) :=
      p _ 8 (by omega) (by omega)
    have v37 : F (37 + 10 * (i + 1)) =
        csSelP b z κ i * (word 1 0 0 + b (κ + (i + 1)) + z (κ + (i + 1))) := p _ 9 (by omega) (by omega)
    have vb : F (2 + κ + (i + 1)) = b (κ + (i + 1)) :=
      csF_bit (k := κ + (i + 1)) (by omega) (by omega)
    have fr : F (csReb i) = csRebP b κ i := csF_reb (by omega)
    have fs : F (37 + 10 * i) = csSelP b z κ i := csF_sel (by omega)
    refine ⟨?_, v28, v29, ?_, ?_, ?_, v33, ?_, ?_, ?_, ?_⟩
    · show F (2 + κ + (i + 1)) = F (2 + κ + (i + 1)) * F (2 + κ + (i + 1))
      rw [vb]; exact hbool _
    · show F (30 + 10 * (i + 1)) = F (2 + κ + (i + 1)) * F (29 + 10 * (i + 1))
      rw [v30, vb, v29]
    · show F (31 + 10 * (i + 1)) = F (28 + 10 * (i + 1)) + F (30 + 10 * (i + 1))
      rw [v31, v28, v30]
    · show F (32 + 10 * (i + 1)) = F (csReb (i + 1 - 1)) * F (31 + 10 * (i + 1))
      rw [v32, Nat.add_sub_cancel, fr, v31]
    · show F (34 + 10 * (i + 1)) = F (33 + 10 * (i + 1)) + F (2 + κ + (i + 1))
      rw [v34, v33, vb]
    · show LoadHolds rd (F 1) (κ + (i + 1)) (F (35 + 10 * (i + 1)))
      rw [f1, v35]; exact hz _ (by omega) (by omega)
    · show F (36 + 10 * (i + 1)) = F (34 + 10 * (i + 1)) + F (35 + 10 * (i + 1))
      rw [v36, v34, v35]
    · show F (37 + 10 * (i + 1)) = F (27 + 10 * (i + 1)) * F (36 + 10 * (i + 1))
      rw [v37, show 27 + 10 * (i + 1) = 37 + 10 * i by ring, fs, v36]
  · have freb : F (csReb (27 - κ)) = csRebP b κ (27 - κ) := csF_reb le_rfl
    have f0 : F 0 = offset := csF_lt2 (by omega)
    show F (csReb (27 - κ)) + F 0 = 0
    rw [freb, f0, csRebP_eq b κ _ (by omega),
      show 27 - κ + 1 = 28 - κ by omega, cs_rebuild_complete hoff hdvd, hoffset]
    exact e_add_self _
  · have flast : F (38 + 10 * (27 - κ)) = csSelP b z κ (27 - κ) := csF_last rfl
    have fsel : F (37 + 10 * (27 - κ)) = csSelP b z κ (27 - κ) := csF_sel le_rfl
    show F (38 + 10 * (27 - κ)) = F (37 + 10 * (27 - κ))
    rw [flast, fsel]
  · have flast : F (38 + 10 * (27 - κ)) = csSelP b z κ (27 - κ) := csF_last rfl
    show [F (38 + 10 * (27 - κ))] = rets
    rw [flast, hret, csSelP_eq, eqAbove_eq_prod zs hlen, show 27 - κ + 1 = 28 - κ by omega]

/-! ## `κ = 28` and the specializations -/

theorem cs28_iff {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = csBody28) (rd : Reader)
    (offset point : E) (rets : List E) :
    coreProgram.Rel rd name [offset, point] rets ↔
      MeaningColumnSelector 28 rd [offset, point] rets := by
  rw [rel_iff_sem hfind, hbody, hparams, csBody28, csHint]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  have hsel : ∀ zs : List E, zs.length = 28 →
      ({ vars := 28, index := 0 } : Placement).eqAbove zs = 1 := fun zs hzs => by
    rw [eqAbove_eq_prod zs hzs]; rfl
  constructor
  · rintro ⟨σ, hp, h30, a30, h31, hret⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨h0, -⟩ := hp
    refine ⟨0, List.replicate 28 0, by decide, dvd_zero _, ?_, by simp, fun k hk h => by
      simp at hk; omega, ?_⟩
    · rw [pow_zero, ← h0, ← e_add_eq_zero_iff.mp a30, h30, word_one]
    · rw [← hret, hsel _ (by simp), h31, word_one]
  · rintro ⟨off, zs, hoff, hdvd, hoffset, hlen, -, hret⟩
    have h0 : off = 0 := by
      obtain ⟨q, rfl⟩ := hdvd
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · rfl
      · exact absurd hoff (by have := Nat.le_mul_of_pos_right (2 ^ 28) hq; omega)
    subst h0
    refine ⟨fun v => if v.idx < 2 then [offset, point].getD v.idx 0 else 1, rfl, ?_, ?_, ?_, ?_⟩
    · exact word_one.symm
    · show (1 : E) + offset = 0
      rw [hoffset, pow_zero]; exact e_add_self 1
    · exact word_one.symm
    · show [(1 : E)] = rets
      rw [hret, hsel zs hlen]

/-- **`column_selector` at every `κ ≤ 28`**, for a compiled function whose body is the
expansion at `κ`. -/
theorem column_selector_iff {name : String} {f : Fn} (κ : ℕ) (h28 : κ ≤ 28)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = if κ = 28 then csBody28 else csBody κ) (rd : Reader) (offset point : E)
    (rets : List E) :
    coreProgram.Rel rd name [offset, point] rets ↔
      MeaningColumnSelector κ rd [offset, point] rets := by
  rcases Nat.lt_or_ge κ 28 with h | h
  · rw [ite_neg' (by omega)] at hbody
    exact ⟨cs_sound κ (by omega) hfind hparams hbody rd offset point rets,
      cs_complete κ (by omega) hfind hparams hbody rd offset point rets⟩
  · obtain rfl : κ = 28 := by omega
    exact cs28_iff hfind hparams hbody rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L0_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L0" [offset, point] rets ↔
      MeaningColumnSelector 0 rd [offset, point] rets :=
  column_selector_iff 0 (by decide)
    (Program.find?_of_indexOf? (j := 143) (by decide +kernel) rfl) rfl
    (by rw [core143_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L1_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L1" [offset, point] rets ↔
      MeaningColumnSelector 1 rd [offset, point] rets :=
  column_selector_iff 1 (by decide)
    (Program.find?_of_indexOf? (j := 144) (by decide +kernel) rfl) rfl
    (by rw [core144_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L2_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L2" [offset, point] rets ↔
      MeaningColumnSelector 2 rd [offset, point] rets :=
  column_selector_iff 2 (by decide)
    (Program.find?_of_indexOf? (j := 145) (by decide +kernel) rfl) rfl
    (by rw [core145_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L3_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L3" [offset, point] rets ↔
      MeaningColumnSelector 3 rd [offset, point] rets :=
  column_selector_iff 3 (by decide)
    (Program.find?_of_indexOf? (j := 146) (by decide +kernel) rfl) rfl
    (by rw [core146_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L4_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L4" [offset, point] rets ↔
      MeaningColumnSelector 4 rd [offset, point] rets :=
  column_selector_iff 4 (by decide)
    (Program.find?_of_indexOf? (j := 147) (by decide +kernel) rfl) rfl
    (by rw [core147_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L5_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L5" [offset, point] rets ↔
      MeaningColumnSelector 5 rd [offset, point] rets :=
  column_selector_iff 5 (by decide)
    (Program.find?_of_indexOf? (j := 148) (by decide +kernel) rfl) rfl
    (by rw [core148_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L6_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L6" [offset, point] rets ↔
      MeaningColumnSelector 6 rd [offset, point] rets :=
  column_selector_iff 6 (by decide)
    (Program.find?_of_indexOf? (j := 149) (by decide +kernel) rfl) rfl
    (by rw [core149_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L7_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L7" [offset, point] rets ↔
      MeaningColumnSelector 7 rd [offset, point] rets :=
  column_selector_iff 7 (by decide)
    (Program.find?_of_indexOf? (j := 150) (by decide +kernel) rfl) rfl
    (by rw [core150_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L8_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L8" [offset, point] rets ↔
      MeaningColumnSelector 8 rd [offset, point] rets :=
  column_selector_iff 8 (by decide)
    (Program.find?_of_indexOf? (j := 151) (by decide +kernel) rfl) rfl
    (by rw [core151_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L9_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L9" [offset, point] rets ↔
      MeaningColumnSelector 9 rd [offset, point] rets :=
  column_selector_iff 9 (by decide)
    (Program.find?_of_indexOf? (j := 152) (by decide +kernel) rfl) rfl
    (by rw [core152_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L10_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L10" [offset, point] rets ↔
      MeaningColumnSelector 10 rd [offset, point] rets :=
  column_selector_iff 10 (by decide)
    (Program.find?_of_indexOf? (j := 153) (by decide +kernel) rfl) rfl
    (by rw [core153_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L11_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L11" [offset, point] rets ↔
      MeaningColumnSelector 11 rd [offset, point] rets :=
  column_selector_iff 11 (by decide)
    (Program.find?_of_indexOf? (j := 154) (by decide +kernel) rfl) rfl
    (by rw [core154_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L12_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L12" [offset, point] rets ↔
      MeaningColumnSelector 12 rd [offset, point] rets :=
  column_selector_iff 12 (by decide)
    (Program.find?_of_indexOf? (j := 155) (by decide +kernel) rfl) rfl
    (by rw [core155_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L13_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L13" [offset, point] rets ↔
      MeaningColumnSelector 13 rd [offset, point] rets :=
  column_selector_iff 13 (by decide)
    (Program.find?_of_indexOf? (j := 156) (by decide +kernel) rfl) rfl
    (by rw [core156_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L14_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L14" [offset, point] rets ↔
      MeaningColumnSelector 14 rd [offset, point] rets :=
  column_selector_iff 14 (by decide)
    (Program.find?_of_indexOf? (j := 157) (by decide +kernel) rfl) rfl
    (by rw [core157_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L15_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L15" [offset, point] rets ↔
      MeaningColumnSelector 15 rd [offset, point] rets :=
  column_selector_iff 15 (by decide)
    (Program.find?_of_indexOf? (j := 158) (by decide +kernel) rfl) rfl
    (by rw [core158_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L16_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L16" [offset, point] rets ↔
      MeaningColumnSelector 16 rd [offset, point] rets :=
  column_selector_iff 16 (by decide)
    (Program.find?_of_indexOf? (j := 159) (by decide +kernel) rfl) rfl
    (by rw [core159_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L17_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L17" [offset, point] rets ↔
      MeaningColumnSelector 17 rd [offset, point] rets :=
  column_selector_iff 17 (by decide)
    (Program.find?_of_indexOf? (j := 160) (by decide +kernel) rfl) rfl
    (by rw [core160_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L18_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L18" [offset, point] rets ↔
      MeaningColumnSelector 18 rd [offset, point] rets :=
  column_selector_iff 18 (by decide)
    (Program.find?_of_indexOf? (j := 161) (by decide +kernel) rfl) rfl
    (by rw [core161_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L19_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L19" [offset, point] rets ↔
      MeaningColumnSelector 19 rd [offset, point] rets :=
  column_selector_iff 19 (by decide)
    (Program.find?_of_indexOf? (j := 162) (by decide +kernel) rfl) rfl
    (by rw [core162_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L20_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L20" [offset, point] rets ↔
      MeaningColumnSelector 20 rd [offset, point] rets :=
  column_selector_iff 20 (by decide)
    (Program.find?_of_indexOf? (j := 163) (by decide +kernel) rfl) rfl
    (by rw [core163_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L21_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L21" [offset, point] rets ↔
      MeaningColumnSelector 21 rd [offset, point] rets :=
  column_selector_iff 21 (by decide)
    (Program.find?_of_indexOf? (j := 164) (by decide +kernel) rfl) rfl
    (by rw [core164_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L22_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L22" [offset, point] rets ↔
      MeaningColumnSelector 22 rd [offset, point] rets :=
  column_selector_iff 22 (by decide)
    (Program.find?_of_indexOf? (j := 165) (by decide +kernel) rfl) rfl
    (by rw [core165_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L23_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L23" [offset, point] rets ↔
      MeaningColumnSelector 23 rd [offset, point] rets :=
  column_selector_iff 23 (by decide)
    (Program.find?_of_indexOf? (j := 166) (by decide +kernel) rfl) rfl
    (by rw [core166_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L24_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L24" [offset, point] rets ↔
      MeaningColumnSelector 24 rd [offset, point] rets :=
  column_selector_iff 24 (by decide)
    (Program.find?_of_indexOf? (j := 167) (by decide +kernel) rfl) rfl
    (by rw [core167_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L25_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L25" [offset, point] rets ↔
      MeaningColumnSelector 25 rd [offset, point] rets :=
  column_selector_iff 25 (by decide)
    (Program.find?_of_indexOf? (j := 168) (by decide +kernel) rfl) rfl
    (by rw [core168_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L26_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L26" [offset, point] rets ↔
      MeaningColumnSelector 26 rd [offset, point] rets :=
  column_selector_iff 26 (by decide)
    (Program.find?_of_indexOf? (j := 169) (by decide +kernel) rfl) rfl
    (by rw [core169_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L27_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L27" [offset, point] rets ↔
      MeaningColumnSelector 27 rd [offset, point] rets :=
  column_selector_iff 27 (by decide)
    (Program.find?_of_indexOf? (j := 170) (by decide +kernel) rfl) rfl
    (by rw [core170_body]; rfl) rd offset point rets

set_option maxRecDepth 100000 in
theorem column_selector_L28_iff (rd : Reader) (offset point : E) (rets : List E) :
    coreProgram.Rel rd "column_selector__L28" [offset, point] rets ↔
      MeaningColumnSelector 28 rd [offset, point] rets :=
  column_selector_iff 28 (by decide)
    (Program.find?_of_indexOf? (j := 171) (by decide +kernel) rfl) rfl
    (by rw [core171_body]; rfl) rd offset point rets

end
end LeanVM.Guest.B1
