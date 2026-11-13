/-
  LeanVM.Guest.B1.Placement.Certify

  B1 for `certify_placement`: the committed columns' groups, their hinted order certified by
  strictly descending rank keys, and every column's offset laid out from its group's base, as
  `stackOffsets` lays them out.
-/

module

public import LeanVM.Guest.B1.Placement.Common

/-!
# `certify_placement` (TRIAGE G #67)

`certify_placement(kappa_base, g_squares)` (G:3310-3354) reads `kb[i] = kappa_base[g^i]`, then
for each column group `gi < 9` (`colGroupStart`) builds its `g^κ` from its first column's source
and adjustment, range-checks `κ < 34`, keys the group by `g^(κ·247)·INV_GEN^c₀` (the rank keys at
`g_squares·g^178`) and sizes it `g^((#columns)·2^κ)` (an addition chain over `g_squares[g^κ]`).
It reads the hinted group order `col_group_order`, range-checks each entry below `9`, certifies
each key below the previous one (`prev_key / key · INV_GEN = g^e`, `e < 8398`), stores the
running total at the group's base write-once and multiplies the total by the group's size; then
it lays every column out from its group's base, `g_squares[g^κ]` apart.

The expansion is `cpPre` (`cpFound`, by kernel evaluation): the eight loads, the groups
(`cpGroup`), the order hint, rank `0` (`cpRank0`) and ranks `1 .. 8` (`cpRank`, from value
`131 + 18·r`), the columns (`cpCols`) and the returns.

The keys: with `K·g^c₀ = g^(κ·247)` per group, `K_prev = g^(e+1)·K` multiplies out to
`κ_prev·247 + c₀ = κ·247 + c₀_prev + e + 1` over small naturals, so `κ` does not increase along the
ranks and a tie has `c₀` increase: `stackOffsets`'s order, group by group. `tb_group_stack_cert`
(`Placement/Common`) expands it to the columns.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Words -/

/-- `g^33`, the range check against `SIZE_BITS = 34`. -/
abbrev w33 : E := word 8589934592 0

/-- `g^8`, the range check against `N_COL_GROUPS = 9`. -/
abbrev w8 : E := word 256 0

/-- `g^8397`, the range check against `RANK_KEY_BOUND = 34·247`. -/
abbrev wRankBound : E := word 267460055567564800 0

/-- `INV_GEN`. -/
abbrev wInvGen : E := word 9223372036854775821 0

theorem word_g8 : word 256 0 = ofK (Parameters.addressOfIndex 8) := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 256) = ofK (Parameters.addressOfIndex 8)
  rw [show K.ofBits 256 = Parameters.addressOfIndex 8 by decide +kernel]

theorem word_g8397 : word 267460055567564800 0 = ofK (Parameters.addressOfIndex 8397) := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 267460055567564800) = ofK (Parameters.addressOfIndex 8397)
  rw [show K.ofBits 267460055567564800 = Parameters.addressOfIndex 8397 by decide +kernel]

theorem wInvGen_mul_gen : wInvGen * gen = 1 := by
  rw [show gen = ofK (K.ofBits 2) from rfl,
    show wInvGen = ofK (K.ofBits 9223372036854775821) from tb_word_eOfNat _, ← ofK_mul,
    show K.ofBits 9223372036854775821 * K.ofBits 2 = 1 by decide +kernel]
  exact map_one (algebraMap K E)

/-! ## The groups -/

/-- Group `gi`'s first column `c₀` (`COL_GROUP_START`; `cpC0 9 = 94`). -/
def cpC0 (gi : ℕ) : ℕ := colGroupStart.getD gi 0

/-- Group `gi`'s number of columns. -/
def cpLen (gi : ℕ) : ℕ := cpC0 (gi + 1) - cpC0 gi

/-- Group `gi`'s `kappa_base` source and adjustment, its first column's. -/
def cpSrc (gi : ℕ) : ℕ := colKappaSrc (cpC0 gi)
def cpAdj (gi : ℕ) : ℕ := colKappaAdj (cpC0 gi)

/-- `INV_GEN^c₀` per group, as the data writes it (`1` for `c₀ = 0`, where the data has none). -/
def cpInvWords : List ℕ :=
  [1, 16140901064495857672, 8070450532247928836, 4035225266123964418, 2049630411662819329,
    10248191151106424845, 14347467612877750283, 8198552921648689156, 6661324248839560310]

theorem cpInvWords_K : ∀ gi < 9,
    K.ofBits (cpInvWords.getD gi 0) * Parameters.addressOfIndex (cpC0 gi) = 1 := by
  decide +kernel

theorem cpInvWord_mul {gi : ℕ} (h : gi < 9) :
    word (cpInvWords.getD gi 0) 0 * gen ^ cpC0 gi = 1 := by
  rw [tb_word_eOfNat, gen_pow_eq_ofK, eOfNat, ← ofK_mul, cpInvWords_K gi h]
  exact map_one (algebraMap K E)

/-- Group `gi`'s first value. -/
def cpB (gi : ℕ) : ℕ := [12, 22, 34, 46, 61, 76, 90, 105, 120].getD gi 0

/-- The value of group `gi`'s `g^κ`: the source word, or its product with `g^adj`. -/
def cpKv (gi : ℕ) : ℕ := if cpAdj gi = 0 then 2 + cpSrc gi else cpB gi + 1

/-- The range check's constant. -/
def cpQ (gi : ℕ) : ℕ := if cpAdj gi = 0 then cpB gi else cpB gi + 2

/-- The pointer to `g_squares[g^κ]`; the key is the value before it. -/
def cpZ (gi : ℕ) : ℕ := if cpC0 gi = 0 then cpQ gi + 6 else cpQ gi + 8

/-- Group `gi`'s addition chain for its size: `true` squares, `false` multiplies by the base. -/
def cpCh (gi : ℕ) : List Bool :=
  [[true, false], [], [], [true, false, true, true, false], [true, false, true, true, false],
    [true, false, true, false], [true, false, true, false, true],
    [true, false, true, false, true], [true, false, true, false, true, true]].getD gi []

/-- An addition chain from value `v0`. -/
def cpChain (v0 : ℕ) (bs : List Bool) : List Stmt :=
  ((List.range bs.length).map fun j ↦
    [Stmt.atom (.mul (.n (v0 + 1 + j)) (.n (v0 + j))
      (.n (if bs.getD j false then v0 + j else v0)))]).flatten

/-- The exponent an addition chain reaches. -/
def cpChainExp (bs : List Bool) : ℕ := bs.foldl (fun e b ↦ if b then 2 * e else e + 1) 1

/-! ## The template -/

/-- The group's `g^κ = kb[src]·g^adj`, when `adj ≠ 0`. -/
def cpKapS (gi : ℕ) : List Stmt :=
  if cpAdj gi = 0 then [] else
    [.atom (.const (.n (cpB gi)) (word (2 ^ cpAdj gi) 0)),
      .atom (.mul (.n (cpB gi + 1)) (.n (2 + cpSrc gi)) (.n (cpB gi)))]

/-- `assert log(g^κ) < 34` and the rank key's load. -/
def cpRcS (gi : ℕ) : List Stmt :=
  [.atom (.const (.n (cpQ gi)) w33),
    .atom (.rangeCheck (.n (cpKv gi)) (.n (cpQ gi + 1)) (.n (cpQ gi + 2)) (.n (cpQ gi + 3))
      (.n (cpQ gi))),
    .atom (.mul (.n (cpQ gi + 4)) (.n 1) (.n (cpKv gi))),
    .atom (.load (.n (cpQ gi + 5)) (.n (cpQ gi + 4)) 178)]

/-- The key times `INV_GEN^c₀`, when `c₀ ≠ 0`. -/
def cpKeyS (gi : ℕ) : List Stmt :=
  if cpC0 gi = 0 then [] else
    [.atom (.const (.n (cpQ gi + 6)) (word (cpInvWords.getD gi 0) 0)),
      .atom (.mul (.n (cpQ gi + 7)) (.n (cpQ gi + 5)) (.n (cpQ gi + 6)))]

/-- The key's store, the size's chain and its store. -/
def cpSizeS (gi : ℕ) : List Stmt :=
  [.atom (.load (.n (cpZ gi - 1)) (.n 10) gi), .atom (.mul (.n (cpZ gi)) (.n 1) (.n (cpKv gi))),
    .atom (.load (.n (cpZ gi + 1)) (.n (cpZ gi)) 0)] ++
  cpChain (cpZ gi + 1) (cpCh gi) ++
  [.atom (.load (.n (cpZ gi + 1 + (cpCh gi).length)) (.n 11) gi)]

/-- Group `gi`: its `g^κ`, key and size. -/
def cpGroup (gi : ℕ) : List Stmt := cpKapS gi ++ cpRcS gi ++ cpKeyS gi ++ cpSizeS gi

/-- Rank `0`, values `138 .. 148`. -/
def cpRank0 : List Stmt :=
  [.atom (.load (.n 138) (.n 136) 0), .atom (.const (.n 139) w8),
    .atom (.rangeCheck (.n 138) (.n 140) (.n 141) (.n 142) (.n 139)),
    .atom (.mul (.n 143) (.n 10) (.n 138)), .atom (.load (.n 144) (.n 143) 0),
    .atom (.const (.n 145) (word 1 0)), .atom (.mul (.n 146) (.n 137) (.n 138)),
    .atom (.load (.n 145) (.n 146) 0), .atom (.mul (.n 147) (.n 11) (.n 138)),
    .atom (.load (.n 148) (.n 147) 0)]

/-- Rank `r`'s group, key, base (the total before it) and total after it, by value number. -/
def cpRB (r : ℕ) : ℕ := if r = 0 then 138 else 131 + 18 * r
def cpRK (r : ℕ) : ℕ := if r = 0 then 144 else 137 + 18 * r
def cpRP (r : ℕ) : ℕ := if r = 0 then 145 else 130 + 18 * r
def cpRT (r : ℕ) : ℕ := 148 + 18 * r

/-- Rank `r ≥ 1`, from value `B = 131 + 18·r`. -/
def cpRank (r : ℕ) : List Stmt :=
  let B := 131 + 18 * r
  [.atom (.load (.n B) (.n 136) r), .atom (.const (.n (B + 1)) w8),
    .atom (.rangeCheck (.n B) (.n (B + 2)) (.n (B + 3)) (.n (B + 4)) (.n (B + 1))),
    .atom (.mul (.n (B + 5)) (.n 10) (.n B)), .atom (.load (.n (B + 6)) (.n (B + 5)) 0),
    .atom (.const (.n (B + 7)) wRankBound),
    .atom (.mul (.n (cpRK (r - 1))) (.n (B + 8)) (.n (B + 6))),
    .atom (.const (.n (B + 9)) wInvGen), .atom (.mul (.n (B + 10)) (.n (B + 8)) (.n (B + 9))),
    .atom (.rangeCheck (.n (B + 10)) (.n (B + 11)) (.n (B + 12)) (.n (B + 13)) (.n (B + 7))),
    .atom (.mul (.n (B + 14)) (.n 137) (.n B)), .atom (.load (.n (B - 1)) (.n (B + 14)) 0),
    .atom (.mul (.n (B + 15)) (.n 11) (.n B)), .atom (.load (.n (B + 16)) (.n (B + 15)) 0),
    .atom (.mul (.n (B + 17)) (.n (B - 1)) (.n (B + 16)))]

/-- Group `gi`'s columns' first value. -/
def cpD (gi : ℕ) : ℕ := 294 + 2 * gi + cpC0 gi

/-- Group `gi`'s columns: the step `g_squares[g^κ]`, the base, and each column's offset. -/
def cpCols (gi : ℕ) : List Stmt :=
  [.atom (.mul (.n (cpD gi)) (.n 1) (.n (2 + cpSrc gi))),
    .atom (.load (.n (cpD gi + 1)) (.n (cpD gi)) (cpAdj gi)),
    .atom (.load (.n (cpD gi + 2)) (.n 137) gi),
    .atom (.load (.n (cpD gi + 2)) (.n 293) (cpC0 gi))] ++
  ((List.range (cpLen gi - 1)).map fun j ↦
    [.atom (.mul (.n (cpD gi + 3 + j)) (.n (cpD gi + 2 + j)) (.n (cpD gi + 1))),
      .atom (.load (.n (cpD gi + 3 + j)) (.n 293) (cpC0 gi + 1 + j))]).flatten

/-- `certify_placement`'s statements before its `ret`. -/
def cpPre : List Stmt :=
  ((List.range 8).map fun i ↦ [Stmt.atom (.load (.n (2 + i)) (.n 0) i)]).flatten ++
    [.atom (.hint (.alloc (.n 10) 9)), .atom (.hint (.alloc (.n 11) 9))] ++
    ((List.range 9).map cpGroup).flatten ++
    [.atom (.hint (.alloc (.n 136) 9)),
      .atom (.hint (.witness "col_group_order" (.heap (.n 136) 0 9))),
      .atom (.hint (.alloc (.n 137) 9))] ++
    cpRank0 ++ ((List.range 8).map fun r ↦ cpRank (r + 1)).flatten ++
    [.atom (.hint (.alloc (.n 293) 94))] ++ ((List.range 9).map cpCols).flatten ++
    [.atom (.copy (.n 406) (.n 292)), .atom (.copy (.n 407) (.n 293))]

/-- The function found by name is the template. -/
noncomputable def cpCheck : Bool :=
  match coreProgram.find? "certify_placement" with
  | some fn => decide (fn.params = [.n 0, .n 1]) &&
      tbStmtsEqb fn.body (cpPre ++ [.ret [.n 406, .n 407]])
  | none => false

theorem cpCheck_eq : cpCheck = true := by decide +kernel

theorem cpFound : ∃ fn : Fn, coreProgram.find? "certify_placement" = some fn ∧
    fn.params = [.n 0, .n 1] ∧ fn.body = cpPre ++ [.ret [.n 406, .n 407]] := by
  have h := cpCheck_eq
  unfold cpCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-! ## The tables' facts -/

theorem cpC0_zero : cpC0 0 = 0 := rfl

theorem cpC0_nine : cpC0 9 = 94 := rfl

theorem cpC0_mono : ∀ g < 9, cpC0 g ≤ cpC0 (g + 1) := by decide +kernel

theorem cpC0_le : ∀ g < 9, cpC0 (g + 1) ≤ 94 := by decide +kernel

/-- `c₀` orders the groups. -/
theorem cpC0_lt : ∀ a < 9, ∀ b < 9, cpC0 a < cpC0 b → a < b := by decide +kernel

/-- A group's columns share its first column's source and adjustment. -/
theorem cp_group_const : ∀ g < 9, ∀ c < 94, cpC0 g ≤ c → c < cpC0 (g + 1) →
    colKappaSrc c = cpSrc g ∧ colKappaAdj c = cpAdj g := by decide +kernel

theorem cpSrc_lt : ∀ g < 9, cpSrc g < 8 := by decide +kernel

theorem cpAdj_le : ∀ g < 9, cpAdj g ≤ 19 := by decide +kernel

theorem cpChainExp_eq : ∀ g < 9, cpChainExp (cpCh g) = cpLen g := by decide +kernel

theorem cpInvWords_zero : ∀ g < 9, cpC0 g = 0 → cpInvWords.getD g 0 = 1 := by decide +kernel

/-! ## No `ret` -/

theorem cpChain_noRet (v0 : ℕ) (bs : List Bool) : Stmt.noRetList (cpChain v0 bs) = true :=
  tb_noRetList_flatten_range _ _ fun _ ↦ rfl

theorem cpGroup_noRet (gi : ℕ) : Stmt.noRetList (cpGroup gi) = true := by
  simp only [cpGroup, cpSizeS, tb_noRetList_append, cpChain_noRet, cpKapS, cpKeyS]
  split_ifs <;> rfl

theorem cpCols_noRet (gi : ℕ) : Stmt.noRetList (cpCols gi) = true := by
  rw [cpCols, tb_noRetList_append, tb_noRetList_flatten_range _ _ fun _ ↦ rfl]; rfl

theorem cpPre_noRet : Stmt.noRetList cpPre = true := by
  simp only [cpPre, tb_noRetList_append, tb_noRetList_flatten_range _ _ cpGroup_noRet,
    tb_noRetList_flatten_range _ _ cpCols_noRet,
    tb_noRetList_flatten_range _ _ (fun r ↦ (rfl : Stmt.noRetList (cpRank (r + 1)) = true)),
    tb_noRetList_flatten_range 8 (fun i ↦ [Stmt.atom (.load (.n (2 + i)) (.n 0) i)])
      (fun _ ↦ rfl)]
  rfl

/-! ## The template's conditions -/

/-- A range check's atom holds. -/
def TbRcHolds (rd : Reader) (σ : Val) (x y t1 t2 k : ℕ) : Prop :=
  LoadHolds rd (σ (.n x)) 0 (σ (.n t1)) ∧ σ (.n k) = σ (.n x) * σ (.n y) ∧
    LoadHolds rd (σ (.n y)) 0 (σ (.n t2))

/-- What group `gi` asks of a valuation. -/
def CpGroupOk (rd : Reader) (σ : Val) (gi : ℕ) : Prop :=
  σ (.n (cpKv gi)) = σ (.n (2 + cpSrc gi)) * word (2 ^ cpAdj gi) 0 ∧
    σ (.n (cpQ gi)) = w33 ∧ TbRcHolds rd σ (cpKv gi) (cpQ gi + 1) (cpQ gi + 2) (cpQ gi + 3) (cpQ gi) ∧
    LoadHolds rd (σ (.n 1) * σ (.n (cpKv gi))) 178 (σ (.n (cpQ gi + 5))) ∧
    σ (.n (cpZ gi - 1)) = σ (.n (cpQ gi + 5)) * word (cpInvWords.getD gi 0) 0 ∧
    LoadHolds rd (σ (.n 10)) gi (σ (.n (cpZ gi - 1))) ∧
    LoadHolds rd (σ (.n 1) * σ (.n (cpKv gi))) 0 (σ (.n (cpZ gi + 1))) ∧
    (∀ j ≤ (cpCh gi).length,
      σ (.n (cpZ gi + 1 + j)) = σ (.n (cpZ gi + 1)) ^ cpChainExp ((cpCh gi).take j)) ∧
    LoadHolds rd (σ (.n 11)) gi (σ (.n (cpZ gi + 1 + (cpCh gi).length)))

/-- What rank `r ≥ 1` asks of a valuation. -/
def CpRankOk (rd : Reader) (σ : Val) (r : ℕ) : Prop :=
  let B := 131 + 18 * r
  LoadHolds rd (σ (.n 136)) r (σ (.n B)) ∧ σ (.n (B + 1)) = w8 ∧
    TbRcHolds rd σ B (B + 2) (B + 3) (B + 4) (B + 1) ∧ σ (.n (B + 5)) = σ (.n 10) * σ (.n B) ∧
    LoadHolds rd (σ (.n (B + 5))) 0 (σ (.n (B + 6))) ∧ σ (.n (B + 7)) = wRankBound ∧
    σ (.n (cpRK (r - 1))) = σ (.n (B + 8)) * σ (.n (B + 6)) ∧ σ (.n (B + 9)) = wInvGen ∧
    σ (.n (B + 10)) = σ (.n (B + 8)) * σ (.n (B + 9)) ∧
    TbRcHolds rd σ (B + 10) (B + 11) (B + 12) (B + 13) (B + 7) ∧
    σ (.n (B + 14)) = σ (.n 137) * σ (.n B) ∧ LoadHolds rd (σ (.n (B + 14))) 0 (σ (.n (B - 1))) ∧
    σ (.n (B + 15)) = σ (.n 11) * σ (.n B) ∧ LoadHolds rd (σ (.n (B + 15))) 0 (σ (.n (B + 16))) ∧
    σ (.n (B + 17)) = σ (.n (B - 1)) * σ (.n (B + 16))

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem holds_cpChain {v0 : ℕ} {bs : List Bool}
    (h : Stmt.HoldsList C rd σ (cpChain v0 bs) True kret) :
    ∀ j ≤ bs.length, σ (.n (v0 + j)) = σ (.n v0) ^ cpChainExp (bs.take j) := by
  rw [cpChain, tb_holdsList_flatten_range _ _ fun _ ↦ rfl] at h
  intro j hj
  induction j with
  | zero => simp [cpChainExp]
  | succ j ih =>
    have hj' : j < bs.length := by omega
    have hs := h j hj'
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
    have e : cpChainExp (bs.take (j + 1)) =
        if bs[j] then 2 * cpChainExp (bs.take j) else cpChainExp (bs.take j) + 1 := by
      rw [cpChainExp, cpChainExp, List.take_add_one, List.getElem?_eq_getElem hj',
        Option.toList_some, List.foldl_append]
      rfl
    rw [List.getD_eq_getElem _ _ hj'] at hs
    rw [show v0 + (j + 1) = v0 + 1 + j by omega, hs, e]
    cases bs[j]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih (by omega), pow_succ]
    · simp only [↓reduceIte]
      rw [ih (by omega), two_mul, pow_add]

theorem holds_cpGroup {gi : ℕ} (hgi : gi < 9)
    (h : Stmt.HoldsList C rd σ (cpGroup gi) True kret) : CpGroupOk rd σ gi := by
  rw [cpGroup, tb_holdsList_append_noRet (by
      simp only [tb_noRetList_append, cpKapS, cpKeyS]; split_ifs <;> rfl),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, cpKapS]; split_ifs <;> rfl),
    tb_holdsList_append_noRet (by simp only [cpKapS]; split_ifs <;> rfl), cpSizeS,
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, cpChain_noRet]; rfl),
    tb_holdsList_append_noRet rfl] at h
  obtain ⟨⟨⟨hK, hR⟩, hY⟩, ⟨hS, hC⟩, hL⟩ := h
  have hkv : σ (.n (cpKv gi)) = σ (.n (2 + cpSrc gi)) * word (2 ^ cpAdj gi) 0 := by
    unfold cpKapS at hK
    unfold cpKv
    split_ifs at hK ⊢ with ha
    · rw [ha, pow_zero, tb_word_one, mul_one]
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hK
      rw [hK.2, hK.1]
  have hkey : σ (.n (cpZ gi - 1)) = σ (.n (cpQ gi + 5)) * word (cpInvWords.getD gi 0) 0 := by
    unfold cpKeyS at hY
    unfold cpZ
    split_ifs at hY ⊢ with hc
    · rw [cpInvWords_zero gi hgi hc, tb_word_one, mul_one,
        show cpQ gi + 6 - 1 = cpQ gi + 5 by omega]
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hY
      rw [show cpQ gi + 8 - 1 = cpQ gi + 7 by omega, hY.2, hY.1]
  simp only [cpRcS, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hR
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hS hL
  obtain ⟨r1, r2, r3, r4⟩ := hR
  obtain ⟨s1, s2, s3⟩ := hS
  refine ⟨hkv, r1, r2, by rw [← r3]; exact r4, hkey, s1, by rw [← s2]; exact s3,
    holds_cpChain hC, hL⟩

theorem holds_cpRank (r : ℕ) :
    Stmt.HoldsList C rd σ (cpRank r) True kret ↔ CpRankOk rd σ r := by
  simp only [cpRank, CpRankOk, TbRcHolds, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

theorem holds_cpCols {gi : ℕ} (h : Stmt.HoldsList C rd σ (cpCols gi) True kret) :
    LoadHolds rd (σ (.n 1) * σ (.n (2 + cpSrc gi))) (cpAdj gi) (σ (.n (cpD gi + 1))) ∧
    LoadHolds rd (σ (.n 137)) gi (σ (.n (cpD gi + 2))) ∧
    ∀ j < cpLen gi, LoadHolds rd (σ (.n 293)) (cpC0 gi + j)
      (σ (.n (cpD gi + 2)) * σ (.n (cpD gi + 1)) ^ j) := by
  rw [cpCols, tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ fun _ ↦ rfl] at h
  obtain ⟨h0, h1⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
  obtain ⟨m0, l1, l2, l3⟩ := h0
  have hv : ∀ j < cpLen gi, σ (.n (cpD gi + 2 + j)) = σ (.n (cpD gi + 2)) * σ (.n (cpD gi + 1)) ^ j ∧
      LoadHolds rd (σ (.n 293)) (cpC0 gi + j) (σ (.n (cpD gi + 2 + j))) := by
    intro j hj
    induction j with
    | zero => exact ⟨by rw [pow_zero, mul_one], l3⟩
    | succ j ih =>
      have hs := h1 j (by omega)
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
      rw [show cpD gi + 2 + (j + 1) = cpD gi + 3 + j by omega,
        show cpC0 gi + (j + 1) = cpC0 gi + 1 + j by omega]
      refine ⟨?_, hs.2⟩
      rw [hs.1, (ih (by omega)).1, pow_succ, mul_assoc]
  refine ⟨by rw [← m0]; exact l1, l2, fun j hj ↦ ?_⟩
  rw [← (hv j hj).1]
  exact (hv j hj).2

end

/-! ## Soundness -/

/-- What rank `r` gives, uniformly. -/
def CpFacts (rd : Reader) (σ : Val) (r : ℕ) : Prop :=
  (∃ gi < 9, σ (.n (cpRB r)) = gen ^ gi) ∧
    LoadHolds rd (σ (.n 10) * σ (.n (cpRB r))) 0 (σ (.n (cpRK r))) ∧
    LoadHolds rd (σ (.n 137) * σ (.n (cpRB r))) 0 (σ (.n (cpRP r))) ∧
    (∃ t, LoadHolds rd (σ (.n 11) * σ (.n (cpRB r))) 0 t ∧
      σ (.n (cpRT r)) = σ (.n (cpRP r)) * t) ∧
    (r = 0 → σ (.n (cpRP r)) = 1) ∧ (1 ≤ r → σ (.n (cpRP r)) = σ (.n (cpRT (r - 1)))) ∧
    (1 ≤ r → ∃ e < 8398, σ (.n (cpRK (r - 1))) = gen ^ (e + 1) * σ (.n (cpRK r)))

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

theorem cp_rc9 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w8)
    (h : TbRcHolds Lm.read σ x y t1 t2 k) : ∃ e < 9, σ (.n x) = gen ^ e :=
  tb_rc_sound' hμ Lm (K := 9) (by omega) (by decide) (by rw [hk]; exact word_g8) h.1 h.2.1 h.2.2

theorem cp_rc34 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w33)
    (h : TbRcHolds Lm.read σ x y t1 t2 k) : ∃ e < 34, σ (.n x) = gen ^ e :=
  tb_rc_sound' hμ Lm (K := 34) (by omega) (by decide) (by rw [hk]; exact word_g33) h.1 h.2.1
    h.2.2

theorem cp_rcKey {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = wRankBound)
    (h : TbRcHolds Lm.read σ x y t1 t2 k) : ∃ e < 8398, σ (.n x) = gen ^ e :=
  tb_rc_sound' hμ Lm (K := 8398) (by omega) (by decide) (by rw [hk]; exact word_g8397) h.1
    h.2.1 h.2.2

theorem cpFacts_succ {σ : Val} {r : ℕ} (h : CpRankOk Lm.read σ (r + 1)) :
    CpFacts Lm.read σ (r + 1) := by
  obtain ⟨-, c1, rc0, m5, l6, c7, m8, c9, m10, rc10, m14, l14, m15, l16, m17⟩ := h
  have eB : cpRB (r + 1) = 131 + 18 * (r + 1) := by
    simp only [cpRB, Nat.add_one_ne_zero, ↓reduceIte]
  have eK : cpRK (r + 1) = 131 + 18 * (r + 1) + 6 := by
    simp only [cpRK, Nat.add_one_ne_zero, ↓reduceIte]; omega
  have eP : cpRP (r + 1) = 131 + 18 * (r + 1) - 1 := by
    simp only [cpRP, Nat.add_one_ne_zero, ↓reduceIte]; omega
  have eT : cpRT (r + 1) = 131 + 18 * (r + 1) + 17 := by unfold cpRT; omega
  have eT' : cpRT (r + 1 - 1) = 131 + 18 * (r + 1) - 1 := by unfold cpRT; omega
  unfold CpFacts
  rw [eB, eK, eP, eT, eT']
  refine ⟨cp_rc9 hμ Lm c1 rc0, by rw [← m5]; exact l6, by rw [← m14]; exact l14,
    ⟨_, by rw [← m15]; exact l16, m17⟩, fun h ↦ absurd h (by omega), fun _ ↦ rfl, fun _ ↦ ?_⟩
  obtain ⟨e, he, hq⟩ := cp_rcKey hμ Lm c7 rc10
  refine ⟨e, he, ?_⟩
  have hy : σ (.n (131 + 18 * (r + 1) + 8)) = gen ^ (e + 1) := by
    rw [pow_succ, ← hq, m10, c9, mul_assoc, wInvGen_mul_gen, mul_one]
  rw [m8, hy]

/-- Group `gi`'s `κ`, key and size. -/
theorem cp_group_meaning {σ : Val} {gi : ℕ} (hgi : gi < 9) {eb : ℕ} (heb : eb ≤ 33)
    (hkb : σ (.n (2 + cpSrc gi)) = gen ^ eb)
    (hsq : ∀ j < 34, LoadHolds Lm.read (σ (.n 1)) j (gen ^ 2 ^ j))
    (hrk : ∀ k < 34, LoadHolds Lm.read (σ (.n 1)) (178 + k) (gen ^ (k * rankStride)))
    (h : CpGroupOk Lm.read σ gi) :
    eb + cpAdj gi < 34 ∧
      (∃ K, LoadHolds Lm.read (σ (.n 10)) gi K ∧
        K * gen ^ cpC0 gi = gen ^ ((eb + cpAdj gi) * rankStride)) ∧
      LoadHolds Lm.read (σ (.n 11)) gi (gen ^ (cpLen gi * 2 ^ (eb + cpAdj gi))) := by
  obtain ⟨hkv, hq, hrc, hload, hkey, hkeyL, hsqL, hch, hsz⟩ := h
  have hadj := cpAdj_le gi hgi
  have ekv : σ (.n (cpKv gi)) = gen ^ (eb + cpAdj gi) := by
    rw [hkv, hkb, tb_word_two_pow (by omega), ← pow_add]
  obtain ⟨x, hx, ex⟩ := cp_rc34 hμ Lm hq hrc
  have hκ : eb + cpAdj gi = x := tb_gen_pow_inj' (by omega) (by omega) (ekv.symm.trans ex)
  rw [ekv, tb_loadHolds_mul_gen_pow] at hload hsqL
  have e5 := tb_loadHolds_unique hload (by
    rw [add_comm]; exact hrk (eb + cpAdj gi) (by omega))
  have e1 := tb_loadHolds_unique hsqL (hsq (eb + cpAdj gi) (by omega))
  refine ⟨by omega, ⟨_, hkeyL, ?_⟩, ?_⟩
  · rw [hkey, e5, mul_assoc, cpInvWord_mul hgi, mul_one]
  · rw [hch _ le_rfl, List.take_length, cpChainExp_eq gi hgi, e1, ← pow_mul, mul_comm] at hsz
    exact hsz

/-- A group whose first column has no adjustment range-checks its `kappa_base` entry itself:
`g^x`, `x < 34`. -/
theorem cp_src_pow {σ : Val} {gi : ℕ} (h0 : cpAdj gi = 0) (h : CpGroupOk Lm.read σ gi) :
    ∃ x < 34, σ (.n (2 + cpSrc gi)) = gen ^ x := by
  obtain ⟨hkv, hq, hrc, -⟩ := h
  obtain ⟨x, hx, ex⟩ := cp_rc34 hμ Lm hq hrc
  refine ⟨x, hx, ?_⟩
  rw [hkv, h0, tb_word_two_pow (by omega), pow_zero, mul_one] at ex
  exact ex

end

/-- **`certify_placement` is sound** on every memory of at most `2^32` words. -/
theorem certify_placement_holds {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) :
    certify_placement_Spec Lm.read := by
  intro logMem ds kb sq rets hlm hl hkb0 hsq hrk h
  obtain ⟨fn, hf, hp, hb⟩ := cpFound
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb cpPre_noRet _ _).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar hret
  obtain ⟨h0, h1⟩ := hpar
  simp only [cpPre, holdsList_append,
    tb_holdsList_range_flatten 8 (fun i ↦ [Stmt.atom (.load (.n (2 + i)) (.n 0) i)])
      (fun _ ↦ rfl),
    tb_holdsList_range_flatten 9 cpGroup cpGroup_noRet,
    tb_holdsList_range_flatten 8 (fun r ↦ cpRank (r + 1)) (fun _ ↦ rfl),
    tb_holdsList_range_flatten 9 cpCols cpCols_noRet, holds_cpRank, cpRank0,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and] at hpre
  obtain ⟨hloads, hgroups, l138, c139, rc138, m143, l144, c145, m146, l145, m147, l148, hranks,
    hcols, e406, e407⟩ := hpre
  -- the table logs, from the groups' own range checks
  have hds : ∀ t < 6, LoadHolds Lm.read kb (2 + t) (σ (.n (2 + (2 + t)))) := fun t ht ↦ by
    rw [← h0]; exact hloads (2 + t) (by omega)
  have hsrc : ∀ t < 6, ∃ x < 34, σ (.n (2 + (2 + t))) = gen ^ x := fun t ht ↦ by
    obtain ⟨gi, hgi, hs2, ha0⟩ : ∃ gi < 9, cpSrc gi = 2 + t ∧ cpAdj gi = 0 :=
      ⟨t + 3, by omega, by interval_cases t <;> decide, by interval_cases t <;> decide⟩
    rw [← hs2]
    exact cp_src_pow hμ Lm ha0 (holds_cpGroup hgi (hgroups gi hgi))
  choose! xs hxs34 hxs using hsrc
  set hs : List ℕ := (List.range 6).map xs with hhsdef
  have hl' : hs.length = 6 := by simp [hs]
  have hhs : ∀ h ∈ hs, h < 34 := fun h hh ↦ by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hh
    exact hxs34 t (List.mem_range.1 ht)
  have hdsE : ds = hs.map (gen ^ ·) := by
    refine List.ext_getElem (by simp [hs, hl]) fun t h1 h2 ↦ ?_
    have ht : t < 6 := by omega
    have hk : LoadHolds Lm.read kb (t + 1 + 1) ds[t] := by
      have := hkb0 (t + 1 + 1) (by simp; omega)
      simpa only [List.getElem_cons_succ] using this
    have e := hds t ht
    rw [show 2 + t = t + 1 + 1 by omega] at e
    rw [tb_loadHolds_unique hk e, show t + 1 + 1 = 2 + t by omega, hxs t ht]
    simp [hs]
  have hkb : TbReadsAt Lm.read kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) := by
    rw [← hdsE]; exact hkb0
  refine ⟨hs, hl', hdsE, hhs, ?_⟩
  have hl : hs.length = 6 := hl'
  -- the base `[0, log_mem, τ…]` and the tables
  set ebL : List ℕ := 0 :: logMem :: hs with hebL
  have hebLlen : ebL.length = 8 := by simp [ebL, hl]
  have hkb' : TbReadsAt Lm.read kb (ebL.map (gen ^ ·)) := by simpa [ebL] using hkb
  have heb : ∀ i < 8, σ (.n (2 + i)) = gen ^ ebL.getD i 0 ∧ ebL.getD i 0 ≤ 33 := fun i hi ↦ by
    refine ⟨tb_loadHolds_unique (by rw [← h0]; exact hloads i hi)
      ((tbReadsAt_map_iff.mp hkb') i (by omega)), ?_⟩
    rcases i with _ | _ | i
    · simp [ebL]
    · simp only [ebL, List.getD_cons_succ, List.getD_cons_zero]; omega
    · simp only [ebL, List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by omega)]
      have := hhs _ (List.getElem_mem (by omega : i < hs.length))
      omega
  have hsq' : ∀ j < 34, LoadHolds Lm.read (σ (.n 1)) j (gen ^ 2 ^ j) := fun j hj ↦ by
    have := hsq j (by simp [gSquaresList]; omega)
    rw [h1]; simpa [gSquaresList] using this
  have hrk' : ∀ k < 34, LoadHolds Lm.read (σ (.n 1)) (178 + k) (gen ^ (k * rankStride)) :=
    fun k hk ↦ by
      have := tbReadsAt_gen_pow_mul.mp hrk k (by simp [rankKeysList]; omega)
      rw [h1]; simpa [rankKeysList] using this
  -- the columns' sizes
  set κc : ℕ → ℕ := fun c ↦ ebL.getD (colKappaSrc c) 0 + colKappaAdj c with hκc
  have hG : ∀ gi < 9, κc (cpC0 gi) < 34 ∧
      (∃ K, LoadHolds Lm.read (σ (.n 10)) gi K ∧
        K * gen ^ cpC0 gi = gen ^ (κc (cpC0 gi) * rankStride)) ∧
      LoadHolds Lm.read (σ (.n 11)) gi (gen ^ (cpLen gi * 2 ^ κc (cpC0 gi))) := fun gi hgi ↦
    cp_group_meaning hμ Lm hgi (heb _ (cpSrc_lt gi hgi)).2 (heb _ (cpSrc_lt gi hgi)).1 hsq' hrk'
      (holds_cpGroup hgi (hgroups gi hgi))
  obtain ⟨Kf, hKf⟩ := tb_exists_fun_of_forall (n := 9) fun gi hgi ↦ (hG gi hgi).2.1
  -- the ranks
  have hf : ∀ r < 9, CpFacts Lm.read σ r := fun r hr ↦ by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · unfold CpFacts
      simp only [cpRB, cpRK, cpRP, cpRT, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      refine ⟨cp_rc9 hμ Lm c139 rc138, by rw [← m143]; exact l144, by rw [← m146]; exact l145,
        ⟨_, by rw [← m147]; exact l148, by rw [c145, tb_word_one, one_mul]⟩,
        fun _ ↦ by rw [c145, tb_word_one], fun h ↦ absurd h (by omega),
        fun h ↦ absurd h (by omega)⟩
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      exact cpFacts_succ hμ Lm (hranks r' (by omega))
  obtain ⟨π, hπ⟩ := tb_exists_fun_of_forall (n := 9) fun r hr ↦ (hf r hr).1
  have hπ9 : ∀ r < 9, π r < 9 := fun r hr ↦ (hπ r hr).1
  have hkeyR : ∀ r < 9, σ (.n (cpRK r)) = Kf (π r) := fun r hr ↦ by
    have := (hf r hr).2.1
    rw [(hπ r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero] at this
    exact tb_loadHolds_unique this (hKf _ (hπ9 r hr)).1
  set P := tbGroupPrefix cpC0 κc π with hP
  have hstep : ∀ r < 9, σ (.n (cpRP r)) = gen ^ P r → σ (.n (cpRT r)) = gen ^ P (r + 1) :=
    fun r hr hb ↦ by
      obtain ⟨-, -, -, ⟨t, ht, et⟩, -⟩ := hf r hr
      rw [(hπ r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero] at ht
      rw [et, hb, tb_loadHolds_unique ht (hG _ (hπ9 r hr)).2.2, ← pow_add, hP,
        tb_groupPrefix_succ]
      rfl
  have hTP : ∀ r < 9, σ (.n (cpRP r)) = gen ^ P r := by
    intro r hr
    induction r with
    | zero => rw [(hf 0 hr).2.2.2.2.1 rfl]; simp [P, tbGroupPrefix]
    | succ r ih =>
      rw [(hf (r + 1) hr).2.2.2.2.2.1 (by omega), Nat.add_sub_cancel]
      exact hstep r (by omega) (ih (by omega))
  have hT : ∀ r < 9, σ (.n (cpRP r)) = gen ^ P r ∧ σ (.n (cpRT r)) = gen ^ P (r + 1) :=
    fun r hr ↦ ⟨hTP r hr, hstep r hr (hTP r hr)⟩
  have hbase : ∀ r < 9, LoadHolds Lm.read (σ (.n 137)) (π r) (gen ^ P r) := fun r hr ↦ by
    have := (hf r hr).2.2.1
    rw [(hπ r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero, (hT r hr).1] at this
    exact this
  -- the keys descend
  have hadj : ∀ r, r + 1 < 9 → κc (cpC0 (π (r + 1))) ≤ κc (cpC0 (π r)) ∧
      (κc (cpC0 (π (r + 1))) = κc (cpC0 (π r)) → π r < π (r + 1)) := fun r hr ↦ by
    obtain ⟨e, he, hrel⟩ := (hf (r + 1) hr).2.2.2.2.2.2 (by omega)
    rw [Nat.add_sub_cancel, hkeyR r (by omega), hkeyR (r + 1) hr] at hrel
    have ha := hπ9 r (by omega)
    have hb := hπ9 (r + 1) hr
    have k1 := (hKf _ ha).2
    have k2 := (hKf _ hb).2
    rw [show rankStride = 247 from rfl] at k1 k2
    have b1 := (hG _ ha).1
    have b2 := (hG _ hb).1
    have c1 := cpC0_le _ ha
    have c2 := cpC0_le _ hb
    have c1' := cpC0_mono _ ha
    have c2' := cpC0_mono _ hb
    have heq : gen ^ (κc (cpC0 (π r)) * 247 + cpC0 (π (r + 1))) =
        gen ^ (e + 1 + κc (cpC0 (π (r + 1))) * 247 + cpC0 (π r)) := by
      rw [pow_add, pow_add, pow_add, ← k1, ← k2, hrel]
      ring
    have := tb_gen_pow_inj' (by omega) (by omega) heq
    refine ⟨by omega, fun ht ↦ cpC0_lt _ ha _ hb (by omega)⟩
  -- the columns
  have hoff : ∀ r < 9, ∀ i, cpC0 (π r) + i < cpC0 (π r + 1) →
      LoadHolds Lm.read (σ (.n 293)) (cpC0 (π r) + i)
        (gen ^ (P r + i * 2 ^ κc (cpC0 (π r)))) := fun r hr i hi ↦ by
    have hg := hπ9 r hr
    obtain ⟨lstep, lbase, lcols⟩ := holds_cpCols (hcols _ hg)
    have ebs := heb _ (cpSrc_lt _ hg)
    rw [ebs.1, tb_loadHolds_mul_gen_pow, Nat.add_zero] at lstep
    have estep := tb_loadHolds_unique lstep (hsq' _ (hG _ hg).1)
    have ebase := tb_loadHolds_unique lbase (hbase r hr)
    have := lcols i (by unfold cpLen; omega)
    rw [ebase, estep, ← pow_mul, ← pow_add, mul_comm (2 ^ _) i] at this
    exact this
  have hconst : ∀ g < 9, ∀ c, cpC0 g ≤ c → c < cpC0 (g + 1) → κc c = κc (cpC0 g) :=
    fun g hg c hc1 hc2 ↦ by
      obtain ⟨e1, e2⟩ := cp_group_const g hg c (by have := cpC0_le g hg; omega) hc1 hc2
      simp only [κc, e1, e2, cpSrc, cpAdj]
  obtain ⟨hoffs, htot⟩ := tb_group_stack_cert (rd := Lm.read) (off := σ (.n 293)) (m := 9) cpC0 κc π
    cpC0_zero cpC0_mono hconst hπ9 hadj hoff
  rw [cpC0_nine] at hoffs htot
  -- the statement's sizes
  have hκ : committedKappas (columnKappas logMem guestLogBytecode hs) = (List.range 94).map κc :=
    committedKappas_columnKappas logMem hs hl
  refine ⟨σ (.n 407), ?_, columnKappas_length _ _ _, ?_⟩
  · rw [← hret, e406, e407, stackTotal, hκ, List.map_map]
    have := (hT 8 (by omega)).2
    rw [show cpRT 8 = 292 from rfl] at this
    rw [this]
    show [gen ^ tbGroupPrefix cpC0 κc π 9, _] = _
    rw [htot]
    rfl
  · rw [hκ, e407]
    refine tbReadsAt_map_iff.mpr fun c hc ↦ ?_
    rw [tb_stackOffsets_length, List.length_map, List.length_range] at hc
    exact hoffs c hc

end
end LeanVM.Guest.B1.Tables
