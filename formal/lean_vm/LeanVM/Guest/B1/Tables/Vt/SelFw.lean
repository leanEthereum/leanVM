/-
  LeanVM.Guest.B1.Tables.Vt.SelFw

  `verify_tables`' framework blocks' selectors on the push side (`block_selector`).
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SelBlock
public import LeanVM.Guest.B1.Selectors.BlockSelector

/-!
# The framework blocks' selectors (G:2398-2408)

The push side's framework blocks `0, 1, 2` (state, memory, bytecode) take their selector from
`block_selector` over `1 + ζ` and the index MLE's factors above their `κ` (`vtFwSelT`).
`vt_fwblock`: the block's eq weight is `eqAbove ⟨κ, offset⟩` at the bus point.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `block_selector`'s 34 arms. -/
def vtBsNames : List String := (List.range 34).map (lName "block_selector")

/-- `index_mle`'s 34 arms. -/
def vtImNames : List String := (List.range 34).map (lName "index_mle")

/-- `2^34`'s word: the offset bits' buffer, `g^34` words. -/
abbrev vtW34 : E := word 17179869184 0

/-- A framework block's running sum and copy. -/
def vtFwTail (w : ℕ) : Option ℕ → List Stmt
  | none => [.atom (.copy (.n (w + 12)) (.n (w + 10)))]
  | some p => [.atom (.add (.n (w + 12)) (.n p) (.n (w + 10))),
      .atom (.copy (.n (w + 13)) (.n (w + 10)))]

/-- A framework block's selector statements, values from `w`, its `kappa_g` the variable `kv`. -/
def vtFwSelT (w b kv : ℕ) (prev : Option ℕ) : List Stmt :=
  [.atom (.mul (.n 9) (.n w) (.n kv)), .atom (.const (.n (w + 1)) vtW33),
    .atom (.rangeCheck (.n w) (.n (w + 2)) (.n (w + 3)) (.n (w + 4)) (.n (w + 1))),
    .atom (.const (.n (w + 5)) vtW34), .atom (.hint (.allocDyn (.n (w + 6)) (.n (w + 5)))),
    .atom (.hint (.bitsExp (.n (vtBoffV b)) 34 (.heap (.n (w + 6)) 0 34))),
    .atom (.mul (.n (w + 7)) (.n (w + 6)) (.n kv)), .atom (.mul (.n (w + 8)) (.n 699) (.n kv)),
    .atom (.mul (.n (w + 9)) (.n 664) (.n kv)),
    .dispatch (.n w) vtBsNames [.n (w + 7), .n (w + 8), .n (w + 9)] [.n (w + 10), .n (w + 11)],
    .atom (.assertEq (.n (w + 11)) (.n (vtBoffV b)))] ++
  vtFwTail w prev

theorem vtFw0_check : tbStmtsEqb (vtFwSelT 778 0 25 none)
    ((vtAt 766).take (vtFwSelT 778 0 25 none).length) = true := by
  decide +kernel

theorem vtFw1_check : tbStmtsEqb (vtFwSelT 794 1 26 (some 788))
    ((vtAt 781).take (vtFwSelT 794 1 26 (some 788)).length) = true := by
  decide +kernel

theorem vtFw2_check : tbStmtsEqb (vtFwSelT 822 2 821 (some 806))
    ((vtAt 811).take (vtFwSelT 822 2 821 (some 806)).length) = true := by
  decide +kernel

/-- Block `2`'s `kappa_g = kb[0]·g^19`. -/
theorem vt_fw2_kappa {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 821) = σ (.n 25) * gen ^ 19 := by
  have c := h.atomAt 809 (.const (.n 820) (word 524288 0)) (by decide +kernel)
  have m := h.atomAt 810 (.mul (.n 821) (.n 25) (.n 820)) (by decide +kernel)
  simp only [Atom.Holds] at c m
  rw [m, c, show (524288 : ℕ) = 2 ^ 19 by norm_num, tb_word_two_pow (by norm_num)]

theorem vt_eq_plusOne {bs : List Bool} {zs : List E} :
    ((List.zip bs (zs.map (1 + ·))).map fun p ↦ bitE p.1 + p.2).prod = bitsEq bs zs (zs.map (1 + ·)) := by
  induction bs generalizing zs with
  | nil => rfl
  | cons b bs ih =>
    cases zs with
    | nil => rfl
    | cons z zs =>
      simp only [List.map_cons, List.zip_cons_cons, List.prod_cons, bitsEq] at ih ⊢
      rw [ih]
      congr 1
      cases b
      · simp [bitE]
      · simp only [bitE, ↓reduceIte]; rw [← add_assoc, e_add_self, zero_add]

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **A framework block's selector.** -/
theorem vt_fwblock {σ : Val} (h : VtH Lm.read σ) {w b kv pos : ℕ} {prev : Option ℕ}
    (hcheck : tbStmtsEqb (vtFwSelT w b kv prev) ((vtAt pos).take (vtFwSelT w b kv prev).length) =
      true) {point : List E} (hmu : σ (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hz1 : TbReadsAt Lm.read (σ (.n 699)) (point.map (1 + ·)))
    (hidxc : ∀ t < 34, LoadHolds Lm.read (σ (.n 664)) t (1 + gen ^ 2 ^ t))
    {κ : ℕ} (hκ : σ (.n kv) = gen ^ κ) (hκb : κ < 34)
    {off : ℕ} (hoff : σ (.n (vtBoffV b)) = gen ^ off) (hob : off < 2 ^ 62) :
    κ ≤ point.length ∧ σ (.n (w + 10)) = Placement.eqAbove ⟨κ, off⟩ point ∧
      σ (.n (if prev.isNone then w + 12 else w + 13)) = σ (.n (w + 10)) ∧
      σ (.n (if prev.isNone then w + 10 else w + 12)) =
        (match prev with | none => 0 | some p => σ (.n p)) + σ (.n (w + 10)) := by
  obtain ⟨k, hs⟩ := h.sliceAt pos _ hcheck
  simp only [vtFwSelT, List.cons_append, Stmt.HoldsList, Stmt.Holds, List.map_cons,
    List.map_nil] at hs
  obtain ⟨m8, c9, rc8, -, -, -, m13, m14, m15, hdisp, q, hr⟩ := hs
  simp only [Atom.Holds] at m8 c9 m13 m14 m15 q
  obtain ⟨d, hd, hdv⟩ := vt_rc hμ Lm (K := 34) (by omega) (by norm_num)
    (by rw [c9]; exact vt_word_g33) rc8
  rw [hmu, hdv, hκ, ← pow_add] at m8
  have hpl := gen_pow_inj (by omega) (by omega) m8
  obtain ⟨j, hj, hjv, hrel⟩ := hdisp
  have hj34 : j < 34 := by simpa [vtBsNames] using hj
  rw [hdv, ← gen_pow_eq_ofK] at hjv
  have hjd : d = j := gen_pow_inj (by omega) (by omega) hjv
  subst hjd
  simp only [vtBsNames, List.getElem_map, List.getElem_range] at hrel
  have hb := block_selector_holds _ hj34 _ _ _ hrel
  simp only [BlockSelOut] at hb
  obtain ⟨bs, zs1, cs, hbl, hz1l, hcl, -, hrz1, hrc, he, hg⟩ := hb
  rw [m14, hκ] at hrz1
  rw [m15, hκ] at hrc
  have ez1 : zs1 = (point.map (1 + ·)).drop κ :=
    tbReadsAt_unique hrz1 (tbReadsAt_drop hz1 κ) (by simp; omega)
  have hidl : TbReadsAt Lm.read (σ (.n 664)) vtIdxcList := fun t ht => by
    simp only [vtIdxcList, List.length_map, List.length_range] at ht
    simp only [vtIdxcList, List.getElem_map, List.getElem_range]
    exact hidxc t ht
  have ec : cs = (vtIdxcList.drop κ).take d :=
    tbReadsAt_unique hrc (tbReadsAt_take (tbReadsAt_drop hidl κ) d)
      (by simp [vtIdxcList]; omega)
  rw [ec, vt_idxcProd hbl (by omega)] at hg
  have hoff' : gen ^ (2 ^ κ * vtBitsV bs d) = gen ^ off := by
    rw [← hoff, ← e_add_eq_zero_iff.mp q, hg]
  have e := vt_offset_bits (by omega) hob hoff'
  rw [ez1, ← List.map_drop, vt_eq_plusOne, List.map_drop, vt_eqAbove hbl (by omega), ← e] at he
  refine ⟨by omega, he, ?_, ?_⟩
  · cases prev with
    | none => exact hr.1
    | some p => exact hr.2.1
  · cases prev with
    | none => simp
    | some p => exact hr.1

end

end
end LeanVM.Guest.B1.Tables
