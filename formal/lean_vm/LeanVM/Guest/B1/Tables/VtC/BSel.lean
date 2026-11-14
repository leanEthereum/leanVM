/-
  LeanVM.Guest.B1.Tables.VtC.BSel

  `verify_tables`' block selectors complete: a table block's (`vtSelT`, hinted `g`-power digits,
  `block_selector_tab`) and a framework block's (`vtFwSelT`, hinted bits, `block_selector`), on an
  aligned offset whose digits or bits the memory holds, the callee returning the honest eq weight
  and `g^offset`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SBase
public import LeanVM.Guest.B1.Tables.Vt.SelBlocks
public import LeanVM.Guest.B1.Tables.Vt.SelFw
public import LeanVM.Guest.B1.Tables.Vt.SelMath
public import LeanVM.Guest.B1.Selectors.BlockSelectorTabComplete
public import LeanVM.Guest.B1.Selectors.BlockSelectorComplete

/-!
# The block selectors, complete (G:2178-2224)

`offBits off`: the `34` bits of an offset, as the `bitsExp` hint writes them; `selBitsOf off τ d`:
its bits `τ ..< τ + d`, whose value shifted by `τ` is the offset when it is aligned to `2^τ` and
below `2^(τ + d)` (`selBitsOf_val`); `offDigits off τ`: the `9` `g`-power digits of `off >> τ`, as
the `digitsExp` hint writes them, whose first `⌈d/4⌉` are `nibDigits (selBitsOf off τ d)`
(`offDigits_reads`).

`vtc_selblock`: a table block's statements hold, its eq weight is `eqAbove ⟨τ, off⟩` at the bus
point, its copy is it, its running sum grows by it. `vtc_fwblock`: the same for a framework block.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The `34` bits of an offset, as words. -/
def offBits (off : ℕ) : List E := (List.range 34).map fun j ↦ bitE (off.testBit j)

/-- Bits `τ ..< τ + d` of an offset. -/
def selBitsOf (off τ d : ℕ) : List Bool := (List.range d).map fun i ↦ off.testBit (τ + i)

/-- The `9` `g`-power digits of `off >> τ`. -/
def offDigits (off τ : ℕ) : List E := nibDigits (selBitsOf off τ 36)

theorem selBitsOf_length (off τ d : ℕ) : (selBitsOf off τ d).length = d := by simp [selBitsOf]

theorem offBits_length (off : ℕ) : (offBits off).length = 34 := by simp [offBits]

theorem offDigits_length (off τ : ℕ) : (offDigits off τ).length = 9 := by
  simp [offDigits, nibDigits, selBitsOf]

theorem selBitsOf_val {off τ d : ℕ} (hal : 2 ^ τ ∣ off) (hob : off < 2 ^ (τ + d)) :
    2 ^ τ * vtBitsV (selBitsOf off τ d) d = off := by
  have hq : off / 2 ^ τ < 2 ^ d := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos τ), ← pow_add, Nat.add_comm]; exact hob
  have e : vtBitsV (selBitsOf off τ d) d = off / 2 ^ τ := by
    rw [vtBitsV, bitsVal_congr (f' := (off / 2 ^ τ).testBit) (fun i hi ↦ ?_), bitsVal_testBit hq]
    rw [Nat.testBit_div_two_pow, selBitsOf, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [Nat.add_comm]
  rw [e, Nat.mul_div_cancel' hal]

/-- The selector bits the shifted pointer reads. -/
theorem selBits_reads {rd : Reader} {p : E} {off τ d : ℕ} (hd : τ + d ≤ 34)
    (h : TbReadsAt rd p (offBits off)) :
    TbReadsAt rd (p * gen ^ τ) ((selBitsOf off τ d).map bitE) := by
  have e : (selBitsOf off τ d).map bitE = ((offBits off).drop τ).take d := by
    apply List.ext_getElem (by simp [selBitsOf, offBits]; omega)
    intro i h1 _
    simp only [selBitsOf, List.length_map, List.length_range] at h1
    simp [selBitsOf, offBits]
  rw [e]
  exact tbReadsAt_take (tbReadsAt_drop h τ) d

/-- **The digits the table block's selector reads**: the first `⌈d/4⌉` of `off >> τ`'s, when
`off < 2^(τ + d)`. -/
theorem offDigits_reads {rd : Reader} {p : E} {off τ d : ℕ} (hd : d ≤ 36)
    (hob : off < 2 ^ (τ + d)) (h : TbReadsAt rd p (offDigits off τ)) :
    TbReadsAt rd p (nibDigits (selBitsOf off τ d)) := by
  have e : nibDigits (selBitsOf off τ d) = (offDigits off τ).take ((d + 3) / 4) := by
    apply List.ext_getElem (by simp [offDigits, nibDigits, selBitsOf]; omega)
    intro j h1 _
    simp only [nibDigits, selBitsOf_length, List.length_map, List.length_range] at h1
    simp only [offDigits, nibDigits, List.getElem_map, List.getElem_range, List.getElem_take,
      selBitsOf_length]
    congr 1
    refine bitsVal_congr fun t ht ↦ ?_
    simp only [selBitsOf, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hlt : 4 * j + t < d
    · simp [hlt, show 4 * j + t < 36 by omega]
    · have hz : off.testBit (τ + (4 * j + t)) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hob (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hlt, show 4 * j + t < 36 by omega, hz]
  rw [e]
  exact tbReadsAt_take h _

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

local notation "σv" => vtσ rd wo args

/-- A slice read at `vtAt` holds when its statements beyond evaluation do. -/
theorem vt_blockAt (hl : args.length = 20) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vtAt n).take blk.length) = true)
    (h : ∀ s ∈ blk, autoB s = false → VSH (coreProgram.Rel rd) rd σv s) :
    ∀ s ∈ blk, VSH (coreProgram.Rel rd) rd σv s := by
  intro s hs
  cases ha : autoB s
  · exact h s hs ha
  · exact vsh_auto hl (vt_mem_slice (vtPre_drop n ▸ heq) hs) ha

theorem vshB_eq {σ : Val} {x y : V} (h : σ x = σ y) :
    VSH (coreProgram.Rel rd) rd σ (.atom (.assertEq x y)) := by
  exact e_add_eq_zero_iff.mpr h

/-- **A dispatch**, its arm `j` named by `g^j`. -/
theorem vshB_dispatch {σ : Val} {x : V} {fs : List String} {args' rets : List V} {j : ℕ}
    (hj : j < fs.length) (hx : σ x = gen ^ j)
    (hr : coreProgram.Rel rd fs[j] (args'.map σ) (rets.map σ)) :
    VSH (coreProgram.Rel rd) rd σ (.dispatch x fs args' rets) :=
  ⟨j, hj, by rw [hx, gen_pow_eq_ofK], hr⟩

/-- **A table block's selector, complete.** -/
theorem vtc_selblock (hl : args.length = 20) {w b t pos : ℕ} {prev : Option ℕ} {es gs gw : ℕ}
    (hcheck : tbStmtsEqb (vtSelT w b t prev es gs gw)
      ((vtAt pos).take (vtSelT w b t prev es gs gw).length) = true) (ht : t < 6)
    (hes : es < w + 2) (hgs : gs < w + 4)
    (hptr : 0 < t → σv (.n es) * vtW288 = σv (.n 701) * gen ^ (288 * t) ∧
      σv (.n gs) * word gw 0 = σv (.n 702) * gen ^ (144 * t))
    {point : List E} {d τ : ℕ} (hpl : point.length = d + τ) (hml : point.length < 33)
    (hdv : σv (.n (vtShLen t)) = gen ^ d)
    (hrun : RunTables rd (σv (.n 701) * gen ^ (288 * t)) (σv (.n 702) * gen ^ (144 * t)) d
      (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take d))
    {off : ℕ} (hoff : σv (.n (vtBoffV b)) = gen ^ off) (hal : 2 ^ τ ∣ off)
    (hob : off < 2 ^ point.length)
    (hdig : TbReadsAt rd (wo w) (offDigits off τ))
    (hw0 : wo (vtSelE w t) = Placement.eqAbove ⟨τ, off⟩ point)
    (hw1 : wo (vtSelE w t + 1) = gen ^ off)
    (hlow : ∀ i < 16, (rd (Parameters.addressOfIndex i)).isSome) :
    (∀ s ∈ vtSelT w b t prev es gs gw, VSH (coreProgram.Rel rd) rd σv s) ∧
      σv (.n (vtSelE w t)) = Placement.eqAbove ⟨τ, off⟩ point ∧
      σv (.n (vtSelCopy w t prev)) = σv (.n (vtSelE w t)) ∧
      σv (.n (vtSelSum w t prev)) =
        (match prev with | none => 0 | some p => σv (.n p)) + σv (.n (vtSelE w t)) := by
  have hmem : ∀ s ∈ vtSelT w b t prev es gs gw, s ∈ vtPre :=
    fun s hs ↦ vt_mem_slice (vtPre_drop pos ▸ hcheck) hs
  have hG : ∀ s ∈ vtSelT w b t prev es gs gw, GoodS rd vtSL wo σv (fixNe s) :=
    fun s hs ↦ vt_goodS hl (hmem s hs)
  have hd33 : d < 34 := by omega
  -- the digits' buffer
  have g0 := hG (.atom (.hint (.alloc (.n w) 9))) (by simp [vtSelT])
  simp only [fixNe, GoodS, Good] at g0
  -- the table pointers
  set eqt : V := .n (if t = 0 then 701 else w + 2) with heqt_def
  set gt : V := .n (if t = 0 then 702 else w + 4) with hgt_def
  have hdm : Stmt.dispatch (.n (vtShLen t)) vtBstNames [.n w, eqt, gt]
      [.n (vtSelE w t), .n (vtSelE w t + 1)] ∈ vtSelT w b t prev es gs gw := by
    simp [vtSelT, eqt, gt]
  have heqt : σv eqt = σv (.n 701) * gen ^ (288 * t) ∧ σv gt = σv (.n 702) * gen ^ (144 * t) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp [eqt, gt]
    · have ht' : t ≠ 0 := by omega
      have c1 := hG (.atom (.const (.n (w + 1)) vtW288)) (by simp [vtSelT, ht'])
      have m2 := hG (.atom (.mul (.n (w + 2)) (.n es) (.n (w + 1)))) (by simp [vtSelT, ht'])
      have c3 := hG (.atom (.const (.n (w + 3)) (word gw 0))) (by simp [vtSelT, ht'])
      have m4 := hG (.atom (.mul (.n (w + 4)) (.n gs) (.n (w + 3)))) (by simp [vtSelT, ht'])
      simp only [fixNe, GoodS, Good, show es < w + 2 ∧ w + 1 < w + 2 from ⟨hes, by omega⟩,
        show gs < w + 4 ∧ w + 3 < w + 4 from ⟨hgs, by omega⟩] at c1 m2 c3 m4
      obtain ⟨p1, p2⟩ := hptr ht0
      simp only [eqt, gt, ht', ↓reduceIte]
      exact ⟨by rw [m2, c1, p1], by rw [m4, c3, p2]⟩
  obtain ⟨heqt, hgt⟩ := heqt
  have hrets : ∀ v ∈ [V.n (vtSelE w t), .n (vtSelE w t + 1)], σv v = wo v.idx :=
    vt_goodS (rd := rd) (w := wo) hl (hmem _ hdm)
  have e0 : σv (.n (vtSelE w t)) = Placement.eqAbove ⟨τ, off⟩ point := by
    rw [hrets _ (by simp), ← hw0]
  have e1 : σv (.n (vtSelE w t + 1)) = gen ^ off := by rw [hrets _ (by simp), ← hw1]
  -- the callee
  set bs := selBitsOf off τ d with hbs
  have hbl : bs.length = d := selBitsOf_length off τ d
  have hval := selBitsOf_val hal (by rw [Nat.add_comm, ← hpl]; exact hob)
  have hsb : TbReadsAt rd (σv (.n w)) (nibDigits bs) := by
    rw [g0]; exact offDigits_reads (by omega) (by rw [Nat.add_comm, ← hpl]; exact hob) hdig
  have hrel := block_selector_tab_complete_holds d hd33 rd (σv (.n w)) (σv eqt) (σv gt)
    bs (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take d) hbl
    (by simp; omega) (by simp; omega) (by simp [gSquaresList]; omega) hsb hlow
    (by rw [heqt, hgt]; exact hrun)
  rw [vt_eqAbove (κ := τ) hbl (by omega), hval, vt_bitsPow_sq (κ := τ) hbl (by omega), hval]
    at hrel
  -- the tail
  have hT : ∀ s ∈ vtSelTail w t prev, GoodS rd vtSL wo σv (fixNe s) :=
    fun s hs ↦ hG s (by simp only [vtSelT, List.mem_append]; exact Or.inr hs)
  have hcopy : σv (.n (vtSelCopy w t prev)) = σv (.n (vtSelE w t)) := by
    cases prev with
    | none =>
      have := hT (.atom (.copy (.n (vtSelE w t + 2)) (.n (vtSelE w t)))) (by simp [vtSelTail])
      simpa [vtSelCopy, fixNe, GoodS, Good] using this
    | some p =>
      have := hT (.atom (.copy (.n (vtSelE w t + 3)) (.n (vtSelE w t)))) (by simp [vtSelTail])
      simpa [vtSelCopy, fixNe, GoodS, Good] using this
  refine ⟨?_, e0, hcopy, ?_⟩
  swap
  · cases prev with
    | none =>
      show σv (.n (vtSelE w t)) = 0 + _
      rw [zero_add]
    | some p =>
      have := hT (.atom (.add (.n (vtSelE w t + 2)) (.n p) (.n (vtSelE w t)))) (by simp [vtSelTail])
      simpa [vtSelSum, fixNe, GoodS, Good] using this
  -- every statement
  refine vt_blockAt hl pos _ hcheck fun s hs ha ↦ ?_
  have hdl : d < vtBstNames.length := by simp [vtBstNames]; omega
  have hdisp : VSH (coreProgram.Rel rd) rd σv (.dispatch (.n (vtShLen t)) vtBstNames [.n w, eqt, gt]
      [.n (vtSelE w t), .n (vtSelE w t + 1)]) := by
    refine vshB_dispatch hdl hdv ?_
    simp only [vtBstNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
    rw [e0, e1]
    exact hrel
  have hasrt : VSH (coreProgram.Rel rd) rd σv (.atom (.assertEq (.n (vtSelE w t + 1)) (.n (vtBoffV b)))) :=
    vshB_eq (by rw [e1, hoff])
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp only [vtSelT, ↓reduceIte, List.nil_append, List.cons_append, List.mem_cons] at hs
    simp only [eqt, gt, ↓reduceIte] at hdisp
    rcases hs with rfl | rfl | rfl | rfl | hs
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha
    · exact hdisp
    · exact hasrt
    · cases prev <;> simp only [vtSelTail, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
        (try rcases hs with rfl | rfl) <;> simp [autoB, pureB, hintB] at ha
  · have ht' : t ≠ 0 := by omega
    simp only [vtSelT, ht', ↓reduceIte, List.cons_append, List.mem_cons, List.nil_append] at hs
    simp only [eqt, gt, ht', ↓reduceIte] at hdisp
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hs
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha; omega
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha; omega
    · exact hdisp
    · exact hasrt
    · cases prev <;> simp only [vtSelTail, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
        (try rcases hs with rfl | rfl) <;> simp [autoB, pureB, hintB] at ha

/-- **A framework block's selector, complete.** -/
theorem vtc_fwblock (hl : args.length = 20) {w b kv pos : ℕ} {prev : Option ℕ}
    (hcheck : tbStmtsEqb (vtFwSelT w b kv prev) ((vtAt pos).take (vtFwSelT w b kv prev).length) =
      true) (hw : 699 < w) (hkv : kv < w)
    {point : List E} (hmu : σv (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hz1 : TbReadsAt rd (σv (.n 699)) (point.map (1 + ·)))
    (hidxc : TbReadsAt rd (σv (.n 664)) vtIdxcList)
    {κ : ℕ} (hκ : σv (.n kv) = gen ^ κ) (hκμ : κ ≤ point.length)
    {off : ℕ} (hoff : σv (.n (vtBoffV b)) = gen ^ off) (hal : 2 ^ κ ∣ off)
    (hob : off < 2 ^ point.length)
    (hbits : TbReadsAt rd (wo (w + 6)) (offBits off))
    (hw0 : wo (w + 10) = Placement.eqAbove ⟨κ, off⟩ point) (hw1 : wo (w + 11) = gen ^ off)
    (hlow : LowDefB 14 rd) :
    (∀ s ∈ vtFwSelT w b kv prev, VSH (coreProgram.Rel rd) rd σv s) ∧
      σv (.n (w + 10)) = Placement.eqAbove ⟨κ, off⟩ point ∧
      σv (.n (if prev.isNone then w + 12 else w + 13)) = σv (.n (w + 10)) ∧
      σv (.n (if prev.isNone then w + 10 else w + 12)) =
        (match prev with | none => 0 | some p => σv (.n p)) + σv (.n (w + 10)) := by
  have hmem : ∀ s ∈ vtFwSelT w b kv prev, s ∈ vtPre :=
    fun s hs ↦ vt_mem_slice (vtPre_drop pos ▸ hcheck) hs
  obtain ⟨d, hpl⟩ : ∃ d, point.length = κ + d := ⟨point.length - κ, by omega⟩
  have hG : ∀ s ∈ vtFwSelT w b kv prev, GoodS rd vtSL wo σv (fixNe s) :=
    fun s hs ↦ vt_goodS hl (hmem s hs)
  have g0 := hG (.atom (.mul (.n 9) (.n w) (.n kv))) (by simp [vtFwSelT])
  have g1 := hG (.atom (.const (.n (w + 1)) vtW33)) (by simp [vtFwSelT])
  have g2 := hG (.atom (.rangeCheck (.n w) (.n (w + 2)) (.n (w + 3)) (.n (w + 4)) (.n (w + 1))))
    (by simp [vtFwSelT])
  have g6 := hG (.atom (.hint (.allocDyn (.n (w + 6)) (.n (w + 5))))) (by simp [vtFwSelT])
  have g7 := hG (.atom (.mul (.n (w + 7)) (.n (w + 6)) (.n kv))) (by simp [vtFwSelT])
  have g8 := hG (.atom (.mul (.n (w + 8)) (.n 699) (.n kv))) (by simp [vtFwSelT])
  have g9 := hG (.atom (.mul (.n (w + 9)) (.n 664) (.n kv))) (by simp [vtFwSelT])
  simp only [fixNe, GoodS, Good, show ¬ (w < 9 ∧ kv < 9) from fun h ↦ by omega,
    show w + 6 < w + 7 ∧ kv < w + 7 from ⟨by omega, by omega⟩,
    show (699 : ℕ) < w + 8 ∧ kv < w + 8 from ⟨by omega, by omega⟩,
    show (664 : ℕ) < w + 9 ∧ kv < w + 9 from ⟨by omega, by omega⟩,
    show w + 1 < w + 2 by omega, ↓reduceIte] at g0 g1 g2 g6 g7 g8 g9
  have ew : σv (.n w) = gen ^ d := by
    rw [g0, hmu, hκ, hpl, ← pow_sub₀ _ gen_ne_zero (by omega : κ ≤ κ + d), Nat.add_sub_cancel_left]
  have hrets : ∀ v ∈ [V.n (w + 10), .n (w + 11)], σv v = wo v.idx :=
    vt_goodS (rd := rd) (w := wo) hl (hmem _ (by simp [vtFwSelT] :
      Stmt.dispatch (.n w) vtBsNames [.n (w + 7), .n (w + 8), .n (w + 9)]
        [.n (w + 10), .n (w + 11)] ∈ vtFwSelT w b kv prev))
  have e10 : σv (.n (w + 10)) = Placement.eqAbove ⟨κ, off⟩ point := by
    rw [hrets _ (by simp), ← hw0]
  have e11 : σv (.n (w + 11)) = gen ^ off := by rw [hrets _ (by simp), ← hw1]
  -- the callee
  have hbl : (selBitsOf off κ d).length = d := selBitsOf_length off κ d
  have hval := selBitsOf_val hal (by rw [← hpl]; exact hob)
  have hsb : TbReadsAt rd (σv (.n (w + 7))) ((selBitsOf off κ d).map bitE) := by
    rw [g7, g6, hκ]; exact selBits_reads (by omega) hbits
  have hz1' : TbReadsAt rd (σv (.n (w + 8))) ((point.map (1 + ·)).drop κ) := by
    rw [g8, hκ]; exact tbReadsAt_drop hz1 κ
  have hic : TbReadsAt rd (σv (.n (w + 9))) ((vtIdxcList.drop κ).take d) := by
    rw [g9, hκ]; exact tbReadsAt_take (tbReadsAt_drop hidxc κ) d
  have hrel := block_selector_complete_holds d (by omega) rd
    [σv (.n (w + 7)), σv (.n (w + 8)), σv (.n (w + 9))]
    [Placement.eqAbove ⟨κ, off⟩ point, gen ^ off]
    ⟨selBitsOf off κ d, (point.map (1 + ·)).drop κ, (vtIdxcList.drop κ).take d, hbl,
      by simp; omega, by simp [vtIdxcList]; omega, hsb, hz1', hic, ?_, ?_⟩
  rotate_left
  · rw [← List.map_drop, vt_eq_plusOne, List.map_drop, vt_eqAbove (κ := κ) hbl hpl, hval]
  · rw [vt_idxcProd (κ := κ) hbl (by omega), hval]
  have hT : ∀ s ∈ vtFwTail w prev, GoodS rd vtSL wo σv (fixNe s) :=
    fun s hs ↦ hG s (by simp only [vtFwSelT, List.cons_append, List.mem_cons]; simp [hs])
  refine ⟨?_, e10, ?_, ?_⟩
  rotate_left
  · cases prev with
    | none =>
      have := hT (.atom (.copy (.n (w + 12)) (.n (w + 10)))) (by simp [vtFwTail])
      simpa [fixNe, GoodS, Good] using this
    | some p =>
      have := hT (.atom (.copy (.n (w + 13)) (.n (w + 10)))) (by simp [vtFwTail])
      simpa [fixNe, GoodS, Good] using this
  · cases prev with
    | none =>
      show σv (.n (w + 10)) = 0 + _
      rw [zero_add]
    | some p =>
      have := hT (.atom (.add (.n (w + 12)) (.n p) (.n (w + 10)))) (by simp [vtFwTail])
      simpa [fixNe, GoodS, Good] using this
  obtain ⟨r1, r2, r3⟩ := g2
  obtain ⟨hrc, -⟩ := rc_holds (κ := 14) hlow r1 r2 r3 ew (by rw [g1, vtW33_gen]) (by omega)
    (by norm_num)
  refine vt_blockAt hl pos _ hcheck fun s hs ha ↦ ?_
  simp only [vtFwSelT, List.cons_append, List.mem_cons] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hs
  · exact mulDiv_holds (rd := rd) g0 (by rw [hκ]; exact gen_pow_ne_zero _)
  · simp [autoB, pureB, hintB] at ha
  · exact hrc
  · simp [autoB, pureB, hintB] at ha
  · simp [autoB, pureB, hintB] at ha
  · simp [autoB, pureB, hintB] at ha
  · simp [autoB, pureB, hintB] at ha; omega
  · simp [autoB, pureB, hintB] at ha; omega
  · simp [autoB, pureB, hintB] at ha; omega
  · refine vshB_dispatch (j := d) (by simp [vtBsNames]; omega) ew ?_
    simp only [vtBsNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
    rw [e10, e11]
    exact hrel
  · exact vshB_eq (by rw [e11, hoff])
  · cases prev with
    | none =>
      simp [vtFwTail] at hs
      subst hs; simp [autoB, pureB, hintB] at ha
    | some p =>
      simp [vtFwTail] at hs
      rcases hs with rfl | rfl <;> simp [autoB, pureB, hintB] at ha

end

end
end LeanVM.Guest.B1.Tables
