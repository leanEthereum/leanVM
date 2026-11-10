import Rv64Verifier.Proofs.Bus.TsPoint

/-!
# `table_sumcheck`: the weights

```rust
let mut weights = vec![ONE; tables.len()];
for (variable, &challenge) in point.iter().enumerate() {
    let equality = ONE + equality_point[variable] + challenge;
    for (index, &height) in table_log_heights.iter().enumerate() {
        weights[index] *= if height > variable { equality } else { challenge };
    }
}
```

`0x80008210` calls `from_elem` into `S - 320`; the loop over the point starts at `0x800082b4`
(`outerLoop`), the one over the heights at `0x80008368` (`innerLoop`), each `*=` a `mul` into
`S - 152` copied back. Both loops trap where the Rust indexes out of bounds: `equality_point` at
`variable`, `weights` at `index`. They reach `0x80008384` (`AtRows`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The mirror, a variable at a time -/

/-- The weights after the first `v` variables. -/
def twPre (n : ℕ) (heights : List ℕ) (equalityPoint point : List E) (v : ℕ) : List E :=
  (point.zipIdx.take v).foldl (fun weights cv ↦
      let equality := 1 + equalityPoint.getD cv.2 0 + cv.1
      heights.zipIdx.foldl (fun weights hi ↦
        weights.modify hi.2 (· * if hi.1 > cv.2 then equality else cv.1)) weights)
    (List.replicate n 1)

theorem twPre_length_eq (n : ℕ) (heights : List ℕ) (equalityPoint point : List E) :
    twPre n heights equalityPoint point point.length =
      tableWeightsRust n heights equalityPoint point := by
  simp only [twPre, tableWeightsRust]
  rw [List.take_of_length_le (by simp)]

theorem foldl_length {α : Type} (F : List E → α → List E)
    (hF : ∀ ws a, (F ws a).length = ws.length) :
    ∀ (l : List α) (ws : List E), (l.foldl F ws).length = ws.length
  | [], _ => rfl
  | a :: l, ws => by rw [List.foldl_cons, foldl_length F hF l, hF]

/-- One variable: each weight below `heights.length` times its factor. -/
theorem modifyFold_getD (g : ℕ → E → E) (hs : List ℕ) (ws : List E) (hl : hs.length ≤ ws.length)
    (j : ℕ) : (hs.zipIdx.foldl (fun ws hi ↦ ws.modify hi.2 (g hi.1)) ws).getD j 0 =
      if j < hs.length then g (hs.getD j 0) (ws.getD j 0) else ws.getD j 0 := by
  have e := modifyLoop_eq g hs [] ws hl
  simp only [List.length_nil, List.nil_append] at e
  rw [e]
  by_cases hj : j < hs.length
  · simp only [hj, ↓reduceIte]
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj]
    rfl
  · simp only [hj, ↓reduceIte]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.length_zipWith]
    congr 2
    omega

theorem twPre_length (n : ℕ) (heights : List ℕ) (equalityPoint point : List E) (v : ℕ) :
    (twPre n heights equalityPoint point v).length = n := by
  simp only [twPre]
  generalize point.zipIdx.take v = l
  suffices ∀ (l : List (E × ℕ)) (ws : List E), ws.length = n →
      (l.foldl (fun weights cv ↦ heights.zipIdx.foldl (fun weights hi ↦
        weights.modify hi.2 (· * if hi.1 > cv.2 then 1 + equalityPoint.getD cv.2 0 + cv.1
          else cv.1)) weights) ws).length = n from this l _ (by simp)
  intro l
  induction l with
  | nil => intro ws h; exact h
  | cons a l ih =>
    intro ws h
    rw [List.foldl_cons]
    exact ih _ (by rw [foldl_length _ (fun _ _ ↦ List.length_modify ..)]; exact h)

theorem twPre_succ (n : ℕ) (heights : List ℕ) (equalityPoint point : List E) (v : ℕ)
    (hv : v < point.length) :
    twPre n heights equalityPoint point (v + 1) =
      heights.zipIdx.foldl (fun weights hi ↦ weights.modify hi.2 (· * if hi.1 > v then
        1 + equalityPoint.getD v 0 + point[v] else point[v]))
        (twPre n heights equalityPoint point v) := by
  simp only [twPre]
  rw [List.take_add_one, List.foldl_append, List.getElem?_zipIdx, List.getElem?_eq_getElem hv]
  simp

/-! ## The loop over the heights -/

theorem mask_sel (c : Bool) (x y : Word) :
    x ^^^ ((0 - if c = true then 1 else 0) &&& y) = if c = true then x ^^^ y else x := by
  cases c
  · simp
  · simp only [↓reduceIte]
    rw [show (0 : Word) - 1 = BitVec.allOnes 64 by decide, BitVec.allOnes_and]

/-- The factor `if height > variable { equality } else { challenge }` from its limbs. -/
def factorOf (v h : ℕ) (c e : E) : E := if h > v then 1 + e + c else c

theorem factor_limbs (v h : ℕ) (c e : E) :
    Model.limbs (factorOf v h c e) =
      (if v < h then (Model.limbs c).1 ^^^ (Model.limbs e).1 ^^^ 1 else (Model.limbs c).1,
        if v < h then (Model.limbs c).2.1 ^^^ (Model.limbs e).2.1 else (Model.limbs c).2.1,
        if v < h then (Model.limbs c).2.2 ^^^ (Model.limbs e).2.2 else (Model.limbs c).2.2) := by
  unfold factorOf
  by_cases hv : v < h
  · simp only [gt_iff_lt, hv, ↓reduceIte, limbs_add, limbs_one]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ac_rfl
  · simp only [gt_iff_lt, hv, ↓reduceIte]

/-- What the heights loop writes: the product and the factor below `sp`, `mul`'s stack, the
weights. -/
def IW (s : MachineState) (W : Word) (n : ℕ) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 200) 72 ∨ Within a (s.getReg .x2 - 2128) 1632 ∨ Within a W (24 * n)

/-- The heights loop's head, `0x80008368`, `i` weights updated for variable `v`. -/
structure InnerAt (s uv u : MachineState) (W hp : Word) (n m v i : ℕ) (c e : E) (ws : List E)
    (hs : List ℕ) : Prop where
  pc : u.pc = 0x80008368
  x2 : u.getReg .x2 = s.getReg .x2 - 496
  x9 : u.getReg .x9 = W + BitVec.ofNat 64 (24 * i)
  x18 : u.getReg .x18 = hp + BitVec.ofNat 64 (8 * i)
  x19 : u.getReg .x19 = BitVec.ofNat 64 v
  x26 : u.getReg .x26 = BitVec.ofNat 64 (n + 1 - i)
  x8 : u.getReg .x8 = (Model.limbs c).1
  x25 : u.getReg .x25 = (Model.limbs c).2.1
  x20 : u.getReg .x20 = (Model.limbs c).2.2
  x21 : u.getReg .x21 = (Model.limbs c).1 ^^^ (Model.limbs e).1 ^^^ 1
  x22 : u.getReg .x22 = (Model.limbs e).2.1
  x23 : u.getReg .x23 = (Model.limbs e).2.2
  x24 : u.getReg .x24 = hp + BitVec.ofNat 64 (8 * (m + 1))
  frame : DFrame uv u (IW s W n)
  elems : ∀ j < n, eAt u (W + BitVec.ofNat 64 (24 * j)) =
    if j < i then ws.getD j 0 * factorOf v (hs.getD j 0) c e else ws.getD j 0

/-- The heights loop: it traps at `index = weights.len()`, or updates every weight below
`table_log_heights.len()` and reaches `0x80008298`. -/
theorem innerLoop (hMul : MulSpec) {s uv : MachineState} {W hp : Word} {n hlen m v : ℕ} {c e : E}
    {ws : List E} {hs : List ℕ} (hpre : TableSumcheckPre s) (hro : RodataOk uv)
    (hWb : n = 0 ∨ (0x20000000 ≤ W.toNat ∧ W.toNat + 24 * n ≤ 0x78000000))
    (hW3 : W.toNat % 8 = 0)
    (hH : ValidMemRange hp hlen) (hHW : Apart hp (8 * hlen) W (24 * n))
    (hHS : Apart hp (8 * hlen) (s.getReg .x2 - 2128) 2128)
    (hhs : ∀ i < hlen, (uv.getMem (hp + BitVec.ofNat 64 (8 * i))).toNat = hs.getD i 0)
    (hm : m = min n (hlen - 1)) (hl1 : 1 ≤ hlen) (hv : v < 2 ^ 32) (hn : n < 2 ^ 32) :
    ∀ k i u, m + 1 - i = k → i ≤ m → InnerAt s uv u W hp n m v i c e ws hs →
      ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80008298 ∧ hlen ≤ n ∧
        t.getReg .x2 = s.getReg .x2 - 496 ∧ t.getReg .x19 = BitVec.ofNat 64 v ∧
        t.getReg .x24 = hp + BitVec.ofNat 64 (8 * (m + 1)) ∧ DFrame uv t (IW s W n) ∧
        ∀ j < n, eAt t (W + BitVec.ofNat 64 (24 * j)) =
          if j < hlen then ws.getD j 0 * factorOf v (hs.getD j 0) c e else ws.getD j 0) ∨
        Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hrs := hpre.stack.rodata
  simp only [stack_eq] at hrs
  have hHb := ValidMemRange.bounds hH (by omega)
  intro k
  induction k with
  | zero => intro i u hk hi; omega
  | succ k ih =>
    intro i u hk hi h
    -- `0x80008368`: `index < weights.len()`
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008368_spec h.pc trivial
    have k₁ := b80008368_keeps h₁
    have hm₁ := b80008368_mem_same h₁
    by_cases hin : i = n
    · exact ⟨u₁, hr₁, Or.inr (trap (b80008368_pc_taken h₁ (by
        rw [h.x26, hin]; addr_omega [hm, hi])))⟩
    have hin' : i < n := by omega
    have hih : i < hlen := by omega
    have hW1 : 0x20000000 ≤ W.toNat := by
      rcases hWb with h0 | h0
      · omega
      · exact h0.1
    have hW2 : W.toNat + 24 * n ≤ 0x78000000 := by
      rcases hWb with h0 | h0
      · omega
      · exact h0.2
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80008370_spec
      (b80008368_pc_not_taken h₁ (by rw [h.x26]; addr_omega [hm, hi, hin', hn])) (by
        rv_eval [k₁ .x18 (by decide), h.x18]
        valid_access hH [hHb, hih])
    have hm₂ := b80008370_mem_same h₂
    have k₂ := b80008370_keeps h₂
    have hh : u₁.getMem (u₁.getReg .x18) = uv.getMem (hp + BitVec.ofNat 64 (8 * i)) := by
      rw [k₁ .x18 (by decide), h.x18, hm₁]
      exact h.frame _ fun j hj hw ↦ by
        rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hHW, hHS, hHb, hih, hW1, hW2, hb1]
    set hgt := (hs.getD i 0) with hgtdef
    have hhv : (u₁.getMem (u₁.getReg .x18)).toNat = hgt := by rw [hh]; exact hhs i hih
    -- the factor's low limb in `a0`, at `0x80008308`
    obtain ⟨u₃, hr₃, hpc₃, hm₃, hx10₃, k₃⟩ : ∃ u₃, Reaches Image.code u₂ u₃ ∧
        u₃.pc = 0x80008308 ∧ (∀ a, u₃.getMem a = u₂.getMem a) ∧
        u₃.getReg .x10 = (if v < hgt then u₂.getReg .x21 else u₂.getReg .x8) ∧
        ∀ r, r ≠ .x10 → u₃.getReg r = u₂.getReg r := by
      have hx19 : (u₁.getReg .x19).toNat = v := by
        rw [k₁ .x19 (by decide), h.x19, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      by_cases hlt : v < hgt
      · refine ⟨u₂, Reaches.refl _, b80008370_pc_taken h₂ (by rw [hx19, hhv]; exact hlt),
          fun _ ↦ rfl, by
          simp only [hlt, ↓reduceIte]; exact (b80008370_x10 h₂).trans (k₂ .x21 (by decide)).symm,
          fun _ _ ↦ rfl⟩
      · obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000837c_spec
          (b80008370_pc_not_taken h₂ (by rw [hx19, hhv]; omega)) trivial
        refine ⟨u₃, hr₃, b8000837c_pc h₃, b8000837c_mem_same h₃, by
          simp only [hlt, ↓reduceIte]; rw [b8000837c_x10 h₃], fun r hr ↦ ?_⟩
        have := b8000837c_keeps h₃
        rcases r <;> first | (exfalso; exact hr rfl) | exact this _ (by decide) | rfl
    have R3 (r : Reg) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h26 : r ≠ .x26) :
        u₃.getReg r = u.getReg r := by
      rw [k₃ r h10]
      rcases r <;> first
        | (exfalso; exact h10 rfl) | (exfalso; exact h11 rfl) | (exfalso; exact h26 rfl)
        | (rw [k₂ _ (by decide), k₁ _ (by decide)]) | rfl
    have hx2₃ : u₃.getReg .x2 = s.getReg .x2 - 496 := (R3 .x2 (by decide) (by decide) (by decide)).trans h.x2
    have hx9₃ : u₃.getReg .x9 = W + BitVec.ofNat 64 (24 * i) :=
      (R3 .x9 (by decide) (by decide) (by decide)).trans h.x9
    have hx11₃ : (u₃.getReg .x11).toNat = hgt := by
      rw [k₃ .x11 (by decide), b80008370_x11 h₂]; exact hhv
    have hx19₃ : u₃.getReg .x19 = BitVec.ofNat 64 v := (R3 .x19 (by decide) (by decide) (by decide)).trans h.x19
    have hult : (u₃.getReg .x19).ult (u₃.getReg .x11) = decide (v < hgt) := by
      rw [BitVec.ult, hx11₃, hx19₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    -- `0x80008308`: the factor at `S - 200`, `mul` into `S - 152`
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008308_spec hpc₃ (by
      rv_eval [hx2₃]; and_intros <;> valid_access hval [hb1])
    have k₄ := b80008308_keeps h₄
    have hf₄ := DFrame.of_memFrame (b80008308_frame h₄ (by rw [hx2₃]; addr_omega [hb1]))
    rw [hx2₃, show s.getReg .x2 - 496 + 296 = s.getReg .x2 - 200 by addr_omega [hb1]] at hf₄
    have hfac : eAt u₄ (s.getReg .x2 - 200) = factorOf v hgt c e := by
      apply eAt_eq_of_limbs
      rw [factor_limbs]
      have m0 := b80008308_m_x2_296 h₄
      have m1 : u₄.getMem (u₃.getReg .x2 + 304) = u₃.getReg .x25 ^^^
          ((0 - if (u₃.getReg .x19).ult (u₃.getReg .x11) = true then 1 else 0) &&&
            u₃.getReg .x22) :=
        h₄.mem_eq 1 (by decide) (by rv_eval []) (by rv_eval []; rfl)
      have m2 : u₄.getMem (u₃.getReg .x2 + 312) = u₃.getReg .x20 ^^^
          ((0 - if (u₃.getReg .x19).ult (u₃.getReg .x11) = true then 1 else 0) &&&
            u₃.getReg .x23) :=
        h₄.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval []; rfl)
      rw [mask_sel, hult] at m1 m2
      rw [hx2₃] at m0 m1 m2
      rv_eval [] at m0 m1 m2
      rw [show s.getReg .x2 - 200 + 8 = s.getReg .x2 - 192 by addr_omega [hb1],
        show s.getReg .x2 - 200 + 16 = s.getReg .x2 - 184 by addr_omega [hb1], m0, m1, m2, hx10₃,
        R3 .x20 (by decide) (by decide) (by decide), R3 .x22 (by decide) (by decide) (by decide),
        R3 .x23 (by decide) (by decide) (by decide), R3 .x25 (by decide) (by decide) (by decide),
        k₂ .x21 (by decide), k₂ .x8 (by decide), k₁ .x21 (by decide), k₁ .x8 (by decide),
        h.x8, h.x20, h.x21, h.x22, h.x23, h.x25]
      by_cases hlt : v < hgt <;> simp [hlt]
    have hx2₄ : u₄.getReg .x2 = s.getReg .x2 - 496 := (k₄ .x2 (by decide)).trans hx2₃
    have hx10₄ : u₄.getReg .x10 = s.getReg .x2 - 152 := by
      rw [b80008308_x10 h₄, hx2₃]; addr_omega [hb1]
    have hx11₄ : u₄.getReg .x11 = W + BitVec.ofNat 64 (24 * i) := by rw [b80008308_x11 h₄, hx9₃]
    have hx12₄ : u₄.getReg .x12 = s.getReg .x2 - 200 := by
      rw [b80008308_x12 h₄, hx2₃]; addr_omega [hb1]
    have hWi : ValidMemRange (W + BitVec.ofNat 64 (24 * i)) 3 :=
      heap_range (by addr_omega [hW1, hW2, hin']) (by addr_omega [hW1, hW2, hin'])
        (by addr_omega [hW1, hW2, hW3, hin'])
    have hsl : stackLo u₄ mulStack = s.getReg .x2 - 1520 := by
      simp only [stackLo, mulStack, hx2₄]; addr_omega [hb1]
    -- the frame so far
    have hfu₄ : DFrame u u₄ (Within · (s.getReg .x2 - 200) 24) :=
      (DFrame.of_same (fun a ↦ (hm₃ a).trans ((hm₂ a).trans (hm₁ a))) _).trans hf₄ fun _ h ↦ h
    have hro₄ : RodataOk u₄ := hro.dframe ((h.frame.trans hfu₄ fun a ha ↦ Or.inl
      (by addr_omega [ha, hb1])) : DFrame uv u₄ (IW s W n)) fun a ha hw ↦ by
        rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hrs, hb1, hW1, hW2]
    have hpre₅ : MulPre u₄ := {
      out := by rw [hx10₄]; valid_sub hval [hb1]
      lhs := by rw [hx11₄]; exact hWi
      rhs := by rw [hx12₄]; valid_sub hval [hb1]
      stack := ⟨by rw [hsl]; valid_sub hval [hb1], by rw [hx2₄]; addr_omega [hb1, hb3]⟩
      outLhs := by rw [hx10₄, hx11₄]; addr_omega [hb1, hW1, hW2, hin']
      outRhs := by rw [hx10₄, hx12₄]; addr_omega [hb1]
      outStack := by rw [hx10₄, hsl]; addr_omega [hb1]
      lhsStack := by rw [hx11₄, hsl]; addr_omega [hb1, hW1, hW2, hin']
      rhsStack := by rw [hx12₄, hsl]; addr_omega [hb1]
      rodata := hro₄
      stackRodata := by rw [hsl]; addr_omega [hrs, hb1] }
    obtain ⟨u₅, hr₅, ⟨hpc₅, hp₅, post₅⟩ | hd⟩ := hMul.call hr₄ (b80008308_pc h₄) hpre₅
    swap
    · exact ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans hr₅)), Or.inr hd⟩
    have hprod : eAt u₅ (s.getReg .x2 - 152) = ws.getD i 0 * factorOf v hgt c e := by
      have hv₅ := post₅.value
      rw [hx10₄, hx11₄, hx12₄, hfac] at hv₅
      rw [hv₅, hfu₄.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb1, hW1, hW2, hin'], h.elems i hin']
      simp
    have R5 (r : Reg) (hr : r ∈ calleeSaved) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h26 : r ≠ .x26)
        (h4 : r ∈ ([.x2, .x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26] : List Reg)) :
        u₅.getReg r = u.getReg r := by
      rw [hp₅ r hr, k₄ r (mem_of_mem h4 _), R3 r h10 h11 h26]
    have hx2₅ : u₅.getReg .x2 = s.getReg .x2 - 496 := (hp₅.reg .x2).trans hx2₄
    have hx9₅ : u₅.getReg .x9 = W + BitVec.ofNat 64 (24 * i) := (hp₅.reg .x9).trans ((k₄ .x9 (by decide)).trans hx9₃)
    -- `0x80008348`: `weights[index]` is the product
    obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80008348_spec
      (by rw [hpc₅, returnAddress_eq, b80008308_x1 h₄]; decide) (by
        rv_eval [hx2₅, hx9₅]
        and_intros <;> first
          | valid_access hval [hb1]
          | valid_access hWi [hW1, hW2, hin']
          | addr_omega [hb1, hW1, hW2, hin'])
    have k₆ := b80008348_keeps h₆
    have hf₆ := DFrame.of_memFrame (b80008348_frame h₆ (by rw [hx9₅]; addr_omega [hW1, hW2, hin']))
    rw [hx9₅] at hf₆
    have hnew : eAt u₆ (W + BitVec.ofNat 64 (24 * i)) = ws.getD i 0 * factorOf v hgt c e := by
      rw [← hprod, ← hx9₅]
      apply eAt_congr
      · rw [b80008348_m_x9_0 h₆, hx2₅]; congr 1; addr_omega [hb1]
      · rw [b80008348_m_x9_8 h₆, hx2₅, show s.getReg .x2 - 152 + 8 = s.getReg .x2 - 496 + 352 by
          addr_omega [hb1]]
      · rw [b80008348_m_x9_16 h₆, hx2₅, show s.getReg .x2 - 152 + 16 = s.getReg .x2 - 496 + 360 by
          addr_omega [hb1]]
    have hf₅ : DFrame u₄ u₅ fun a ↦ Within a (s.getReg .x2 - 152) 24 ∨
        Within a (s.getReg .x2 - 1520) 1024 := fun a ha ↦ by
      have h0 := ha 0 (by decide)
      rw [add_ofNat_zero] at h0
      refine post₅.frame a (fun hw ↦ h0 (Or.inl ?_)) (fun hw ↦ h0 (Or.inr ?_))
      · rwa [hx10₄] at hw
      · rwa [hsl] at hw
    have hfr : DFrame uv u₆ (IW s W n) := ((h.frame.trans hfu₄ fun a ha ↦ Or.inl
      (by addr_omega [ha, hb1])).trans hf₅ fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl (by addr_omega [ha, hb1])
        · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))).trans hf₆
      fun a ha ↦ Or.inr (Or.inr (by addr_omega [ha, hW1, hW2, hin']))
    have hel (j : ℕ) (hj : j < n) : eAt u₆ (W + BitVec.ofNat 64 (24 * j)) =
        if j < i + 1 then ws.getD j 0 * factorOf v (hs.getD j 0) c e else ws.getD j 0 := by
      by_cases hji : j = i
      · subst hji
        rw [hnew]; simp [hgtdef]
      · have e1 : eAt u₆ (W + BitVec.ofNat 64 (24 * j)) = eAt u (W + BitVec.ofNat 64 (24 * j)) := by
          rw [hf₆.eAt fun k hk hw ↦ by addr_omega [hw, hk, hW1, hW2, hin', hj, hji],
            hf₅.eAt fun k hk hw ↦ by
              rcases hw with hw | hw <;> addr_omega [hw, hk, hb1, hW1, hW2, hj],
            hfu₄.eAt fun k hk hw ↦ by addr_omega [hw, hk, hb1, hW1, hW2, hj]]
        rw [e1, h.elems j hj]
        by_cases hlt : j < i
        · simp [hlt, show j < i + 1 by omega]
        · simp [hlt, show ¬ j < i + 1 by omega]
    have hx18₅ : u₅.getReg .x18 = hp + BitVec.ofNat 64 (8 * (i + 1)) := by
      rw [hp₅.reg .x18, b80008308_x18 h₄, R3 .x18 (by decide) (by decide) (by decide), h.x18]
      addr_omega [hHb, hih]
    have hx24₅ : u₅.getReg .x24 = hp + BitVec.ofNat 64 (8 * (m + 1)) :=
      (R5 .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x24
    have hreach := hr₁.trans (hr₂.trans (hr₃.trans (hr₅.trans hr₆)))
    by_cases hlast : i = m
    · subst hlast
      have hmh : i + 1 = hlen := by omega
      refine ⟨u₆, hreach, Or.inl ⟨b80008348_pc_taken h₆ (by rw [hx18₅, hx24₅]), by omega,
        by rw [k₆ .x2 (by decide), hx2₅], ?_, by rw [k₆ .x24 (by decide), hx24₅], hfr,
        fun j hj ↦ by rw [hel j hj, hmh]⟩⟩
      rw [k₆ .x19 (by decide), R5 .x19 (by decide) (by decide) (by decide) (by decide) (by decide),
        h.x19]
    · obtain ⟨t, hrt, ht⟩ := ih (i + 1) u₆ (by omega) (by omega) {
        pc := b80008348_pc_not_taken h₆ (by rw [hx18₅, hx24₅]; addr_omega [hHb, hm, hi, hlast])
        x2 := by rw [k₆ .x2 (by decide), hx2₅]
        x9 := by
          rw [b80008348_x9 h₆, hp₅.reg .x27, b80008308_x27 h₄, hx9₃]; addr_omega [hW1, hW2, hin']
        x18 := by rw [k₆ .x18 (by decide), hx18₅]
        x19 := by rw [k₆ .x19 (by decide), R5 .x19 (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x19]
        x26 := by
          rw [k₆ .x26 (by decide), hp₅.reg .x26, k₄ .x26 (by decide), k₃ .x26 (by decide),
            k₂ .x26 (by decide), b80008368_x26 h₁, h.x26]
          addr_omega [hin', hn]
        x8 := by rw [k₆ .x8 (by decide), R5 .x8 (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x8]
        x25 := by rw [k₆ .x25 (by decide), R5 .x25 (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x25]
        x20 := by rw [k₆ .x20 (by decide), R5 .x20 (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x20]
        x21 := by rw [k₆ .x21 (by decide), R5 .x21 (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x21]
        x22 := by rw [k₆ .x22 (by decide), R5 .x22 (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x22]
        x23 := by rw [k₆ .x23 (by decide), R5 .x23 (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x23]
        x24 := by rw [k₆ .x24 (by decide), hx24₅]
        frame := hfr
        elems := hel }
      exact ⟨t, hreach.trans hrt, ht⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
