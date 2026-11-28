/-
  LeanVM.Guest.B1.VsC.VsPh2

  `verify_sub`'s tables' sizes: the six `table_size` dispatches and the checks after each
  (windows `7 ..< 18` of `wA`, and the least-height branch's arm).
-/

module

public import LeanVM.Guest.B1.VsC.VsSel
public import LeanVM.Guest.B1.VsC.LeavesA
import LeanVM.Guest.B1.Link.Forms

/-!
# Phase 2: the tables' sizes

Table `t`'s height `h` is certified by `table_size__L{h}` on its row count `R` and a buffer of its bits,
returning `g^R`, `lead`, `rest` (`table_size_leafA`); the body then checks `lead = 1` and
`rest ≠ 0` (`tsChk n`, the returns at `.n n`, `.n (n + 1)`, `.n (n + 2)`), the least-height terms, which
pass exactly when `h = 0` or `2^(h - 1) < R` (`tsLeadRest_iff`): what `buildLayout`'s height
`max(log2_ceil R, floor)` gives (`VsShape.height_least`) for the tables with floor `0`. The
`KECCAK` table's (floor `9`) checks sit in the least-height branch's arm `vsI1n = tsChk 224`, taken when
its height is not `9`.

* `tsChk_pureF`: the six check atoms' side conditions from the returns.
* `tsRun n x pp pv off`: the run after table `t ≥ 1`'s dispatch (`tsChk n`, the product of the `g^R`,
  the next height `.n x` range checked below `g^24`, the next row count loaded from the sizes' buffer at
  `off`, the next bits' buffer `26` words on); `tsRun0` after table `0`'s. `tsRun_runHyp`,
  `tsRun0_runHyp`: their hypotheses.
* `ts_disp`: a dispatch window's hypotheses from `table_size_leafA`, the rest at its end.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- The least-height checks on `table_size`'s returns at `.n n`, `.n (n + 1)`, `.n (n + 2)`. -/
def tsChk (n m : ℕ) : List Atom := [
    .const (.n m) (word 1 0),
    .assertEq (.n (n + 1)) (.n m),
    .const (.n (m + 1)) (word 0 0),
    .add (.n (m + 2)) (.n (n + 2)) (.n (m + 1)),
    .hint (.inverse (.n (m + 2)) (.n (m + 3))),
    .assertNe (.n (m + 2)) (.n (m + 3)) (.n (m + 4))]

/-- The run after table `t ≥ 1`'s dispatch. -/
def tsRun (n x pp pv off : ℕ) : List Atom := tsChk n (n + 3) ++ [
    .mul (.n (n + 8)) (.n pp) (.n n),
    .const (.n (n + 9)) (word 16777216 0),
    .rangeCheck (.n x) (.n (n + 10)) (.n (n + 11)) (.n (n + 12)) (.n (n + 9)),
    .load (.n (n + 13)) (.n 56) off,
    .const (.n (n + 14)) (word 67108864 0),
    .mul (.n (n + 15)) (.n pv) (.n (n + 14))]

/-- The run after table `0`'s dispatch. -/
def tsRun0 : List Atom := tsChk 145 148 ++ [
    .const (.n 153) (word 16777216 0),
    .rangeCheck (.n 116) (.n 154) (.n 155) (.n 156) (.n 153),
    .load (.n 157) (.n 56) 1,
    .const (.n 158) (word 67108864 0),
    .mul (.n 159) (.n 7) (.n 158)]

theorem one_eq_word : word 1 0 = 1 := (wordG (j := 0) (by norm_num) : word 1 0 = gen ^ 0).trans (pow_zero _)

theorem zero_eq_word : word 0 0 = 0 := by decide

section
variable {k : ℕ} {rd0 : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- **The least-height checks' side conditions** from `table_size`'s returns, where they pass. -/
theorem tsChk_pureF {n m R h : ℕ} (hg : ∀ a ∈ tsChk n m, Good rd0 S w σ (fixA a)) (hh : h ≤ 24)
    (hR : R ≤ 2 ^ h) (hl : h = 0 ∨ 2 ^ (h - 1) < R) (h1 : σ (.n (n + 1)) = tsLeadW R h)
    (h2 : σ (.n (n + 2)) = tsRestW R h) :
    ∀ x ∈ tsChk n m, PureF k σ x := by
  obtain ⟨hlead, hrest⟩ := (tsLeadRest_iff hh hR).mpr hl
  have h3 : σ (.n m) = 1 := (hg (.const _ _) (by simp [tsChk])).trans one_eq_word
  have h4 : σ (.n (m + 1)) = 0 := (hg (.const _ _) (by simp [tsChk])).trans zero_eq_word
  have h5 : σ (.n (m + 2)) = tsRestW R h := by
    have := hg (.add (.n (m + 2)) (.n (n + 2)) (.n (m + 1))) (by simp [tsChk])
    simp only [fixA, Good] at this
    rw [this, h2, h4, add_zero]
  have h6 : σ (.n (m + 3)) = (tsRestW R h)⁻¹ := by
    have := hg (.hint (.inverse (.n (m + 2)) (.n (m + 3)))) (by simp [tsChk])
    simp only [fixA, Good] at this
    rw [this, h5]
  intro x hx
  simp only [tsChk, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · show σ (.n (n + 1)) + σ (.n m) = 0
    rw [h1, h3, hlead]; exact Link.add_self_E 1
  · trivial
  · trivial
  · trivial
  · show σ (.n (m + 2)) * σ (.n (m + 3)) = 1
    rw [h5, h6, mul_inv_cancel₀ hrest]

end

theorem ptrAt_add (c j : ℕ) : ptrAt c * gen ^ j = ptrAt (c + j) := by
  show ofK (addressOfIndex c) * gen ^ j = ofK (addressOfIndex (c + j))
  rw [← Value.gen_pow_eq_ofK, ← Value.gen_pow_eq_ofK, pow_add]

section
variable {k : ℕ} {rd0 : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **The run after table `t ≥ 1`'s dispatch**: its hypotheses, the next row count, and the next bits'
buffer `26` words on. -/
theorem tsRun_runHyp {n x pp pv off : ℕ} (hk : 6 ≤ k) (hpp : pp < n + 8) (hpv' : pv < n + 15)
    (hg : ∀ a ∈ tsRun n x pp pv off, Good rd0 S w σ (fixA a))
    (hS : Atom.load (.n (n + 13)) (.n 56) off ∉ S)
    {Rt h h' b56 c a : ℕ} (hh : h ≤ 24) (hR : Rt ≤ 2 ^ h) (hl : h = 0 ∨ 2 ^ (h - 1) < Rt)
    (h1 : σ (.n (n + 1)) = tsLeadW Rt h) (h2 : σ (.n (n + 2)) = tsRestW Rt h)
    (hh' : h' ≤ 24) (hxv : σ (.n x) = gen ^ h')
    (p56 : σ (.n 56) = ptrAt b56) (bs : List E) (hoff : off < bs.length) (r56 : ReadsAt rd0 (ptrAt b56) bs)
    (hpv : σ (.n pv) = ptrAt c)
    {D : ℕ → Prop} {O : Reader → Prop} (hOb : Own (b56 + off))
    (hrd : ∀ rd, O rd → ReadsAt rd (ptrAt b56) bs) :
    RunHyp k σ w a Own R D Pre O (tsRun n x pp pv off) ∧ σ (.n (n + 13)) = bs[off] ∧
      σ (.n (n + 15)) = ptrAt (c + 26) := by
  have hgc : ∀ a ∈ tsChk n (n + 3), Good rd0 S w σ (fixA a) := fun a ha => hg a (List.mem_append_left _ ha)
  have mem : ∀ a ∈ [Atom.mul (.n (n + 8)) (.n pp) (.n n), .const (.n (n + 9)) (word 16777216 0),
      .rangeCheck (.n x) (.n (n + 10)) (.n (n + 11)) (.n (n + 12)) (.n (n + 9)),
      .load (.n (n + 13)) (.n 56) off, .const (.n (n + 14)) (word 67108864 0),
      .mul (.n (n + 15)) (.n pv) (.n (n + 14))], a ∈ tsRun n x pp pv off := fun a ha =>
    List.mem_append_right _ ha
  have h9 : σ (.n (n + 9)) = gen ^ 24 := (hg (.const _ _) (mem _ (by simp))).trans (wordG (j := 24) (by norm_num))
  have h14 : σ (.n (n + 14)) = gen ^ 26 :=
    (hg (.const _ _) (mem _ (by simp))).trans (wordG (j := 26) (by norm_num))
  have h10 : σ (.n (n + 10)) = gen ^ (24 - h') := by
    have := (hg (.rangeCheck (.n x) (.n (n + 10)) (.n (n + 11)) (.n (n + 12)) (.n (n + 9))) (mem _ (by simp))).2.2
    have hl' : (V.n (n + 9)).idx < (V.n (n + 10)).idx := by show n + 9 < n + 10; omega
    simp only [hl', ↓reduceIte] at this
    rw [this, h9, hxv, gen_div hh']
  have h13 : σ (.n (n + 13)) = bs[off] :=
    good_loadAt hS (hg (.load (.n (n + 13)) (.n 56) off) (mem _ (by simp))) p56 hoff r56
  have h15 : σ (.n (n + 15)) = ptrAt (c + 26) := by
    have := hg (.mul (.n (n + 15)) (.n pv) (.n (n + 14))) (mem _ (by simp))
    have hc : (V.n pv).idx < (V.n (n + 15)).idx ∧ (V.n (n + 14)).idx < (V.n (n + 15)).idx :=
      ⟨hpv', by show n + 14 < n + 15; omega⟩
    simp only [fixA, Good, hc, and_self, ↓reduceIte] at this
    rw [this, hpv, h14, ptrAt_add]
  have hh0 : heapHintAddrs σ ((tsRun n x pp pv off).map Ev.atom) = [] := rfl
  refine ⟨⟨rfl, ?_, fun A hA => by rw [hh0] at hA; simp at hA, ?_, ?_⟩, h13, h15⟩
  · intro A hA
    obtain ⟨d, p, off', hm, rfl⟩ := mem_loadAddrs hA
    simp only [tsRun, tsChk, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_or, Atom.load.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨b56 + off', by rw [p56, ptrAt, B1.Main.addr_ofK], Or.inl hOb⟩
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact tsChk_pureF hgc hh hR hl h1 h2 y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · show (if (V.n pp).idx < (V.n (n + 8)).idx ∧ (V.n n).idx < (V.n (n + 8)).idx then True else σ (.n n) ≠ 0)
      split
      · trivial
      · next hc => exact absurd ⟨hpp, by show n < n + 8; omega⟩ hc
    · trivial
    · exact ⟨by rw [hxv]; exact lowW_pow (lt_two_pow_k hk (by omega)),
        by rw [h10]; exact lowW_pow (lt_two_pow_k hk (by omega))⟩
    · trivial
    · trivial
    · show (if (V.n pv).idx < (V.n (n + 15)).idx ∧ (V.n (n + 14)).idx < (V.n (n + 15)).idx then True
        else σ (.n (n + 14)) ≠ 0)
      split
      · trivial
      · next hc => exact absurd ⟨hpv', by show n + 14 < n + 15; omega⟩ hc
  · intro rd _ _ ho y hy
    rcases List.mem_append.mp hy with hy | hy
    · simp only [tsChk, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · trivial
    · show LoadHolds rd (σ (.n 56)) off (σ (.n (n + 13)))
      rw [p56, h13]; exact hrd rd ho off hoff
    · trivial
    · trivial

/-- **The run after table `0`'s dispatch**: its hypotheses, the next row count, the next bits' buffer. -/
theorem tsRun0_runHyp (hk : 6 ≤ k) (hg : ∀ a ∈ tsRun0, Good rd0 S w σ (fixA a))
    (hS : Atom.load (.n 157) (.n 56) 1 ∉ S)
    {Rt h h' b56 c a : ℕ} (hh : h ≤ 24) (hR : Rt ≤ 2 ^ h) (hl : h = 0 ∨ 2 ^ (h - 1) < Rt)
    (h1 : σ (.n 146) = tsLeadW Rt h) (h2 : σ (.n 147) = tsRestW Rt h)
    (hh' : h' ≤ 24) (hxv : σ (.n 116) = gen ^ h')
    (p56 : σ (.n 56) = ptrAt b56) (bs : List E) (hoff : 1 < bs.length) (r56 : ReadsAt rd0 (ptrAt b56) bs)
    (hpv : σ (.n 7) = ptrAt c)
    {D : ℕ → Prop} {O : Reader → Prop} (hOb : Own (b56 + 1))
    (hrd : ∀ rd, O rd → ReadsAt rd (ptrAt b56) bs) :
    RunHyp k σ w a Own R D Pre O tsRun0 ∧ σ (.n 157) = bs[1] ∧ σ (.n 159) = ptrAt (c + 26) := by
  have hgc : ∀ a ∈ tsChk 145 148, Good rd0 S w σ (fixA a) := fun a ha => hg a (List.mem_append_left _ ha)
  have mem : ∀ a ∈ [Atom.const (.n 153) (word 16777216 0),
      .rangeCheck (.n 116) (.n 154) (.n 155) (.n 156) (.n 153), .load (.n 157) (.n 56) 1,
      .const (.n 158) (word 67108864 0), .mul (.n 159) (.n 7) (.n 158)], a ∈ tsRun0 := fun a ha =>
    List.mem_append_right _ ha
  have h9 : σ (.n 153) = gen ^ 24 := (hg (.const _ _) (mem _ (by simp))).trans (wordG (j := 24) (by norm_num))
  have h14 : σ (.n 158) = gen ^ 26 := (hg (.const _ _) (mem _ (by simp))).trans (wordG (j := 26) (by norm_num))
  have h10 : σ (.n 154) = gen ^ (24 - h') := by
    have := (hg (.rangeCheck (.n 116) (.n 154) (.n 155) (.n 156) (.n 153)) (mem _ (by simp))).2.2
    have hl' : (V.n 153).idx < (V.n 154).idx := by decide
    simp only [hl', ↓reduceIte] at this
    rw [this, h9, hxv, gen_div hh']
  have h13 : σ (.n 157) = bs[1] := good_loadAt hS (hg (.load (.n 157) (.n 56) 1) (mem _ (by simp))) p56 hoff r56
  have h15 : σ (.n 159) = ptrAt (c + 26) := by
    have := hg (.mul (.n 159) (.n 7) (.n 158)) (mem _ (by simp))
    have hc : (V.n 7).idx < (V.n 159).idx ∧ (V.n 158).idx < (V.n 159).idx := by decide
    simp only [fixA, Good, hc, and_self, ↓reduceIte] at this
    rw [this, hpv, h14, ptrAt_add]
  have hh0 : heapHintAddrs σ (tsRun0.map Ev.atom) = [] := rfl
  refine ⟨⟨rfl, ?_, fun A hA => by rw [hh0] at hA; simp at hA, ?_, ?_⟩, h13, h15⟩
  · intro A hA
    obtain ⟨d, p, off', hm, rfl⟩ := mem_loadAddrs hA
    simp only [tsRun0, tsChk, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_or, Atom.load.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨b56 + 1, by rw [p56, ptrAt, B1.Main.addr_ofK], Or.inl hOb⟩
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact tsChk_pureF hgc hh hR hl h1 h2 y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact ⟨by rw [hxv]; exact lowW_pow (lt_two_pow_k hk (by omega)),
        by rw [h10]; exact lowW_pow (lt_two_pow_k hk (by omega))⟩
    · trivial
    · trivial
    · show (if (V.n 7).idx < (V.n 159).idx ∧ (V.n 158).idx < (V.n 159).idx then True else σ (.n 158) ≠ 0)
      split
      · trivial
      · next hc => exact absurd (by decide) hc
  · intro rd _ _ ho y hy
    rcases List.mem_append.mp hy with hy | hy
    · simp only [tsChk, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · show LoadHolds rd (σ (.n 56)) 1 (σ (.n 157))
      rw [p56, h13]; exact hrd rd ho 1 hoff
    · trivial
    · trivial

end

theorem tsNames_getElem! : ∀ h < 25, Link.tsNames[h]! = Link.tsNames.getD h "" := by decide +kernel

theorem tsNames_length : Link.tsNames.length = 25 := rfl

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {σ0 : Val} {w : ℕ → E}
  {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **A `table_size` dispatch window's hypotheses**: the height `g^h` selects `table_size__L{h}`, on the
row count `R ≤ 2^h` and the bits' buffer at `c` (its `h + 1` cells `verify_sub`'s own, the memory holding
the bits), returning `g^R`, `lead`, `rest`; the rest from its end. -/
theorem ts_disp {x av pv r h Rt c : ℕ} {ws : List W0} {st : St} {K : St → Prop} (hh : h ≤ 24) (hR : Rt ≤ 2 ^ h)
    (hx : σ0 (.n x) = gen ^ h) (hav : σ0 (.n av) = eOfNat Rt) (hpv : σ0 (.n pv) = ptrAt c)
    (hr0 : σ0 (.n r) = gen ^ Rt) (hr1 : σ0 (.n (r + 1)) = tsLeadW Rt h) (hr2 : σ0 (.n (r + 2)) = tsRestW Rt h)
    (hOwn : ∀ j < h + 1, Own (c + j)) (hpre : ∀ rd, st.O rd → ReadsAt rd (ptrAt c) (tsBitsW Rt h))
    (hrest : WinsHyp fs al cert k σ0 w Own R Pre ws
      ⟨st.a, leafEnd fs al (Link.tsNames.getD h "") st.kc, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
        st.Qs ++ [PostQuiet]⟩ K) :
    WinsHyp fs al cert k σ0 w Own R Pre
      (.call (.dispatch (.n x) Link.tsNames [.n av, .n pv] [.n r, .n (r + 1), .n (r + 2)]) :: ws) st K := by
  have c := table_size_leafA fs al cert k hh hR (bits := ptrAt c) (R := fun i => (R i ∨ Own i) ∨ st.D i)
    (fun off hoff => ⟨c + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hOwn off hoff))⟩)
  rw [← hav, ← hpv, ← hr0, ← hr1, ← hr2] at c
  refine winsHyp_call_leaf (g := Link.tsNames.getD h "")
    ⟨h, by rw [tsNames_length]; omega, by rw [hx, Value.gen_pow_eq_ofK], tsNames_getElem! h (by omega)⟩
    c (fun _ hi => hi) (fun rd hp => ?_) hrest
  rw [hpv]; exact hpre rd hp.2

end

/-! ## `wA`'s windows `7 ..< 18`, and the least-height arm -/

/-- Table `t`'s dispatch. -/
def tsDisp (x av pv r : ℕ) : Stmt := .dispatch (.n x) Link.tsNames [.n av, .n pv] [.n r, .n (r + 1), .n (r + 2)]

set_option maxRecDepth 100000 in
theorem vsA_tables_eq :
    (vsA.drop 109).take 1 = [tsDisp 115 144 7 145] ∧ (vsA.drop 110).take 11 = tsRun0.map Stmt.atom ∧
    (vsA.drop 121).take 1 = [tsDisp 116 157 159 160] ∧
    (vsA.drop 122).take 12 = (tsRun 160 117 145 159 2).map Stmt.atom ∧
    (vsA.drop 134).take 1 = [tsDisp 117 173 175 176] ∧
    (vsA.drop 135).take 12 = (tsRun 176 118 168 175 3).map Stmt.atom ∧
    (vsA.drop 147).take 1 = [tsDisp 118 189 191 192] ∧
    (vsA.drop 148).take 12 = (tsRun 192 119 184 191 4).map Stmt.atom ∧
    (vsA.drop 160).take 1 = [tsDisp 119 205 207 208] ∧
    (vsA.drop 161).take 12 = (tsRun 208 120 200 207 5).map Stmt.atom ∧
    (vsA.drop 173).take 1 = [tsDisp 120 221 223 224] := by
  refine ⟨stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_,
    stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_, stmtsEqb_sound ?_,
    stmtsEqb_sound ?_⟩ <;> decide +kernel

/-- `wA`'s windows `7 ..< 18`. -/
theorem vsA_w7_17 : [vsA_w7, vsA_w8, vsA_w9, vsA_w10, vsA_w11, vsA_w12, vsA_w13, vsA_w14, vsA_w15, vsA_w16,
    vsA_w17] = [.call (tsDisp 115 144 7 145), .run tsRun0, .call (tsDisp 116 157 159 160),
      .run (tsRun 160 117 145 159 2), .call (tsDisp 117 173 175 176), .run (tsRun 176 118 168 175 3),
      .call (tsDisp 118 189 191 192), .run (tsRun 192 119 184 191 4), .call (tsDisp 119 205 207 208),
      .run (tsRun 208 120 200 207 5), .call (tsDisp 120 221 223 224)] := by
  obtain ⟨e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17⟩ := vsA_tables_eq
  rw [vsA_w7, vsA_w8, vsA_w9, vsA_w10, vsA_w11, vsA_w12, vsA_w13, vsA_w14, vsA_w15, vsA_w16, vsA_w17,
    headD_of_take_one e7, headD_of_take_one e9, headD_of_take_one e11, headD_of_take_one e13,
    headD_of_take_one e15, headD_of_take_one e17, e8, e10, e12, e14, e16, atomsOf_map, atomsOf_map,
    atomsOf_map, atomsOf_map, atomsOf_map]

/-- The least-height arm is table `5`'s checks. -/
theorem vsI1n_atoms : atomsOf vsI1n = tsChk 224 235 := by decide +kernel

/-- **A run of `vsA`'s atoms satisfies its equations** as the checker reads them (`fixA`). -/
theorem vsA_run_goodF {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {i n : ℕ}
    {as : List Atom} (h : (vsA.drop i).take n = as.map Stmt.atom) :
    ∀ a ∈ as, Good rd0 (storesOf 6 vsAf) w (vsVal rd0 w args) (fixA a) := by
  intro a ha'
  have hm : Stmt.atom a ∈ vsA :=
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [h]; exact List.mem_map_of_mem ha'))
  exact vsVal_goodA (rd := rd0) (w := w) ha (fixS (.atom a)) (List.mem_map_of_mem hm)

/-- **A dispatch of `vsA` returns the oracle's words.** -/
theorem vsVal_disp_ret {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {i : ℕ}
    {x : V} {gs : List String} {as rs : List V} (h : (vsA.drop i).take 1 = [.dispatch x gs as rs]) :
    ∀ v ∈ rs, vsVal rd0 w args v = w v.idx := by
  have hm : Stmt.dispatch x gs as rs ∈ vsA :=
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [h]; exact List.mem_singleton_self _))
  exact vsVal_goodA (rd := rd0) (w := w) ha (fixS (.dispatch x gs as rs)) (List.mem_map_of_mem hm)

set_option maxRecDepth 100000 in
/-- The row counts' loads are no stores. -/
theorem vsA_rows_fresh : (([157, 173, 189, 205, 221].zip [1, 2, 3, 4, 5]).all fun q =>
    !(storesOf 6 vsAf).contains (.load (.n q.1) (.n 56) q.2)) = true := by decide +kernel

end
end LeanVM.Guest.B1.VsC
