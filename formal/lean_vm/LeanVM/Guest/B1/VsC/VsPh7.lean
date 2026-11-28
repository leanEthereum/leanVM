/-
  LeanVM.Guest.B1.VsC.VsPh7

  `wC`'s windows `9 ..< 13`: the eq tensor of the packed point, `state_ends`, the rounds' claim, `link_rounds`.
-/

module

public import LeanVM.Guest.B1.VsC.VsRunData
public import LeanVM.Guest.B1.VsC.EqTreeC

/-!
# `wC`'s windows `9 ..< 13`

`vsC_w9` (statements `575 ..< 672`): seven fresh loads of `.n 10`'s words, the link's pointer `.n 694 = ptrAt (b10 + 89 + n)`
(`pkC = g^88`), the eq tensor of the packed point (`.n 10`'s words `50 ..< 54`) into `.n 11` (`eqtreeAt`, its stores by
`eqtreeAt_complete` on the evaluation memory), `.n 751 = g^(w - 19)`; its `RunHyp` by `runHyp_bufs`. `vsC_w10`
(statement `672`): `state_ends__L{w}`, a leaf. `vsC_w11` (statements `673 ..< 686`): the rounds' claim `lrClaim`.
`vsC_w12` (statement `686`): `link_rounds__L1_L0`, at a given end. `vsPh7_wins` from numeric hypotheses.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

theorem pkC_eq : pkC = gen ^ 88 := by
  show word 452984832 0 = gen ^ 88
  rw [show (88 : ℕ) = 32 + 32 + 24 from rfl, pow_add, pow_add, ← wordG (j := 32) (by norm_num),
    ← wordG (j := 24) (by norm_num), show word (2 ^ 32) 0 = ofK (K.ofBits (2 ^ 32)) from word_eOfNat _,
    show word (2 ^ 24) 0 = ofK (K.ofBits (2 ^ 24)) from word_eOfNat _,
    show word 452984832 0 = ofK (K.ofBits 452984832) from word_eOfNat _, ← ofK_mul, ← ofK_mul,
    show K.ofBits (2 ^ 32) * K.ofBits (2 ^ 32) * K.ofBits (2 ^ 24) = K.ofBits 452984832 by decide +kernel]

/-- Statements `575 ..< 586`. -/
def vsC9a : List Atom :=
  [.load (.n 685) (.n 10) 6, .load (.n 686) (.n 10) 7, .load (.n 687) (.n 10) 8, .load (.n 688) (.n 10) 9,
    .load (.n 689) (.n 10) 10, .load (.n 690) (.n 10) 54, .load (.n 691) (.n 10) 55, .const (.n 692) (word 452984832 0),
    .mul (.n 693) (.n 679) (.n 692), .mul (.n 694) (.n 693) (.n 408), .mul (.n 695) (.n 694) (.n 409)]

/-- Statements `586 ..< 670`: the eq tensor of the packed point into `.n 11`. -/
abbrev vsEq9 : List Stmt := eqtreeAt (.n 10) (.n 11) 50 0 696 4

/-- Statements `670 ..< 672`. -/
def vsC9b : List Atom := [.const (.n 750) (word 10248187242686185485 0), .mul (.n 751) (.n 409) (.n 750)]

/-- Statement `672`: `state_ends__L{w}`. -/
def vsC10s : Stmt := .dispatch (.n 751) seNames [.n 694, .n 8] [.n 752, .n 753]

/-- Statements `673 ..< 686`: the rounds' claim. -/
def vsC11 : List Atom :=
  [.const (.n 754) (word 1 0), .add (.n 755) (.n 754) (.n 685), .add (.n 756) (.n 755) (.n 686),
    .mul (.n 757) (.n 752) (.n 756), .const (.n 758) (word 1 0), .const (.n 759) (word 12261764870545049476 0),
    .mul (.n 760) (.n 685) (.n 759), .add (.n 761) (.n 758) (.n 760), .add (.n 762) (.n 761) (.n 686),
    .mul (.n 763) (.n 753) (.n 762), .add (.n 764) (.n 757) (.n 763), .const (.n 765) (word 365917469723852800 0),
    .mul (.n 766) (.n 4) (.n 765)]

/-- Statement `686`: `link_rounds__L1_L0`. -/
def vsC12s : Stmt :=
  .call "link_rounds__L1_L0" [.n 680, .n 681, .n 682, .n 683, .n 684, .n 580, .n 764, .n 12, .n 409, .n 766]
    [.n 767, .n 768, .n 769, .n 770, .n 771, .n 772, .n 773]

/-- The rounds' claim from `state_ends`' two products and the packed opening's words `6`, `7`. -/
def lrClaim (a b x6 x7 : E) : E :=
  a * (word 1 0 + x6 + x7) + b * (word 1 0 + x6 * word 12261764870545049476 0 + x7)

set_option maxRecDepth 200000 in
theorem vsC9_eq : (vsC.drop 147).take 97 = vsC9a.map Stmt.atom ++ vsEq9 ++ vsC9b.map Stmt.atom :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC10_eq : (vsC.drop 244).take 1 = [vsC10s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC11_eq : (vsC.drop 245).take 13 = vsC11.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC12_eq : (vsC.drop 258).take 1 = [vsC12s] := stmtsEqb_sound (by decide +kernel)

theorem as9_eq : atomsOf ((vsC.drop 147).take 97) = vsC9a ++ atomsOf vsEq9 ++ vsC9b := by
  rw [vsC9_eq, atomsOf_append', atomsOf_append', atomsOf_map, atomsOf_map]

theorem vsC_w10_eq : vsC_w10 = .call vsC10s := by rw [vsC_w10, headD_of_take_one vsC10_eq]

theorem vsC_w11_eq : vsC_w11 = .run vsC11 := by rw [vsC_w11, vsC11_eq, atomsOf_map]

theorem vsC_w12_eq : vsC_w12 = .call vsC12s := by rw [vsC_w12, headD_of_take_one vsC12_eq]

set_option maxRecDepth 200000 in
/-- The eq tensor's stores are the run's, its other atoms ask nothing, its reads are no stores. -/
theorem vsEq9_shape : stC9.all (fun a => (atomsOf vsEq9).contains a) = true ∧
    (atomsOf vsEq9).all (fun a => !pureAsks a && noFTB a) = true ∧
    (eqReadsAt (.n 10) (.n 11) 50 0 696 4).all (fun a => !vsSL.contains a) = true := by decide +kernel

set_option maxRecDepth 200000 in
/-- The two loads the claim reads are fresh. -/
theorem vsC9_fresh : vsSL.contains (.load (.n 685) (.n 10) 6) = false ∧
    vsSL.contains (.load (.n 686) (.n 10) 7) = false := by decide +kernel

theorem seNames_getElem! : ∀ j < 6, seNames[j]! = seNames.getD j "" := by decide +kernel

theorem seNames_length : seNames.length = 6 := rfl

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- **A window's atoms satisfy their equations**, the stores `vsSL`. -/
theorem vsC_atoms_good (ha : args.length = 6) (i n : ℕ) :
    ∀ x ∈ atomsOf ((vsC.drop i).take n), Good rd0 vsSL w (vsVal rd0 w args) x := fun x hx => by
  have := vsVal_goodC (rd := rd0) (w := w) ha (.atom x)
    (List.mem_of_mem_drop (List.mem_of_mem_take (mem_of_mem_atomsOf hx)))
  rw [vsSL_eq] at this
  exact this

end

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `9 ..< 13`' hypotheses**: the opening's buffer `.n 10` at `b10` (its words `xs10`, at least `56`,
on the evaluation memory and on every memory with `Pre` and the words held, own; word `50 + t` the packed point's
coordinate `rs[t]`, words `6`, `7` the claim's `x6`, `x7`), the eq buffer `.n 11` at `b11` (its words `xs11`, the
point's eq tensor level by level, own), `.n 408 = g^n`, `.n 409 = g^w`; `state_ends`' arrays (`wd` words at
`b10 + 89 + n`, and at `.n 8`'s `b8`; own), its preconditions and returns; `link_rounds__L1_L0`'s `CallAtA` on its
arguments' values at a given end `ec`, its returns the oracle's; `K` at `ec`. -/
theorem vsPh7_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    {b8 b10 b11 b12 qt n wd : ℕ} {xs10 xs11 rs zs cs : List E} {x6 x7 : E}
    (hw19 : 19 ≤ wd) (hw24 : wd ≤ 24)
    (h10 : vsVal rd0 w args (.n 10) = ptrAt b10) (hl10 : 56 ≤ xs10.length) (r10 : ReadsAt rd0 (ptrAt b10) xs10)
    (hO10 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b10) xs10) (hOwn10 : ∀ j < 56, Own (b10 + j))
    (hrs : rs.length = 4) (hrs10 : ∀ t < 4, xs10[50 + t]? = some (rs.getD t 0))
    (hx6 : xs10[6]? = some x6) (hx7 : xs10[7]? = some x7)
    (h11 : vsVal rd0 w args (.n 11) = ptrAt b11) (hl11 : 30 ≤ xs11.length) (r11 : ReadsAt rd0 (ptrAt b11) xs11)
    (hO11 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b11) xs11) (hOwn11 : ∀ j < 30, Own (b11 + j))
    (hlev : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t, xs11[2 ^ t - 2 + i]? = some ((eqKernel (rs.take t)).getD i 0))
    (h408 : vsVal rd0 w args (.n 408) = gen ^ n) (h409 : vsVal rd0 w args (.n 409) = gen ^ wd)
    (h8 : vsVal rd0 w args (.n 8) = ptrAt b8) (hz : zs.length = wd) (hcs : cs.length = wd)
    (hOz : ∀ j < wd, Own (b10 + 89 + n + j)) (hO8 : ∀ j < wd, Own (b8 + j))
    (hPse : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (b10 + 89 + n)) zs ∧ ReadsAt rd (ptrAt b8) cs)
    (hse : w 752 = prodE (zs.map (1 + ·)) ∧ w 753 = endsProd cs zs)
    (h12 : vsVal rd0 w args (.n 12) = ptrAt b12) (h4 : vsVal rd0 w args (.n 4) = ptrAt qt)
    {Rc Dc : ℕ → Prop} {Oc Pc : Reader → Prop} {Qc : Reader → Tree → Prop} {Bc ec : ℕ}
    (hc : CallAtA fs al cert k "link_rounds__L1_L0"
      [w 680, w 681, w 682, w 683, w 684, w 580, lrClaim (w 752) (w 753) x6 x7, ptrAt b12, gen ^ wd,
        ptrAt qt * word 365917469723852800 0]
      [w 767, w 768, w 769, w 770, w 771, w 772, w 773] Rc Dc Oc Pc Qc Bc
      (allocBase (al "link_rounds__L1_L0") (leafEnd fs al (seNames.getD (wd - 19) "") st.kc))
      (allocBase (al "link_rounds__L1_L0") (leafEnd fs al (seNames.getD (wd - 19) "") st.kc) + Bc) ec)
    (hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) (hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd)
    (hK : K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [PostQuiet, Qc]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w9, vsC_w10, vsC_w11, vsC_w12] st K := by
  rw [vsC_w9, vsC_w10_eq, vsC_w11_eq, vsC_w12_eq, WinsHyp]
  set σ := vsVal rd0 w args with hσ
  have hg9 : ∀ x ∈ atomsOf ((vsC.drop 147).take 97), Good rd0 vsSL w σ x := vsC_atoms_good ha 147 97
  have m9a : ∀ x ∈ vsC9a, x ∈ atomsOf ((vsC.drop 147).take 97) := fun x h => by
    rw [as9_eq]; exact List.mem_append_left _ (List.mem_append_left _ h)
  have m9e : ∀ x ∈ atomsOf vsEq9, x ∈ atomsOf ((vsC.drop 147).take 97) := fun x h => by
    rw [as9_eq]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have m9b : ∀ x ∈ vsC9b, x ∈ atomsOf ((vsC.drop 147).take 97) := fun x h => by
    rw [as9_eq]; exact List.mem_append_right _ h
  -- the buffers
  let bs : ℕ → ℕ := fun v => [b10, b11].getD (v - 10) 0
  let xs : ℕ → List E := fun v => [xs10, xs11].getD (v - 10) []
  have hp : ∀ q ∈ spC9, σ (.n q.1) = ptrAt (bs q.1) := fun q hq => by
    simp only [spC9, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [h10, h11]
  have hn : ∀ q ∈ spC9, q.2 ≤ (xs q.1).length := fun q hq => by
    simp only [spC9, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [hl10, hl11]
  have h0 : ∀ q ∈ spC9, ReadsAt rd0 (ptrAt (bs q.1)) (xs q.1) := fun q hq => by
    simp only [spC9, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [r10, r11]
  have e1 : ∀ x ∈ stC9, x ∈ atomsOf vsEq9 := fun x hx => by
    simpa using List.all_eq_true.mp vsEq9_shape.1 x hx
  have e2 : ∀ x ∈ atomsOf vsEq9, pureAsks x = false ∧ noFTB x = true := fun x hx => by
    simpa using List.all_eq_true.mp vsEq9_shape.2.1 x hx
  -- the eq tensor on the evaluation memory
  have eqH : ∀ a, Stmt.atom a ∈ vsEq9 → a.Holds rd0 σ := by
    refine eqtreeAt_complete (by norm_num) (S := vsSL) (fun a h => storesOf_isLoad (by rw [vsSL_eq]; exact h))
      (fun a h hS => absurd (List.all_eq_true.mp vsEq9_shape.2.2 a h) (by simpa using hS))
      (fun a h hS => holds_bufs vsC_w9_bufs hg9 bs xs hp hn h0 (m9e a (mem_atomsOf' h)) hS
        (e2 a (mem_atomsOf' h)).1 (e2 a (mem_atomsOf' h)).2)
      hrs (fun t ht => ?_) (fun t h1 h2 i hi => ?_)
    · rw [h10]; exact loadHolds_of_get? r10 (hrs10 t ht)
    · rw [h11, Nat.zero_add]; exact loadHolds_of_get? r11 (hlev t h1 h2 i hi)
  have hst : ∀ x ∈ stC9, MemF rd0 σ x := fun x hx => by
    have := eqH x (mem_of_mem_atomsOf (e1 x hx))
    cases x with
    | load d p off => exact this
    | _ => trivial
  refine ⟨runHyp_bufs vsC_w9_bufs hg9 bs xs hp hn h0 (fun q hq j hj => ?_) (fun rd hpr ho q hq => ?_) hst
    (fun x hx => by rw [vsC_w9_pure] at hx; simp [pureC9] at hx), ?_⟩
  · simp only [spC9, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [Or.inl (hOwn10 j hj), Or.inl (hOwn11 j hj)]
  · simp only [spC9, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [hO10 rd hpr ho, hO11 rd hpr ho]
  rw [(noAlloc_fields (σ := σ) (as := atomsOf ((vsC.drop 147).take 97))
    (List.all_eq_true.mpr fun x hm => by
      have := List.all_eq_true.mp vsC_w9_bufs x hm
      simp only [Bool.and_eq_true] at this
      exact this.1.1.2)).2, List.sum_nil, Nat.add_zero]
  -- the values the later windows read
  have hgC := vsVal_goodC (rd := rd0) (w := w) ha
  have m7 : ∀ a ∈ vsC7q, Stmt.atom a ∈ vsC := fun a h =>
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [vsC7_eq]; exact List.mem_append_right _ (List.mem_map_of_mem h)))
  have hg7 : ∀ a ∈ vsC7q, Good rd0 (storesOf 482 vsC) w σ a := fun a h => hgC (.atom a) (m7 a h)
  have e679 : σ (.n 679) = ptrAt (b10 + 1) := by
    rw [good_mulF (hg7 (.mul (.n 679) (.n 10) (.n 678)) (by simp [vsC7q])) (by omega) (by omega), h10,
      show σ (.n 678) = word 2 0 from hg7 (.const (.n 678) (word 2 0)) (by simp [vsC7q]),
      show word 2 0 = gen ^ 1 from wordG (j := 1) (by norm_num), ptrAt_add]
  have cs9 : ∀ (d : ℕ) (e : E), Atom.const (.n d) e ∈ vsC9a → σ (.n d) = e := fun d e h => hg9 _ (m9a _ h)
  have mf9 : ∀ d x y, Atom.mul (.n d) (.n x) (.n y) ∈ vsC9a → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y h hx hy => good_mulF (hg9 _ (m9a _ h)) hx hy
  have e694 : σ (.n 694) = ptrAt (b10 + 89 + n) := by
    rw [show b10 + 89 + n = b10 + 1 + 88 + n by omega, mf9 694 693 408 (by simp [vsC9a]) (by omega) (by omega), mf9 693 679 692 (by simp [vsC9a]) (by omega) (by omega),
      e679, cs9 692 (word 452984832 0) (by simp [vsC9a]), show word 452984832 0 = gen ^ 88 from pkC_eq, h408, ptrAt_add, ptrAt_add]
  have e751 : σ (.n 751) = gen ^ (wd - 19) := by
    rw [good_mulF (hg9 _ (m9b (.mul (.n 751) (.n 409) (.n 750)) (by simp [vsC9b]))) (by omega) (by omega), h409,
      show σ (.n 750) = word 10248187242686185485 0 from hg9 _ (m9b (.const (.n 750) _) (by simp [vsC9b])),
      VerifySub.pow_mul_winv19 hw19]
  have fr := vsC9_fresh
  have e685 : σ (.n 685) = x6 :=
    good_load_get? (by intro h; rw [List.contains_iff_mem.mpr h] at fr; exact absurd fr.1 (by decide))
      (hg9 _ (m9a _ (by simp [vsC9a]))) h10 r10 hx6
  have e686 : σ (.n 686) = x7 :=
    good_load_get? (by intro h; rw [List.contains_iff_mem.mpr h] at fr; exact absurd fr.2 (by decide))
      (hg9 _ (m9a _ (by simp [vsC9a]))) h10 r10 hx7
  -- `state_ends`
  have r10s : ∀ v ∈ [V.n 752, .n 753], σ v = w v.idx := vsVal_retC (rd0 := rd0) (w := w) ha vsC10_eq
  have hargs10 : (argsOf vsC10s).map σ = [ptrAt (b10 + 89 + n), ptrAt b8] := by
    show [σ (.n 694), σ (.n 8)] = _
    rw [e694, h8]
  have hrets10 : (retsOf vsC10s).map σ = [prodE (zs.map (1 + ·)), endsProd cs zs] := by
    show [σ (.n 752), σ (.n 753)] = _
    rw [r10s (.n 752) (by simp), r10s (.n 753) (by simp), hse.1, hse.2]
  have L10 := state_ends_leafA fs al cert k hw19 hw24 (ptrAt (b10 + 89 + n)) (ptrAt b8) zs cs hz hcs
    (R := fun i => (R i ∨ Own i) ∨ st.D i)
    (fun off hoff => ⟨b10 + 89 + n + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hOz off hoff))⟩)
    (fun off hoff => ⟨b8 + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hO8 off hoff))⟩)
  rw [← hargs10, ← hrets10] at L10
  refine winsHyp_call_leaf (g := seNames.getD (wd - 19) "")
    ⟨wd - 19, by rw [seNames_length]; omega, by rw [e751, Value.gen_pow_eq_ofK],
      seNames_getElem! _ (by omega)⟩ L10 (fun _ h => h) (fun rd hp => hPse rd hp) ?_
  -- the rounds' claim
  have hg11 : ∀ a ∈ vsC11, Good rd0 (storesOf 482 vsC) w σ a := vsC_run_good (rd0 := rd0) (w := w) ha vsC11_eq
  have cs11 : ∀ (d : ℕ) (e : E), Atom.const (.n d) e ∈ vsC11 → σ (.n d) = e := fun d e h => hg11 _ h
  have ad11 : ∀ d x y, Atom.add (.n d) (.n x) (.n y) ∈ vsC11 → σ (.n d) = σ (.n x) + σ (.n y) :=
    fun d x y h => hg11 _ h
  have mf11 : ∀ d x y, Atom.mul (.n d) (.n x) (.n y) ∈ vsC11 → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y h hx hy => good_mulF (hg11 _ h) hx hy
  rw [WinsHyp]
  refine ⟨RunHyp.of_asks rfl (fun A hA => by simp [loadAddrs, vsC11, Ev.loadAddr?] at hA)
    (fun A hA => by rw [show heapHintAddrs σ (vsC11.map Ev.atom) = [] from rfl] at hA; simp at hA)
    (fun x hx => by rw [show vsC11.filter pureAsks = [] by decide +kernel] at hx; simp at hx)
    (fun rd _ _ _ x hx => by rw [show vsC11.filter memAsks = [] by decide +kernel] at hx; simp at hx), ?_⟩
  rw [show allocs σ (vsC11.map Ev.atom) = [] from rfl, List.sum_nil, Nat.add_zero]
  have e764 : σ (.n 764) = lrClaim (w 752) (w 753) x6 x7 := by
    rw [lrClaim, ad11 764 757 763 (by simp [vsC11]), mf11 757 752 756 (by simp [vsC11]) (by omega) (by omega),
      mf11 763 753 762 (by simp [vsC11]) (by omega) (by omega), ad11 756 755 686 (by simp [vsC11]),
      ad11 755 754 685 (by simp [vsC11]), ad11 762 761 686 (by simp [vsC11]), ad11 761 758 760 (by simp [vsC11]),
      mf11 760 685 759 (by simp [vsC11]) (by omega) (by omega), cs11 754 (word 1 0) (by simp [vsC11]),
      cs11 758 (word 1 0) (by simp [vsC11]), cs11 759 (word 12261764870545049476 0) (by simp [vsC11]), e685, e686, r10s (.n 752) (by simp),
      r10s (.n 753) (by simp)]
  have e766 : σ (.n 766) = ptrAt qt * word 365917469723852800 0 := by
    rw [mf11 766 4 765 (by simp [vsC11]) (by omega) (by omega), h4, cs11 765 (word 365917469723852800 0) (by simp [vsC11])]
  -- `link_rounds__L1_L0`
  have r12 : ∀ v ∈ [V.n 767, .n 768, .n 769, .n 770, .n 771, .n 772, .n 773], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC12_eq
  have r8 : ∀ v ∈ [V.n 680, .n 681, .n 682, .n 683, .n 684], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC8_eq
  have e580 : σ (.n 580) = w 580 := vsVal_retC (rd0 := rd0) (w := w) ha vsC6_eq (.n 580) (by simp)
  have hargs12 : (argsOf vsC12s).map σ = [w 680, w 681, w 682, w 683, w 684, w 580, lrClaim (w 752) (w 753) x6 x7,
      ptrAt b12, gen ^ wd, ptrAt qt * word 365917469723852800 0] := by
    show [σ (.n 680), σ (.n 681), σ (.n 682), σ (.n 683), σ (.n 684), σ (.n 580), σ (.n 764), σ (.n 12), σ (.n 409),
      σ (.n 766)] = _
    rw [r8 (.n 680) (by simp), r8 (.n 681) (by simp), r8 (.n 682) (by simp), r8 (.n 683) (by simp),
      r8 (.n 684) (by simp), e580, e764, h12, h409, e766]
  have hrets12 : (retsOf vsC12s).map σ = [w 767, w 768, w 769, w 770, w 771, w 772, w 773] := by
    show [σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771), σ (.n 772), σ (.n 773)] = _
    rw [r12 (.n 767) (by simp), r12 (.n 768) (by simp), r12 (.n 769) (by simp), r12 (.n 770) (by simp),
      r12 (.n 771) (by simp), r12 (.n 772) (by simp), r12 (.n 773) (by simp)]
  rw [← hargs12, ← hrets12] at hc
  refine winsHyp_call_at (g := "link_rounds__L1_L0") rfl hc (fun i hi => (hRc i hi).imp_right Or.inl)
    (fun rd hp => hPc rd ⟨hp.1, hp.2.1⟩) ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => by simp) (fun i => by simp) (by simp)

end

end
end LeanVM.Guest.B1.VsC
