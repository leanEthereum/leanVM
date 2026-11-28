/-
  LeanVM.Guest.B1.VsC.VsPh12

  `wC`'s windows `22 ..< 32`: the five other tables' points, `table_point__L{h}`.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh11

/-!
# `wC`'s windows `22 ..< 32`

Five times a run and a leaf: the run (`vsC_w22`, `w24`, `w26`, `w28`, `w30`) reads `.n 18`'s word at the previous
table's height (`.n 18·g^h`), and `.n 1076`, `.n 11`, `.n 10`, `.n 17` (no store, no asking atom), and ends with the
next table's arguments: `.n 10`'s word `t`, `.n 679·g^88 = ptrAt (b10 + 89)`, `.n 15`, the table's bits pointer
`·g^26`; the leaf (`w23`, …, `w31`) is `table_point__L{h}`. `BufAt` bundles a buffer's facts, `tp_step` is one table,
`vsPh12_wins` the five.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **A buffer** `.n v` at `b`: its words `xs` (at least `n`) held on the evaluation memory and on every memory with
`Pre` and `O`, its first `n` cells in `C`. -/
structure BufAt (rd0 : Reader) (σ : Val) (Pre O : Reader → Prop) (C : ℕ → Prop) (v b n : ℕ) (xs : List E) : Prop where
  ptr : σ (.n v) = ptrAt b
  len : n ≤ xs.length
  r0 : ReadsAt rd0 (ptrAt b) xs
  rO : ∀ rd, Pre rd → O rd → ReadsAt rd (ptrAt b) xs
  cell : ∀ j < n, C (b + j)

section
variable {rd0 : Reader} {σ : Val} {Pre O : Reader → Prop} {C : ℕ → Prop} {v b n : ℕ} {xs : List E}

theorem BufAt.le (h : BufAt rd0 σ Pre O C v b n xs) {m : ℕ} (hm : m ≤ n) : BufAt rd0 σ Pre O C v b m xs :=
  ⟨h.ptr, le_trans hm h.len, h.r0, h.rO, fun j hj => h.cell j (by omega)⟩

/-- The buffer from its word `m` on, through another pointer. -/
theorem BufAt.drop (h : BufAt rd0 σ Pre O C v b n xs) {u m : ℕ} (hu : σ (.n u) = ptrAt (b + m)) (hm : m + 1 ≤ n) :
    BufAt rd0 σ Pre O C u (b + m) 1 (xs.drop m) :=
  ⟨hu, by rw [List.length_drop]; have := h.len; omega, readsAt_drop h.r0, fun rd hp ho => readsAt_drop (h.rO rd hp ho),
    fun j hj => by rw [Nat.add_assoc]; exact h.cell _ (by omega)⟩

theorem BufAt.getD (h : BufAt rd0 σ Pre O C v b n xs) {t : ℕ} (ht : t < n) : xs[t]? = some (xs.getD t 0) := by
  have : t < xs.length := lt_of_lt_of_le ht h.len
  rw [List.getElem?_eq_getElem this, List.getD_eq_getElem _ _ this]

end

theorem cl_swap {Own R D : ℕ → Prop} {i : ℕ} (h : Own i ∨ R i ∨ D i) : (R i ∨ Own i) ∨ D i := by
  rcases h with h | h | h
  exacts [Or.inl (Or.inr h), Or.inl (Or.inl h), Or.inr h]

/-- `table_point__L{h}` on the table whose `.n 10` word is `d`'s, its pointers `d + 2`, `d + 4`, returns `d + 5 …`. -/
def tpS (sel d : ℕ) : Stmt :=
  .dispatch (.n (sel + 1)) tpNames [.n d, .n (d + 2), .n 15, .n (d + 4)] [.n (d + 5), .n (d + 6), .n (d + 7)]

/-- The atoms of a table's run `tp_step` reads values of. -/
def tpL (v0 sel t d bv : ℕ) : List Atom :=
  [.mul (.n v0) (.n 18) (.n sel), .load (.n d) (.n 10) t, .const (.n (d + 1)) (word 452984832 0),
    .mul (.n (d + 2)) (.n 679) (.n (d + 1)), .const (.n (d + 3)) (word 67108864 0),
    .mul (.n (d + 4)) (.n bv) (.n (d + 3))]

theorem word_2_26 : word 67108864 0 = gen ^ 26 := wordG (j := 26) (by norm_num)

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop} {sp : List (ℕ × ℕ)} {sts S as : List Atom}
  {σ0 : Val}

/-- **A run window read through known buffers**, each a `BufAt`. -/
theorem winsHyp_run_bufAt {ws : List W0} {st : St} {K : St → Prop} (hok : bufsOk sp sts S as = true)
    (hg : ∀ x ∈ as, Good rd0 S w σ0 x) (bs : ℕ → ℕ) (xs : ℕ → List E)
    (hb : ∀ q ∈ sp, BufAt rd0 σ0 Pre st.O (fun i => Own i ∨ R i ∨ st.D i) q.1 (bs q.1) q.2 (xs q.1))
    (hst : ∀ x ∈ sts, MemF rd0 σ0 x) (hpure : ∀ x ∈ as.filter pureAsks, PureF k σ0 x)
    (hrest : WinsHyp fs al cert k σ0 w Own R Pre ws st K) :
    WinsHyp fs al cert k σ0 w Own R Pre (.run as :: ws) st K :=
  winsHyp_run_bufs hok hg bs xs (fun q hq => (hb q hq).ptr) (fun q hq => (hb q hq).len) (fun q hq => (hb q hq).r0)
    (fun q hq => (hb q hq).cell) (fun rd hp ho q hq => (hb q hq).rO rd hp ho) hst hpure hrest

/-- **One table**: the run `(vsC.drop i).take n` (buffers `.n v0 = .n 18·g^hp`, `.n 1076`, `.n 11`, `.n 10`, `.n 17`,
no store, no asking atom), then `table_point__L{h}` (statement `j`) on `.n 10`'s word `t`, `ptrAt (b10 + 89)`,
`.n 15`, `.n bv·g^26`, its returns the oracle's; the rest past the leaf. -/
theorem tp_step (ha : args.length = 6) {i n j : ℕ} {ws : List W0} {st : St} {K : St → Prop}
    {v0 sel t d bv n1 n2 n3 n4 hp h b18 b1076 b11 b10 b17 b15 bb : ℕ}
    {xs18 xs1076 xs11 xs10 xs17 ts xs cs : List E} {top : E}
    (hok : bufsOk [(v0, 1), (1076, n1), (11, n2), (10, n3), (17, n4)] [] vsSL (atomsOf ((vsC.drop i).take n)) = true)
    (hpure : (atomsOf ((vsC.drop i).take n)).filter pureAsks = [])
    (hmem : (tpL v0 sel t d bv).all (fun a => (atomsOf ((vsC.drop i).take n)).contains a) = true)
    (hθS : vsSL.contains (.load (.n d) (.n 10) t) = false)
    (hidx : 18 < v0 ∧ sel < v0 ∧ 679 < d + 2 ∧ bv < d + 4)
    (hv0 : v0 ≠ 1076 ∧ v0 ≠ 11 ∧ v0 ≠ 10 ∧ v0 ≠ 17)
    (hs : (vsC.drop j).take 1 = [tpS sel d])
    (B18 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 18 b18 25 xs18)
    (B1076 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 1076 b1076 n1 xs1076)
    (B11 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 11 b11 n2 xs11)
    (B10 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 10 b10 n3 xs10)
    (B17 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 17 b17 n4 xs17)
    (hsel : vsVal rd0 w args (.n sel) = gen ^ hp) (hhp : hp ≤ 24) (ht : t < n3)
    (hsel' : vsVal rd0 w args (.n (sel + 1)) = gen ^ h) (hh : h ≤ 24)
    (h15 : vsVal rd0 w args (.n 15) = ptrAt b15) (hbv : vsVal rd0 w args (.n bv) = ptrAt bb)
    (hts : ts.length = h) (hxs : xs.length = h) (hcs : cs.length = h)
    (hOt : ∀ j < h, Own (b10 + 89 + j) ∨ R (b10 + 89 + j) ∨ st.D (b10 + 89 + j))
    (hO15 : ∀ j < h, Own (b15 + j) ∨ R (b15 + j) ∨ st.D (b15 + j))
    (hOb : ∀ j < h + 1, Own (bb + 26 + j) ∨ R (bb + 26 + j) ∨ st.D (bb + 26 + j))
    (hPtp : ∀ rd, Pre rd ∧ st.O rd →
      ReadsAt rd (ptrAt (b10 + 89)) ts ∧ ReadsAt rd (ptrAt b15) xs ∧ ReadsAt rd (ptrAt (bb + 26)) (cs ++ [top]))
    (htp : w (d + 5) = xs10.getD t 0 * tpTotalG ts xs cs top h ∧ w (d + 6) = 1 + (1 + top) * tpPad cs xs ∧
      w (d + 7) = tpFullAt ts xs h)
    (hrest : WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre ws
      ⟨st.a, leafEnd fs al (tpNames.getD h "") st.kc, st.O, st.D, st.Qs ++ [PostQuiet]⟩ K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre
      (.run (atomsOf ((vsC.drop i).take n)) :: .call ((vsC.drop j).headD (.ret [])) :: ws) st K := by
  obtain ⟨i1, i2, i3, i4⟩ := hidx
  rw [headD_of_take_one hs]
  set σ := vsVal rd0 w args with hσ
  have hg : ∀ x ∈ atomsOf ((vsC.drop i).take n), Good rd0 vsSL w σ x := vsC_atoms_good ha i n
  have hm : ∀ a ∈ tpL v0 sel t d bv, a ∈ atomsOf ((vsC.drop i).take n) := fun a h => by
    simpa using List.all_eq_true.mp hmem a h
  have e0 : σ (.n v0) = ptrAt (b18 + hp) := by
    rw [good_mulF (hg _ (hm (.mul (.n v0) (.n 18) (.n sel)) (by simp [tpL]))) (by omega) (by omega), B18.ptr, hsel,
      ptrAt_add]
  let bs : ℕ → ℕ := fun v => if v = v0 then b18 + hp else if v = 1076 then b1076 else if v = 11 then b11 else
    if v = 10 then b10 else b17
  let xs' : ℕ → List E := fun v => if v = v0 then xs18.drop hp else if v = 1076 then xs1076 else if v = 11 then xs11
    else if v = 10 then xs10 else xs17
  have hsp : ∀ q ∈ [(v0, 1), (1076, n1), (11, n2), (10, n3), (17, n4)],
      q = (v0, 1) ∨ q = (1076, n1) ∨ q = (11, n2) ∨ q = (10, n3) ∨ q = (17, n4) := fun q hq => by simpa using hq
  refine winsHyp_run_bufAt hok hg bs xs' (fun q hq => ?_) (fun x hx => by simp at hx)
    (fun x hx => by rw [hpure] at hx; simp at hx) ?_
  · rcases hsp q hq with rfl | rfl | rfl | rfl | rfl
    · simp only [bs, xs', ↓reduceIte]; exact B18.drop e0 (by omega)
    · simp only [bs, xs', Ne.symm hv0.1, ↓reduceIte]; exact B1076
    · simp only [bs, xs', Ne.symm hv0.2.1, show (11 : ℕ) ≠ 1076 by decide, ↓reduceIte]
      exact B11
    · simp only [bs, xs', Ne.symm hv0.2.2.1, show (10 : ℕ) ≠ 1076 by decide, show (10 : ℕ) ≠ 11 by decide,
        ↓reduceIte]
      exact B10
    · simp only [bs, xs', Ne.symm hv0.2.2.2, show (17 : ℕ) ≠ 1076 by decide, show (17 : ℕ) ≠ 11 by decide,
        show (17 : ℕ) ≠ 10 by decide, ↓reduceIte]
      exact B17
  -- the table's arguments
  have fr : Atom.load (.n d) (.n 10) t ∉ vsSL := fun h' => by
    rw [List.contains_iff_mem.mpr h'] at hθS; exact absurd hθS (by decide)
  have eθ : σ (.n d) = xs10.getD t 0 :=
    good_load_get? fr (hg _ (hm _ (by simp [tpL]))) B10.ptr B10.r0 (B10.getD ht)
  have eτ : σ (.n (d + 2)) = ptrAt (b10 + 89) := by
    rw [show b10 + 89 = b10 + 1 + 88 by omega,
      good_mulF (hg _ (hm (.mul (.n (d + 2)) (.n 679) (.n (d + 1))) (by simp [tpL]))) (by omega) (by omega),
      show σ (.n 679) = ptrAt (b10 + 1) from vsVal_679 ha B10.ptr,
      show σ (.n (d + 1)) = word 452984832 0 from hg (.const (.n (d + 1)) (word 452984832 0)) (hm _ (by simp [tpL])),
      show word 452984832 0 = gen ^ 88 from pkC_eq, ptrAt_add]
  have eβ : σ (.n (d + 4)) = ptrAt (bb + 26) := by
    rw [good_mulF (hg _ (hm (.mul (.n (d + 4)) (.n bv) (.n (d + 3))) (by simp [tpL]))) (by omega) (by omega), hbv,
      show σ (.n (d + 3)) = word 67108864 0 from hg (.const (.n (d + 3)) (word 67108864 0)) (hm _ (by simp [tpL])),
      word_2_26, ptrAt_add]
  have r : ∀ v ∈ [V.n (d + 5), .n (d + 6), .n (d + 7)], σ v = w v.idx := vsVal_retC (rd0 := rd0) (w := w) ha hs
  have hargs : (argsOf (tpS sel d)).map σ = [xs10.getD t 0, ptrAt (b10 + 89), ptrAt b15, ptrAt (bb + 26)] := by
    show [σ (.n d), σ (.n (d + 2)), σ (.n 15), σ (.n (d + 4))] = _
    rw [eθ, eτ, h15, eβ]
  have hrets : (retsOf (tpS sel d)).map σ =
      [xs10.getD t 0 * tpTotalG ts xs cs top h, 1 + (1 + top) * tpPad cs xs, tpFullAt ts xs h] := by
    show [σ (.n (d + 5)), σ (.n (d + 6)), σ (.n (d + 7))] = _
    rw [r (.n (d + 5)) (by simp), r (.n (d + 6)) (by simp), r (.n (d + 7)) (by simp), htp.1, htp.2.1, htp.2.2]
  have L := table_point_leafA fs al cert k hh (xs10.getD t 0) (ptrAt (b10 + 89)) (ptrAt b15) (ptrAt (bb + 26)) top
    ts xs cs hts hxs hcs (R := fun i => (R i ∨ Own i) ∨ st.D i)
    (fun off hoff => ⟨b10 + 89 + off, by rw [ptrAt, B1.Main.addr_ofK], cl_swap (hOt off hoff)⟩)
    (fun off hoff => ⟨b15 + off, by rw [ptrAt, B1.Main.addr_ofK], cl_swap (hO15 off hoff)⟩)
    (fun off hoff => ⟨bb + 26 + off, by rw [ptrAt, B1.Main.addr_ofK], cl_swap (hOb off hoff)⟩)
  rw [← hrets, ← hargs] at L
  refine winsHyp_call_leaf (g := tpNames.getD h "")
    ⟨h, by rw [tpNames_length]; omega, by rw [hsel', Value.gen_pow_eq_ofK], tpNames_getElem! _ (by omega)⟩ L
    (fun _ h => h) (fun rd hp => hPtp rd hp) ?_
  exact st_congr (K := fun s => WinsHyp fs al cert k σ w Own R Pre ws s K) hrest rfl (fun rd => by simp)
    (fun i => by simp) rfl

end

/-- The tables' bits pointers' values, tables `1 ..< 6`. -/
def tpBv (t : ℕ) : ℕ := [7, 159, 175, 191, 207].getD (t - 1) 0

/-- The cursor past tables `1 ..= t`'s `table_point` leaves. -/
def tpKc (fs : String → ℕ) (al : String → Bool) (hg : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, kc => kc
  | t + 1, kc => leafEnd fs al (tpNames.getD (hg (t + 1)) "") (tpKc fs al hg t kc)

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

set_option maxRecDepth 200000 in
theorem vsC23_eq : (vsC.drop 989).take 1 = [tpS 115 1403] := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 200000 in
theorem vsC25_eq : (vsC.drop 1108).take 1 = [tpS 116 1524] := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 200000 in
theorem vsC27_eq : (vsC.drop 1189).take 1 = [tpS 117 1607] := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 200000 in
theorem vsC29_eq : (vsC.drop 1314).take 1 = [tpS 118 1734] := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 200000 in
theorem vsC31_eq : (vsC.drop 1458).take 1 = [tpS 119 1880] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC22_mem : (tpL 1299 115 1 1403 7).all (fun a => (atomsOf ((vsC.drop 880).take 109)).contains a) = true ∧
    vsSL.contains (.load (.n 1403) (.n 10) 1) = false := by decide +kernel
set_option maxRecDepth 200000 in
theorem vsC24_mem : (tpL 1411 116 2 1524 159).all (fun a => (atomsOf ((vsC.drop 990).take 118)).contains a) = true ∧
    vsSL.contains (.load (.n 1524) (.n 10) 2) = false := by decide +kernel
set_option maxRecDepth 200000 in
theorem vsC26_mem : (tpL 1532 117 3 1607 175).all (fun a => (atomsOf ((vsC.drop 1109).take 80)).contains a) = true ∧
    vsSL.contains (.load (.n 1607) (.n 10) 3) = false := by decide +kernel
set_option maxRecDepth 200000 in
theorem vsC28_mem : (tpL 1615 118 4 1734 191).all (fun a => (atomsOf ((vsC.drop 1190).take 124)).contains a) = true ∧
    vsSL.contains (.load (.n 1734) (.n 10) 4) = false := by decide +kernel
set_option maxRecDepth 200000 in
theorem vsC30_mem : (tpL 1742 119 5 1880 207).all (fun a => (atomsOf ((vsC.drop 1315).take 143)).contains a) = true ∧
    vsSL.contains (.load (.n 1880) (.n 10) 5) = false := by decide +kernel

/-- **`wC`'s windows `22 ..< 32`' hypotheses**: the buffers `.n 18` (`25` words), `.n 1076` (`80`), `.n 11` (`30`),
`.n 10` (`89`), `.n 17` (`95`) as `BufAt`s; the six tables' heights `.n (115 + t) = g^(hg t)`, `hg t ≤ 24`; for
tables `t = 1 … 5`: their bits pointers `.n (tpBv t) = ptrAt (bb t)`, `table_point`'s arrays (`hg t` words at
`b10 + 89`, at `.n 15`'s `b15`, `hg t + 1` at `bb t + 26`; in the region), its precondition and returns (at
`w (tpRet t)`, `tpRet t = d + 5` for the table's first value `d`); `K` past the five leaves. -/
theorem vsPh12_wins (ha : args.length = 6) {st : St} {K : St → Prop} {b18 b1076 b11 b10 b17 b15 : ℕ}
    {xs18 xs1076 xs11 xs10 xs17 : List E} {hg bb : ℕ → ℕ} {ts xs cs : ℕ → List E} {top : ℕ → E}
    (B18 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 18 b18 25 xs18)
    (B1076 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 1076 b1076 80 xs1076)
    (B11 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 11 b11 30 xs11)
    (B10 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 10 b10 89 xs10)
    (B17 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 17 b17 95 xs17)
    (hsel : ∀ t ≤ 5, vsVal rd0 w args (.n (115 + t)) = gen ^ hg t) (hh : ∀ t ≤ 5, hg t ≤ 24)
    (h15 : vsVal rd0 w args (.n 15) = ptrAt b15)
    (hbv : ∀ t, 1 ≤ t → t ≤ 5 → vsVal rd0 w args (.n (tpBv t)) = ptrAt (bb t))
    (hts : ∀ t, 1 ≤ t → t ≤ 5 → (ts t).length = hg t ∧ (xs t).length = hg t ∧ (cs t).length = hg t)
    (hOt : ∀ j < 24, Own (b10 + 89 + j) ∨ R (b10 + 89 + j) ∨ st.D (b10 + 89 + j))
    (hO15 : ∀ j < 24, Own (b15 + j) ∨ R (b15 + j) ∨ st.D (b15 + j))
    (hOb : ∀ t, 1 ≤ t → t ≤ 5 → ∀ j < hg t + 1, Own (bb t + 26 + j) ∨ R (bb t + 26 + j) ∨ st.D (bb t + 26 + j))
    (hPtp : ∀ t, 1 ≤ t → t ≤ 5 → ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (b10 + 89)) (ts t) ∧
      ReadsAt rd (ptrAt b15) (xs t) ∧ ReadsAt rd (ptrAt (bb t + 26)) (cs t ++ [top t]))
    (htp : ∀ t, 1 ≤ t → t ≤ 5 → ∀ d, d = [1403, 1524, 1607, 1734, 1880].getD (t - 1) 0 →
      w (d + 5) = xs10.getD t 0 * tpTotalG (ts t) (xs t) (cs t) (top t) (hg t) ∧
      w (d + 6) = 1 + (1 + top t) * tpPad (cs t) (xs t) ∧ w (d + 7) = tpFullAt (ts t) (xs t) (hg t))
    (hK : K ⟨st.a, tpKc fs al hg 5 st.kc, st.O, st.D, st.Qs ++ List.replicate 5 PostQuiet⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre
      [vsC_w22, vsC_w23, vsC_w24, vsC_w25, vsC_w26, vsC_w27, vsC_w28, vsC_w29, vsC_w30, vsC_w31] st K := by
  rw [vsC_w22, vsC_w23, vsC_w24, vsC_w25, vsC_w26, vsC_w27, vsC_w28, vsC_w29, vsC_w30, vsC_w31]
  have e1 := hts 1 le_rfl (by norm_num)
  have e2 := hts 2 (by norm_num) (by norm_num)
  have e3 := hts 3 (by norm_num) (by norm_num)
  have e4 := hts 4 (by norm_num) (by norm_num)
  have e5 := hts 5 (by norm_num) le_rfl
  refine tp_step ha vsC_w22_bufs vsC_w22_pure vsC22_mem.1 vsC22_mem.2 (by norm_num) (by decide) vsC23_eq B18
    (B1076.le (by norm_num)) (B11.le (by norm_num)) (B10.le (by norm_num)) (B17.le (by norm_num)) (hsel 0 (by norm_num))
    (hh 0 (by norm_num)) (by norm_num) (hsel 1 (by norm_num)) (hh 1 (by norm_num)) h15 (hbv 1 le_rfl (by norm_num))
    e1.1 e1.2.1 e1.2.2 (fun j hj => hOt j (by have := hh 1 (by norm_num); omega))
    (fun j hj => hO15 j (by have := hh 1 (by norm_num); omega)) (hOb 1 le_rfl (by norm_num))
    (hPtp 1 le_rfl (by norm_num)) (htp 1 le_rfl (by norm_num) _ rfl) ?_
  refine tp_step ha vsC_w24_bufs vsC_w24_pure vsC24_mem.1 vsC24_mem.2 (by norm_num) (by decide) vsC25_eq B18
    (B1076.le (by norm_num)) (B11.le (by norm_num)) (B10.le (by norm_num)) (B17.le (by norm_num)) (hsel 1 (by norm_num))
    (hh 1 (by norm_num)) (by norm_num) (hsel 2 (by norm_num)) (hh 2 (by norm_num)) h15
    (hbv 2 (by norm_num) (by norm_num)) e2.1 e2.2.1 e2.2.2 (fun j hj => hOt j (by have := hh 2 (by norm_num); omega))
    (fun j hj => hO15 j (by have := hh 2 (by norm_num); omega)) (hOb 2 (by norm_num) (by norm_num))
    (hPtp 2 (by norm_num) (by norm_num)) (htp 2 (by norm_num) (by norm_num) _ rfl) ?_
  refine tp_step ha vsC_w26_bufs vsC_w26_pure vsC26_mem.1 vsC26_mem.2 (by norm_num) (by decide) vsC27_eq B18
    (B1076.le (by norm_num)) (B11.le (by norm_num)) (B10.le (by norm_num)) (B17.le (by norm_num)) (hsel 2 (by norm_num))
    (hh 2 (by norm_num)) (by norm_num) (hsel 3 (by norm_num)) (hh 3 (by norm_num)) h15
    (hbv 3 (by norm_num) (by norm_num)) e3.1 e3.2.1 e3.2.2 (fun j hj => hOt j (by have := hh 3 (by norm_num); omega))
    (fun j hj => hO15 j (by have := hh 3 (by norm_num); omega)) (hOb 3 (by norm_num) (by norm_num))
    (hPtp 3 (by norm_num) (by norm_num)) (htp 3 (by norm_num) (by norm_num) _ rfl) ?_
  refine tp_step ha vsC_w28_bufs vsC_w28_pure vsC28_mem.1 vsC28_mem.2 (by norm_num) (by decide) vsC29_eq B18
    (B1076.le (by norm_num)) (B11.le (by norm_num)) (B10.le (by norm_num)) (B17.le (by norm_num)) (hsel 3 (by norm_num))
    (hh 3 (by norm_num)) (by norm_num) (hsel 4 (by norm_num)) (hh 4 (by norm_num)) h15
    (hbv 4 (by norm_num) (by norm_num)) e4.1 e4.2.1 e4.2.2 (fun j hj => hOt j (by have := hh 4 (by norm_num); omega))
    (fun j hj => hO15 j (by have := hh 4 (by norm_num); omega)) (hOb 4 (by norm_num) (by norm_num))
    (hPtp 4 (by norm_num) (by norm_num)) (htp 4 (by norm_num) (by norm_num) _ rfl) ?_
  refine tp_step ha vsC_w30_bufs vsC_w30_pure vsC30_mem.1 vsC30_mem.2 (by norm_num) (by decide) vsC31_eq B18
    (B1076.le (by norm_num)) (B11.le (by norm_num)) (B10.le (by norm_num)) (B17.le (by norm_num)) (hsel 4 (by norm_num))
    (hh 4 (by norm_num)) (by norm_num) (hsel 5 (by norm_num)) (hh 5 (by norm_num)) h15
    (hbv 5 (by norm_num) le_rfl) e5.1 e5.2.1 e5.2.2 (fun j hj => hOt j (by have := hh 5 (by norm_num); omega))
    (fun j hj => hO15 j (by have := hh 5 (by norm_num); omega)) (hOb 5 (by norm_num) le_rfl)
    (hPtp 5 (by norm_num) le_rfl) (htp 5 (by norm_num) le_rfl _ rfl) ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => Iff.rfl) (fun i => Iff.rfl) (by simp [List.replicate])

end

end
end LeanVM.Guest.B1.VsC
