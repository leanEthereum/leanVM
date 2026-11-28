/-
  LeanVM.Guest.B1.VsC.VsPh13

  `wC`'s windows `32 ..< 35`: the link's terminal claim, `link_terminal__L{w}`, the two limbs in `K`.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh12

/-!
# `wC`'s windows `32 ..< 35`

`vsC_w32` (statements `1887 ..< 2905`, 1018 atoms): the link's terminal sums over `.n 18`'s word at the last table's
height, `.n 1076`, `.n 11`, `.n 10`, `.n 17`, its twelve stores into `.n 19`, the selector `.n 2893 = g^(w - 19)`;
its `RunHyp` by `winsHyp_run_bufAt`, the stores' words on the evaluation memory a hypothesis. `vsC_w33` (statement
`2905`): `link_terminal__L{w}`, at a given end. `vsC_w34` (statements `2906 ..< 2928`): `verify_sub`'s two first
arguments split into limbs, each limb asserted in `K` (`split_inK`). `vsPh13_wins` from numeric hypotheses.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Statement `2905`: `link_terminal__L{w}`. -/
def vsC33s : Stmt :=
  .dispatch (.n 2893) ltNames [.n 12, .n 1076, .n 2846, .n 19, .n 2891, .n 695, .n 2890, .n 1077] [.n 2894]

set_option maxRecDepth 200000 in
theorem vsC33_eq : (vsC.drop 2477).take 1 = [vsC33s] := stmtsEqb_sound (by decide +kernel)

theorem vsC_w33_eq : vsC_w33 = .call vsC33s := by rw [vsC_w33, headD_of_take_one vsC33_eq]

/-- The atoms of `vsC_w32` `vsPh13_wins` reads values of. -/
def vs32L : List Atom :=
  [.mul (.n 1888) (.n 18) (.n 120), .const (.n 2892) (word 10248187242686185485 0), .mul (.n 2893) (.n 409) (.n 2892)]

/-- The atoms of `vsC_w34` `vsPh13_wins` reads values of. -/
def vs34L : List Atom :=
  [.hint (.limbs (.n 0) [.n 2895]), .add (.n 2896) (.n 0) (.n 2895), .const (.n 2897) (word 2 1),
    .mul (.n 2898) (.n 2896) (.n 2897), .hint (.limbs (.n 1) [.n 2899]), .add (.n 2900) (.n 1) (.n 2899),
    .const (.n 2901) (word 2 1), .mul (.n 2902) (.n 2900) (.n 2901)]

set_option maxRecDepth 200000 in
theorem vsC32_sub : vs32L.all (fun a => (atomsOf ((vsC.drop 1459).take 1018)).contains a) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem vsC34_sub : vs34L.all (fun a => (atomsOf ((vsC.drop 2478).take 22)).contains a) = true := by decide +kernel

theorem ltNames_getElem! : ∀ j < 6, ltNames[j]! = ltNames.getD j "" := by decide +kernel

theorem ltNames_length6 : ltNames.length = 6 := rfl

section
variable {rd0 : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- **A word split into limbs, both in `K`**: the hinted low limb `b`, `v + b` at `b + 1`, `y⁻¹` at `b + 2`, the high
limb at `b + 3`. -/
theorem split_inK {v : V} {b : ℕ} (h0 : Good rd0 S w σ (.hint (.limbs v [.n b])))
    (h1 : Good rd0 S w σ (.add (.n (b + 1)) v (.n b))) (h2 : Good rd0 S w σ (.const (.n (b + 2)) (word 2 1)))
    (h3 : Good rd0 S w σ (.mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2)))) :
    IsInK (σ (.n b)) ∧ IsInK (σ (.n (b + 3))) := by
  have e0 : σ (.n b) = ofK ((σ v).limb 0) := (h0 0 (by simp)).trans (by simp [limbAt])
  have h1' : σ (.n (b + 1)) = σ v + σ (.n b) := h1
  have h2' : σ (.n (b + 2)) = word 2 1 := h2
  refine ⟨by rw [e0]; exact Value.ofK_isInK _, ?_⟩
  rw [good_mulF h3 (by omega) (by omega), h1', h2', e0, word_y_inv, Value.split_hi]
  exact Value.ofK_isInK _

end

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `32 ..< 35`' hypotheses**: the buffers `.n 18` (`25` words), `.n 1076` (`80`), `.n 11` (`30`),
`.n 10` (`89`), `.n 17` (`95`), `.n 19` (`12`) as `BufAt`s; the last table's height `.n 120 = g^h`, `h ≤ 24`; the
stores' words into `.n 19` on the evaluation memory; the link's width `.n 409 = g^w`, `19 ≤ w ≤ 24`;
`link_terminal__L{w}`'s `CallAtA` on its arguments' values at a given end `ec`, its return the oracle's; `K` at `ec`. -/
theorem vsPh13_wins (ha : args.length = 6) {st : St} {K : St → Prop} {b18 b1076 b11 b10 b17 b19 h wd : ℕ}
    {xs18 xs1076 xs11 xs10 xs17 xs19 : List E} {a12 coef certW nu rest : E}
    (B18 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 18 b18 25 xs18)
    (B1076 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 1076 b1076 80 xs1076)
    (B11 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 11 b11 30 xs11)
    (B10 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 10 b10 89 xs10)
    (B17 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 17 b17 95 xs17)
    (B19 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 19 b19 12 xs19)
    (h120 : vsVal rd0 w args (.n 120) = gen ^ h) (hh : h ≤ 24)
    (hst : ∀ x ∈ stC32, MemF rd0 (vsVal rd0 w args) x)
    (h409 : vsVal rd0 w args (.n 409) = gen ^ wd) (hw19 : 19 ≤ wd) (hw24 : wd ≤ 24)
    (e12 : vsVal rd0 w args (.n 12) = a12) (e2846 : vsVal rd0 w args (.n 2846) = coef)
    (e2891 : vsVal rd0 w args (.n 2891) = certW) (e695 : vsVal rd0 w args (.n 695) = nu)
    (e2890 : vsVal rd0 w args (.n 2890) = rest)
    {Rc Dc : ℕ → Prop} {Oc Pc : Reader → Prop} {Qc : Reader → Tree → Prop} {Bc ec : ℕ}
    (hc : CallAtA fs al cert k (ltNames.getD (wd - 19) "")
      [a12, ptrAt b1076, coef, ptrAt b19, certW, nu, rest, w 1077] [w 2894] Rc Dc Oc Pc Qc Bc
      (allocBase (al (ltNames.getD (wd - 19) "")) st.kc) (allocBase (al (ltNames.getD (wd - 19) "")) st.kc + Bc) ec)
    (hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) (hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd)
    (hK : K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Qc]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w32, vsC_w33, vsC_w34] st K := by
  rw [vsC_w32, vsC_w33_eq, vsC_w34]
  set σ := vsVal rd0 w args with hσ
  have hg32 : ∀ x ∈ atomsOf ((vsC.drop 1459).take 1018), Good rd0 vsSL w σ x := vsC_atoms_good ha 1459 1018
  have m32 : ∀ a ∈ vs32L, a ∈ atomsOf ((vsC.drop 1459).take 1018) := fun a h => by
    simpa using List.all_eq_true.mp vsC32_sub a h
  have e1888 : σ (.n 1888) = ptrAt (b18 + h) := by
    rw [good_mulF (hg32 _ (m32 (.mul (.n 1888) (.n 18) (.n 120)) (by simp [vs32L]))) (by omega) (by omega), B18.ptr,
      h120, ptrAt_add]
  let bs : ℕ → ℕ := fun v => if v = 1888 then b18 + h else if v = 1076 then b1076 else if v = 11 then b11 else
    if v = 10 then b10 else if v = 17 then b17 else b19
  let xs' : ℕ → List E := fun v => if v = 1888 then xs18.drop h else if v = 1076 then xs1076 else if v = 11 then xs11
    else if v = 10 then xs10 else if v = 17 then xs17 else xs19
  have hsp : ∀ q ∈ spC32, q = (1888, 1) ∨ q = (1076, 80) ∨ q = (11, 30) ∨ q = (10, 89) ∨ q = (17, 95) ∨
      q = (19, 12) := fun q hq => by simpa [spC32] using hq
  refine winsHyp_run_bufAt vsC_w32_bufs hg32 bs xs' (fun q hq => ?_) hst
    (fun x hx => by rw [vsC_w32_pure] at hx; simp [pureC32] at hx) ?_
  · rcases hsp q hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact B18.drop e1888 (by omega)
    · exact B1076
    · exact B11
    · exact B10
    · exact B17
    · exact B19
  -- `link_terminal__L{w}`
  have e2893 : σ (.n 2893) = gen ^ (wd - 19) := by
    rw [good_mulF (hg32 _ (m32 (.mul (.n 2893) (.n 409) (.n 2892)) (by simp [vs32L]))) (by omega) (by omega), h409,
      show σ (.n 2892) = word 10248187242686185485 0 from hg32 (.const (.n 2892) (word 10248187242686185485 0))
        (m32 _ (by simp [vs32L])), VerifySub.pow_mul_winv19 hw19]
  have r33 : ∀ v ∈ [V.n 2894], σ v = w v.idx := vsVal_retC (rd0 := rd0) (w := w) ha vsC33_eq
  have e1077 : σ (.n 1077) = w 1077 := vsVal_retC (rd0 := rd0) (w := w) ha vsC16_eq (.n 1077) (by simp)
  have hargs : (argsOf vsC33s).map σ = [a12, ptrAt b1076, coef, ptrAt b19, certW, nu, rest, w 1077] := by
    show [σ (.n 12), σ (.n 1076), σ (.n 2846), σ (.n 19), σ (.n 2891), σ (.n 695), σ (.n 2890), σ (.n 1077)] = _
    rw [e12, B1076.ptr, e2846, B19.ptr, e2891, e695, e2890, e1077]
  have hrets : (retsOf vsC33s).map σ = [w 2894] := by
    show [σ (.n 2894)] = _
    rw [r33 (.n 2894) (by simp)]
  rw [← hargs, ← hrets] at hc
  refine winsHyp_call_at (g := ltNames.getD (wd - 19) "")
    ⟨wd - 19, by rw [ltNames_length6]; omega, by rw [e2893, Value.gen_pow_eq_ofK], ltNames_getElem! _ (by omega)⟩
    hc hRc hPc ?_
  -- the limbs
  have hg34 : ∀ x ∈ atomsOf ((vsC.drop 2478).take 22), Good rd0 vsSL w σ x := vsC_atoms_good ha 2478 22
  have m34 : ∀ a ∈ vs34L, a ∈ atomsOf ((vsC.drop 2478).take 22) := fun a h => by
    simpa using List.all_eq_true.mp vsC34_sub a h
  have k0 := split_inK (v := .n 0) (b := 2895) (hg34 _ (m34 _ (by simp [vs34L]))) (hg34 _ (m34 _ (by simp [vs34L])))
    (hg34 _ (m34 _ (by simp [vs34L]))) (hg34 _ (m34 (.mul (.n 2898) (.n 2896) (.n 2897)) (by simp [vs34L])))
  have k1 := split_inK (v := .n 1) (b := 2899) (hg34 _ (m34 _ (by simp [vs34L]))) (hg34 _ (m34 _ (by simp [vs34L])))
    (hg34 _ (m34 _ (by simp [vs34L]))) (hg34 _ (m34 (.mul (.n 2902) (.n 2900) (.n 2901)) (by simp [vs34L])))
  refine winsHyp_run_bufs vsC_w34_bufs hg34 (fun _ => 0) (fun _ => []) (fun q hq => by simp [spC34] at hq)
    (fun q hq => by simp [spC34] at hq) (fun q hq => by simp [spC34] at hq) (fun q hq => by simp [spC34] at hq)
    (fun _ _ _ q hq => by simp [spC34] at hq) (fun x hx => by simp [stC34] at hx) (fun x hx => ?_) ?_
  · rw [vsC_w34_pure] at hx
    simp only [pureC34, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [k0, k1]
  rw [WinsHyp]
  exact hK


theorem wC_drop22 : wC.drop 22 = [vsC_w22, vsC_w23, vsC_w24, vsC_w25, vsC_w26, vsC_w27, vsC_w28, vsC_w29, vsC_w30,
    vsC_w31] ++ ([vsC_w32, vsC_w33, vsC_w34] ++ wC.drop 35) := rfl

/-- **`wC`'s windows `22 ..< 35`' hypotheses** (`vsPh12_wins`' and `vsPh13_wins`', the latter at the cursor past the five
`table_point` leaves), the windows from `verify_keccak`'s call on (`wC.drop 35`) from the state past
`link_terminal__L{w}` and the limbs. -/
theorem vsPh12_13_wins (ha : args.length = 6) {st : St} {K : St → Prop} {b18 b1076 b11 b10 b17 b15 b19 wd : ℕ}
    {xs18 xs1076 xs11 xs10 xs17 xs19 : List E} {hg bb : ℕ → ℕ} {ts xs cs : ℕ → List E} {top : ℕ → E}
    {a12 coef certW nu rest : E}
    (B18 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 18 b18 25 xs18)
    (B1076 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 1076 b1076 80 xs1076)
    (B11 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 11 b11 30 xs11)
    (B10 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 10 b10 89 xs10)
    (B17 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 17 b17 95 xs17)
    (B19 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 19 b19 12 xs19)
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
    (hst : ∀ x ∈ stC32, MemF rd0 (vsVal rd0 w args) x)
    (h409 : vsVal rd0 w args (.n 409) = gen ^ wd) (hw19 : 19 ≤ wd) (hw24 : wd ≤ 24)
    (e12 : vsVal rd0 w args (.n 12) = a12) (e2846 : vsVal rd0 w args (.n 2846) = coef)
    (e2891 : vsVal rd0 w args (.n 2891) = certW) (e695 : vsVal rd0 w args (.n 695) = nu)
    (e2890 : vsVal rd0 w args (.n 2890) = rest)
    {Rc Dc : ℕ → Prop} {Oc Pc : Reader → Prop} {Qc : Reader → Tree → Prop} {Bc ec : ℕ}
    (hc : CallAtA fs al cert k (ltNames.getD (wd - 19) "")
      [a12, ptrAt b1076, coef, ptrAt b19, certW, nu, rest, w 1077] [w 2894] Rc Dc Oc Pc Qc Bc
      (allocBase (al (ltNames.getD (wd - 19) "")) (tpKc fs al hg 5 st.kc))
      (allocBase (al (ltNames.getD (wd - 19) "")) (tpKc fs al hg 5 st.kc) + Bc) ec)
    (hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) (hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd)
    (hK : WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre (wC.drop 35)
      ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ List.replicate 5 PostQuiet ++ [Qc]⟩ K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre (wC.drop 22) st K := by
  rw [wC_drop22, winsHyp_append]
  refine vsPh12_wins ha B18 B1076 B11 B10 B17 hsel hh h15 hbv hts hOt hO15 hOb hPtp htp ?_
  rw [winsHyp_append]
  exact vsPh13_wins ha B18 B1076 B11 B10 B17 B19 (hsel 5 le_rfl) (hh 5 le_rfl) hst h409 hw19 hw24 e12 e2846 e2891
    e695 e2890 hc hRc hPc hK

end

end
end LeanVM.Guest.B1.VsC
