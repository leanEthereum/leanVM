/-
  LeanVM.Guest.B1.VsC.VsPh8

  `wC`'s windows `13 ..< 15`: the rounds' state absorbed, `index_side__L{w}`.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh7
public import LeanVM.Guest.B1.VsC.IndexSideA

/-!
# `wC`'s windows `13 ..< 15`

`vsC_w13` (statements `687 ..< 698`): `link_rounds`' state copied, the word at its returned cursor `.n 772` read, one
permutation, `.n 796 = g^(w - 19)`; its `RunHyp` by `winsHyp_run_bufs`. `vsC_w14` (statement `698`): `index_side__L{w}`
on the rounds' point `.n 12`, the link's `.n 694` and the output `.n 13`, at its own end (`index_side_atA`: the frame of
`index_mle__L{w}` past its own). `vsPh8_wins` from numeric hypotheses.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **`index_side__L{w}` at its end**: its frame at `fp`, its callee `index_mle__L{w}`'s frame at the aligned base
of `c`. -/
theorem index_side_atA (kd : ℕ) {w : ℕ} (hw : 19 ≤ w) (hw' : w ≤ 24) (r zeta below : E) (rs zs : List E)
    (hrs : rs.length = w) (hzs : zs.length = w) (hap : ArraysApart [r, zeta, below] [(0, w), (1, w), (2, w + 1)])
    {R : ℕ → Prop} (hr : ArrIn R r w) (hz : ArrIn R zeta w) (hb : ArrIn R below (w + 1)) (fp c : ℕ) :
    CallAtA fs al cert kd (isNames.getD (w - 19) "") [r, zeta, below]
      [indexMle rs, (sideFold zs rs).1, (sideFold zs rs).2.1] R (fun _ => False) (fun _ => True)
      (fun rd ↦ HoldsArrays rd [r, zeta, below] (isIns rs zs) ∧ HoldsArrays rd [r, zeta, below] (isOuts rs w))
      PostQuiet (fs (isNames.getD (w - 19) "")) fp c
      (allocBase (al (imNames.getD (w - 19) "")) c + fs (imNames.getD (w - 19) "")) := by
  obtain ⟨fi, fm, hfi, hfm, hbd, hck⟩ := is_place w hw hw'
  have hck' := hck
  simp only [isPlaceOk, Bool.and_eq_true] at hck'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hpi⟩, -⟩, -⟩, -⟩, hpm⟩ := hck'
  have hS : coreProgram.PureIn [isNames.getD (w - 19) "", imNames.getD (w - 19) ""] := by
    intro g hg fn hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [hfi] at hf; cases hf; exact hpi
    · rw [hfm] at hf; cases hf; exact hpm
  have h0 := index_side_complete kd w hw hw' r zeta below rs zs hrs hzs hap
  refine callAtA_of_callCompletes0 hS List.mem_cons_self ?_ h0
    fun rd t _ _ hn hv hbo _ => is_shape hfi hfm hbd hck hS hr hz hb hn hv hbo c
  exact le_trans (le_allocBase _ _) (Nat.le_add_right _ _)

end

/-- Statement `698`: `index_side__L{w}`. -/
def vsC14s : Stmt := .dispatch (.n 796) isNames [.n 12, .n 694, .n 13] [.n 797, .n 798, .n 799]

set_option maxRecDepth 200000 in
theorem vsC14_eq : (vsC.drop 270).take 1 = [vsC14s] := stmtsEqb_sound (by decide +kernel)

theorem vsC_w14_eq : vsC_w14 = .call vsC14s := by rw [vsC_w14, headD_of_take_one vsC14_eq]

set_option maxRecDepth 200000 in
/-- The rounds' cursor word, and `.n 796`'s two atoms. -/
theorem vsC13_atoms : Atom.const (.n 795) (word 10248187242686185485 0) ∈ atomsOf ((vsC.drop 259).take 11) ∧
    Atom.mul (.n 796) (.n 409) (.n 795) ∈ atomsOf ((vsC.drop 259).take 11) := by decide +kernel

theorem isNames_getElem! : ∀ j < 6, isNames[j]! = isNames.getD j "" := by decide +kernel

theorem isNames_length : isNames.length = 6 := rfl

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `13 ..< 15`' hypotheses**: `link_rounds`' returned cursor `w 772 = ptrAt b772`, its word `v`
held on the evaluation memory and on every memory with `Pre` and the words held, its cell in `Own`, `R` or the claimed
data; `.n 409 = g^w`; `index_side__L{w}`'s arrays (the point `rs` at `.n 12`'s `b12`, `zs` at `.n 694`'s `bz`, the
`w + 1` outputs at `.n 13`'s `b13`; own, apart), its preconditions and returns; `K` at its end. -/
theorem vsPh8_wins (ha : args.length = 6) {st : St} {K : St → Prop} {b772 b12 bz b13 wd : ℕ} {v : E}
    {rs zs : List E} (hw19 : 19 ≤ wd) (hw24 : wd ≤ 24)
    (hw772 : w 772 = ptrAt b772) (r772 : ReadsAt rd0 (ptrAt b772) [v])
    (hO772 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b772) [v]) (hc772 : Own b772 ∨ R b772 ∨ st.D b772)
    (h409 : vsVal rd0 w args (.n 409) = gen ^ wd)
    (h12 : vsVal rd0 w args (.n 12) = ptrAt b12) (h694 : vsVal rd0 w args (.n 694) = ptrAt bz)
    (h13 : vsVal rd0 w args (.n 13) = ptrAt b13) (hrs : rs.length = wd) (hzs : zs.length = wd)
    (hap : ArraysApart [ptrAt b12, ptrAt bz, ptrAt b13] [(0, wd), (1, wd), (2, wd + 1)])
    (hO12 : ∀ j < wd, Own (b12 + j)) (hOz : ∀ j < wd, Own (bz + j)) (hO13 : ∀ j < wd + 1, Own (b13 + j))
    (hPis : ∀ rd, Pre rd ∧ st.O rd → HoldsArrays rd [ptrAt b12, ptrAt bz, ptrAt b13] (isIns rs zs) ∧
      HoldsArrays rd [ptrAt b12, ptrAt bz, ptrAt b13] (isOuts rs wd))
    (his : w 797 = indexMle rs ∧ w 798 = (sideFold zs rs).1 ∧ w 799 = (sideFold zs rs).2.1)
    (hK : K ⟨st.a, allocBase (al (imNames.getD (wd - 19) "")) (allocBase (al (isNames.getD (wd - 19) "")) st.kc +
        fs (isNames.getD (wd - 19) "")) + fs (imNames.getD (wd - 19) ""), st.O, st.D, st.Qs ++ [PostQuiet]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w13, vsC_w14] st K := by
  rw [vsC_w13, vsC_w14_eq]
  set σ := vsVal rd0 w args with hσ
  have hg13 : ∀ x ∈ atomsOf ((vsC.drop 259).take 11), Good rd0 vsSL w σ x := vsC_atoms_good ha 259 11
  have e772 : σ (.n 772) = ptrAt b772 :=
    (vsVal_retC (rd0 := rd0) (w := w) ha vsC12_eq (.n 772) (by simp)).trans hw772
  refine winsHyp_run_bufs vsC_w13_bufs hg13 (fun _ => b772) (fun _ => [v])
    (fun q hq => by simp only [spC13, List.mem_singleton] at hq; subst hq; exact e772)
    (fun q hq => by simp only [spC13, List.mem_singleton] at hq; subst hq; exact le_rfl)
    (fun q hq => by simp only [spC13, List.mem_singleton] at hq; subst hq; exact r772)
    (fun q hq j hj => by
      simp only [spC13, List.mem_singleton] at hq; subst hq
      obtain rfl : j = 0 := by simpa using hj
      exact hc772)
    (fun rd hp ho q hq => by simp only [spC13, List.mem_singleton] at hq; subst hq; exact hO772 rd hp ho)
    (fun x hx => by simp [stC13] at hx)
    (fun x hx => by rw [vsC_w13_pure] at hx; simp [pureC13] at hx) ?_
  -- `index_side__L{w}`
  have e796 : σ (.n 796) = gen ^ (wd - 19) := by
    rw [good_mulF (hg13 _ vsC13_atoms.2) (by omega) (by omega), h409,
      show σ (.n 795) = word 10248187242686185485 0 from hg13 _ vsC13_atoms.1, VerifySub.pow_mul_winv19 hw19]
  have r14 : ∀ v ∈ [V.n 797, .n 798, .n 799], σ v = w v.idx := vsVal_retC (rd0 := rd0) (w := w) ha vsC14_eq
  have hargs : (argsOf vsC14s).map σ = [ptrAt b12, ptrAt bz, ptrAt b13] := by
    show [σ (.n 12), σ (.n 694), σ (.n 13)] = _
    rw [h12, h694, h13]
  have hrets : (retsOf vsC14s).map σ = [indexMle rs, (sideFold zs rs).1, (sideFold zs rs).2.1] := by
    show [σ (.n 797), σ (.n 798), σ (.n 799)] = _
    rw [r14 (.n 797) (by simp), r14 (.n 798) (by simp), r14 (.n 799) (by simp), his.1, his.2.1, his.2.2]
  have hc := index_side_atA (fs := fs) (al := al) (cert := cert) k hw19 hw24 (ptrAt b12) (ptrAt bz) (ptrAt b13) rs zs
    hrs hzs hap (R := fun i => (R i ∨ Own i) ∨ st.D i)
    (fun off hoff => ⟨b12 + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hO12 off hoff))⟩)
    (fun off hoff => ⟨bz + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hOz off hoff))⟩)
    (fun off hoff => ⟨b13 + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hO13 off hoff))⟩)
    (allocBase (al (isNames.getD (wd - 19) "")) st.kc)
    (allocBase (al (isNames.getD (wd - 19) "")) st.kc + fs (isNames.getD (wd - 19) ""))
  rw [← hargs, ← hrets] at hc
  refine winsHyp_call_at (g := isNames.getD (wd - 19) "")
    ⟨wd - 19, by rw [isNames_length]; omega, by rw [e796, Value.gen_pow_eq_ofK], isNames_getElem! _ (by omega)⟩
    hc (fun _ h => h) (fun rd hp => by rw [hargs]; exact hPis rd hp) ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => by simp) (fun i => by simp) rfl

end

end
end LeanVM.Guest.B1.VsC
