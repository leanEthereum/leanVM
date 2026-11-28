/-
  LeanVM.Guest.B1.VsC.VsPh4

  `wC`'s windows `0 ..< 3`: the chunk selector, `chunk_d`, `certify_stack`.
-/

module

public import LeanVM.Guest.B1.VsC.VsFront

/-!
# `wC`'s first windows

`vsC_w0` (statements `428 ..< 430`: `.n 483 = g^w · g^(-19) = g^(w - 19)`), `vsC_w1` (statement `430`: the
`chunk_d` dispatch on `.n 483`, a leaf ending at its cursor, returning `g^(chunkCount w)` into `.n 484`) and
`vsC_w2` (statement `431`: `certify_stack(.n 112, .n 4)` into `.n 485 … .n 487`).

`certify_stack` returns pointers into its own words, at its frame `allocBase (al "certify_stack") kc` past the
callees' cursor `kc`, so the oracle's words `485 … 487` depend on `kc`. The front's callees and `chunk_d` are
leaves ending at their cursor (`LeafAtA`), so `kc` is explicit; `vsPh4_wins` takes `certify_stack`'s
`CallAtA` at that frame and at a given end `ec`, the rest of `wC` asked at `ec`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Statements `428 ..< 430`. -/
def vsC0 : List Atom :=
  [.const (.n 482) (word 10248187242686185485 0), .mul (.n 483) (.n 409) (.n 482)]

/-- Statement `430`: the `chunk_d` dispatch. -/
def vsC1s : Stmt := .dispatch (.n 483) cdNames [] [.n 484]

/-- Statement `431`: `certify_stack`. -/
def vsC2s : Stmt := .call "certify_stack" [.n 112, .n 4] [.n 485, .n 486, .n 487]

theorem vsC0_eq : (vsC.drop 0).take 2 = vsC0.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

theorem vsC1_eq : (vsC.drop 2).take 1 = [vsC1s] := stmtsEqb_sound (by decide +kernel)

theorem vsC2_eq : (vsC.drop 3).take 1 = [vsC2s] := stmtsEqb_sound (by decide +kernel)

theorem vsC_w0_eq : vsC_w0 = .run vsC0 := by rw [vsC_w0, vsC0_eq, atomsOf_map]

theorem vsC_w1_eq : vsC_w1 = .call vsC1s := by rw [vsC_w1, headD_of_take_one vsC1_eq]

theorem vsC_w2_eq : vsC_w2 = .call vsC2s := by rw [vsC_w2, headD_of_take_one vsC2_eq]

theorem cdNames_getElem! : ∀ j < 6, cdNames[j]! = cdNames.getD j "" := by decide +kernel

theorem cdNames_length : cdNames.length = 6 := rfl

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- **A call or dispatch of `vsC` returns the oracle's words.** -/
theorem vsVal_retC (ha : args.length = 6) {i : ℕ} {s : Stmt} (h : (vsC.drop i).take 1 = [s]) :
    GoodS rd0 (storesOf 482 vsC) w (vsVal rd0 w args) s :=
  vsVal_goodC (rd := rd0) (w := w) ha s
    (List.mem_of_mem_drop (List.mem_of_mem_take (by rw [h]; exact List.mem_singleton_self _)))

/-- **A run of `vsC`'s atoms satisfies its equations.** -/
theorem vsC_run_good (ha : args.length = 6) {i n : ℕ} {as : List Atom} (h : (vsC.drop i).take n = as.map Stmt.atom) :
    ∀ a ∈ as, Good rd0 (storesOf 482 vsC) w (vsVal rd0 w args) a := fun a ha' =>
  vsVal_goodC (rd := rd0) (w := w) ha (.atom a)
    (List.mem_of_mem_drop (List.mem_of_mem_take (by rw [h]; exact List.mem_map_of_mem ha')))

/-- `.n 483 = g^(w - 19)`. -/
theorem vsVal_483 (ha : args.length = 6) {wd : ℕ} (hw19 : 19 ≤ wd) (h409 : vsVal rd0 w args (.n 409) = gen ^ wd) :
    vsVal rd0 w args (.n 483) = gen ^ (wd - 19) := by
  have hg := vsC_run_good (rd0 := rd0) (w := w) ha vsC0_eq
  have e482 : vsVal rd0 w args (.n 482) = word 10248187242686185485 0 := hg (.const (.n 482) (word 10248187242686185485 0)) (by simp [vsC0])
  rw [good_mulF (hg (.mul (.n 483) (.n 409) (.n 482)) (by simp [vsC0])) (by omega) (by omega), h409, e482,
    VerifySub.pow_mul_winv19 hw19]

end

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `0 ..< 3`' hypotheses**: the link's width `19 ≤ w ≤ 24` (`.n 409 = g^w`), `chunk_d`'s
return `g^(chunkCount w)` in the oracle, `certify_stack`'s arguments' values and its returns the oracle's, its
`CallAtA` at its frame past `chunk_d`'s end, ending at `ec`, its region and precondition the window's; `K` at
`ec`. -/
theorem vsPh4_wins (ha : args.length = 6) {st : St} {K : St → Prop} {wd : ℕ} (hw19 : 19 ≤ wd) (hw24 : wd ≤ 24)
    (h409 : vsVal rd0 w args (.n 409) = gen ^ wd) (hw484 : w 484 = gen ^ chunkCount wd)
    {a0 a1 r0 r1 r2 : E} {Rc Dc : ℕ → Prop} {Oc Pc : Reader → Prop} {Qc : Reader → Tree → Prop} {ec : ℕ}
    (h112 : vsVal rd0 w args (.n 112) = a0) (h4 : vsVal rd0 w args (.n 4) = a1)
    (hw485 : w 485 = r0) (hw486 : w 486 = r1) (hw487 : w 487 = r2)
    (hc : CallAtA fs al cert k "certify_stack" [a0, a1] [r0, r1, r2] Rc Dc Oc Pc Qc (fs "certify_stack")
      (allocBase (al "certify_stack") (leafEnd fs al (cdNames.getD (wd - 19) "") st.kc))
      (allocBase (al "certify_stack") (leafEnd fs al (cdNames.getD (wd - 19) "") st.kc) + fs "certify_stack") ec)
    (hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) (hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd)
    (hK : K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [PostQuiet, Qc]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w0, vsC_w1, vsC_w2] st K := by
  rw [vsC_w0_eq, vsC_w1_eq, vsC_w2_eq, WinsHyp]
  refine ⟨RunHyp.of_asks rfl (fun A hA => by simp [loadAddrs, vsC0, Ev.loadAddr?] at hA)
    (fun A hA => by
      rw [show heapHintAddrs (vsVal rd0 w args) (vsC0.map Ev.atom) = [] from rfl] at hA
      simp at hA)
    (fun x hx => by rw [show vsC0.filter pureAsks = [] by decide +kernel] at hx; simp at hx)
    (fun rd _ _ _ x hx => by rw [show vsC0.filter memAsks = [] by decide +kernel] at hx; simp at hx), ?_⟩
  rw [show allocs (vsVal rd0 w args) (vsC0.map Ev.atom) = [] from rfl, List.sum_nil, Nat.add_zero]
  have e483 := vsVal_483 (rd0 := rd0) (w := w) ha hw19 h409
  have e484 : vsVal rd0 w args (.n 484) = gen ^ chunkCount wd :=
    (vsVal_retC (rd0 := rd0) (w := w) ha vsC1_eq (.n 484) (List.mem_singleton_self _)).trans hw484
  have cd := chunk_d_leafA fs al cert k (fun rd => Pre rd ∧ st.O rd) hw19 hw24 (fun _ => False)
  rw [← e484] at cd
  refine winsHyp_call_leaf (g := cdNames.getD (wd - 19) "")
    ⟨wd - 19, by rw [cdNames_length]; omega, by rw [e483, Value.gen_pow_eq_ofK],
      cdNames_getElem! _ (by omega)⟩ cd (fun _ h => h.elim) (fun _ h => h) ?_
  have ret := vsVal_retC (rd0 := rd0) (w := w) ha vsC2_eq
  have e485 : vsVal rd0 w args (.n 485) = r0 := (ret (.n 485) (by simp)).trans hw485
  have e486 : vsVal rd0 w args (.n 486) = r1 := (ret (.n 486) (by simp)).trans hw486
  have e487 : vsVal rd0 w args (.n 487) = r2 := (ret (.n 487) (by simp)).trans hw487
  rw [← h112, ← h4, ← e485, ← e486, ← e487] at hc
  refine winsHyp_call_at (g := "certify_stack") rfl hc (fun i hi => (hRc i hi).imp_right Or.inl)
    (fun rd hp => hPc rd ⟨hp.1, hp.2.1⟩) ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => by simp) (fun i => by simp) (by simp)

end

end
end LeanVM.Guest.B1.VsC
