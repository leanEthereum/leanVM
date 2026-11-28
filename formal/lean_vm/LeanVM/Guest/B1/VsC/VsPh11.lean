/-
  LeanVM.Guest.B1.VsC.VsPh11

  `wC`'s windows `20 ..< 22`: the first table's point, `table_point__L{h}`.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh10

/-!
# `wC`'s windows `20 ..< 22`

`vsC_w20` (statements `1304 ..< 1307`): the opening's word `0` read (`θ`), `.n 1295 = ptrAt (b10 + 89)`; its `RunHyp` by
`winsHyp_run_bufs`. `vsC_w21` (statement `1307`): `table_point__L{h}` on `[θ, .n 1295, .n 15, .n 7]`, a leaf.
`vsPh11_wins` from numeric hypotheses.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Statements `1304 ..< 1307`. -/
def vsC20 : List Atom := [.load (.n 1293) (.n 10) 0, .const (.n 1294) (word 452984832 0), .mul (.n 1295) (.n 679) (.n 1294)]

/-- Statement `1307`: `table_point__L{h}`. -/
def vsC21s : Stmt := .dispatch (.n 115) tpNames [.n 1293, .n 1295, .n 15, .n 7] [.n 1296, .n 1297, .n 1298]

set_option maxRecDepth 200000 in
theorem vsC20_eq : (vsC.drop 876).take 3 = vsC20.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC21_eq : (vsC.drop 879).take 1 = [vsC21s] := stmtsEqb_sound (by decide +kernel)

theorem vsC_w21_eq : vsC_w21 = .call vsC21s := by rw [vsC_w21, headD_of_take_one vsC21_eq]

theorem tpNames_getElem! : ∀ j < 25, tpNames[j]! = tpNames.getD j "" := by decide +kernel

theorem tpNames_length : tpNames.length = 25 := rfl

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- `.n 679 = ptrAt (b10 + 1)`, the stream's cursor past the opening's word `0`. -/
theorem vsVal_679 (ha : args.length = 6) {b10 : ℕ} (h10 : vsVal rd0 w args (.n 10) = ptrAt b10) :
    vsVal rd0 w args (.n 679) = ptrAt (b10 + 1) := by
  have m7 : ∀ a ∈ vsC7q, Stmt.atom a ∈ vsC := fun a h =>
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [vsC7_eq]; exact List.mem_append_right _ (List.mem_map_of_mem h)))
  have hg7 : ∀ a ∈ vsC7q, Good rd0 (storesOf 482 vsC) w (vsVal rd0 w args) a := fun a h =>
    vsVal_goodC (rd := rd0) (w := w) ha (.atom a) (m7 a h)
  rw [good_mulF (hg7 (.mul (.n 679) (.n 10) (.n 678)) (by simp [vsC7q])) (by omega) (by omega), h10,
    show vsVal rd0 w args (.n 678) = word 2 0 from hg7 (.const (.n 678) (word 2 0)) (by simp [vsC7q]),
    show word 2 0 = gen ^ 1 from wordG (j := 1) (by norm_num), ptrAt_add]

end

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `20 ..< 22`' hypotheses**: the opening's buffer `.n 10` at `b10` (its words `xs10`, word `0` the
table's `θ`, held on the evaluation memory and on every memory with `Pre` and the words held, own); the first table's
height `.n 115 = g^h`, `h ≤ 24`; `table_point`'s arrays (`h` words at `b10 + 89`, at `.n 15`'s `b15`, `h + 1` at
`.n 7`'s `b7`; own), its precondition and returns; `K` past the leaf. -/
theorem vsPh11_wins (ha : args.length = 6) {st : St} {K : St → Prop} {b7 b10 b15 h : ℕ} {xs10 ts xs cs : List E}
    {θ top : E}
    (h10 : vsVal rd0 w args (.n 10) = ptrAt b10) (hl10 : 1 ≤ xs10.length) (r10 : ReadsAt rd0 (ptrAt b10) xs10)
    (hO10 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b10) xs10) (hOwn10 : Own (b10 + 0))
    (hθ : xs10[0]? = some θ)
    (h115 : vsVal rd0 w args (.n 115) = gen ^ h) (hh : h ≤ 24)
    (h15 : vsVal rd0 w args (.n 15) = ptrAt b15) (h7 : vsVal rd0 w args (.n 7) = ptrAt b7)
    (hts : ts.length = h) (hxs : xs.length = h) (hcs : cs.length = h)
    (hOt : ∀ j < h, Own (b10 + 89 + j)) (hO15 : ∀ j < h, Own (b15 + j)) (hO7 : ∀ j < h + 1, Own (b7 + j))
    (hPtp : ∀ rd, Pre rd ∧ st.O rd →
      ReadsAt rd (ptrAt (b10 + 89)) ts ∧ ReadsAt rd (ptrAt b15) xs ∧ ReadsAt rd (ptrAt b7) (cs ++ [top]))
    (htp : w 1296 = θ * tpTotalG ts xs cs top h ∧ w 1297 = 1 + (1 + top) * tpPad cs xs ∧ w 1298 = tpFullAt ts xs h)
    (hK : K ⟨st.a, leafEnd fs al (tpNames.getD h "") st.kc, st.O, st.D, st.Qs ++ [PostQuiet]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w20, vsC_w21] st K := by
  rw [vsC_w20, vsC_w21_eq]
  set σ := vsVal rd0 w args with hσ
  have hg20 : ∀ x ∈ atomsOf ((vsC.drop 876).take 3), Good rd0 vsSL w σ x := vsC_atoms_good ha 876 3
  have m20 : ∀ x ∈ vsC20, x ∈ atomsOf ((vsC.drop 876).take 3) := fun x h => by rw [vsC20_eq, atomsOf_map]; exact h
  have hsp : ∀ q ∈ spC20, q = (10, 1) := fun q hq => by simpa [spC20] using hq
  refine winsHyp_run_bufs vsC_w20_bufs hg20 (fun _ => b10) (fun _ => xs10)
    (fun q hq => by obtain rfl := hsp q hq; exact h10)
    (fun q hq => by obtain rfl := hsp q hq; exact hl10)
    (fun q hq => by obtain rfl := hsp q hq; exact r10)
    (fun q hq j hj => by
      obtain rfl := hsp q hq
      obtain rfl : j = 0 := by change j < 1 at hj; omega
      exact Or.inl hOwn10)
    (fun rd hp ho q hq => by obtain rfl := hsp q hq; exact hO10 rd hp ho)
    (fun x hx => by simp [stC20] at hx)
    (fun x hx => by rw [vsC_w20_pure] at hx; simp [pureC20] at hx) ?_
  -- the table's point
  have fr : vsSL.contains (.load (.n 1293) (.n 10) 0) = false := by decide +kernel
  have e1293 : σ (.n 1293) = θ :=
    good_load_get? (by intro h; rw [List.contains_iff_mem.mpr h] at fr; exact absurd fr (by decide))
      (hg20 _ (m20 _ (by simp [vsC20]))) h10 r10 hθ
  have e1295 : σ (.n 1295) = ptrAt (b10 + 89) := by
    rw [show b10 + 89 = b10 + 1 + 88 by omega,
      good_mulF (hg20 (.mul (.n 1295) (.n 679) (.n 1294)) (m20 _ (by simp [vsC20]))) (by omega) (by omega),
      show σ (.n 679) = ptrAt (b10 + 1) from vsVal_679 ha h10, show σ (.n 1294) = word 452984832 0 from hg20 (.const (.n 1294) (word 452984832 0))
        (m20 _ (by simp [vsC20])), show word 452984832 0 = gen ^ 88 from pkC_eq, ptrAt_add]
  have r21 : ∀ v ∈ [V.n 1296, .n 1297, .n 1298], σ v = w v.idx := vsVal_retC (rd0 := rd0) (w := w) ha vsC21_eq
  have hargs : (argsOf vsC21s).map σ = [θ, ptrAt (b10 + 89), ptrAt b15, ptrAt b7] := by
    show [σ (.n 1293), σ (.n 1295), σ (.n 15), σ (.n 7)] = _
    rw [e1293, e1295, h15, h7]
  have hrets : (retsOf vsC21s).map σ =
      [θ * tpTotalG ts xs cs top h, 1 + (1 + top) * tpPad cs xs, tpFullAt ts xs h] := by
    show [σ (.n 1296), σ (.n 1297), σ (.n 1298)] = _
    rw [r21 (.n 1296) (by simp), r21 (.n 1297) (by simp), r21 (.n 1298) (by simp), htp.1, htp.2.1, htp.2.2]
  have L := table_point_leafA fs al cert k hh θ (ptrAt (b10 + 89)) (ptrAt b15) (ptrAt b7) top ts xs cs hts hxs hcs
    (R := fun i => (R i ∨ Own i) ∨ st.D i)
    (fun off hoff => ⟨b10 + 89 + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hOt off hoff))⟩)
    (fun off hoff => ⟨b15 + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hO15 off hoff))⟩)
    (fun off hoff => ⟨b7 + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hO7 off hoff))⟩)
  rw [← hrets, ← hargs] at L
  refine winsHyp_call_leaf (g := tpNames.getD h "")
    ⟨h, by rw [tpNames_length]; omega, by rw [h115, Value.gen_pow_eq_ofK], tpNames_getElem! _ (by omega)⟩ L
    (fun _ h => h) (fun rd hp => hPtp rd hp) ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => by simp) (fun i => by simp) rfl

end

end
end LeanVM.Guest.B1.VsC
