/-
  LeanVM.Guest.B1.VsC.VsPh9

  `wC`'s windows `15 ..< 17`: the link's index side and its chunk selector, `link_row_side__L{d}`.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh8

/-!
# `wC`'s windows `15 ..< 17`

`vsC_w15` (statements `699 ..< 969`, 270 atoms): the link's sums over `index_side`'s outputs `.n 13`, the hinted split
values `.n 14`, the eq tensor `.n 11` and the opening `.n 10` (no store), the chunk selector `.n 1061 = g^(c - 6)` and
its range check below `g^3`, the cursor `.n 1066 = .n 772·g`; its `RunHyp` by `winsHyp_run_bufs`. `vsC_w16` (statement
`969`): `link_row_side__L{c}`, at a given end. `vsPh9_wins` from numeric hypotheses.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- A held buffer from its word `m` on. -/
theorem readsAt_drop {rd : Reader} {b m : ℕ} {xs : List E} (h : ReadsAt rd (ptrAt b) xs) :
    ReadsAt rd (ptrAt (b + m)) (xs.drop m) := by
  intro j hj
  rw [← ptrAt_add, loadHolds_mul_gen_pow, List.getElem_drop]
  exact h (m + j) (by rw [List.length_drop] at hj; omega)

theorem winv6_mul : word 2017612633061982209 0 * gen ^ 6 = 1 := by
  rw [show gen ^ 6 = ofK (K.ofBits 64) by
      rw [← word_two_pow (a := 6) (by decide)]; exact word_eOfNat _,
    show word 2017612633061982209 0 = ofK (K.ofBits 2017612633061982209) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 2017612633061982209 * K.ofBits 64 = 1 by decide +kernel]
  exact map_one (algebraMap K E)

theorem pow_mul_winv6 {c : ℕ} (h : 6 ≤ c) : gen ^ c * word 2017612633061982209 0 = gen ^ (c - 6) := by
  conv_lhs => rw [show c = (c - 6) + 6 by omega, pow_add, mul_assoc, mul_comm (gen ^ 6), winv6_mul, mul_one]

/-- Statement `969`: `link_row_side__L{c}`. -/
def vsC16s : Stmt :=
  .dispatch (.n 1070) lrsNames [.n 790, .n 791, .n 792, .n 793, .n 794, .n 1066, .n 773, .n 15, .n 16, .n 408, .n 1068]
    [.n 1071, .n 1072, .n 1073, .n 1074, .n 1075, .n 1076, .n 1077]

set_option maxRecDepth 200000 in
theorem vsC16_eq : (vsC.drop 541).take 1 = [vsC16s] := stmtsEqb_sound (by decide +kernel)

theorem vsC_w16_eq : vsC_w16 = .call vsC16s := by rw [vsC_w16, headD_of_take_one vsC16_eq]

/-- The atoms `vsPh9_wins` reads values of. -/
def vs15L : List Atom :=
  [.mul (.n 801) (.n 13) (.n 101), .const (.n 1059) (word 8 0), .const (.n 1060) (word 2017612633061982209 0),
    .mul (.n 1061) (.n 484) (.n 1060), .rangeCheck (.n 1061) (.n 1062) (.n 1063) (.n 1064) (.n 1059),
    .const (.n 1065) (word 2 0), .mul (.n 1066) (.n 772) (.n 1065), .const (.n 1067) (word 365917469723852800 0),
    .mul (.n 1068) (.n 4) (.n 1067), .const (.n 1069) (word 2017612633061982209 0), .mul (.n 1070) (.n 484) (.n 1069)]

set_option maxRecDepth 200000 in
theorem vsC15_sub : vs15L.all (fun a => (atomsOf ((vsC.drop 271).take 270)).contains a) = true := by decide +kernel

theorem vsC15_mem {a : Atom} (h : a ∈ vs15L) : a ∈ atomsOf ((vsC.drop 271).take 270) := by
  simpa using List.all_eq_true.mp vsC15_sub a h

theorem lrsNames_getElem! : ∀ j < 4, lrsNames[j]! = lrsNames.getD j "" := by decide +kernel

theorem lrsNames_length : lrsNames.length = 4 := rfl

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `15 ..< 17`' hypotheses**: the buffers the link's sums read (`.n 13` at `b13`, its word `m` at
`.n 801 = .n 13·g^m`; `.n 14` at `b14`; `.n 11` at `b11`; `.n 10` at `b10`), each held on the evaluation memory and on
every memory with `Pre` and the words held, own; `chunk_d`'s `w 484 = g^c`, `6 ≤ c ≤ 9`; `link_rounds`' cursor
`w 772 = ptrAt b772`; the permutation's five words `f`, `.n 15`, `.n 16` at `b15`, `b16`, `.n 408 = g^n`;
`link_row_side__L{c}`'s `CallAtA` on its arguments' values at a given end `ec`, its returns the oracle's; `K` at `ec`. -/
theorem vsPh9_wins (hk : 6 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    {b10 b11 b13 b14 b15 b16 b772 m n cc qt : ℕ} {xs10 xs11 xs13 xs14 : List E} {f0 f1 f2 f3 f4 : E}
    (h13 : vsVal rd0 w args (.n 13) = ptrAt b13) (hl13 : 20 ≤ xs13.length) (r13 : ReadsAt rd0 (ptrAt b13) xs13)
    (hO13 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b13) xs13) (hOwn13 : ∀ j < xs13.length, Own (b13 + j))
    (h101 : vsVal rd0 w args (.n 101) = gen ^ m) (hm : m < xs13.length)
    (h14 : vsVal rd0 w args (.n 14) = ptrAt b14) (hl14 : 36 ≤ xs14.length) (r14 : ReadsAt rd0 (ptrAt b14) xs14)
    (hO14 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b14) xs14) (hOwn14 : ∀ j < 36, Own (b14 + j))
    (h11 : vsVal rd0 w args (.n 11) = ptrAt b11) (hl11 : 30 ≤ xs11.length) (r11 : ReadsAt rd0 (ptrAt b11) xs11)
    (hO11 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b11) xs11) (hOwn11 : ∀ j < 30, Own (b11 + j))
    (h10 : vsVal rd0 w args (.n 10) = ptrAt b10) (hl10 : 37 ≤ xs10.length) (r10 : ReadsAt rd0 (ptrAt b10) xs10)
    (hO10 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b10) xs10) (hOwn10 : ∀ j < 37, Own (b10 + j))
    (hc6 : 6 ≤ cc) (hc9 : cc ≤ 9) (hw484 : w 484 = gen ^ cc) (hw772 : w 772 = ptrAt b772)
    (hf : vsVal rd0 w args (.n 790) = f0 ∧ vsVal rd0 w args (.n 791) = f1 ∧ vsVal rd0 w args (.n 792) = f2 ∧
      vsVal rd0 w args (.n 793) = f3 ∧ vsVal rd0 w args (.n 794) = f4)
    (h15 : vsVal rd0 w args (.n 15) = ptrAt b15) (h16 : vsVal rd0 w args (.n 16) = ptrAt b16)
    (h408 : vsVal rd0 w args (.n 408) = gen ^ n) (h4 : vsVal rd0 w args (.n 4) = ptrAt qt)
    {Rc Dc : ℕ → Prop} {Oc Pc : Reader → Prop} {Qc : Reader → Tree → Prop} {Bc ec : ℕ}
    (hc : CallAtA fs al cert k (lrsNames.getD (cc - 6) "")
      [f0, f1, f2, f3, f4, ptrAt (b772 + 1), w 773, ptrAt b15, ptrAt b16, gen ^ n, ptrAt qt * word 365917469723852800 0]
      [w 1071, w 1072, w 1073, w 1074, w 1075, w 1076, w 1077] Rc Dc Oc Pc Qc Bc
      (allocBase (al (lrsNames.getD (cc - 6) "")) st.kc) (allocBase (al (lrsNames.getD (cc - 6) "")) st.kc + Bc) ec)
    (hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) (hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd)
    (hK : K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Qc]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w15, vsC_w16] st K := by
  rw [vsC_w15, vsC_w16_eq]
  set σ := vsVal rd0 w args with hσ
  have hg15 : ∀ x ∈ atomsOf ((vsC.drop 271).take 270), Good rd0 vsSL w σ x := vsC_atoms_good ha 271 270
  have e801 : σ (.n 801) = ptrAt (b13 + m) := by
    rw [good_mulF (hg15 (.mul (.n 801) (.n 13) (.n 101)) (vsC15_mem (by simp [vs15L]))) (by omega) (by omega), h13, h101,
      ptrAt_add]
  let bs : ℕ → ℕ := fun v => if v = 13 then b13 else if v = 801 then b13 + m else if v = 14 then b14 else
    if v = 11 then b11 else b10
  let xs : ℕ → List E := fun v => if v = 13 then xs13 else if v = 801 then xs13.drop m else if v = 14 then xs14 else
    if v = 11 then xs11 else xs10
  have hsp : ∀ q ∈ spC15, q = (13, 20) ∨ q = (801, 1) ∨ q = (14, 36) ∨ q = (11, 30) ∨ q = (10, 37) := fun q hq => by
    simpa [spC15] using hq
  -- the chunk selector
  have e484 : σ (.n 484) = gen ^ cc :=
    (vsVal_retC (rd0 := rd0) (w := w) ha vsC1_eq (.n 484) (List.mem_singleton_self _)).trans hw484
  have e1061 : σ (.n 1061) = gen ^ (cc - 6) := by
    rw [good_mulF (hg15 (.mul (.n 1061) (.n 484) (.n 1060)) (vsC15_mem (by simp [vs15L]))) (by omega) (by omega), e484,
      show σ (.n 1060) = word 2017612633061982209 0 from hg15 (.const (.n 1060) (word 2017612633061982209 0)) (vsC15_mem (by simp [vs15L])), pow_mul_winv6 hc6]
  have e1070 : σ (.n 1070) = gen ^ (cc - 6) := by
    rw [good_mulF (hg15 (.mul (.n 1070) (.n 484) (.n 1069)) (vsC15_mem (by simp [vs15L]))) (by omega) (by omega), e484,
      show σ (.n 1069) = word 2017612633061982209 0 from hg15 (.const (.n 1069) (word 2017612633061982209 0)) (vsC15_mem (by simp [vs15L])), pow_mul_winv6 hc6]
  refine winsHyp_run_bufs vsC_w15_bufs hg15 bs xs
    (fun q hq => by
      rcases hsp q hq with rfl | rfl | rfl | rfl | rfl
      exacts [h13, e801, h14, h11, h10])
    (fun q hq => by
      rcases hsp q hq with rfl | rfl | rfl | rfl | rfl
      · exact hl13
      · show 1 ≤ (xs13.drop m).length
        rw [List.length_drop]; omega
      · exact hl14
      · exact hl11
      · exact hl10)
    (fun q hq => by
      rcases hsp q hq with rfl | rfl | rfl | rfl | rfl
      exacts [r13, readsAt_drop r13, r14, r11, r10])
    (fun q hq j hj => by
      rcases hsp q hq with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (hOwn13 j (by change j < 20 at hj; omega))
      · show Own (b13 + m + j) ∨ _
        exact Or.inl (by rw [Nat.add_assoc]; exact hOwn13 _ (by change j < 1 at hj; omega))
      · exact Or.inl (hOwn14 j hj)
      · exact Or.inl (hOwn11 j hj)
      · exact Or.inl (hOwn10 j hj))
    (fun rd hp ho q hq => by
      rcases hsp q hq with rfl | rfl | rfl | rfl | rfl
      exacts [hO13 rd hp ho, readsAt_drop (hO13 rd hp ho), hO14 rd hp ho, hO11 rd hp ho, hO10 rd hp ho])
    (fun x hx => by simp [stC15] at hx)
    (fun x hx => by
      rw [vsC_w15_pure, pureC15, List.mem_singleton] at hx
      subst hx
      exact rc_pureF (by omega) (by norm_num) (show cc - 6 ≤ 3 by omega)
        (hg15 (.rangeCheck (.n 1061) (.n 1062) (.n 1063) (.n 1064) (.n 1059)) (vsC15_mem (by simp [vs15L])))
        (by omega) e1061
        ((show σ (.n 1059) = word 8 0 from hg15 (.const (.n 1059) (word 8 0)) (vsC15_mem (by simp [vs15L]))).trans (wordG (j := 3) (by norm_num))))
    ?_
  -- `link_row_side__L{c}`
  have e772 : σ (.n 772) = ptrAt b772 :=
    (vsVal_retC (rd0 := rd0) (w := w) ha vsC12_eq (.n 772) (by simp)).trans hw772
  have e1066 : σ (.n 1066) = ptrAt (b772 + 1) := by
    rw [good_mulF (hg15 (.mul (.n 1066) (.n 772) (.n 1065)) (vsC15_mem (by simp [vs15L]))) (by omega) (by omega), e772,
      show σ (.n 1065) = word 2 0 from hg15 (.const (.n 1065) (word 2 0)) (vsC15_mem (by simp [vs15L])), show word 2 0 = gen ^ 1 from wordG (j := 1) (by norm_num),
      ptrAt_add]
  have e1068 : σ (.n 1068) = ptrAt qt * word 365917469723852800 0 := by
    rw [good_mulF (hg15 (.mul (.n 1068) (.n 4) (.n 1067)) (vsC15_mem (by simp [vs15L]))) (by omega) (by omega), h4,
      show σ (.n 1067) = word 365917469723852800 0 from hg15 (.const (.n 1067) (word 365917469723852800 0)) (vsC15_mem (by simp [vs15L]))]
  have e773 : σ (.n 773) = w 773 := vsVal_retC (rd0 := rd0) (w := w) ha vsC12_eq (.n 773) (by simp)
  have r16 : ∀ v ∈ [V.n 1071, .n 1072, .n 1073, .n 1074, .n 1075, .n 1076, .n 1077], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC16_eq
  have hargs : (argsOf vsC16s).map σ = [f0, f1, f2, f3, f4, ptrAt (b772 + 1), w 773, ptrAt b15, ptrAt b16, gen ^ n,
      ptrAt qt * word 365917469723852800 0] := by
    show [σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794), σ (.n 1066), σ (.n 773), σ (.n 15), σ (.n 16),
      σ (.n 408), σ (.n 1068)] = _
    rw [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2, e1066, e773, h15, h16, h408, e1068]
  have hrets : (retsOf vsC16s).map σ = [w 1071, w 1072, w 1073, w 1074, w 1075, w 1076, w 1077] := by
    show [σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075), σ (.n 1076), σ (.n 1077)] = _
    rw [r16 (.n 1071) (by simp), r16 (.n 1072) (by simp), r16 (.n 1073) (by simp), r16 (.n 1074) (by simp),
      r16 (.n 1075) (by simp), r16 (.n 1076) (by simp), r16 (.n 1077) (by simp)]
  rw [← hargs, ← hrets] at hc
  refine winsHyp_call_at (g := lrsNames.getD (cc - 6) "")
    ⟨cc - 6, by rw [lrsNames_length]; omega, by rw [e1070, Value.gen_pow_eq_ofK], lrsNames_getElem! _ (by omega)⟩
    hc hRc hPc ?_
  rw [WinsHyp]
  exact hK

end

end
end LeanVM.Guest.B1.VsC
