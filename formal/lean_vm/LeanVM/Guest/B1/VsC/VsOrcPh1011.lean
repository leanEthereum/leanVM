/-
  LeanVM.Guest.B1.VsC.VsOrcPh1011

  `Ph10Hyp` and `Ph11Hyp` at the honest oracle: the rows' eq tensor, `one_plus_suffixes`, `packed_message`,
  the first `table_point`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh9

/-!
# `Ph10` and `Ph11` at the honest values

`Ph10In`: the rows' point `.n 16` (its first six words `rs`), the eq buffer `.n 17` holding `eqLevels rs 6`,
`one_plus_suffixes`' and `packed_message`'s inputs, the hint `w 1286` and `packed_message`'s returns as
`ret`'s constants. `Ph11In`: the first `table_point`'s inputs, its returns as `ret`'s constants.
**`ph10Ok_in`**, **`ph11Ok_in`**.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **`Ph10`'s honest inputs**, on the honest oracle `vsW rd1 args cur p ret`. -/
structure Ph10In (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 rd1 : Reader)
    (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b15 b16 b17 b18 bm n : ℕ) (xs16 as15 xm : List E) : Prop where
  B16 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O Own 16 b16 6 xs16
  B17 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O Own 17 b17 126 (eqLevels (xs16.take 6) 6)
  h408 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 408) = gen ^ n
  hn : n ≤ 40
  h18 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 18) = ptrAt b18
  h15 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 15) = ptrAt b15
  hl15 : as15.length = n
  hO18 : ∀ j < n + 1, Own (b18 + j)
  hO15 : ∀ j < n, Own (b15 + j)
  hPops : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt b15) as15 ∧
    ReadsAt rd (ptrAt b18) ((List.range (n + 1)).map (belowE as15))
  r1286 : ∀ σ, ret 1286 σ = 0
  hwm : vsW rd1 args cur p ret 1076 = ptrAt bm
  hxm : xm.length = 144
  hcm : ∀ j < 144, (R (bm + j) ∨ Own (bm + j)) ∨ st.D (bm + j)
  hPpm : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt bm) xm
  rpm : ∀ j < 6, ∀ σ, ret (1287 + j) σ =
    (pmRets xm ((List.range 5).map fun i => vsW rd1 args cur p ret (1071 + i))).getD j 0
  hpm6 : (pmRets xm ((List.range 5).map fun i => vsW rd1 args cur p ret (1071 + i))).length = 6

/-- **`Ph11`'s honest inputs**, on the honest oracle `vsW rd1 args cur p ret`. -/
structure Ph11In (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 rd1 : Reader)
    (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b7 b10 b15 h : ℕ) (xs10 ts xs cs : List E) (top : E) : Prop where
  B10 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O Own 10 b10 1 xs10
  h115 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 115) = gen ^ h
  hh : h ≤ 24
  h15 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 15) = ptrAt b15
  h7 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 7) = ptrAt b7
  hts : ts.length = h
  hxs : xs.length = h
  hcs : cs.length = h
  hOt : ∀ j < h, Own (b10 + 89 + j)
  hO15 : ∀ j < h, Own (b15 + j)
  hO7 : ∀ j < h + 1, Own (b7 + j)
  hPtp : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (b10 + 89)) ts ∧ ReadsAt rd (ptrAt b15) xs ∧
    ReadsAt rd (ptrAt b7) (cs ++ [top])
  r1296 : ∀ σ, ret 1296 σ = xs10.getD 0 0 * tpTotalG ts xs cs top h
  r1297 : ∀ σ, ret 1297 σ = 1 + (1 + top) * tpPad cs xs
  r1298 : ∀ σ, ret 1298 σ = tpFullAt ts xs h

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 rd1 : Reader}
  {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`Ph10` at the honest values.** -/
theorem ph10Ok_in (ha : args.length = 6) (hr : CausalRule ret) {st : St} {K : St → Prop}
    {b15 b16 b17 b18 bm n : ℕ} {xs16 as15 xm : List E}
    (H : Ph10In fs al cert k rd0 rd1 args cur p ret Own R Pre st b15 b16 b17 b18 bm n xs16 as15 xm)
    (hK : K ⟨st.a, leafEnd fs al "packed_message__L144" (leafEnd fs al (opsNames.getD n "") st.kc), st.O, st.D,
      st.Qs ++ [PostQuiet, PostQuiet]⟩) :
    Ph10Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  have hl16 := H.B16.len
  have hrs : (xs16.take 6).length = 6 := by simp; omega
  have e := vsW_rets (rd1 := rd1) (cur := cur) (p := p) ha hr (i0 := 1287)
    (cs := pmRets xm ((List.range 5).map fun i => vsW rd1 args cur p ret (1071 + i)))
    (fun j hj => by rw [H.hpm6] at hj; interval_cases j <;> decide)
    (fun j hj σ => H.rpm j (by rw [H.hpm6] at hj; exact hj) σ)
  rw [H.hpm6] at e
  refine ⟨b15, b16, b17, b18, bm, n, xs16, eqLevels (xs16.take 6) 6, xs16.take 6, as15, xm, ⟨H.B16.ptr, H.B16.len,
    H.B16.r0, H.B16.rO, H.B16.cell, hrs, fun t ht => ?_, H.B17.ptr, H.B17.len, H.B17.r0, H.B17.rO, H.B17.cell,
    eqLevels_lev (by omega), H.h408, H.hn, H.h18, H.h15, H.hl15, H.hO18, H.hO15, H.hPops,
    vsW_retC ha hr (by decide) H.r1286, H.hwm, H.hxm, H.hcm, H.hPpm, ?_⟩, hK⟩
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem?_eq_getElem (by omega)]
  · have h5 : (List.range 5).map (fun i => vsW rd1 args cur p ret (1071 + i)) =
        [vsW rd1 args cur p ret 1071, vsW rd1 args cur p ret 1072, vsW rd1 args cur p ret 1073, vsW rd1 args cur p ret 1074, vsW rd1 args cur p ret 1075] := by
      simp [List.range_succ]
    have h6 : (List.range 6).map (fun j => vsW rd1 args cur p ret (1287 + j)) =
        [vsW rd1 args cur p ret 1287, vsW rd1 args cur p ret 1288, vsW rd1 args cur p ret 1289, vsW rd1 args cur p ret 1290, vsW rd1 args cur p ret 1291, vsW rd1 args cur p ret 1292] := by
      simp [List.range_succ]
    rw [h5, h6, pmRets] at e
    rw [← e]

/-- **`Ph11` at the honest values.** -/
theorem ph11Ok_in (ha : args.length = 6) (hr : CausalRule ret) {st : St} {K : St → Prop}
    {b7 b10 b15 h : ℕ} {xs10 ts xs cs : List E} {top : E}
    (H : Ph11In fs al cert k rd0 rd1 args cur p ret Own R Pre st b7 b10 b15 h xs10 ts xs cs top)
    (hK : K ⟨st.a, leafEnd fs al (tpNames.getD h "") st.kc, st.O, st.D, st.Qs ++ [PostQuiet]⟩) :
    Ph11Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K :=
  ⟨b7, b10, b15, h, xs10, ts, xs, cs, xs10.getD 0 0, top, ⟨H.B10.ptr, H.B10.len, H.B10.r0, H.B10.rO,
    H.B10.cell 0 (by omega), H.B10.getD (by omega), H.h115, H.hh, H.h15, H.h7, H.hts, H.hxs, H.hcs, H.hOt, H.hO15,
    H.hO7, H.hPtp, ⟨vsW_retC ha hr (by decide) H.r1296, vsW_retC ha hr (by decide) H.r1297,
    vsW_retC ha hr (by decide) H.r1298⟩⟩, hK⟩

end

end
end LeanVM.Guest.B1.VsC
