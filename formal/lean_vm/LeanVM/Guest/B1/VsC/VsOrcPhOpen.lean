/-
  LeanVM.Guest.B1.VsC.VsOrcPhOpen

  `PhOpenHyp` at the honest oracle: `open_stacked__L{sl}`, `check_stack_terminal`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh35

/-!
# `PhOpen` at the honest values

`PhOpenIn`: `PhOpenHyp`'s facts, with `open_stacked__L{sl}`'s call returning its native values
`osRets wE bp bp1 ie` (the WHIR end's target, the two point buffers `bp`, `bp1` in its frame, the inner and residual
values, the cursor past its stream words) and `ret`'s constants equal to them on `3991 … 3996`; `check_stack_terminal`
from the native terminal check (`stackedClaims … = some claims`, the stacked identity on `cstArgsOf`), its pointer
arrays as index arrays `carr`. **`phOpenOk_in`**: `PhOpenOk` from it, `check_stack_terminal` from
`CheckStackTerminalCompleteA`, its region narrowed to the indices.

`bp`, `bp1` and `open_stacked`'s end are its completeness statement's witnesses at the cursor the ring's call
leaves (`OpenStackedCompleteA`'s `∃ bp bp1 e`), so the honest `ret` is chosen from them (`openCall_of`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **`PhOpen`'s honest inputs**, on the honest oracle `vsW rd1 args cur p ret`. -/
structure PhOpenIn (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 rd1 : Reader)
    (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b23 bm : ℕ) (xs23 xm : List E) (sl ic0 qt : ℕ) (a96 h1 h2 : E) (fsv : List E)
    (Ro Do : ℕ → Prop) (Oo Po : Reader → Prop) (Qo : Reader → Tree → Prop) (Bo eo : ℕ) (s0 c pp : ℕ)
    (wE : WhirEnd) (bp bp1 nx : ℕ)
    (layout : Layout) (link : LinkEnd) (chi r qPoint kOut kIn f g x z : List E) (rho lam rm : E)
    (outputs : List ColumnClaim) (keccakSlices : List E) (oodValue v0 v1 : E) (claims : List StackClaim)
    (carr : List (ℕ × ℕ)) : Prop where
  h23 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 23) = ptrAt b23
  hl23 : 1 ≤ xs23.length
  r23 : ReadsAt rd0 (ptrAt b23) xs23
  hO23 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b23) xs23
  hc23 : Own b23 ∨ R b23 ∨ st.D b23
  h1076 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 1076) = ptrAt bm
  hlm : 55 ≤ xm.length
  rm' : ReadsAt rd0 (ptrAt bm) xm
  hOm : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt bm) xm
  hcm : ∀ j < 55, Own (bm + j) ∨ R (bm + j) ∨ st.D (bm + j)
  h16 : 16 ≤ sl
  h30 : sl ≤ 30
  h489 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 489) = gen ^ (sl - 16)
  h96 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 96) = a96
  hfsv : [vsVal rd0 (vsW rd1 args cur p ret) args (.n 3033), vsVal rd0 (vsW rd1 args cur p ret) args (.n 3034),
    vsVal rd0 (vsW rd1 args cur p ret) args (.n 3035), vsVal rd0 (vsW rd1 args cur p ret) args (.n 3036),
    vsVal rd0 (vsW rd1 args cur p ret) args (.n 3037)] = fsv
  h134 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 134) = h1
  h137 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 137) = h2
  h2920 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 2920) = ptrAt ic0
  h4 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 4) = ptrAt qt
  hos : CallAtA fs al cert k (Whir.openName sl)
    (a96 :: fsv ++ [vsOpenTarget (vsVal rd0 (vsW rd1 args cur p ret) args (.n 3810))
      (vsVal rd0 (vsW rd1 args cur p ret) args (.n 3027)) (vsVal rd0 (vsW rd1 args cur p ret) args (.n 779))
      (vsVal rd0 (vsW rd1 args cur p ret) args (.n 2905)) (vsVal rd0 (vsW rd1 args cur p ret) args (.n 2908))
      (vsVal rd0 (vsW rd1 args cur p ret) args (.n 2921)) (xs23.getD 0 0) xm, h1, h2, ptrAt (ic0 + 1),
      ptrAt (qt + 178)])
    (osRets wE bp bp1 (ic0 + 1 + nx)) Ro Do Oo Po Qo Bo
    (allocBase (al (Whir.openName sl)) st.kc) (allocBase (al (Whir.openName sl)) st.kc + Bo) eo
  ro : ∀ j < 6, ∀ σ, ret (3991 + j) σ = (osRets wE bp bp1 (ic0 + 1 + nx)).getD j 0
  hRo : ∀ i, Ro i → (R i ∨ Own i) ∨ st.D i
  hPo : ∀ rd, Pre rd ∧ st.O rd → Po rd
  hc : c ≤ 256 * pp
  hpk : 256 * pp < 2 ^ k
  hie : ic0 + 1 + nx = s0 + c
  h55 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 55) = ptrAt s0
  h42 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 42) = gen ^ pp
  hcl : stackedClaims layout link (publicClaimsPure layout rm v0 v1) outputs kIn keccakSlices f g rho
    (fun y ↦ eqEval z y, oodValue) = some claims
  hsl : layout.stackLog ≤ 30
  hid : ((cstArgsOf (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret)).getD 19 0 +
      stackedBasis claims lam x) * (cstArgsOf (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret)).getD 20 0 =
    (cstArgsOf (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret)).getD 21 0
  hcarr : cstArrays (cstArgsOf (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret)) chi r kOut kIn f g z =
    carr.map fun q => (ptrAt q.1, q.2)
  hfc : ∀ q ∈ carr, q.1 + q.2 ≤ eo
  hcc : ∀ q ∈ carr, ∀ t < q.2, (R (q.1 + t) ∨ Own (q.1 + t)) ∨ (st.D (q.1 + t) ∨ Do (q.1 + t))
  hPc : ∀ rd, Pre rd ∧ (st.O rd ∧ Oo rd) →
    StackCtxAt rd (cstArgsOf (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret)) layout link chi r
      qPoint kOut kIn f g x z rho lam rm outputs

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 rd1 : Reader}
  {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`PhOpen` at the honest values**: `PhOpenOk` from `PhOpenIn`, `check_stack_terminal` from its completeness. -/
theorem phOpenOk_in (hC : CheckStackTerminalCompleteA fs al cert k) (ha : args.length = 6) (hr : CausalRule ret)
    {st : St} {K : St → Prop} {b23 bm : ℕ} {xs23 xm : List E} {sl ic0 qt : ℕ} {a96 h1 h2 : E} {fsv : List E}
    {Ro Do : ℕ → Prop} {Oo Po : Reader → Prop} {Qo : Reader → Tree → Prop} {Bo eo : ℕ} {s0 c pp : ℕ}
    {wE : WhirEnd} {bp bp1 nx : ℕ} {layout : Layout} {link : LinkEnd} {chi r qPoint kOut kIn f g x z : List E}
    {rho lam rm : E} {outputs : List ColumnClaim} {keccakSlices : List E} {oodValue v0 v1 : E}
    {claims : List StackClaim} {carr : List (ℕ × ℕ)}
    (H : PhOpenIn fs al cert k rd0 rd1 args cur p ret Own R Pre st b23 bm xs23 xm sl ic0 qt a96 h1 h2 fsv Ro Do Oo Po
      Qo Bo eo s0 c pp wE bp bp1 nx layout link chi r qPoint kOut kIn f g x z rho lam rm outputs keccakSlices oodValue
      v0 v1 claims carr)
    (hK : ∀ ec : ℕ, st.kc ≤ ec → K ⟨st.a, ec, fun rd => (st.O rd ∧ Oo rd) ∧ True, fun i => (st.D i ∨ Do i) ∨ False,
      st.Qs ++ [Qo, PostQuiet]⟩) :
    PhOpenOk fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  have hl : (osRets wE bp bp1 (ic0 + 1 + nx)).length = 6 := rfl
  have e := vsW_rets (rd1 := rd1) (cur := cur) (p := p) ha hr (i0 := 3991) (cs := osRets wE bp bp1 (ic0 + 1 + nx))
    (fun j hj => by rw [hl] at hj; interval_cases j <;> decide)
    (fun j hj σ => H.ro j (by rw [hl] at hj; exact hj) σ)
  have hrets : osRets wE bp bp1 (ic0 + 1 + nx) =
      [vsW rd1 args cur p ret 3991, vsW rd1 args cur p ret 3992, vsW rd1 args cur p ret 3993,
        vsW rd1 args cur p ret 3994, vsW rd1 args cur p ret 3995, vsW rd1 args cur p ret 3996] := by
    rw [← e, hl]; rfl
  have hos := H.hos
  rw [hrets] at hos
  have h3996 : vsW rd1 args cur p ret 3996 = ptrAt (s0 + c) := by
    have := congrArg (fun l => l.getD 5 0) hrets
    simp only [osRets, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [← this, H.hie]
  obtain ⟨ec, hcs⟩ := hC (cstArgsOf (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret)) layout link
    chi r qPoint kOut kIn f g x z rho lam rm outputs keccakSlices oodValue v0 v1 claims
    (allocBase (al "check_stack_terminal") eo) H.hcl H.hsl H.hid
    (by rw [H.hcarr]; exact ptrsBelow_idx fun q hq => le_trans (H.hfc q hq) (le_allocBase _ _))
  rw [H.hcarr] at hcs
  have hcs := CallAtA.idxR hcs
  obtain ⟨_, _, hoe, _⟩ := id hos
  obtain ⟨_, _, hce, _⟩ := id hcs
  have hke : st.kc ≤ ec := le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) (le_trans hoe
    (le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) hce))))
  refine ⟨b23, bm, xs23, xm, sl, ic0, qt, a96, h1, h2, fsv, Ro, Do, Oo, Po, Qo, Bo, eo, s0, c, pp, _, _, _, _, _, _,
    ec, ⟨H.h23, H.hl23, H.r23, H.hO23, H.hc23, H.h1076, H.hlm, H.rm', H.hOm, H.hcm, H.h16, H.h30, H.h489, H.h96,
    H.hfsv, H.h134, H.h137, H.h2920, H.h4, hos, H.hRo, H.hPo, H.hc, H.hpk, h3996, H.h55, H.h42, hcs, ?_,
    fun rd hrd => H.hPc rd hrd⟩, hK ec hke⟩
  rintro i ⟨q, hq, t, ht, rfl⟩
  exact H.hcc q hq t ht

/-- **`open_stacked`'s call from its completeness**: at the native WHIR run and its queries, at the cursor `kc`,
the point buffers and the end exist. The honest `ret` is chosen from them. -/
theorem openCall_of (hO : ∀ m, m ≤ 14 → OpenStackedCompleteA fs al cert k m) {sl r : ℕ} (h16 : 16 ≤ sl)
    (h30 : sl ≤ 30) {root : Digest} {fsv : List E} {target : E} {ic it : ℕ} {xs : List E}
    {os : List (List Opening)} {wE : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)} {qs : List (ℕ × List ℕ)}
    {Rg : ℕ → Prop} (hr1 : 1 ≤ r) (hr4 : r ≤ 4) (hf : fsv.length = 5) (hsp : ∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp)
    (hrun : RunsWith (whirOpen sl r target) ⟨fsv, []⟩ xs os [(root, stackShape sl r)] wE s' roots')
    (hq : OpenRunQueries sl r root target ⟨fsv, []⟩ xs os qs)
    (hxs : ∀ i < xs.length, Rg (ic + i)) (hit : ∀ n < 2 ^ winTabBits, Rg (it + n)) (kc : ℕ) :
    ∃ bp bp1 e : ℕ, CallAtA fs al cert k (Whir.openName sl)
      (rateSel r :: fsv ++ [target, (digestHalves root).1, (digestHalves root).2, ptrAt ic, ptrAt it])
      (osRets wE bp bp1 (ic + xs.length)) Rg
      (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
      (fun rd => ReadsAt rd (ptrAt bp) (wE.point ++ List.replicate (pointCap - sl) 0) ∧
        ReadsAt rd (ptrAt bp1) (wE.point.map (1 + ·) ++ List.replicate (pointCap - sl) 1))
      (fun rd => ReadsAt rd (ptrAt ic) xs ∧ WinTabs rd (ptrAt it))
      (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.merkleHints true qs os) ∧
        t.Every (ExactAt coreProgram rd))
      (fs (Whir.openName sl)) (allocBase (al (Whir.openName sl)) kc)
      (allocBase (al (Whir.openName sl)) kc + fs (Whir.openName sl)) e := by
  have hsl : minOpenLog + (sl - 16) = sl := by show 16 + (sl - 16) = sl; omega
  have h := hO (sl - 16) (by omega) r root fsv target ic it xs os wE s' roots' qs Rg hr1 hr4 hf hsp
    (by rw [hsl]; exact hrun) (by rw [hsl]; exact hq) hxs hit (allocBase (al (Whir.openName sl)) kc)
    (allocBase (al (Whir.openName sl)) kc + fs (Whir.openName sl)) (le_of_eq (by rw [hsl]))
  rw [hsl] at h
  exact h

end

end
end LeanVM.Guest.B1.VsC
