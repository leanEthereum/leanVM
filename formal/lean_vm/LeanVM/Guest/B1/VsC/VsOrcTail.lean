/-
  LeanVM.Guest.B1.VsC.VsOrcTail

  `wC`'s windows from `35` on (the siblings' phases) grouped by phase, as `VsOrc`'s phases are.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrc
public import LeanVM.Guest.B1.VsC.VsPh35
public import LeanVM.Guest.B1.VsC.VsPhOpen

/-!
# `wC`'s tail by phase

`Ph35Hyp` (`vsPh35_wins`: `verify_keccak`, the ring's run, `ring_switch_target`), `PhOpenHyp`
(`vsPhOpen_wins`: `open_stacked__L{sl}`, `check_stack_terminal`), `PhExportHyp` (`vsPhExport_wins`: the
export into `.n 5`), each the lemma's hypotheses but its continuation, and `PhNOk` their continuation form.
`TailOk st K` chains them; `tailOk_wins` gives `WinsHyp … (wC.drop 35) st K`, and `WCOkT` is `WCOk` with
the tail by phase (`WCOkT.wcOk`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier LeanVM.Protocol
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **Ph35's hypotheses**: `wC`'s windows `35 ..< 38` (`vsPh35_wins`), but its continuation. -/
structure Ph35Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader)
    (w : ℕ → E) (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (qt b15 b20 b21 bm cs τ : ℕ) (nz : E) (xs21 xsm : List E) (Rv Dv : ℕ → Prop) (Ov Pv : Reader → Prop)
    (Qv : Reader → Tree → Prop) (Bv ev : ℕ) (Rr Dr : ℕ → Prop) (Ort Pr : Reader → Prop)
    (Qr : Reader → Tree → Prop) (Br er : ℕ) : Prop where
  h120 : vsVal rd0 w args (.n 120) = gen ^ τ
  h15 : vsVal rd0 w args (.n 15) = ptrAt b15
  h20 : vsVal rd0 w args (.n 20) = ptrAt b20
  h21 : vsVal rd0 w args (.n 21) = ptrAt b21
  h4 : vsVal rd0 w args (.n 4) = ptrAt qt
  hv : CallAtA fs al cert k "verify_keccak"
    [w 1288, w 1289, w 1290, w 1291, w 1292, w 1076 * word 21299200 0, gen ^ τ, ptrAt b15,
      w 1076 * word 36028797018963968 0, ptrAt b20, ptrAt b21, ptrAt qt * word 365917469723852800 0]
    [w 2915, w 2916, w 2917, w 2918, w 2919, w 2920, w 2921] Rv Dv Ov Pv Qv Bv
    (allocBase (al "verify_keccak") st.kc) (allocBase (al "verify_keccak") st.kc + Bv) ev
  hRv : ∀ i, Rv i → (R i ∨ Own i) ∨ st.D i
  hPv : ∀ rd, Pre rd ∧ st.O rd → Pv rd
  hw2920 : w 2920 = ptrAt cs
  r0cs : ReadsAt rd0 (ptrAt cs) [nz]
  hOcs : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt cs) [nz]
  hOwncs : Own cs
  hl0 : LowDef k rd0
  rt : ExpWinTab rd0 (ptrAt qt)
  hPt : ∀ rd, Pre rd → ExpWinTab rd (ptrAt qt)
  hRq : ∀ j < 2 ^ 11, R (qt + (j + 178))
  hwin : ∀ j ≤ gcW 13, w (2943 + j) = gcWin 13 (vsVal rd0 w args (.n 2931)) j
  hlow : ((vsVal rd0 w args (.n 2931)).limb 0).lane.toNat % 2 ^ 13 = 0
  hw3039 : w 3039 = ptrAt st.a
  hw3040 : w 3040 = ptrAt (st.a + 16)
  hw3553 : w 3553 = ptrAt (st.a + 80)
  hOwn : ∀ j < 144, Own (st.a + j)
  r39 : ReadsAt rd0 (ptrAt st.a) (mcW (vsVal rd0 w args))
  hO39 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt st.a) (mcW (vsVal rd0 w args))
  r40 : ReadsAt rd0 (ptrAt (st.a + 16)) (mcRc (vsVal rd0 w args))
  hO40 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt (st.a + 16)) (mcRc (vsVal rd0 w args))
  hl21 : 64 ≤ xs21.length
  r21 : ReadsAt rd0 (ptrAt b21) xs21
  hO21 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b21) xs21
  hOwn21 : ∀ j < 64, Own (b21 + j)
  hwm : w 1076 = ptrAt bm
  hlm : 144 ≤ xsm.length
  rm : ReadsAt rd0 (ptrAt bm) xsm
  hOm : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt bm) xsm
  hcm : ∀ j < 144, (R (bm + j) ∨ Own (bm + j)) ∨ st.D (bm + j)
  r53 : ReadsAt rd0 (ptrAt (st.a + 80)) (rsW xs21 xsm (vsVal rd0 w args (.n 3026)))
  hO53 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt (st.a + 80)) (rsW xs21 xsm (vsVal rd0 w args (.n 3026)))
  hr : CallAtA fs al cert k "ring_switch_target" [ptrAt (st.a + 80), ptrAt st.a] [w 3810] Rr Dr Ort Pr Qr Br
    (allocBase (al "ring_switch_target") ev) (allocBase (al "ring_switch_target") ev + Br) er
  hRr : ∀ i, Rr i → (R i ∨ Own i) ∨ (st.D i ∨ Dv i)
  hPr : ∀ rd, Pre rd ∧ (st.O rd ∧ Ov rd) → Pr rd

/-- **Ph35 in continuation form.** -/
def Ph35Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (qt b15 b20 b21 bm cs τ : ℕ) (nz : E) (xs21 xsm : List E) (Rv Dv : ℕ → Prop) (Ov Pv : Reader → Prop)
    (Qv : Reader → Tree → Prop) (Bv ev : ℕ) (Rr Dr : ℕ → Prop) (Ort Pr : Reader → Prop)
    (Qr : Reader → Tree → Prop) (Br er : ℕ),
    Ph35Hyp fs al cert k rd0 w args Own R Pre st qt b15 b20 b21 bm cs τ nz xs21 xsm Rv Dv Ov Pv Qv Bv ev
      Rr Dr Ort Pr Qr Br er ∧
    K ⟨st.a + 144, er, fun rd => (st.O rd ∧ Ov rd) ∧ Ort rd, fun i => (st.D i ∨ Dv i) ∨ Dr i, st.Qs ++ [Qv, Qr]⟩

theorem ph35Ok_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph35Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w35, vsC_w36, vsC_w37] st K := by
  obtain ⟨qt, b15, b20, b21, bm, cs, τ, nz, xs21, xsm, Rv, Dv, Ov, Pv, Qv, Bv, ev, Rr, Dr, Ort, Pr, Qr, Br, er,
    H, hK⟩ := H
  exact vsPh35_wins hk ha H.h120 H.h15 H.h20 H.h21 H.h4 H.hv H.hRv H.hPv H.hw2920 H.r0cs H.hOcs H.hOwncs H.hl0
    H.rt H.hPt H.hRq H.hwin H.hlow H.hw3039 H.hw3040 H.hw3553 H.hOwn H.r39 H.hO39 H.r40 H.hO40 H.hl21 H.r21
    H.hO21 H.hOwn21 H.hwm H.hlm H.rm H.hOm H.hcm H.r53 H.hO53 H.hr H.hRr H.hPr hK

theorem Ph35Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph35Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph35Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨qt, b15, b20, b21, bm, cs, τ, nz, xs21, xsm, Rv, Dv, Ov, Pv, Qv, Bv, ev, Rr, Dr, Ort, Pr, Qr, Br, er,
    H, hK⟩ := H
  exact ⟨qt, b15, b20, b21, bm, cs, τ, nz, xs21, xsm, Rv, Dv, Ov, Pv, Qv, Bv, ev, Rr, Dr, Ort, Pr, Qr, Br, er,
    H, hm _ hK⟩

/-- **PhOpen's hypotheses**: `wC`'s windows `38 ..< 42` (`vsPhOpen_wins`), but its continuation. -/
structure PhOpenHyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader)
    (w : ℕ → E) (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b23 bm : ℕ) (xs23 xm : List E) (sl ic0 qt : ℕ) (a96 h1 h2 : E) (fsv : List E)
    (Ro Do : ℕ → Prop) (Oo Po : Reader → Prop) (Qo : Reader → Tree → Prop) (Bo eo : ℕ) (s0 c p : ℕ)
    (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ) : Prop where
  h23 : vsVal rd0 w args (.n 23) = ptrAt b23
  hl23 : 1 ≤ xs23.length
  r23 : ReadsAt rd0 (ptrAt b23) xs23
  hO23 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b23) xs23
  hc23 : Own b23 ∨ R b23 ∨ st.D b23
  h1076 : vsVal rd0 w args (.n 1076) = ptrAt bm
  hlm : 55 ≤ xm.length
  rm : ReadsAt rd0 (ptrAt bm) xm
  hOm : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt bm) xm
  hcm : ∀ j < 55, Own (bm + j) ∨ R (bm + j) ∨ st.D (bm + j)
  h16 : 16 ≤ sl
  h30 : sl ≤ 30
  h489 : vsVal rd0 w args (.n 489) = gen ^ (sl - 16)
  h96 : vsVal rd0 w args (.n 96) = a96
  hfsv : [vsVal rd0 w args (.n 3033), vsVal rd0 w args (.n 3034), vsVal rd0 w args (.n 3035),
    vsVal rd0 w args (.n 3036), vsVal rd0 w args (.n 3037)] = fsv
  h134 : vsVal rd0 w args (.n 134) = h1
  h137 : vsVal rd0 w args (.n 137) = h2
  h2920 : vsVal rd0 w args (.n 2920) = ptrAt ic0
  h4 : vsVal rd0 w args (.n 4) = ptrAt qt
  hos : CallAtA fs al cert k (Whir.openName sl)
    (a96 :: fsv ++ [vsOpenTarget (vsVal rd0 w args (.n 3810)) (vsVal rd0 w args (.n 3027))
      (vsVal rd0 w args (.n 779)) (vsVal rd0 w args (.n 2905)) (vsVal rd0 w args (.n 2908))
      (vsVal rd0 w args (.n 2921)) (xs23.getD 0 0) xm, h1, h2, ptrAt (ic0 + 1), ptrAt (qt + 178)])
    [w 3991, w 3992, w 3993, w 3994, w 3995, w 3996] Ro Do Oo Po Qo Bo
    (allocBase (al (Whir.openName sl)) st.kc) (allocBase (al (Whir.openName sl)) st.kc + Bo) eo
  hRo : ∀ i, Ro i → (R i ∨ Own i) ∨ st.D i
  hPo : ∀ rd, Pre rd ∧ st.O rd → Po rd
  hc : c ≤ 256 * p
  hpk : 256 * p < 2 ^ k
  hw3996 : w 3996 = ptrAt (s0 + c)
  h55 : vsVal rd0 w args (.n 55) = ptrAt s0
  h42 : vsVal rd0 w args (.n 42) = gen ^ p
  hcs : CallAtA fs al cert k "check_stack_terminal" (cstArgsOf (vsVal rd0 w args) w) [] Rc Dc Oc Pc Qc Bc
    (allocBase (al "check_stack_terminal") eo) (allocBase (al "check_stack_terminal") eo + Bc) ec
  hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ (st.D i ∨ Do i)
  hPc : ∀ rd, Pre rd ∧ (st.O rd ∧ Oo rd) → Pc rd

/-- **PhOpen in continuation form.** -/
def PhOpenOk (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (b23 bm : ℕ) (xs23 xm : List E) (sl ic0 qt : ℕ) (a96 h1 h2 : E) (fsv : List E)
    (Ro Do : ℕ → Prop) (Oo Po : Reader → Prop) (Qo : Reader → Tree → Prop) (Bo eo : ℕ) (s0 c p : ℕ)
    (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ),
    PhOpenHyp fs al cert k rd0 w args Own R Pre st b23 bm xs23 xm sl ic0 qt a96 h1 h2 fsv Ro Do Oo Po Qo Bo eo
      s0 c p Rc Dc Oc Pc Qc Bc ec ∧
    K ⟨st.a, ec, fun rd => (st.O rd ∧ Oo rd) ∧ Oc rd, fun i => (st.D i ∨ Do i) ∨ Dc i, st.Qs ++ [Qo, Qc]⟩

theorem phOpenOk_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : PhOpenOk fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w38, vsC_w39, vsC_w40, vsC_w41] st K := by
  obtain ⟨b23, bm, xs23, xm, sl, ic0, qt, a96, h1, h2, fsv, Ro, Do, Oo, Po, Qo, Bo, eo, s0, c, p, Rc, Dc, Oc, Pc,
    Qc, Bc, ec, H, hK⟩ := H
  exact vsPhOpen_wins ha H.h23 H.hl23 H.r23 H.hO23 H.hc23 H.h1076 H.hlm H.rm H.hOm H.hcm H.h16 H.h30 H.h489
    H.h96 H.hfsv H.h134 H.h137 H.h2920 H.h4 H.hos H.hRo H.hPo H.hc H.hpk H.hw3996 H.h55 H.h42 H.hcs H.hRc H.hPc hK

theorem PhOpenOk.mono {st : St} {K K' : St → Prop}
    (H : PhOpenOk fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    PhOpenOk fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨b23, bm, xs23, xm, sl, ic0, qt, a96, h1, h2, fsv, Ro, Do, Oo, Po, Qo, Bo, eo, s0, c, p, Rc, Dc, Oc, Pc,
    Qc, Bc, ec, H, hK⟩ := H
  exact ⟨b23, bm, xs23, xm, sl, ic0, qt, a96, h1, h2, fsv, Ro, Do, Oo, Po, Qo, Bo, eo, s0, c, p, Rc, Dc, Oc, Pc,
    Qc, Bc, ec, H, hm _ hK⟩

/-- **PhExport's hypotheses**: `wC`'s window `42` (`vsPhExport_wins`), but its continuation. -/
structure PhExportHyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader)
    (w : ℕ → E) (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b5 b12 b14 : ℕ) (xs5 xs12 xs14 : List E) : Prop where
  h12 : vsVal rd0 w args (.n 12) = ptrAt b12
  hl12 : 19 ≤ xs12.length
  r12 : ReadsAt rd0 (ptrAt b12) xs12
  hO12 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b12) xs12
  hc12 : ∀ j < 19, Own (b12 + j) ∨ R (b12 + j) ∨ st.D (b12 + j)
  h14 : vsVal rd0 w args (.n 14) = ptrAt b14
  hl14 : 36 ≤ xs14.length
  r14 : ReadsAt rd0 (ptrAt b14) xs14
  hO14 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b14) xs14
  hc14 : ∀ j < 36, Own (b14 + j) ∨ R (b14 + j) ∨ st.D (b14 + j)
  h5 : vsVal rd0 w args (.n 5) = ptrAt b5
  hx5 : xs5 = xs12.take 19 ++ xs14.take 36
  r5 : ReadsAt rd0 (ptrAt b5) xs5
  hO5 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b5) xs5
  hc5 : ∀ j < 55, Own (b5 + j) ∨ R (b5 + j) ∨ st.D (b5 + j)

/-- **PhExport in continuation form.** -/
def PhExportOk (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader)
    (w : ℕ → E) (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (b5 b12 b14 : ℕ) (xs5 xs12 xs14 : List E),
    PhExportHyp fs al cert k rd0 w args Own R Pre st b5 b12 b14 xs5 xs12 xs14 ∧ K st

theorem phExportOk_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : PhExportOk fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w42] st K := by
  obtain ⟨b5, b12, b14, xs5, xs12, xs14, H, hK⟩ := H
  exact vsPhExport_wins ha H.h12 H.hl12 H.r12 H.hO12 H.hc12 H.h14 H.hl14 H.r14 H.hO14 H.hc14 H.h5 H.hx5 H.r5
    H.hO5 H.hc5 hK

/-- **`wC`'s tail by phase.** -/
def TailOk (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  Ph35Ok fs al cert k rd0 w args Own R Pre st fun s =>
  PhOpenOk fs al cert k rd0 w args Own R Pre s fun s =>
  PhExportOk fs al cert k rd0 w args Own R Pre s K

theorem wC_drop35 : wC.drop 35 = [vsC_w35, vsC_w36, vsC_w37] ++ ([vsC_w38, vsC_w39, vsC_w40, vsC_w41] ++
    [vsC_w42]) := rfl

theorem tailOk_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : TailOk fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre (wC.drop 35) st K := by
  rw [wC_drop35, winsHyp_append]
  refine ph35Ok_wins hk ha (Ph35Ok.mono H fun _ H => ?_)
  rw [winsHyp_append]
  exact phOpenOk_wins ha (PhOpenOk.mono H fun _ H => phExportOk_wins ha H)

/-- **`wC`'s windows' hypotheses, phase by phase, the tail too.** -/
def WCOkT (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  Ph4Ok fs al cert k rd0 w args Own R Pre st fun s4 =>
  Ph5Ok fs al cert k rd0 w args Own R Pre s4 fun s5 =>
  Ph6Ok fs al cert k rd0 w args Own R Pre s5 fun s6 =>
  Ph7Ok fs al cert k rd0 w args Own R Pre s6 fun s7 =>
  Ph8Ok fs al cert k rd0 w args Own R Pre s7 fun s8 =>
  Ph9Ok fs al cert k rd0 w args Own R Pre s8 fun s9 =>
  Ph10Ok fs al cert k rd0 w args Own R Pre s9 fun s10 =>
  Ph11Ok fs al cert k rd0 w args Own R Pre s10 fun s11 =>
  Ph1213Ok fs al cert k rd0 w args Own R Pre s11 fun s =>
  TailOk fs al cert k rd0 w args Own R Pre s K

theorem WCOkT.wcOk (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : WCOkT fs al cert k rd0 w args Own R Pre st K) : WCOk fs al cert k rd0 w args Own R Pre st K :=
  Ph4Ok.mono H fun _ H => Ph5Ok.mono H fun _ H => Ph6Ok.mono H fun _ H => Ph7Ok.mono H fun _ H =>
    Ph8Ok.mono H fun _ H => Ph9Ok.mono H fun _ H => Ph10Ok.mono H fun _ H => Ph11Ok.mono H fun _ H =>
      Ph1213Ok.mono H fun _ H => tailOk_wins hk ha H

end

end
end LeanVM.Guest.B1.VsC
