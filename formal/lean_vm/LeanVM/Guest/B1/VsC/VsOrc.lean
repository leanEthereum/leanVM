/-
  LeanVM.Guest.B1.VsC.VsOrc

  `verify_sub`'s windows' hypotheses grouped by phase: the skeleton the honest oracle discharges.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh13

/-!
# `verify_sub`'s windows by phase

`VsHyp` (the windows' hypotheses, `VsWins.lean`) composed from the phase lemmas (`vsFront_wins`, `vsPh4_wins`
… `vsPh11_wins`, `vsPh12_13_wins`) by `winsHyp_append`. Each phase's hypotheses but its continuation are one
structure (`FrontHyp`, `Ph4Hyp` … `Ph11Hyp`, `Ph1213Hyp`), parametrized by the state it starts from and the
values it names, so the phases are discharged separately. `PhNOk st K` (`∃` values, the structure and `K` at
the phase's end state) chains them in continuation form: `WCOk` is `wC`'s phases, then the siblings' tail
`WinsHyp … (wC.drop 35) s K` (`verify_keccak` on) as it stands. A non-leaf callee's end `ec` is one of the
values, so a proof of `VsOrc` obtains the callees' ends in order, phase by phase, before it names the next
phase's values. `vsHyp_of_orc` gives `VsHyp`, `vsWinHyp_of_orc` gives `VsWinHyp` from `VsOrc`: for every
accepted child and placement, an evaluation memory, an oracle and the node's words with `WordsInA` and the
phases' hypotheses from `vsSt0`, ending in `vsPostA`'s condition `vsKEnd`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **Front's hypotheses**: `wA` to the pointer width's branch (`vsFront_wins`), but its continuation. -/
structure FrontHyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (p r m n wd b6 b7 b8 b9 qt : ℕ) (flag f4 : E) (ws : List E) (h Rr : ℕ → ℕ) : Prop where
  hp1 : 1 ≤ p
  hp : p ≤ 32
  hws : ws.length = 256 * p
  hw7r : ws.getD 7 0 = eOfNat r
  hw0m : ws.getD 0 0 = eOfNat m
  hws56 : (ws.drop 1).take 6 = rowsW Rr
  hr1 : 1 ≤ r
  hr4 : r ≤ 4
  hm1 : 1 ≤ m
  h24 : ∀ t < 6, h t ≤ 24
  hR : ∀ t < 6, Rr t ≤ 2 ^ h t
  hl : ∀ t < 5, h t = 0 ∨ 2 ^ (h t - 1) < Rr t
  h9 : 9 ≤ h 5
  hl5 : h 5 ≠ 9 → 2 ^ (h 5 - 1) < Rr 5
  hht : ∀ t < 6, h t ≤ n
  hn : ∃ t < 6, h t = n
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  hmw : m ≤ wd
  hN : Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5 < 2 ^ wd
  hflag : (flag = 1 ∧ 2 ^ (wd - 1) ≤ Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5) ∨ (flag = 0 ∧ (wd = m ∨ wd = 19))
  hw42 : w 42 = gen ^ p
  hwA : [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55].map w = (bases st.a (vsSz0 ++ [256 * p])).map (fun b => ofK (addressOfIndex b))
  hw6 : w 6 = ptrAt b6
  hw7 : w 7 = ptrAt b7
  hw8 : w 8 = ptrAt b8
  hw9 : w 9 = ptrAt b9
  hw55 : w 55 = ptrAt (st.a + 824)
  hw56 : w 56 = ptrAt (st.a + (824 + 256 * p))
  hw112 : w 112 = ptrAt (st.a + (824 + 256 * p) + 6)
  hw94 : w 94 = gen ^ r
  hw101 : w 101 = gen ^ m
  hret : ∀ t < 6, w (tsRet t) = gen ^ Rr t ∧ w (tsRet t + 1) = tsLeadW (Rr t) (h t) ∧ w (tsRet t + 2) = tsRestW (Rr t) (h t)
  h4 : vsVal rd0 w args (.n 4) = ptrAt qt
  r0 : FrontReads rd0 st.a p ws b6 b7 b8 b9 m h Rr n wd flag f4
  rq : ExpTables rd0 (ptrAt qt)
  hO : ∀ rd, st.O rd → FrontReads rd st.a p ws b6 b7 b8 b9 m h Rr n wd flag f4
  hOwn : ∀ i, st.a + 824 ≤ i → i < st.a + 824 + 256 * p + 14 → Own i
  hO6 : ∀ j < 6, Own (b6 + j)
  hO7 : ∀ j < 156, Own (b7 + j)
  hO8 : ∀ j < 24, Own (b8 + j)
  hO9 : ∀ j < 4, Own (b9 + j)
  hRq : ∀ j < 178, R (qt + j)
  hPre : ∀ rd, Pre rd → ExpTables rd (ptrAt qt)

/-- **Front in continuation form**: its hypotheses at some values, the continuation at its end. -/
def FrontOk (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (KC : St → Prop) : Prop :=
  ∃ (p r m n wd b6 b7 b8 b9 qt : ℕ) (flag f4 : E) (ws : List E) (h Rr : ℕ → ℕ),
    FrontHyp fs al cert k rd0 w args Own R Pre st p r m n wd b6 b7 b8 b9 qt flag f4 ws h Rr ∧
    (flag = 1 → KC ⟨st.a + (824 + 256 * p) + 14, leafEnd fs al "assert_small_g_power" (leafEnd fs al "assert_small_g_power" (frontKc fs al p h st.kc)), st.O, st.D, st.Qs ++ hsQ ws p :: List.replicate 10 PostQuiet⟩) ∧ (flag = 0 → KC ⟨st.a + (824 + 256 * p) + 14, leafEnd fs al "assert_small_g_power" (frontKc fs al p h st.kc), st.O, st.D, st.Qs ++ hsQ ws p :: List.replicate 9 PostQuiet⟩)

theorem frontOk_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {KC : St → Prop}
    (H : FrontOk fs al cert k rd0 w args Own R Pre st KC) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wA st (fun s1 =>
      IteHyp fs al cert k (vsVal rd0 w args) w Own R Pre (.n 234) [] wI1 s1 fun s2 =>
        WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wB s2 fun s3 =>
          IteHyp fs al cert k (vsVal rd0 w args) w Own R Pre (.n 471) wI2z wI2n s3 KC) := by
  obtain ⟨p, r, m, n, wd, b6, b7, b8, b9, qt, flag, f4, ws, h, Rr, H, hKz, hKn⟩ := H
  exact vsFront_wins (by omega) ha ws h Rr H.hp1 H.hp H.hws H.hw7r H.hw0m H.hws56 H.hr1 H.hr4 H.hm1 H.h24 H.hR H.hl H.h9 H.hl5 H.hht H.hn H.hw19 H.hw24 H.hmw H.hN H.hflag H.hw42 H.hwA H.hw6 H.hw7 H.hw8 H.hw9 H.hw55 H.hw56 H.hw112 H.hw94 H.hw101 H.hret H.h4 H.r0 H.rq H.hO H.hOwn H.hO6 H.hO7 H.hO8 H.hO9 H.hRq H.hPre hKz hKn

theorem FrontOk.mono {st : St} {KC KC' : St → Prop}
    (H : FrontOk fs al cert k rd0 w args Own R Pre st KC) (hm : ∀ s, KC s → KC' s) :
    FrontOk fs al cert k rd0 w args Own R Pre st KC' := by
  obtain ⟨p, r, m, n, wd, b6, b7, b8, b9, qt, flag, f4, ws, h, Rr, H, hKz, hKn⟩ := H
  exact ⟨p, r, m, n, wd, b6, b7, b8, b9, qt, flag, f4, ws, h, Rr, H, fun hf => hm _ (hKz hf), fun hf => hm _ (hKn hf)⟩

/-- **Ph4's hypotheses**: `wC`'s windows `0 ..< 3`: `chunk_d`, `certify_stack` at its end `ec` (`vsPh4_wins`), but its continuation. -/
structure Ph4Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (wd : ℕ) (a0 a1 r0 r1 r2 : E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (ec : ℕ) : Prop where
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  h409 : vsVal rd0 w args (.n 409) = gen ^ wd
  hw484 : w 484 = gen ^ chunkCount wd
  h112 : vsVal rd0 w args (.n 112) = a0
  h4 : vsVal rd0 w args (.n 4) = a1
  hw485 : w 485 = r0
  hw486 : w 486 = r1
  hw487 : w 487 = r2
  hc : CallAtA fs al cert k "certify_stack" [a0, a1] [r0, r1, r2] Rc Dc Oc Pc Qc (fs "certify_stack") (allocBase (al "certify_stack") (leafEnd fs al (cdNames.getD (wd - 19) "") st.kc)) (allocBase (al "certify_stack") (leafEnd fs al (cdNames.getD (wd - 19) "") st.kc) + fs "certify_stack") ec
  hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i
  hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd

/-- **Ph4 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph4Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (wd : ℕ) (a0 a1 r0 r1 r2 : E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (ec : ℕ),
    Ph4Hyp fs al cert k rd0 w args Own R Pre st wd a0 a1 r0 r1 r2 Rc Dc Oc Pc Qc ec ∧
    (K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [PostQuiet, Qc]⟩)

theorem ph4Ok_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph4Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w0, vsC_w1, vsC_w2] st K := by
  obtain ⟨wd, a0, a1, r0, r1, r2, Rc, Dc, Oc, Pc, Qc, ec, H, hK⟩ := H
  exact vsPh4_wins ha H.hw19 H.hw24 H.h409 H.hw484 H.h112 H.h4 H.hw485 H.hw486 H.hw487 H.hc H.hRc H.hPc hK

theorem Ph4Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph4Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph4Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨wd, a0, a1, r0, r1, r2, Rc, Dc, Oc, Pc, Qc, ec, H, hK⟩ := H
  exact ⟨wd, a0, a1, r0, r1, r2, Rc, Dc, Oc, Pc, Qc, ec, H, hm _ hK⟩

/-- **Ph5's hypotheses**: `wC`'s windows `3 ..< 7`: the out-of-domain grind and point, `opening_message` (`vsPh5_wins`), but its continuation. -/
structure Ph5Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (sl s qt b22 b23 : ℕ) (ws xs : List E) (nn : E) : Prop where
  hsl16 : 16 ≤ sl
  hsl30 : sl ≤ 30
  hw485 : w 485 = gen ^ sl
  h55 : vsVal rd0 w args (.n 55) = ptrAt s
  hws : 10 < ws.length
  r0 : ReadsAt rd0 (ptrAt s) ws
  hOs : ∀ rd, st.O rd → ReadsAt rd (ptrAt s) ws
  hOwn : ∀ j < 3, Own (s + 10 + j)
  h4 : vsVal rd0 w args (.n 4) = ptrAt qt
  hl0 : LowDef k rd0
  rt : ExpWinTab rd0 (ptrAt qt)
  hPt : ∀ rd, Pre rd → ExpWinTab rd (ptrAt qt)
  hRq : ∀ j < 2 ^ 11, R (qt + (j + 178))
  hwin : ∀ j ≤ gcW 15, w (512 + j) = gcWin 15 (vsVal rd0 w args (.n 500)) j
  hlow : ((vsVal rd0 w args (.n 500)).limb 0).lane.toNat % 2 ^ 15 = 0
  h22 : vsVal rd0 w args (.n 22) = ptrAt b22
  hO22 : ∀ j < sl, Own (b22 + j)
  hspf : [w 566, w 567, w 568, w 569, w 570] = ((⟨[vsVal rd0 w args (.n 507), vsVal rd0 w args (.n 508), vsVal rd0 w args (.n 509), vsVal rd0 w args (.n 510), vsVal rd0 w args (.n 511)], []⟩ : Fs).squeezeN (sl - 1)).2.cap
  hP22 : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt b22) (vsVal rd0 w args (.n 499) :: ((⟨[vsVal rd0 w args (.n 507), vsVal rd0 w args (.n 508), vsVal rd0 w args (.n 509), vsVal rd0 w args (.n 510), vsVal rd0 w args (.n 511)], []⟩ : Fs).squeezeN (sl - 1)).1)
  h23 : vsVal rd0 w args (.n 23) = ptrAt b23
  hO23 : Own (b23 + 0)
  hxs : xs.length = 1
  hom : [w 573, w 574, w 575, w 576, w 577, w 578, w 579, w 580] = omRets (w 566) (w 567) (w 568) (w 569) (w 570) (ptrAt (s + 11)) xs nn
  hP23 : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (s + 11)) (xs ++ [nn]) ∧ ReadsAt rd (ptrAt b23) xs

/-- **Ph5 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph5Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (sl s qt b22 b23 : ℕ) (ws xs : List E) (nn : E),
    Ph5Hyp fs al cert k rd0 w args Own R Pre st sl s qt b22 b23 ws xs nn ∧
    (K ⟨st.a, leafEnd fs al (omName (1, 1)) (leafEnd fs al (spfName sl) st.kc), st.O, st.D, st.Qs ++ [PostQuiet, PostQuiet]⟩)

theorem ph5Ok_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph5Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w3, vsC_w4, vsC_w5, vsC_w6] st K := by
  obtain ⟨sl, s, qt, b22, b23, ws, xs, nn, H, hK⟩ := H
  exact vsPh5_wins (by omega) ha H.hsl16 H.hsl30 H.hw485 H.h55 H.hws H.r0 H.hOs H.hOwn H.h4 H.hl0 H.rt H.hPt H.hRq H.hwin H.hlow H.h22 H.hO22 H.hspf H.hP22 H.h23 H.hO23 H.hxs H.hom H.hP23 hK

theorem Ph5Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph5Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph5Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨sl, s, qt, b22, b23, ws, xs, nn, H, hK⟩ := H
  exact ⟨sl, s, qt, b22, b23, ws, xs, nn, H, hm _ hK⟩

/-- **Ph6's hypotheses**: `wC`'s windows `7 ..< 9`: the link grind, the packing check, `squeeze_packed` at its end (`vsPh6_wins`), but its continuation. -/
structure Ph6Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (qt b9 b10 n wd cc jj : ℕ) (f4 : E) (sh : List E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ) : Prop where
  h4 : vsVal rd0 w args (.n 4) = ptrAt qt
  hl0 : LowDef k rd0
  rt : ExpWinTab rd0 (ptrAt qt)
  hPt : ∀ rd, Pre rd → ExpWinTab rd (ptrAt qt)
  hRq : ∀ j < 2 ^ 11, R (qt + (j + 178))
  hwin : ∀ j ≤ gcW 2, w (581 + j) = gcWin 2 (w 574) j
  hlow : ((w 574).limb 0).lane.toNat % 2 ^ 2 = 0
  h9 : vsVal rd0 w args (.n 9) = ptrAt b9
  hsh : 3 < sh.length
  hf4 : sh[3] = f4
  r9 : ReadsAt rd0 (ptrAt b9) sh
  hO9 : ∀ rd, st.O rd → ReadsAt rd (ptrAt b9) sh
  hOwn9 : Own (b9 + 3)
  h408 : vsVal rd0 w args (.n 408) = gen ^ n
  h409 : vsVal rd0 w args (.n 409) = gen ^ wd
  hw484 : w 484 = gen ^ cc
  hj : jj < 8
  hpk : f4 ^ 8 * (gen ^ n * pkC * gen ^ wd * gen ^ cc)⁻¹ = word (2 ^ jj) 0
  h10 : vsVal rd0 w args (.n 10) = ptrAt b10
  hOwn10 : Own (b10 + 0)
  hO10 : ∀ rd, Pre rd → st.O rd → LoadHolds rd (ptrAt b10) 0 (w 573)
  hc : CallAtA fs al cert k "squeeze_packed" [w 575, w 576, w 577, w 578, w 579, ptrAt (b10 + 1), f4] [w 680, w 681, w 682, w 683, w 684] Rc Dc Oc Pc Qc Bc (allocBase (al "squeeze_packed") st.kc) (allocBase (al "squeeze_packed") st.kc + Bc) ec
  hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i
  hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd

/-- **Ph6 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph6Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (qt b9 b10 n wd cc jj : ℕ) (f4 : E) (sh : List E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ),
    Ph6Hyp fs al cert k rd0 w args Own R Pre st qt b9 b10 n wd cc jj f4 sh Rc Dc Oc Pc Qc Bc ec ∧
    (K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Qc]⟩)

theorem ph6Ok_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph6Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w7, vsC_w8] st K := by
  obtain ⟨qt, b9, b10, n, wd, cc, jj, f4, sh, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hK⟩ := H
  exact vsPh6_wins (by omega) ha H.h4 H.hl0 H.rt H.hPt H.hRq H.hwin H.hlow H.h9 H.hsh H.hf4 H.r9 H.hO9 H.hOwn9 H.h408 H.h409 H.hw484 H.hj H.hpk H.h10 H.hOwn10 H.hO10 H.hc H.hRc H.hPc hK

theorem Ph6Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph6Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph6Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨qt, b9, b10, n, wd, cc, jj, f4, sh, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hK⟩ := H
  exact ⟨qt, b9, b10, n, wd, cc, jj, f4, sh, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hm _ hK⟩

/-- **Ph7's hypotheses**: `wC`'s windows `9 ..< 13`: the packed point's eq tensor, `state_ends`, `link_rounds` at its end (`vsPh7_wins`), but its continuation. -/
structure Ph7Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b8 b10 b11 b12 qt n wd : ℕ) (xs10 xs11 rs zs cs : List E) (x6 x7 : E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ) : Prop where
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  h10 : vsVal rd0 w args (.n 10) = ptrAt b10
  hl10 : 56 ≤ xs10.length
  r10 : ReadsAt rd0 (ptrAt b10) xs10
  hO10 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b10) xs10
  hOwn10 : ∀ j < 56, Own (b10 + j)
  hrs : rs.length = 4
  hrs10 : ∀ t < 4, xs10[50 + t]? = some (rs.getD t 0)
  hx6 : xs10[6]? = some x6
  hx7 : xs10[7]? = some x7
  h11 : vsVal rd0 w args (.n 11) = ptrAt b11
  hl11 : 30 ≤ xs11.length
  r11 : ReadsAt rd0 (ptrAt b11) xs11
  hO11 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b11) xs11
  hOwn11 : ∀ j < 30, Own (b11 + j)
  hlev : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t, xs11[2 ^ t - 2 + i]? = some ((eqKernel (rs.take t)).getD i 0)
  h408 : vsVal rd0 w args (.n 408) = gen ^ n
  h409 : vsVal rd0 w args (.n 409) = gen ^ wd
  h8 : vsVal rd0 w args (.n 8) = ptrAt b8
  hz : zs.length = wd
  hcs : cs.length = wd
  hOz : ∀ j < wd, Own (b10 + 89 + n + j)
  hO8 : ∀ j < wd, Own (b8 + j)
  hPse : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (b10 + 89 + n)) zs ∧ ReadsAt rd (ptrAt b8) cs
  hse : w 752 = prodE (zs.map (1 + ·)) ∧ w 753 = endsProd cs zs
  h12 : vsVal rd0 w args (.n 12) = ptrAt b12
  h4 : vsVal rd0 w args (.n 4) = ptrAt qt
  hc : CallAtA fs al cert k "link_rounds__L1_L0" [w 680, w 681, w 682, w 683, w 684, w 580, lrClaim (w 752) (w 753) x6 x7, ptrAt b12, gen ^ wd, ptrAt qt * word 365917469723852800 0] [w 767, w 768, w 769, w 770, w 771, w 772, w 773] Rc Dc Oc Pc Qc Bc (allocBase (al "link_rounds__L1_L0") (leafEnd fs al (seNames.getD (wd - 19) "") st.kc)) (allocBase (al "link_rounds__L1_L0") (leafEnd fs al (seNames.getD (wd - 19) "") st.kc) + Bc) ec
  hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i
  hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd

/-- **Ph7 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph7Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (b8 b10 b11 b12 qt n wd : ℕ) (xs10 xs11 rs zs cs : List E) (x6 x7 : E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ),
    Ph7Hyp fs al cert k rd0 w args Own R Pre st b8 b10 b11 b12 qt n wd xs10 xs11 rs zs cs x6 x7 Rc Dc Oc Pc Qc Bc ec ∧
    (K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [PostQuiet, Qc]⟩)

theorem ph7Ok_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph7Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w9, vsC_w10, vsC_w11, vsC_w12] st K := by
  obtain ⟨b8, b10, b11, b12, qt, n, wd, xs10, xs11, rs, zs, cs, x6, x7, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hK⟩ := H
  exact vsPh7_wins ha H.hw19 H.hw24 H.h10 H.hl10 H.r10 H.hO10 H.hOwn10 H.hrs H.hrs10 H.hx6 H.hx7 H.h11 H.hl11 H.r11 H.hO11 H.hOwn11 H.hlev H.h408 H.h409 H.h8 H.hz H.hcs H.hOz H.hO8 H.hPse H.hse H.h12 H.h4 H.hc H.hRc H.hPc hK

theorem Ph7Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph7Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph7Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨b8, b10, b11, b12, qt, n, wd, xs10, xs11, rs, zs, cs, x6, x7, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hK⟩ := H
  exact ⟨b8, b10, b11, b12, qt, n, wd, xs10, xs11, rs, zs, cs, x6, x7, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hm _ hK⟩

/-- **Ph8's hypotheses**: `wC`'s windows `13 ..< 15`: `index_side` (`vsPh8_wins`), but its continuation. -/
structure Ph8Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b772 b12 bz b13 wd : ℕ) (v : E) (rs zs : List E) : Prop where
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  hw772 : w 772 = ptrAt b772
  r772 : ReadsAt rd0 (ptrAt b772) [v]
  hO772 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b772) [v]
  hc772 : Own b772 ∨ R b772 ∨ st.D b772
  h409 : vsVal rd0 w args (.n 409) = gen ^ wd
  h12 : vsVal rd0 w args (.n 12) = ptrAt b12
  h694 : vsVal rd0 w args (.n 694) = ptrAt bz
  h13 : vsVal rd0 w args (.n 13) = ptrAt b13
  hrs : rs.length = wd
  hzs : zs.length = wd
  hap : ArraysApart [ptrAt b12, ptrAt bz, ptrAt b13] [(0, wd), (1, wd), (2, wd + 1)]
  hO12 : ∀ j < wd, Own (b12 + j)
  hOz : ∀ j < wd, Own (bz + j)
  hO13 : ∀ j < wd + 1, Own (b13 + j)
  hPis : ∀ rd, Pre rd ∧ st.O rd → HoldsArrays rd [ptrAt b12, ptrAt bz, ptrAt b13] (isIns rs zs) ∧ HoldsArrays rd [ptrAt b12, ptrAt bz, ptrAt b13] (isOuts rs wd)
  his : w 797 = indexMle rs ∧ w 798 = (sideFold zs rs).1 ∧ w 799 = (sideFold zs rs).2.1

/-- **Ph8 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph8Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (b772 b12 bz b13 wd : ℕ) (v : E) (rs zs : List E),
    Ph8Hyp fs al cert k rd0 w args Own R Pre st b772 b12 bz b13 wd v rs zs ∧
    (K ⟨st.a, allocBase (al (imNames.getD (wd - 19) "")) (allocBase (al (isNames.getD (wd - 19) "")) st.kc + fs (isNames.getD (wd - 19) "")) + fs (imNames.getD (wd - 19) ""), st.O, st.D, st.Qs ++ [PostQuiet]⟩)

theorem ph8Ok_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph8Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w13, vsC_w14] st K := by
  obtain ⟨b772, b12, bz, b13, wd, v, rs, zs, H, hK⟩ := H
  exact vsPh8_wins ha H.hw19 H.hw24 H.hw772 H.r772 H.hO772 H.hc772 H.h409 H.h12 H.h694 H.h13 H.hrs H.hzs H.hap H.hO12 H.hOz H.hO13 H.hPis H.his hK

theorem Ph8Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph8Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph8Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨b772, b12, bz, b13, wd, v, rs, zs, H, hK⟩ := H
  exact ⟨b772, b12, bz, b13, wd, v, rs, zs, H, hm _ hK⟩

/-- **Ph9's hypotheses**: `wC`'s windows `15 ..< 17`: the split values, `link_row_side` at its end (`vsPh9_wins`), but its continuation. -/
structure Ph9Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b10 b11 b13 b14 b15 b16 b772 m n cc qt : ℕ) (xs10 xs11 xs13 xs14 : List E) (f0 f1 f2 f3 f4 : E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ) : Prop where
  h13 : vsVal rd0 w args (.n 13) = ptrAt b13
  hl13 : 20 ≤ xs13.length
  r13 : ReadsAt rd0 (ptrAt b13) xs13
  hO13 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b13) xs13
  hOwn13 : ∀ j < xs13.length, Own (b13 + j)
  h101 : vsVal rd0 w args (.n 101) = gen ^ m
  hm : m < xs13.length
  h14 : vsVal rd0 w args (.n 14) = ptrAt b14
  hl14 : 36 ≤ xs14.length
  r14 : ReadsAt rd0 (ptrAt b14) xs14
  hO14 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b14) xs14
  hOwn14 : ∀ j < 36, Own (b14 + j)
  h11 : vsVal rd0 w args (.n 11) = ptrAt b11
  hl11 : 30 ≤ xs11.length
  r11 : ReadsAt rd0 (ptrAt b11) xs11
  hO11 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b11) xs11
  hOwn11 : ∀ j < 30, Own (b11 + j)
  h10 : vsVal rd0 w args (.n 10) = ptrAt b10
  hl10 : 37 ≤ xs10.length
  r10 : ReadsAt rd0 (ptrAt b10) xs10
  hO10 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b10) xs10
  hOwn10 : ∀ j < 37, Own (b10 + j)
  hc6 : 6 ≤ cc
  hc9 : cc ≤ 9
  hw484 : w 484 = gen ^ cc
  hw772 : w 772 = ptrAt b772
  hf : vsVal rd0 w args (.n 790) = f0 ∧ vsVal rd0 w args (.n 791) = f1 ∧ vsVal rd0 w args (.n 792) = f2 ∧ vsVal rd0 w args (.n 793) = f3 ∧ vsVal rd0 w args (.n 794) = f4
  h15 : vsVal rd0 w args (.n 15) = ptrAt b15
  h16 : vsVal rd0 w args (.n 16) = ptrAt b16
  h408 : vsVal rd0 w args (.n 408) = gen ^ n
  h4 : vsVal rd0 w args (.n 4) = ptrAt qt
  hc : CallAtA fs al cert k (lrsNames.getD (cc - 6) "") [f0, f1, f2, f3, f4, ptrAt (b772 + 1), w 773, ptrAt b15, ptrAt b16, gen ^ n, ptrAt qt * word 365917469723852800 0] [w 1071, w 1072, w 1073, w 1074, w 1075, w 1076, w 1077] Rc Dc Oc Pc Qc Bc (allocBase (al (lrsNames.getD (cc - 6) "")) st.kc) (allocBase (al (lrsNames.getD (cc - 6) "")) st.kc + Bc) ec
  hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i
  hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd

/-- **Ph9 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph9Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (b10 b11 b13 b14 b15 b16 b772 m n cc qt : ℕ) (xs10 xs11 xs13 xs14 : List E) (f0 f1 f2 f3 f4 : E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ),
    Ph9Hyp fs al cert k rd0 w args Own R Pre st b10 b11 b13 b14 b15 b16 b772 m n cc qt xs10 xs11 xs13 xs14 f0 f1 f2 f3 f4 Rc Dc Oc Pc Qc Bc ec ∧
    (K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Qc]⟩)

theorem ph9Ok_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph9Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w15, vsC_w16] st K := by
  obtain ⟨b10, b11, b13, b14, b15, b16, b772, m, n, cc, qt, xs10, xs11, xs13, xs14, f0, f1, f2, f3, f4, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hK⟩ := H
  exact vsPh9_wins (by omega) ha H.h13 H.hl13 H.r13 H.hO13 H.hOwn13 H.h101 H.hm H.h14 H.hl14 H.r14 H.hO14 H.hOwn14 H.h11 H.hl11 H.r11 H.hO11 H.hOwn11 H.h10 H.hl10 H.r10 H.hO10 H.hOwn10 H.hc6 H.hc9 H.hw484 H.hw772 H.hf H.h15 H.h16 H.h408 H.h4 H.hc H.hRc H.hPc hK

theorem Ph9Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph9Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph9Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨b10, b11, b13, b14, b15, b16, b772, m, n, cc, qt, xs10, xs11, xs13, xs14, f0, f1, f2, f3, f4, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hK⟩ := H
  exact ⟨b10, b11, b13, b14, b15, b16, b772, m, n, cc, qt, xs10, xs11, xs13, xs14, f0, f1, f2, f3, f4, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hm _ hK⟩

/-- **Ph10's hypotheses**: `wC`'s windows `17 ..< 20`: the rows' eq tensor, `one_plus_suffixes`, `packed_message` (`vsPh10_wins`), but its continuation. -/
structure Ph10Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b15 b16 b17 b18 bm n : ℕ) (xs16 xs17 rs as15 xm : List E) : Prop where
  h16 : vsVal rd0 w args (.n 16) = ptrAt b16
  hl16 : 6 ≤ xs16.length
  r16 : ReadsAt rd0 (ptrAt b16) xs16
  hO16 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b16) xs16
  hOwn16 : ∀ j < 6, Own (b16 + j)
  hrs : rs.length = 6
  hrs16 : ∀ t < 6, xs16[t]? = some (rs.getD t 0)
  h17 : vsVal rd0 w args (.n 17) = ptrAt b17
  hl17 : 126 ≤ xs17.length
  r17 : ReadsAt rd0 (ptrAt b17) xs17
  hO17 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b17) xs17
  hOwn17 : ∀ j < 126, Own (b17 + j)
  hlev : ∀ t, 1 ≤ t → t ≤ 6 → ∀ i < 2 ^ t, xs17[2 ^ t - 2 + i]? = some ((eqKernel (rs.take t)).getD i 0)
  h408 : vsVal rd0 w args (.n 408) = gen ^ n
  hn : n ≤ 40
  h18 : vsVal rd0 w args (.n 18) = ptrAt b18
  h15 : vsVal rd0 w args (.n 15) = ptrAt b15
  hl15 : as15.length = n
  hO18 : ∀ j < n + 1, Own (b18 + j)
  hO15 : ∀ j < n, Own (b15 + j)
  hPops : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt b15) as15 ∧ ReadsAt rd (ptrAt b18) ((List.range (n + 1)).map (belowE as15))
  hw1286 : w 1286 = 0
  hwm : w 1076 = ptrAt bm
  hxm : xm.length = 144
  hcm : ∀ j < 144, (R (bm + j) ∨ Own (bm + j)) ∨ st.D (bm + j)
  hPpm : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt bm) xm
  hpm : [w 1287, w 1288, w 1289, w 1290, w 1291, w 1292] = (Fs.squeeze ⟨pkAbsorb 18 xm [w 1071, w 1072, w 1073, w 1074, w 1075], []⟩).1 :: (Fs.squeeze ⟨pkAbsorb 18 xm [w 1071, w 1072, w 1073, w 1074, w 1075], []⟩).2.cap

/-- **Ph10 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph10Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (b15 b16 b17 b18 bm n : ℕ) (xs16 xs17 rs as15 xm : List E),
    Ph10Hyp fs al cert k rd0 w args Own R Pre st b15 b16 b17 b18 bm n xs16 xs17 rs as15 xm ∧
    (K ⟨st.a, leafEnd fs al "packed_message__L144" (leafEnd fs al (opsNames.getD n "") st.kc), st.O, st.D, st.Qs ++ [PostQuiet, PostQuiet]⟩)

theorem ph10Ok_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph10Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w17, vsC_w18, vsC_w19] st K := by
  obtain ⟨b15, b16, b17, b18, bm, n, xs16, xs17, rs, as15, xm, H, hK⟩ := H
  exact vsPh10_wins (by omega) ha H.h16 H.hl16 H.r16 H.hO16 H.hOwn16 H.hrs H.hrs16 H.h17 H.hl17 H.r17 H.hO17 H.hOwn17 H.hlev H.h408 H.hn H.h18 H.h15 H.hl15 H.hO18 H.hO15 H.hPops H.hw1286 H.hwm H.hxm H.hcm H.hPpm H.hpm hK

theorem Ph10Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph10Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph10Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨b15, b16, b17, b18, bm, n, xs16, xs17, rs, as15, xm, H, hK⟩ := H
  exact ⟨b15, b16, b17, b18, bm, n, xs16, xs17, rs, as15, xm, H, hm _ hK⟩

/-- **Ph11's hypotheses**: `wC`'s windows `20 ..< 22`: the first table point (`vsPh11_wins`), but its continuation. -/
structure Ph11Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b7 b10 b15 h : ℕ) (xs10 ts xs cs : List E) (θ top : E) : Prop where
  h10 : vsVal rd0 w args (.n 10) = ptrAt b10
  hl10 : 1 ≤ xs10.length
  r10 : ReadsAt rd0 (ptrAt b10) xs10
  hO10 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b10) xs10
  hOwn10 : Own (b10 + 0)
  hθ : xs10[0]? = some θ
  h115 : vsVal rd0 w args (.n 115) = gen ^ h
  hh : h ≤ 24
  h15 : vsVal rd0 w args (.n 15) = ptrAt b15
  h7 : vsVal rd0 w args (.n 7) = ptrAt b7
  hts : ts.length = h
  hxs : xs.length = h
  hcs : cs.length = h
  hOt : ∀ j < h, Own (b10 + 89 + j)
  hO15 : ∀ j < h, Own (b15 + j)
  hO7 : ∀ j < h + 1, Own (b7 + j)
  hPtp : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (b10 + 89)) ts ∧ ReadsAt rd (ptrAt b15) xs ∧ ReadsAt rd (ptrAt b7) (cs ++ [top])
  htp : w 1296 = θ * tpTotalG ts xs cs top h ∧ w 1297 = 1 + (1 + top) * tpPad cs xs ∧ w 1298 = tpFullAt ts xs h

/-- **Ph11 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph11Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (b7 b10 b15 h : ℕ) (xs10 ts xs cs : List E) (θ top : E),
    Ph11Hyp fs al cert k rd0 w args Own R Pre st b7 b10 b15 h xs10 ts xs cs θ top ∧
    (K ⟨st.a, leafEnd fs al (tpNames.getD h "") st.kc, st.O, st.D, st.Qs ++ [PostQuiet]⟩)

theorem ph11Ok_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph11Ok fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w20, vsC_w21] st K := by
  obtain ⟨b7, b10, b15, h, xs10, ts, xs, cs, θ, top, H, hK⟩ := H
  exact vsPh11_wins ha H.h10 H.hl10 H.r10 H.hO10 H.hOwn10 H.hθ H.h115 H.hh H.h15 H.h7 H.hts H.hxs H.hcs H.hOt H.hO15 H.hO7 H.hPtp H.htp hK

theorem Ph11Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph11Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph11Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨b7, b10, b15, h, xs10, ts, xs, cs, θ, top, H, hK⟩ := H
  exact ⟨b7, b10, b15, h, xs10, ts, xs, cs, θ, top, H, hm _ hK⟩

/-- **Ph1213's hypotheses**: `wC`'s windows `22 ..< 35`: the table points, the link's terminal at its end (`vsPh12_13_wins`), but its continuation. -/
structure Ph1213Hyp (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b18 b1076 b11 b10 b17 b15 b19 wd : ℕ) (xs18 xs1076 xs11 xs10 xs17 xs19 : List E) (hg bb : ℕ → ℕ) (ts xs cs : ℕ → List E) (top : ℕ → E) (a12 coef certW nu rest : E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ) : Prop where
  B18 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 18 b18 25 xs18
  B1076 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 1076 b1076 80 xs1076
  B11 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 11 b11 30 xs11
  B10 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 10 b10 89 xs10
  B17 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 17 b17 95 xs17
  B19 : BufAt rd0 (vsVal rd0 w args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 19 b19 12 xs19
  hsel : ∀ t ≤ 5, vsVal rd0 w args (.n (115 + t)) = gen ^ hg t
  hh : ∀ t ≤ 5, hg t ≤ 24
  h15 : vsVal rd0 w args (.n 15) = ptrAt b15
  hbv : ∀ t, 1 ≤ t → t ≤ 5 → vsVal rd0 w args (.n (tpBv t)) = ptrAt (bb t)
  hts : ∀ t, 1 ≤ t → t ≤ 5 → (ts t).length = hg t ∧ (xs t).length = hg t ∧ (cs t).length = hg t
  hOt : ∀ j < 24, Own (b10 + 89 + j) ∨ R (b10 + 89 + j) ∨ st.D (b10 + 89 + j)
  hO15 : ∀ j < 24, Own (b15 + j) ∨ R (b15 + j) ∨ st.D (b15 + j)
  hOb : ∀ t, 1 ≤ t → t ≤ 5 → ∀ j < hg t + 1, Own (bb t + 26 + j) ∨ R (bb t + 26 + j) ∨ st.D (bb t + 26 + j)
  hPtp : ∀ t, 1 ≤ t → t ≤ 5 → ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (b10 + 89)) (ts t) ∧ ReadsAt rd (ptrAt b15) (xs t) ∧ ReadsAt rd (ptrAt (bb t + 26)) (cs t ++ [top t])
  htp : ∀ t, 1 ≤ t → t ≤ 5 → ∀ d, d = [1403, 1524, 1607, 1734, 1880].getD (t - 1) 0 → w (d + 5) = xs10.getD t 0 * tpTotalG (ts t) (xs t) (cs t) (top t) (hg t) ∧ w (d + 6) = 1 + (1 + top t) * tpPad (cs t) (xs t) ∧ w (d + 7) = tpFullAt (ts t) (xs t) (hg t)
  hst : ∀ x ∈ stC32, MemF rd0 (vsVal rd0 w args) x
  h409 : vsVal rd0 w args (.n 409) = gen ^ wd
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  e12 : vsVal rd0 w args (.n 12) = a12
  e2846 : vsVal rd0 w args (.n 2846) = coef
  e2891 : vsVal rd0 w args (.n 2891) = certW
  e695 : vsVal rd0 w args (.n 695) = nu
  e2890 : vsVal rd0 w args (.n 2890) = rest
  hc : CallAtA fs al cert k (ltNames.getD (wd - 19) "") [a12, ptrAt b1076, coef, ptrAt b19, certW, nu, rest, w 1077] [w 2894] Rc Dc Oc Pc Qc Bc (allocBase (al (ltNames.getD (wd - 19) "")) (tpKc fs al hg 5 st.kc)) (allocBase (al (ltNames.getD (wd - 19) "")) (tpKc fs al hg 5 st.kc) + Bc) ec
  hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i
  hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd

/-- **Ph1213 in continuation form**: its hypotheses at some values, the continuation at its end. -/
def Ph1213Ok (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
    (args : List E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St) (K : St → Prop) : Prop :=
  ∃ (b18 b1076 b11 b10 b17 b15 b19 wd : ℕ) (xs18 xs1076 xs11 xs10 xs17 xs19 : List E) (hg bb : ℕ → ℕ) (ts xs cs : ℕ → List E) (top : ℕ → E) (a12 coef certW nu rest : E) (Rc Dc : ℕ → Prop) (Oc Pc : Reader → Prop) (Qc : Reader → Tree → Prop) (Bc ec : ℕ),
    Ph1213Hyp fs al cert k rd0 w args Own R Pre st b18 b1076 b11 b10 b17 b15 b19 wd xs18 xs1076 xs11 xs10 xs17 xs19 hg bb ts xs cs top a12 coef certW nu rest Rc Dc Oc Pc Qc Bc ec ∧
    K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ List.replicate 5 PostQuiet ++ [Qc]⟩

theorem ph1213Ok_wins (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : Ph1213Ok fs al cert k rd0 w args Own R Pre st
      fun s => WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre (wC.drop 35) s K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre (wC.drop 22) st K := by
  obtain ⟨b18, b1076, b11, b10, b17, b15, b19, wd, xs18, xs1076, xs11, xs10, xs17, xs19, hg, bb, ts, xs, cs, top, a12, coef, certW, nu, rest, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hK⟩ := H
  exact vsPh12_13_wins ha H.B18 H.B1076 H.B11 H.B10 H.B17 H.B19 H.hsel H.hh H.h15 H.hbv H.hts H.hOt H.hO15 H.hOb H.hPtp H.htp H.hst H.h409 H.hw19 H.hw24 H.e12 H.e2846 H.e2891 H.e695 H.e2890 H.hc H.hRc H.hPc hK

theorem Ph1213Ok.mono {st : St} {K K' : St → Prop}
    (H : Ph1213Ok fs al cert k rd0 w args Own R Pre st K) (hm : ∀ s, K s → K' s) :
    Ph1213Ok fs al cert k rd0 w args Own R Pre st K' := by
  obtain ⟨b18, b1076, b11, b10, b17, b15, b19, wd, xs18, xs1076, xs11, xs10, xs17, xs19, hg, bb, ts, xs, cs, top, a12, coef, certW, nu, rest, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hK⟩ := H
  exact ⟨b18, b1076, b11, b10, b17, b15, b19, wd, xs18, xs1076, xs11, xs10, xs17, xs19, hg, bb, ts, xs, cs, top, a12, coef, certW, nu, rest, Rc, Dc, Oc, Pc, Qc, Bc, ec, H, hm _ hK⟩

/-- **`wC`'s windows' hypotheses, phase by phase**: `Ph4Ok` … `Ph1213Ok` chained, the siblings' tail
(`wC.drop 35`, `verify_keccak` on) last. -/
def WCOk (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
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
  WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre (wC.drop 35) s K

theorem wC_split : wC = [vsC_w0, vsC_w1, vsC_w2] ++ ([vsC_w3, vsC_w4, vsC_w5, vsC_w6] ++ ([vsC_w7, vsC_w8] ++
    ([vsC_w9, vsC_w10, vsC_w11, vsC_w12] ++ ([vsC_w13, vsC_w14] ++ ([vsC_w15, vsC_w16] ++
      ([vsC_w17, vsC_w18, vsC_w19] ++ ([vsC_w20, vsC_w21] ++ wC.drop 22))))))) := rfl

/-- **`wC`'s windows' hypotheses from its phases'.** -/
theorem wcOk_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : WCOk fs al cert k rd0 w args Own R Pre st K) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wC st K := by
  rw [wC_split, winsHyp_append]
  refine ph4Ok_wins ha (Ph4Ok.mono H fun _ H => ?_)
  rw [winsHyp_append]
  refine ph5Ok_wins hk ha (Ph5Ok.mono H fun _ H => ?_)
  rw [winsHyp_append]
  refine ph6Ok_wins hk ha (Ph6Ok.mono H fun _ H => ?_)
  rw [winsHyp_append]
  refine ph7Ok_wins ha (Ph7Ok.mono H fun _ H => ?_)
  rw [winsHyp_append]
  refine ph8Ok_wins ha (Ph8Ok.mono H fun _ H => ?_)
  rw [winsHyp_append]
  refine ph9Ok_wins hk ha (Ph9Ok.mono H fun _ H => ?_)
  rw [winsHyp_append]
  refine ph10Ok_wins hk ha (Ph10Ok.mono H fun _ H => ?_)
  rw [winsHyp_append]
  refine ph11Ok_wins ha (Ph11Ok.mono H fun _ H => ?_)
  exact ph1213Ok_wins ha H

/-- **`verify_sub`'s windows' hypotheses from its phases'**: the front, then `wC`'s. -/
theorem vsHyp_of_orc (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    (H : FrontOk fs al cert k rd0 w args Own R Pre st fun s => WCOk fs al cert k rd0 w args Own R Pre s K) :
    VsHyp fs al cert k rd0 w args Own R Pre st K := by
  rw [VsHyp]
  exact frontOk_wins hk ha (FrontOk.mono H fun _ h => wcOk_wins hk ha h)

end

/-! ## The oracle's statement -/

/-- `verify_sub`'s own cells at a placement, on the valuation `σ0`. -/
noncomputable abbrev vsOwn (fp cur : ℕ) (σ0 : Val) : ℕ → Prop :=
  ownData B2C.cert fp cur "verify_sub" (allocs σ0 (vsEs σ0)) (vsEs σ0)

/-- **`VsWinHyp`'s final condition**: on every memory with `Pre` and the windows' words, the callees' trees
satisfying their posts give `vsPostA`. -/
noncomputable def vsKEnd (k : ℕ) (bytecode : List K) (seed : Digest) (c : Child) (qt qo : ℕ) (σ0 : Val) :
    St → Prop := fun st =>
  ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd → ∀ ts,
    Tree.KidsValid coreProgram rd (rdOver σ0 rd) (calls (vsEs σ0)) ts →
    KidsPost rd st.Qs (calls (vsEs σ0)) ts →
    vsPostA bytecode seed c rd (.node "verify_sub" (rdOver σ0 rd) (allocs σ0 (vsEs σ0)) ts)

/-- **The honest oracle's statement**: at every placement `VsWinHyp` quantifies, an evaluation memory `rd0`,
an oracle `w` and the node's words `Wo` with `WordsInA`, and the phases' hypotheses on `vsσ rd0 w seed c qt qo`
from `vsSt0` (`FrontOk`, then `WCOk`), ending within `2^40` of a cursor below `2^60` (iface's bound on
`VsWinHyp`'s continuation) and in `vsKEnd`. -/
def VsOrc (al : String → Bool) (k : ℕ) (bytecode : List K) (seed : Digest) : Prop :=
  ∀ (c : Child) (qt qo fp cur : ℕ), VsChildOk bytecode seed c → qt + expTabLen ≤ fp →
    qo + c.freshClaim.cells.length ≤ fp → fp + B2C.fs "verify_sub" ≤ cur →
    (∃ rd, vsPreA seed c qt qo rd) → cur < 2 ^ 60 →
    ∃ (rd0 : Reader) (w : ℕ → E) (Wo : Words),
      WordsInA Wo (fp + 2) (fp + B2C.fs "verify_sub") cur
        (cur + (allocs (vsσ rd0 w seed c qt qo) (vsEs (vsσ rd0 w seed c qt qo))).sum) ∧
      FrontOk B2C.fs al B2C.cert k rd0 w (vsArgs seed c (ptrAt qt) (ptrAt qo))
        (vsOwn fp cur (vsσ rd0 w seed c qt qo)) (vsRegion qt qo c.freshClaim.cells.length) (vsPreA seed c qt qo)
        (vsSt0 (vsσ rd0 w seed c qt qo) cur Wo) fun s =>
      WCOk B2C.fs al B2C.cert k rd0 w (vsArgs seed c (ptrAt qt) (ptrAt qo))
        (vsOwn fp cur (vsσ rd0 w seed c qt qo)) (vsRegion qt qo c.freshClaim.cells.length) (vsPreA seed c qt qo)
        s fun st => (cur < 2 ^ 60 → st.kc ≤ cur + 2 ^ 40) ∧ vsKEnd k bytecode seed c qt qo (vsσ rd0 w seed c qt qo) st

/-- **`VsWinHyp` from the honest oracle's statement.** -/
theorem vsWinHyp_of_orc {al : String → Bool} {k : ℕ} {bytecode : List K} {seed : Digest} (hk : 11 ≤ k)
    (h : VsOrc al k bytecode seed) : VsWinHyp al k bytecode seed := by
  intro c qt qo fp cur hc ht ho hfc hP hcur
  obtain ⟨rd0, w, Wo, hWo, H⟩ := h c qt qo fp cur hc ht ho hfc hP hcur
  exact ⟨rd0, w, Wo, hWo, vsHyp_of_orc hk rfl H⟩

/-- **What is left of `verify_sub`'s windows**, as the honest oracle's statement. -/
def VsOrcFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  14 ≤ k → VsCalleesCompleteA B2C.fs al B2C.cert k → ∀ seed, VsOrc al k guestBytecode seed

theorem vsWinHypFromCallees_of_orc {al : String → Bool} {k : ℕ} (h : VsOrcFromCallees al k) :
    VsWinHypFromCallees al k :=
  fun hk hc seed => vsWinHyp_of_orc (by omega) (h hk hc seed)

end
end LeanVM.Guest.B1.VsC
