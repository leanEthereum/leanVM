/-
  LeanVM.Guest.B1.VsC.VsPh2W

  `verify_sub`'s windows `7 ..< 19` of `wA` (`WinsHyp`): the six `table_size` dispatches, the checks
  after each, the least-height selector's window; and the least-height branch (`IteHyp` at `.n 234`).
-/

module

public import LeanVM.Guest.B1.VsC.VsPh2
public import LeanVM.Guest.B1.VsC.VsWins

/-!
# Phase 2's windows

Table `t`'s log height `h t` (the heap witness `table_logs`, read by window `6` into `.n (115 + t)`) and
row count `R t` (the sizes' buffer's word `t`, `.n 144` for table `0`, then loaded after each dispatch),
its bits' buffer `b7 + 26 t` (window `0`'s second `HeapBuf`, `156` words).

* `vsW6_vals`: window `6`'s loads, the heights `.n 115 … .n 120` and the first row count `.n 144`.
* `ts_pair`, `ts_pair0`: a dispatch and the run after it.
* **`vsPh2_wins`**: `WinsHyp … [vsA_w7, …, vsA_w18] st K` from the heights `h t ≤ 24` (`9 ≤ h 5`), the row
  counts `R t ≤ 2^(h t)`, least for tables `0 ..< 5`, `table_size`'s returns in the oracle, the heights at
  `b6` and the row counts at `b56` read by `rd0`, the bits and the row counts held, `K` after.
* **`vsPh2_sel`**: the least-height branch, `IteHyp … (.n 234) [] wI1 st K`, its arm table `5`'s checks
  when `h 5 ≠ 9`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- A state up to equivalent words, data and the same posts. -/
theorem st_congr {K : St → Prop} {a a' kc : ℕ} {O O' : Reader → Prop} {D D' : ℕ → Prop}
    {Qs Qs' : List (Reader → Tree → Prop)} (h : K ⟨a, kc, O, D, Qs⟩) (ha : a' = a) (hO : ∀ rd, O' rd ↔ O rd)
    (hD : ∀ i, D' i ↔ D i) (hQ : Qs' = Qs) : K ⟨a', kc, O', D', Qs'⟩ := by
  have eO : O' = O := funext fun rd => propext (hO rd)
  have eD : D' = D := funext fun i => propext (hD i)
  subst ha eO eD hQ; exact h

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- **Window `6`'s loads**: the six heights from `b6`, the first row count from the sizes' buffer. -/
theorem vsW6_vals (ha : args.length = 6) {b6 b56 : ℕ} (hw6 : w 6 = ptrAt b6) (hw56 : w 56 = ptrAt b56)
    {t0 t1 t2 t3 t4 t5 : E} {bs : List E} (hbs : 1 ≤ bs.length)
    (r6 : ReadsAt rd0 (ptrAt b6) [t0, t1, t2, t3, t4, t5]) (r56 : ReadsAt rd0 (ptrAt b56) bs) :
    vsVal rd0 w args (.n 115) = t0 ∧ vsVal rd0 w args (.n 116) = t1 ∧ vsVal rd0 w args (.n 117) = t2 ∧
      vsVal rd0 w args (.n 118) = t3 ∧ vsVal rd0 w args (.n 119) = t4 ∧ vsVal rd0 w args (.n 120) = t5 ∧
      vsVal rd0 w args (.n 144) = bs[0] := by
  have hg := vsW6_good (rd0 := rd0) (w := w) ha
  set σ0 := vsVal rd0 w args with hσ0
  have p6 : σ0 (.n 6) = ptrAt b6 := by
    rw [hσ0]; exact (vsW0_good ha (a := .hint (.alloc (.n 6) 6)) (by simp [vsW0, vsW0a])).trans hw6
  have p56 : σ0 (.n 56) = ptrAt b56 := by
    rw [hσ0]
    exact (vsA_run_good (rd0 := rd0) (w := w) ha vsW2_eq vsW2_ne (.hint (.alloc (.n 56) 6)) (by simp [vsW2])).trans
      hw56
  have fr := vsW6_fresh
  have fresh : ∀ (b : ℕ) (xs : List E) (d pv off : ℕ), σ0 (.n pv) = ptrAt b → ReadsAt rd0 (ptrAt b) xs →
      (d, pv, off) ∈ vsW6ld → pv ≠ 112 → ∀ h : off < xs.length, σ0 (.n d) = xs[off] := by
    intro b xs d pv off hp hr hq hne h
    have hm' : Atom.load (.n d) (.n pv) off ∈ vsW6ld.map (fun q => Atom.load (.n q.1) (.n q.2.1) q.2.2) :=
      List.mem_map.mpr ⟨_, hq, rfl⟩
    rw [← vsW6_mem] at hm'
    have hm : Atom.load (.n d) (.n pv) off ∈ vsW6 := List.mem_of_mem_filter hm'
    have hs : Atom.load (.n d) (.n pv) off ∉ storesOf 6 vsAf := fun h' => by
      have := List.all_eq_true.mp fr (d, pv, off) (List.mem_filter.mpr ⟨hq, by simpa using hne⟩)
      rw [List.contains_iff_mem.mpr h'] at this
      exact absurd this (by decide)
    exact good_loadAt hs (hg _ hm) hp h hr
  exact ⟨fresh b6 _ 115 6 0 p6 r6 (by simp [vsW6ld]) (by decide) (by simp),
    fresh b6 _ 116 6 1 p6 r6 (by simp [vsW6ld]) (by decide) (by simp),
    fresh b6 _ 117 6 2 p6 r6 (by simp [vsW6ld]) (by decide) (by simp),
    fresh b6 _ 118 6 3 p6 r6 (by simp [vsW6ld]) (by decide) (by simp),
    fresh b6 _ 119 6 4 p6 r6 (by simp [vsW6ld]) (by decide) (by simp),
    fresh b6 _ 120 6 5 p6 r6 (by simp [vsW6ld]) (by decide) (by simp),
    fresh b56 bs 144 56 0 p56 r56 (by simp [vsW6ld]) (by decide) (by omega)⟩

/-- The bits' buffer `.n 7` is the oracle's. -/
theorem vsVal_7 (ha : args.length = 6) {b7 : ℕ} (hw7 : w 7 = ptrAt b7) : vsVal rd0 w args (.n 7) = ptrAt b7 :=
  (vsW0_good ha (a := .hint (.alloc (.n 7) 156)) (by simp [vsW0, vsW0a])).trans hw7

/-- The sizes' buffer `.n 56` is the oracle's. -/
theorem vsVal_56 (ha : args.length = 6) {b56 : ℕ} (hw56 : w 56 = ptrAt b56) :
    vsVal rd0 w args (.n 56) = ptrAt b56 :=
  (vsA_run_good (rd0 := rd0) (w := w) ha vsW2_eq vsW2_ne (.hint (.alloc (.n 56) 6)) (by simp [vsW2])).trans hw56

end

theorem rows_fresh {q : ℕ × ℕ} (hq : q ∈ [157, 173, 189, 205, 221].zip [1, 2, 3, 4, 5]) :
    Atom.load (.n q.1) (.n 56) q.2 ∉ storesOf 6 vsAf := fun h => by
  have := List.all_eq_true.mp vsA_rows_fresh q hq
  rw [List.contains_iff_mem.mpr h] at this
  exact absurd this (by decide)

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {S : List Atom}
  {σ0 : Val} {w : ℕ → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **Table `t ≥ 1`'s dispatch and the run after it.** -/
theorem ts_pair {xd av pv n x pp off h Rt h' c b56 : ℕ} {bs : List E} {ws : List W0} {st : St}
    {K : St → Prop} {O0 : Reader → Prop} (hk : 6 ≤ k) (hpp : pp < n + 8) (hpv' : pv < n + 15)
    (hg : ∀ a ∈ tsRun n x pp pv off, Good rd0 S w σ0 (fixA a))
    (hS : Atom.load (.n (n + 13)) (.n 56) off ∉ S)
    (hh : h ≤ 24) (hR : Rt ≤ 2 ^ h) (hl : h = 0 ∨ 2 ^ (h - 1) < Rt)
    (hxd : σ0 (.n xd) = gen ^ h) (hav : σ0 (.n av) = eOfNat Rt) (hpv : σ0 (.n pv) = ptrAt c)
    (hr0 : σ0 (.n n) = gen ^ Rt) (hr1 : σ0 (.n (n + 1)) = tsLeadW Rt h)
    (hr2 : σ0 (.n (n + 2)) = tsRestW Rt h) (hh' : h' ≤ 24) (hx : σ0 (.n x) = gen ^ h')
    (p56 : σ0 (.n 56) = ptrAt b56) (hoff : off < bs.length) (r56 : ReadsAt rd0 (ptrAt b56) bs)
    (hOwn : ∀ j < h + 1, Own (c + j)) (hOb : Own (b56 + off)) (hO : ∀ rd, st.O rd → O0 rd)
    (hrd : ∀ rd, O0 rd → ReadsAt rd (ptrAt c) (tsBitsW Rt h) ∧ ReadsAt rd (ptrAt b56) bs)
    (hrest : σ0 (.n (n + 13)) = bs[off] → σ0 (.n (n + 15)) = ptrAt (c + 26) →
      WinsHyp fs al cert k σ0 w Own R Pre ws
        ⟨st.a, leafEnd fs al (Link.tsNames.getD h "") st.kc, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
          st.Qs ++ [PostQuiet]⟩ K) :
    WinsHyp fs al cert k σ0 w Own R Pre (.call (tsDisp xd av pv n) :: .run (tsRun n x pp pv off) :: ws) st K := by
  obtain ⟨hrh, e13, e15⟩ := tsRun_runHyp (a := st.a) (D := fun i => st.D i ∨ False)
    (O := fun rd => st.O rd ∧ True) (Own := Own) (R := R) (Pre := Pre) (w := w) hk hpp hpv' hg hS hh hR hl
    hr1 hr2 hh' hx p56 bs hoff r56 hpv hOb (fun rd ho => (hrd rd (hO rd ho.1)).2)
  refine ts_disp hh hR hxd hav hpv hr0 hr1 hr2 hOwn (fun rd ho => (hrd rd (hO rd ho)).1) ?_
  rw [WinsHyp]
  exact ⟨hrh, hrest e13 e15⟩

/-- **Table `0`'s dispatch and the run after it.** -/
theorem ts_pair0 {h Rt h' c b56 : ℕ} {bs : List E} {ws : List W0} {st : St}
    {K : St → Prop} {O0 : Reader → Prop} (hk : 6 ≤ k)
    (hg : ∀ a ∈ tsRun0, Good rd0 S w σ0 (fixA a)) (hS : Atom.load (.n 157) (.n 56) 1 ∉ S)
    (hh : h ≤ 24) (hR : Rt ≤ 2 ^ h) (hl : h = 0 ∨ 2 ^ (h - 1) < Rt)
    (hxd : σ0 (.n 115) = gen ^ h) (hav : σ0 (.n 144) = eOfNat Rt) (hpv : σ0 (.n 7) = ptrAt c)
    (hr0 : σ0 (.n 145) = gen ^ Rt) (hr1 : σ0 (.n 146) = tsLeadW Rt h)
    (hr2 : σ0 (.n 147) = tsRestW Rt h) (hh' : h' ≤ 24) (hx : σ0 (.n 116) = gen ^ h')
    (p56 : σ0 (.n 56) = ptrAt b56) (hoff : 1 < bs.length) (r56 : ReadsAt rd0 (ptrAt b56) bs)
    (hOwn : ∀ j < h + 1, Own (c + j)) (hOb : Own (b56 + 1)) (hO : ∀ rd, st.O rd → O0 rd)
    (hrd : ∀ rd, O0 rd → ReadsAt rd (ptrAt c) (tsBitsW Rt h) ∧ ReadsAt rd (ptrAt b56) bs)
    (hrest : σ0 (.n 157) = bs[1] → σ0 (.n 159) = ptrAt (c + 26) →
      WinsHyp fs al cert k σ0 w Own R Pre ws
        ⟨st.a, leafEnd fs al (Link.tsNames.getD h "") st.kc, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
          st.Qs ++ [PostQuiet]⟩ K) :
    WinsHyp fs al cert k σ0 w Own R Pre (.call (tsDisp 115 144 7 145) :: .run tsRun0 :: ws) st K := by
  obtain ⟨hrh, e13, e15⟩ := tsRun0_runHyp (a := st.a) (D := fun i => st.D i ∨ False)
    (O := fun rd => st.O rd ∧ True) (Own := Own) (R := R) (Pre := Pre) (w := w) hk hg hS hh hR hl
    hr1 hr2 hh' hx p56 bs hoff r56 hpv hOb (fun rd ho => (hrd rd (hO rd ho.1)).2)
  refine ts_disp hh hR hxd hav hpv hr0 hr1 hr2 hOwn (fun rd ho => (hrd rd (hO rd ho)).1) ?_
  rw [WinsHyp]
  exact ⟨hrh, hrest e13 e15⟩

end

/-- `table_size`'s returns for table `t`: `.n (tsRet t)`, `.n (tsRet t + 1)`, `.n (tsRet t + 2)`. -/
def tsRet (t : ℕ) : ℕ := [145, 160, 176, 192, 208, 224].getD t 0

/-- The callees' cursor after the six `table_size` leaves, from `kc`, at log heights `h`. -/
def tsEnd (fs : String → ℕ) (al : String → Bool) (h : ℕ → ℕ) (kc : ℕ) : ℕ :=
  leafEnd fs al (Link.tsNames.getD (h 5) "") (leafEnd fs al (Link.tsNames.getD (h 4) "")
    (leafEnd fs al (Link.tsNames.getD (h 3) "") (leafEnd fs al (Link.tsNames.getD (h 2) "")
      (leafEnd fs al (Link.tsNames.getD (h 1) "") (leafEnd fs al (Link.tsNames.getD (h 0) "") kc)))))

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **Phase 2's windows' hypotheses** (`vsA_w7` … `vsA_w18`): the six tables' log heights `h t ≤ 24`
(`9 ≤ h 5`, the `KECCAK` table's floor) and row counts `R t ≤ 2^(h t)`, least for tables `0 ..< 5`
(`h t = 0` or `2^(h t - 1) < R t`), `table_size`'s returns in the oracle, the heights at `b6` and the row
counts at `b56` read by `rd0`, the bits' buffers `b7 + 26 t` own, they and the row counts read by every
memory holding `st.O`; `K` after the six dispatches. -/
theorem vsPh2_wins (hk : 6 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop} {b6 b7 b56 : ℕ}
    (h Rr : ℕ → ℕ) (h24 : ∀ t < 6, h t ≤ 24) (hR : ∀ t < 6, Rr t ≤ 2 ^ h t)
    (hl : ∀ t < 5, h t = 0 ∨ 2 ^ (h t - 1) < Rr t) (h9 : 9 ≤ h 5)
    (hw6 : w 6 = ptrAt b6) (hw7 : w 7 = ptrAt b7) (hw56 : w 56 = ptrAt b56)
    (hret : ∀ t < 6, w (tsRet t) = gen ^ Rr t ∧ w (tsRet t + 1) = tsLeadW (Rr t) (h t) ∧
      w (tsRet t + 2) = tsRestW (Rr t) (h t))
    (r6 : ReadsAt rd0 (ptrAt b6) [gen ^ h 0, gen ^ h 1, gen ^ h 2, gen ^ h 3, gen ^ h 4, gen ^ h 5])
    (r56 : ReadsAt rd0 (ptrAt b56) [eOfNat (Rr 0), eOfNat (Rr 1), eOfNat (Rr 2), eOfNat (Rr 3), eOfNat (Rr 4),
      eOfNat (Rr 5)])
    (hOb : ∀ j < 6, Own (b56 + j)) (hOc : ∀ j < 156, Own (b7 + j))
    (hrd : ∀ rd, st.O rd → ReadsAt rd (ptrAt b56) [eOfNat (Rr 0), eOfNat (Rr 1), eOfNat (Rr 2), eOfNat (Rr 3),
      eOfNat (Rr 4), eOfNat (Rr 5)] ∧ ∀ t < 6, ∀ c, c = b7 + 26 * t → ReadsAt rd (ptrAt c) (tsBitsW (Rr t) (h t)))
    (hK : K ⟨st.a, tsEnd fs al h st.kc, st.O, st.D, st.Qs ++ List.replicate 6 PostQuiet⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsA_w7, vsA_w8, vsA_w9, vsA_w10, vsA_w11, vsA_w12,
      vsA_w13, vsA_w14, vsA_w15, vsA_w16, vsA_w17, vsA_w18] st K := by
  set bs := [eOfNat (Rr 0), eOfNat (Rr 1), eOfNat (Rr 2), eOfNat (Rr 3), eOfNat (Rr 4), eOfNat (Rr 5)] with hbs
  obtain ⟨e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17⟩ := vsA_tables_eq
  have w17 := vsA_w7_17
  have hl17 : [vsA_w7, vsA_w8, vsA_w9, vsA_w10, vsA_w11, vsA_w12, vsA_w13, vsA_w14, vsA_w15, vsA_w16, vsA_w17,
      vsA_w18] = [vsA_w7, vsA_w8, vsA_w9, vsA_w10, vsA_w11, vsA_w12, vsA_w13, vsA_w14, vsA_w15, vsA_w16,
      vsA_w17] ++ [vsA_w18] := rfl
  rw [hl17, w17, vsA_w18_eq]
  obtain ⟨v115, v116, v117, v118, v119, v120, v144⟩ :=
    vsW6_vals (rd0 := rd0) (w := w) (args := args) ha hw6 hw56 (bs := bs) (by simp [hbs]) r6 r56
  have p7 := vsVal_7 (rd0 := rd0) (w := w) ha hw7
  have p56 := vsVal_56 (rd0 := rd0) (w := w) ha hw56
  have ret : ∀ {i : ℕ} {x av pv : ℕ} (t : ℕ), t < 6 → (vsA.drop i).take 1 = [tsDisp x av pv (tsRet t)] →
      vsVal rd0 w args (.n (tsRet t)) = gen ^ Rr t ∧
      vsVal rd0 w args (.n (tsRet t + 1)) = tsLeadW (Rr t) (h t) ∧
      vsVal rd0 w args (.n (tsRet t + 2)) = tsRestW (Rr t) (h t) := by
    intro i x av pv t ht e
    have hv := vsVal_disp_ret (rd0 := rd0) (w := w) ha e
    obtain ⟨a0, a1, a2⟩ := hret t ht
    exact ⟨(hv _ (by simp)).trans a0, (hv _ (by simp)).trans a1,
      (hv _ (by simp)).trans a2⟩
  obtain ⟨r0a, r0b, r0c⟩ := ret 0 (by norm_num) e7
  obtain ⟨r1a, r1b, r1c⟩ := ret 1 (by norm_num) e9
  obtain ⟨r2a, r2b, r2c⟩ := ret 2 (by norm_num) e11
  obtain ⟨r3a, r3b, r3c⟩ := ret 3 (by norm_num) e13
  obtain ⟨r4a, r4b, r4c⟩ := ret 4 (by norm_num) e15
  obtain ⟨r5a, r5b, r5c⟩ := ret 5 (by norm_num) e17
  have own : ∀ t < 6, ∀ j < h t + 1, Own (b7 + 26 * t + j) := fun t ht j hj => by
    rw [Nat.add_assoc]; exact hOc _ (by have := h24 t ht; omega)
  have rdt : ∀ t < 6, ∀ c, c = b7 + 26 * t → ∀ rd, st.O rd → ReadsAt rd (ptrAt c) (tsBitsW (Rr t) (h t)) ∧
      ReadsAt rd (ptrAt b56) bs := fun t ht c hc rd ho => ⟨(hrd rd ho).2 t ht c hc, (hrd rd ho).1⟩
  simp only [List.cons_append, List.nil_append]
  -- table 0
  refine ts_pair0 (O0 := st.O) hk (vsA_run_goodF ha e8) (rows_fresh (q := (157, 1)) (by decide))
    (h24 0 (by norm_num)) (hR 0 (by norm_num)) (hl 0 (by norm_num)) v115 v144 p7 r0a r0b r0c
    (h24 1 (by norm_num)) v116 p56 (by simp [hbs]) r56 (fun j hj => by simpa using own 0 (by norm_num) j hj)
    (hOb 1 (by norm_num)) (fun _ h => h) (rdt 0 (by norm_num) b7 (by ring)) fun v157 v159 => ?_
  -- table 1
  refine ts_pair (O0 := st.O) (xd := 116) (av := 157) (pv := 159) (n := 160) (x := 117) (pp := 145) (off := 2) hk (by norm_num) (by norm_num) (vsA_run_goodF ha e10)
    (rows_fresh (q := (173, 2)) (by decide)) (h24 1 (by norm_num)) (hR 1 (by norm_num)) (hl 1 (by norm_num))
    v116 v157 v159 r1a r1b r1c (h24 2 (by norm_num)) v117 p56 (by simp [hbs]) r56
    (fun j hj => by have := own 1 (by norm_num) j hj; rwa [show b7 + 26 * 1 = b7 + 26 by ring] at this)
    (hOb 2 (by norm_num)) (fun _ h => h.1) (rdt 1 (by norm_num) _ (by ring)) fun v173 v175 => ?_
  -- table 2
  refine ts_pair (O0 := st.O) (xd := 117) (av := 173) (pv := 175) (n := 176) (x := 118) (pp := 168) (off := 3) hk (by norm_num) (by norm_num) (vsA_run_goodF ha e12)
    (rows_fresh (q := (189, 3)) (by decide)) (h24 2 (by norm_num)) (hR 2 (by norm_num)) (hl 2 (by norm_num))
    v117 v173 v175 r2a r2b r2c (h24 3 (by norm_num)) v118 p56 (by simp [hbs]) r56
    (fun j hj => by have := own 2 (by norm_num) j hj; rwa [show b7 + 26 * 2 = b7 + 26 + 26 by ring] at this)
    (hOb 3 (by norm_num)) (fun _ h => h.1.1) (rdt 2 (by norm_num) _ (by ring)) fun v189 v191 => ?_
  -- table 3
  refine ts_pair (O0 := st.O) (xd := 118) (av := 189) (pv := 191) (n := 192) (x := 119) (pp := 184) (off := 4) hk (by norm_num) (by norm_num) (vsA_run_goodF ha e14)
    (rows_fresh (q := (205, 4)) (by decide)) (h24 3 (by norm_num)) (hR 3 (by norm_num)) (hl 3 (by norm_num))
    v118 v189 v191 r3a r3b r3c (h24 4 (by norm_num)) v119 p56 (by simp [hbs]) r56
    (fun j hj => by
      have := own 3 (by norm_num) j hj; rwa [show b7 + 26 * 3 = b7 + 26 + 26 + 26 by ring] at this)
    (hOb 4 (by norm_num)) (fun _ h => h.1.1.1) (rdt 3 (by norm_num) _ (by ring)) fun v205 v207 => ?_
  -- table 4
  refine ts_pair (O0 := st.O) (xd := 119) (av := 205) (pv := 207) (n := 208) (x := 120) (pp := 200) (off := 5) hk (by norm_num) (by norm_num) (vsA_run_goodF ha e16)
    (rows_fresh (q := (221, 5)) (by decide)) (h24 4 (by norm_num)) (hR 4 (by norm_num)) (hl 4 (by norm_num))
    v119 v205 v207 r4a r4b r4c (h24 5 (by norm_num)) v120 p56 (by simp [hbs]) r56
    (fun j hj => by
      have := own 4 (by norm_num) j hj; rwa [show b7 + 26 * 4 = b7 + 26 + 26 + 26 + 26 by ring] at this)
    (hOb 5 (by norm_num)) (fun _ h => h.1.1.1.1) (rdt 4 (by norm_num) _ (by ring)) fun v221 v223 => ?_
  -- table 5, then the selector's window
  refine ts_disp (h24 5 (by norm_num)) (hR 5 (by norm_num)) v120 v221 v223 r5a r5b r5c
    (fun j hj => by
      have := own 5 (by norm_num) j hj
      rwa [show b7 + 26 * 5 = b7 + 26 + 26 + 26 + 26 + 26 by ring] at this)
    (fun rd ho => (rdt 5 (by norm_num) _ (by ring) rd ho.1.1.1.1.1).1) ?_
  rw [WinsHyp]
  refine ⟨vsW18_runHyp hk ha h9 (h24 5 (by norm_num)) v120, ?_⟩
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => by simp) (fun i => by simp) (by simp [List.replicate])

/-- **The least-height branch** (`IteHyp` at `.n 234`): its selector in `K`; when the `KECCAK` table's height
`h5` is not its floor `9`, the arm's checks on its returns (`2^(h5 - 1) < R5`). -/
theorem vsPh2_sel (ha : args.length = 6) {st : St} {K : St → Prop} {h5 R5 : ℕ} (h9 : 9 ≤ h5)
    (h24 : h5 ≤ 24) (hR : R5 ≤ 2 ^ h5) (hl : h5 ≠ 9 → 2 ^ (h5 - 1) < R5)
    (h120 : vsVal rd0 w args (.n 120) = gen ^ h5) (hw1 : w 225 = tsLeadW R5 h5) (hw2 : w 226 = tsRestW R5 h5)
    (hK : K st) : IteHyp fs al cert k (vsVal rd0 w args) w Own R Pre (.n 234) [] wI1 st K := by
  obtain ⟨hin, hz⟩ := vs_sel234 ha h9 h24 h120
  refine ⟨hin, fun _ => hK, fun hne => ?_⟩
  have h5ne : h5 ≠ 9 := fun e => hne (hz.mpr e)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, e17⟩ := vsA_tables_eq
  have hv := vsVal_disp_ret (rd0 := rd0) (w := w) ha e17
  have v1 : vsVal rd0 w args (.n (224 + 1)) = tsLeadW R5 h5 := (hv _ (by simp)).trans hw1
  have v2 : vsVal rd0 w args (.n (224 + 2)) = tsRestW R5 h5 := (hv _ (by simp)).trans hw2
  have hg : ∀ a ∈ tsChk 224 235, Good rd0 (storesOf 235 vsI1f) w (vsVal rd0 w args) (fixA a) := by
    intro a hm
    rw [← vsI1n_atoms] at hm
    have hm' : Stmt.atom a ∈ vsI1n := by
      have := mem_atomsW (ws := wI1) (by simpa [atomsW, wI1] using hm)
      rwa [wI1_flat] at this
    exact vsVal_goodI1 ha hne (fixS (.atom a)) (List.mem_map_of_mem hm')
  simp only [wI1, vsI1n_atoms, WinsHyp]
  refine ⟨?_, hK⟩
  refine RunHyp.of_asks rfl (fun A hA => by simp [loadAddrs, tsChk, Ev.loadAddr?] at hA)
    (fun A hA => by
      rw [show heapHintAddrs (vsVal rd0 w args) ((tsChk 224 235).map Ev.atom) = [] from rfl] at hA
      simp at hA) (fun x hx => ?_)
    (fun rd _ _ _ x hx => by simp [tsChk, memAsks] at hx)
  exact tsChk_pureF hg h24 hR (Or.inr (hl h5ne)) v1 v2 x (List.mem_of_mem_filter hx)

end

end
end LeanVM.Guest.B1.VsC
