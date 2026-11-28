/-
  LeanVM.Guest.B1.VsC.CstVal

  `check_stack_terminal`'s checked value, from its atoms and what its callees give, without its
  final assertion: the converse direction of the assertion its completeness needs.
-/

module

public import LeanVM.Guest.B1.Stack.TermSound

/-!
# `check_stack_terminal`: the value it checks

`cst_value`: on any valuation whose statements before the final `assertEq` hold (`AllOk`) under the
call relation `CstC` (what the callees give: the selectors' buffer, `q_keccak`'s ring row, the ring
rows, a table's `ring_cols`, a prefix chain, each without the range checks), wherever `StackCtxAt`
holds of its parameters, the stacked claims exist and the value the assertion compares with the
claimed `target` is `(inner + stackedBasis claims lam x) · yr`. The proof is
`check_stack_terminal_sound`'s, its callees' meanings replaced by `CstC`'s facts.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.B1.VerifySub LeanVM.Guest.Value LeanVM.Guest.B1.Stack
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- What `rs_eq_run` gives: the returned row is the last ring row. -/
def RsRunC (rd : Reader) : List E → List E → Prop
  | [z, p1, cg, seed], rets =>
      ∃ count < 64, cg = gen ^ count ∧ ∃ zs ps c : List E, zs.length = count ∧ ps.length = count ∧
        c.length = 64 ∧ ReadsAt rd z zs ∧ ReadsAt rd p1 ps ∧ ReadsAt rd seed c ∧
        ∃ ret, rets = [ret] ∧ ∀ k < 64, LoadHolds rd ret k (ringRow (c.getD k 0) zs ps k)
  | _, _ => False

/-- What `eq_prefix_chain` gives: `MeaningEqPrefixChain` without its range check. -/
def EpcC (rd : Reader) : List E → List E → Prop
  | [chain, seed, a, b1, cg], rets => rets = [] ∧ ∃ n < 41, cg = gen ^ n ∧ EqPrefix rd chain seed a b1 n
  | _, _ => False

/-- **What `check_stack_terminal`'s callees give**, per name. -/
def CstC (rd : Reader) (layout : Layout) (x : List E) : CallRel := fun f args rets =>
  (f ∈ cstArms → ∃ sel, rets = [sel] ∧ ∀ b < 52, LoadHolds rd sel b (selW layout x b)) ∧
  (f = "rs_eq_run" → RsRunC rd args rets) ∧
  (f = "ring_rows" → MeaningRingRows rd args rets) ∧
  (∀ p ∈ ringColsNames, f = p.2 → MeaningRingCols p.1 rd args rets) ∧
  (f = "eq_prefix_chain" → EpcC rd args rets)

/-- The tail before the assertion. -/
def cstTail0 : List Stmt :=
  [osMul 919 918 14, osAdd 920 919 578, osMul 921 920 14, osAdd 922 571 921, osAdd 923 19 922, osMul 924 923 20]

theorem cstTail_eq : cstTail = cstTail0 ++ [.atom (.assertEq (.n 924) (.n 21))] := rfl

/-- `check_stack_terminal`'s statements before its tail. -/
def cstBodyB : List Stmt := cstHead ++ cstRowSum ++ cstRq ++ cstRing ++ cstMem ++ cstSent 633 629 sentList.reverse

theorem cstBodyA_eq : cstBodyA = cstBodyB ++ cstTail0 ++ [.atom (.assertEq (.n 924) (.n 21))] := by
  rw [cstBodyA, cstBodyB, cstTail_eq]; simp only [List.append_assoc]

/-- The parameters' words. -/
def cstValArgs (σ : Val) : List E :=
  [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9),
    σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17), σ (.n 18),
    σ (.n 19), σ (.n 20), σ (.n 21), σ (.n 22)]

variable {rd : Reader} {C : CallRel} {σ : Val}

theorem tail0_facts (hA : AllOk C rd σ cstTail0) :
    σ (.n 924) = (σ (.n 19) + (σ (.n 571) + (σ (.n 918) * σ (.n 14) + σ (.n 578)) * σ (.n 14))) * σ (.n 20) := by
  unfold cstTail0 at hA
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
  obtain ⟨m919, a920, m921, a922, a923, m924⟩ := hA
  rw [m924, a923, a922, m921, a920, m919]

/-- **A prefix chain from `1`**, from `EpcC`. -/
theorem chain_valC {chain a b1 : E} {n : ℕ} {as0 x : List E} (hx40 : x.length ≤ 40) (hn : n ≤ 40)
    (h : EpcC rd [chain, 1, a, b1, gen ^ n] []) (ha : ReadsAt rd a as0) (hlen : n ≤ as0.length)
    (hb : ReadsAt rd b1 (padX1 x)) :
    ∀ j ≤ n, j ≤ x.length → LoadHolds rd chain j (eqEval (as0.take j) (x.take j)) := by
  obtain ⟨-, n', hn', hcg, as, bs, hasl, hbsl, hra, hrb, hch⟩ := h
  have e : n' = n := gen_pow_inj (by omega) (by omega) hcg.symm
  subst e
  have has : as = as0.take n' := by rw [readsAt_prefix hra ha (by omega), hasl]
  have hbs : bs = (padX1 x).take n' := by
    rw [readsAt_prefix hrb hb (by rw [padX1_length x hx40]; omega), hbsl]
  intro j hj hjx
  have hpp : prefixProd 1 as bs j = prefixProd 1 as0 (padX1 x) j := by
    unfold prefixProd
    rw [has, hbs, List.take_take, List.take_take, min_eq_left hj]
  have := hch j hj
  rw [hpp, prefixProd_eq as0 x _ hjx] at this
  exact this

theorem cstArms_get_mem : ∀ j < 15, cstArms.getD j "" ∈ cstArms := by decide

set_option maxHeartbeats 1000000 in
/-- **`check_stack_terminal`'s checked value.** -/
theorem cst_value {layout : Layout} {link : LinkEnd} {chi r qPoint kOut kIn f g x z : List E} {rho lam rm : E}
    {outputs : List ColumnClaim} {keccakSlices : List E} {oodValue v0 v1 : E}
    (hA : AllOk (CstC rd layout x) rd σ cstBodyB) (hT : AllOk (CstC rd layout x) rd σ cstTail0)
    (hctx : StackCtxAt rd (cstValArgs σ) layout link chi r qPoint kOut kIn f g x z rho lam rm outputs) :
    ∃ claims, stackedClaims layout link (publicClaimsPure layout rm v0 v1) outputs kIn keccakSlices f g rho
        (fun y ↦ eqEval z y, oodValue) = some claims ∧
      σ (.n 924) = (σ (.n 19) + stackedBasis claims lam x) * σ (.n 20) := by
  obtain ⟨⟨bytecode, rows, hbl⟩, hexp, hkb, hplaced, hchiR, hgn, hchi24, hheights, hpieces, hcols, hqlen, heqq,
    hrR, hlmr, hglm, hmp, hgm1, hgm2, hrm, hzv, hkin, hout, hkoutl, hkinl, hf, hg, hct, hrho, hlam, hxl, hpt, hpt1,
    hzl, hoodz⟩ := hctx
  obtain ⟨claims, hclaims, hbasis⟩ := stackedBasis_pure (z := z) (rm := rm) (v0 := v0) (v1 := v1) (lam := lam)
    (oodValue := oodValue) (keccakSlices := keccakSlices) hbl link hpieces hcols hheights hmp hlmr hout hkoutl
    hf hg hxl
  refine ⟨claims, hclaims, ?_⟩
  rw [tail0_facts hT, hbasis]
  symm
  simp only [cstBodyB, allOk_append] at hA
  obtain ⟨⟨⟨⟨⟨hH, hR⟩, hQ⟩, hRing⟩, hMem⟩, hSent⟩ := hA
  set cs := ringCoefficients f g with hcsdef
  have hcs : cs.length = 64 := ringCoefficients_length f g hf hg
  -- the header: the stack's size, the selectors, the kappa sources
  obtain ⟨⟨j, hj, hjx, hselc⟩, hkbl, l52, l53, l54, hrs⟩ := head_facts hH
  have hL42 := stackLog_le hbl
  have hLj : layout.stackLog = 16 + j := by
    have hj' := hjx
    rw [hplaced.1, ← gen_pow_eq_ofK] at hj'
    have e : gen ^ layout.stackLog = gen ^ (16 + j) := by
      calc gen ^ layout.stackLog = gen ^ layout.stackLog * (gen ^ 16 * word 8198521646651277316 0) := by rw [gen16_inv, mul_one]
        _ = (gen ^ layout.stackLog * word 8198521646651277316 0) * gen ^ 16 := by ring
        _ = gen ^ (16 + j) := by rw [hj', ← pow_add, add_comm]
    exact gen_pow_inj (by omega) (by omega) e
  have hx40 : x.length ≤ 40 := by omega
  obtain ⟨sel, hsel43, hsel⟩ := hselc.1 (cstArms_get_mem j hj)
  simp only [List.cons.injEq, and_true] at hsel43
  subst hsel43
  have h52 : σ (.n 52) = selW layout x 2 := loadHolds_unique l52 (hsel 2 (by decide))
  have h53 : σ (.n 53) = selW layout x 0 := loadHolds_unique l53 (hsel 0 (by decide))
  have h54 : σ (.n 54) = selW layout x 1 := loadHolds_unique l54 (hsel 1 (by decide))
  have hkbv : ∀ t < 6, σ (.n (46 + t)) = gen ^ hgt layout t := fun t ht ↦ by
    have := loadHolds_unique (hkbl (2 + t) (by omega)) (kappaSources_get hkb (2 + t) (by omega))
    rw [show 44 + (2 + t) = 46 + t by omega] at this
    rw [this]
    simp [kvOf, hgt, show 2 + t ≠ 1 by omega]
  have h51 : σ (.n 51) = gen ^ hgt layout 5 := hkbv 5 (by decide)
  -- the bounds
  have hq6 : hgt layout 5 + 6 ≤ layout.stackLog := by
    have := (block_placed hbl (b := 2) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 2) (by decide)).2.1, (blockKap_eq layout).2.2] at this
  have hlmL : layout.logMemory ≤ layout.stackLog := by
    have := (block_placed hbl (b := 0) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 0) (by decide)).2.1, (blockKap_eq layout).1] at this
  have htL : ∀ t < 6, hgt layout t ≤ layout.stackLog := fun t ht ↦ by
    obtain ⟨b, hb, hsrc, hc⟩ := table_block t ht
    have := (block_placed hbl hb).2.2.2
    rwa [(block_placed hbl hb).2.1, blockKap, layout_kappa _ _ hc hsrc] at this
  have hchiT : ∀ t < 6, hgt layout t ≤ chi.length := fun t ht ↦ hheights t ht
  -- q_keccak's ring row
  obtain ⟨count, hc64, hcg, zs, ps, c, hzsl, hpsl, hcsl, hrz, hrp, hrc, ret, hret59, hrows⟩ := hrs.2.1 rfl
  rw [h51, ← pow_add] at hcg
  have hcount : count = hgt layout 5 + 6 := gen_pow_inj (by omega) (by omega) hcg.symm
  subst hcount
  have hzs : zs = kIn := readsAt_eq hrz hkin (by rw [hzsl, hkinl, hkoutl]; rfl)
  have hc : c = cs := readsAt_eq hrc hct (by rw [hcsl, hcs])
  have hps : ps = (padX1 x).take (hgt layout 5 + 6) := by
    rw [readsAt_prefix hrp hpt1 (by rw [padX1_length x hx40]; omega), hpsl]
  simp only [List.cons.injEq, and_true] at hret59
  obtain ⟨hrowv, h187⟩ := rowSum_facts hR
  have hrowk : ∀ k < 64, rowV σ k = cs.getD k 0 * eqEval (kIn.map (· ^ 2 ^ k)) (x.take (hgt layout 5 + 6)) := by
    intro k hk
    have h1 := hrowv k hk
    rw [hret59] at h1
    have h2 := hrows k hk
    rw [hzs, hc, hps, padX1_take x (by omega), ringRow_eq] at h2
    exact loadHolds_unique h1 h2
  have hkin6 : kIn.length = hgt layout 5 + 6 := by rw [hkinl, hkoutl]; rfl
  have h187' : σ (.n 187) = ringT cs x kIn (selW layout x 2) 1 := by
    rw [h187, h52, ringT, Finset.sum_mul, hkin6]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [hrowk k (Finset.mem_range.1 hk), one_pow, mul_one]
  -- the pointers' scales
  have hek : (eqKernel qPoint).length = 64 := by rw [length_eqKernel_eq, hqlen]; rfl
  have hscl : ∀ q < 33, LoadHolds rd (σ (.n 33)) q (rho * (eqKernel qPoint).getD q 0) := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := rq_facts hQ q hq
    have h4 := readsAt_getD' heqq (i := q) (by simp [hek]; omega)
    rw [loadHolds_mul_gen_pow] at h4
    have e : ((eqKernel qPoint).take 33).getD q 0 = (eqKernel qPoint).getD q 0 := by
      simp [List.getD_eq_getElem?_getD, hq]
    rw [e] at h4
    rw [h2, hrho, loadHolds_unique h1 h4] at h3
    exact h3
  -- the ring rows and the slots' weights
  obtain ⟨hrr, h254, het, ht0, ht1, ht2, ht3, ht4, ht5, h571⟩ := ring_facts hRing
  have hRRm := hrr.2.2.1 rfl
  rw [hgn] at hRRm
  have hRR := ringRows_val hx40 (by omega) hRRm hchiR hpt1 hct hcs
  have hrs6 : ((x.drop (hgt layout 5)).take 6).length = 6 := by simp; omega
  have hpt6 : ∀ t < 6, LoadHolds rd (σ (.n 254)) (0 + t) (((x.drop (hgt layout 5)).take 6).getD t 0) := by
    intro t ht
    rw [h254, h51, loadHolds_mul_gen_pow, Nat.zero_add]
    have := readsAt_getD' hpt (i := hgt layout 5 + t) (by simp; omega)
    have e : (x ++ List.replicate (40 - x.length) 0).getD (hgt layout 5 + t) 0 =
        ((x.drop (hgt layout 5)).take 6).getD t 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show hgt layout 5 + t < x.length by omega), ht]
    rwa [e] at this
  have hkern := eqtree_sound (rd := rd) (σ := σ) (p := .n 254) (o := .n 39) (po := 0) (b := 255) (n := 6)
    (by norm_num) het hrs6 hpt6 6 (by norm_num) le_rfl
  have hkern' : ∀ s < 64, LoadHolds rd (σ (.n 39)) (s + 62) (kernW layout x s) := by
    intro s hs
    have := hkern s (by norm_num; exact hs)
    rw [List.take_of_length_le (by rw [hrs6])] at this
    rw [show s + 62 = 2 ^ 6 - 2 + s by norm_num; omega]
    exact this
  have hmaskv : ∀ k < 116, ∀ val, (k < 52 → LoadHolds rd (σ (.n 43)) k val) →
      (52 ≤ k → ∃ w, LoadHolds rd (σ (.n 39)) (k + 10) w ∧ val = w * σ (.n 52)) → val = maskW layout x k := by
    intro k hk val hb hs
    by_cases hk52 : k < 52
    · simp only [maskW, hk52, ↓reduceIte]
      exact loadHolds_unique (hb hk52) (hsel k hk52)
    · obtain ⟨w, hw, hv⟩ := hs (by omega)
      simp only [maskW, hk52, ↓reduceIte]
      have hw' := hkern' (k - 52) (by omega)
      rw [show k - 52 + 62 = k + 10 by omega] at hw'
      rw [hv, h52, loadHolds_unique hw hw']
  -- the tables
  have hkinds : ∀ q < 33, ptrKinds.getD q 0 < 116 := fun q hq ↦ by
    obtain ⟨⟨-, -, -, -, -, -, hk⟩, hne⟩ := ptr_ok.2 q hq
    omega
  have htab : ∀ (t q0 n : ℕ) (rowp sclp mskp ret : E), t < 6 → q0 + n ≤ 33 →
      (∀ i < n, ptrTab.getD (q0 + i) 0 = t) → MeaningRingCols n rd [rowp, sclp, mskp] [ret] →
      rowp = σ (.n 31) * gen ^ (64 * hgt layout t) → sclp = σ (.n 33) * gen ^ q0 → mskp = σ (.n 32) * gen ^ q0 →
      (∀ i < n, ∃ val, LoadHolds rd (σ (.n 32)) (q0 + i) val ∧
        (ptrKinds.getD (q0 + i) 0 < 52 → LoadHolds rd (σ (.n 43)) (ptrKinds.getD (q0 + i) 0) val) ∧
        (52 ≤ ptrKinds.getD (q0 + i) 0 → ∃ w, LoadHolds rd (σ (.n 39)) (ptrKinds.getD (q0 + i) 0 + 10) w ∧
          val = w * σ (.n 52))) →
      ret = ∑ i ∈ Finset.range n, ringT cs x (chi.take (hgt layout (ptrTab.getD (q0 + i) 0)))
        (maskW layout x (ptrKinds.getD (q0 + i) 0)) (rho * (eqKernel qPoint).getD (q0 + i) 0) := by
    intro t q0 n rowp sclp mskp ret ht hq0 htq hrc hrow hscp hmsp hms
    have hsum := table_sum hrc (fun k ↦ cs.getD k 0 * eqEval ((chi.take (hgt layout t)).map (· ^ 2 ^ k))
        (x.take (hgt layout t))) (fun i ↦ rho * (eqKernel qPoint).getD (q0 + i) 0)
      (fun i ↦ maskW layout x (ptrKinds.getD (q0 + i) 0))
      (fun k hk ↦ by
        rw [hrow, loadHolds_mul_gen_pow]
        exact hRR _ (hchiT t ht) (by rw [hxl]; exact htL t ht) k hk)
      (fun i hi ↦ by rw [hscp, loadHolds_mul_gen_pow]; exact hscl _ (by omega))
      (fun i hi ↦ by
        obtain ⟨val, h1, h2, h3⟩ := hms i hi
        rw [hmsp, loadHolds_mul_gen_pow, ← hmaskv _ (hkinds _ (by omega)) val h2 h3]
        exact h1)
    rw [hsum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [htq i (Finset.mem_range.1 hi), ringT, Finset.mul_sum,
      List.length_take, min_eq_left (hchiT t ht)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have hrcL : ∀ p ∈ ringColsNames, ∀ args rets, CstC rd layout x p.2 args rets → MeaningRingCols p.1 rd args rets :=
    fun p hp args rets h ↦ h.2.2.2.1 p hp rfl
  have hmconv : ∀ (q0 : ℕ) (ks : List ℕ), (∀ i < ks.length, ks.getD i 0 = ptrKinds.getD (q0 + i) 0) →
      (∀ i < ks.length, ∃ val, LoadHolds rd (σ (.n 32)) (q0 + i) val ∧
        (ks.getD i 0 < 52 → LoadHolds rd (σ (.n 43)) (ks.getD i 0) val) ∧
        (52 ≤ ks.getD i 0 → ∃ w, LoadHolds rd (σ (.n 39)) (ks.getD i 0 + 10) w ∧ val = w * σ (.n 52))) →
      ∀ i < ks.length, ∃ val, LoadHolds rd (σ (.n 32)) (q0 + i) val ∧
        (ptrKinds.getD (q0 + i) 0 < 52 → LoadHolds rd (σ (.n 43)) (ptrKinds.getD (q0 + i) 0) val) ∧
        (52 ≤ ptrKinds.getD (q0 + i) 0 → ∃ w, LoadHolds rd (σ (.n 39)) (ptrKinds.getD (q0 + i) 0 + 10) w ∧
          val = w * σ (.n 52)) := by
    intro q0 ks he hm i hi
    rw [← he i hi]
    exact hm i hi
  have hk46 : σ (.n 46) = gen ^ hgt layout 0 := hkbv 0 (by decide)
  have hk47 : σ (.n 47) = gen ^ hgt layout 1 := hkbv 1 (by decide)
  have hk48 : σ (.n 48) = gen ^ hgt layout 2 := hkbv 2 (by decide)
  have hk49 : σ (.n 49) = gen ^ hgt layout 3 := hkbv 3 (by decide)
  have hk50 : σ (.n 50) = gen ^ hgt layout 4 := hkbv 4 (by decide)
  -- table 0
  obtain ⟨hm0, hc0⟩ := tab0_facts ht0
  have hr0 := htab 0 0 5 _ _ _ _ (by decide) (by decide) (by decide)
    (hrcL (5, "ring_cols__L5") (by decide) _ _ hc0) (by rw [hk46, ← pow_mul, Nat.mul_comm]) (by simp) (by simp)
    (fun i hi ↦ by
      obtain ⟨val, h1, h2⟩ := hm0 i hi
      have e : [9, 8, 5, 6, 7].getD i 0 = ptrKinds.getD (0 + i) 0 := by interval_cases i <;> rfl
      have e52 : ptrKinds.getD (0 + i) 0 < 52 := by interval_cases i <;> decide
      exact ⟨val, by simpa using h1, fun _ ↦ e ▸ h2, fun h ↦ absurd h (by omega)⟩)
  -- tables 1 to 5
  obtain ⟨hm1, hc1, hs1, h81, h101⟩ := tab_facts ht1
  obtain ⟨hm2, hc2, hs2, h82, h102⟩ := tab_facts ht2
  obtain ⟨hm3, hc3, hs3, h83, h103⟩ := tab_facts ht3
  obtain ⟨hm4, hc4, hs4, h84, h104⟩ := tab_facts ht4
  obtain ⟨hm5, hc5, hs5, h85, h105⟩ := tab_facts ht5
  have hc1' : CstC rd layout x "ring_cols__L5" [σ (.n 31) * σ (.n 47) ^ 64, σ (.n 33) * word 32 0,
      σ (.n 32) * word 32 0] [σ (.n 488)] := hc1
  have h81' : σ (.n 485) = σ (.n 33) * word 32 0 := h81
  have h101' : σ (.n 487) = σ (.n 32) * word 32 0 := h101
  have hs1' : σ (.n 489) = σ (.n 471) + σ (.n 488) := hs1
  have hc2' : CstC rd layout x "ring_cols__L3" [σ (.n 31) * σ (.n 48) ^ 64, σ (.n 485) * word 32 0,
      σ (.n 487) * word 32 0] [σ (.n 504)] := hc2
  have hs2' : σ (.n 505) = σ (.n 489) + σ (.n 504) := hs2
  have hc3' : CstC rd layout x "ring_cols__L5" [σ (.n 31) * σ (.n 49) ^ 64, σ (.n 33) * word 8192 0,
      σ (.n 32) * word 8192 0] [σ (.n 522)] := hc3
  have h83' : σ (.n 519) = σ (.n 33) * word 8192 0 := h83
  have h103' : σ (.n 521) = σ (.n 32) * word 8192 0 := h103
  have hs3' : σ (.n 523) = σ (.n 505) + σ (.n 522) := hs3
  have hc4' : CstC rd layout x "ring_cols__L5" [σ (.n 31) * σ (.n 50) ^ 64, σ (.n 519) * word 32 0,
      σ (.n 521) * word 32 0] [σ (.n 540)] := hc4
  have h84' : σ (.n 537) = σ (.n 519) * word 32 0 := h84
  have h104' : σ (.n 539) = σ (.n 521) * word 32 0 := h104
  have hs4' : σ (.n 541) = σ (.n 523) + σ (.n 540) := hs4
  have hc5' : CstC rd layout x "ring_cols__L10" [σ (.n 31) * σ (.n 51) ^ 64, σ (.n 537) * word 32 0,
      σ (.n 539) * word 32 0] [σ (.n 569)] := hc5
  have hs5' : σ (.n 570) = σ (.n 541) + σ (.n 569) := hs5
  have hr1 := htab 1 5 5 _ _ _ _ (by decide) (by decide) (by decide)
    (hrcL (5, "ring_cols__L5") (by decide) _ _ hc1') (by rw [hk47, ← pow_mul, Nat.mul_comm]) (by rw [word_g5])
    (by rw [word_g5]) (hmconv 5 _ (by decide) hm1)
  have hr2 := htab 2 10 3 _ _ _ _ (by decide) (by decide) (by decide)
    (hrcL (3, "ring_cols__L3") (by decide) _ _ hc2') (by rw [hk48, ← pow_mul, Nat.mul_comm])
    (by rw [h81', word_g5, mul_assoc, ← pow_add]) (by rw [h101', word_g5, mul_assoc, ← pow_add])
    (hmconv 10 _ (by decide) hm2)
  have hr3 := htab 3 13 5 _ _ _ _ (by decide) (by decide) (by decide)
    (hrcL (5, "ring_cols__L5") (by decide) _ _ hc3') (by rw [hk49, ← pow_mul, Nat.mul_comm]) (by rw [word_g13])
    (by rw [word_g13]) (hmconv 13 _ (by decide) hm3)
  have hr4 := htab 4 18 5 _ _ _ _ (by decide) (by decide) (by decide)
    (hrcL (5, "ring_cols__L5") (by decide) _ _ hc4') (by rw [hk50, ← pow_mul, Nat.mul_comm])
    (by rw [h83', word_g13, word_g5, mul_assoc, ← pow_add]) (by rw [h103', word_g13, word_g5, mul_assoc, ← pow_add])
    (hmconv 18 _ (by decide) hm4)
  have hr5 := htab 5 23 10 _ _ _ _ (by decide) (by decide) (by decide)
    (hrcL (10, "ring_cols__L10") (by decide) _ _ hc5') (by rw [h51, ← pow_mul, Nat.mul_comm])
    (by rw [h84', h83', word_g13, word_g5, mul_assoc, mul_assoc, ← pow_add, ← pow_add])
    (by rw [h104', h103', word_g13, word_g5, mul_assoc, mul_assoc, ← pow_add, ← pow_add])
    (hmconv 23 _ (by decide) hm5)
  have hsplit : ∀ G : ℕ → E, ∑ q ∈ Finset.range 33, G q = ∑ i ∈ Finset.range 5, G i +
      ∑ i ∈ Finset.range 5, G (5 + i) + ∑ i ∈ Finset.range 3, G (10 + i) + ∑ i ∈ Finset.range 5, G (13 + i) +
      ∑ i ∈ Finset.range 5, G (18 + i) + ∑ i ∈ Finset.range 10, G (23 + i) := by
    intro G
    rw [(Finset.sum_range_add G 23 10 : ∑ q ∈ Finset.range 33, G q = _),
      (Finset.sum_range_add G 18 5 : ∑ q ∈ Finset.range 23, G q = _),
      (Finset.sum_range_add G 13 5 : ∑ q ∈ Finset.range 18, G q = _),
      (Finset.sum_range_add G 10 3 : ∑ q ∈ Finset.range 13, G q = _),
      (Finset.sum_range_add G 5 5 : ∑ q ∈ Finset.range 10, G q = _)]
  simp only [Nat.zero_add] at hr0
  have hring : σ (.n 571) = ringPure layout x chi qPoint kIn f g rho := by
    rw [h571, h187', ringPure, ← hcsdef, hsplit, hs5', hs4', hs3', hs2', hs1', hr0, hr1, hr2, hr3, hr4, hr5]
  -- the prefix chains
  obtain ⟨ch1, l574, h578, l9, hz30, ch2, l611, ch3, ch4, ch5, l618, l621, l631, h629, h632⟩ := mem_facts hMem
  rw [hglm] at ch1 ch2 l574 l611
  rw [h51, ← pow_add] at ch3
  rw [hplaced.1] at ch4 l618
  rw [hgn] at ch5
  rw [h51] at l621 l631
  rw [loadHolds_mul_gen_pow, Nat.add_zero] at l574 l611 l618 l631
  rw [loadHolds_mul_gen_pow] at l621
  have hmemc := chain_valC hx40 (by omega) (ch1.2.2.2.2 rfl) hrR hlmr hpt1 _ le_rfl (by omega)
  have hpiR : ReadsAt rd (σ (.n 38)) (rm :: List.replicate 30 0) := fun k hk ↦ by
    rcases k with _ | k
    · simpa [hrm] using l9
    · have hk' : k < 30 := by rw [List.length_cons, List.length_replicate] at hk; omega
      rw [List.getElem_cons_succ, List.getElem_replicate]
      exact hz30 k hk'
  have hpic := chain_valC hx40 (by omega) (ch2.2.2.2.2 rfl) hpiR (by simp; omega) hpt1 _ le_rfl (by omega)
  have houtc := chain_valC hx40 (by omega) (ch3.2.2.2.2 rfl) hzv (by rw [hkoutl]; exact le_refl _) hpt1 _ le_rfl
    (by omega)
  have hoodc := chain_valC hx40 (by omega) (ch4.2.2.2.2 rfl) hoodz (by rw [hzl]) hpt1 _ le_rfl (by omega)
  have hchic := chain_valC hx40 (by omega) (ch5.2.2.2.2 rfl) hchiR le_rfl hpt1
  have h574 := loadHolds_unique l574 hmemc
  have h611 := loadHolds_unique l611 hpic
  have h621 := loadHolds_unique l621 houtc
  have h618 := loadHolds_unique l618 hoodc
  have h631 := loadHolds_unique l631 (hchic _ (hchiT 5 (by decide)) (by omega))
  have hmem : σ (.n 578) = eqEval (r.take layout.logMemory) (x.take layout.logMemory) *
      (link.memoryScales.1 * selW layout x 0 + link.memoryScales.2 * selW layout x 1) := by
    rw [h578, h574, hgm1, hgm2, h53, h54]
  have hpitake : (rm :: List.replicate 30 0).take layout.logMemory =
      rm :: List.replicate (layout.logMemory - 1) 0 := by
    obtain ⟨l, hl⟩ : ∃ l, layout.logMemory = l + 1 := ⟨layout.logMemory - 1, by have := buildLayout_lm hbl; omega⟩
    rw [hl, List.take_succ_cons, List.take_replicate, Nat.add_sub_cancel, min_eq_left (by omega)]
  -- the sent columns
  have hW : ∀ k ∈ sentList.reverse, (k < 52 → ∀ a b c, LoadHolds rd (σ (.n 3)) k a →
      LoadHolds rd (σ (.n 34) * a) 0 b → LoadHolds rd (σ (.n 43)) k c → b * c = sentPure layout x chi k) ∧
      (52 ≤ k → ∀ a, LoadHolds rd (σ (.n 39)) (k + 10) a → σ (.n 632) * a = sentPure layout x chi k) := by
    intro k hk
    obtain ⟨hk116, hkb⟩ := sentList_facts k (List.mem_reverse.1 hk)
    refine ⟨fun hk52 a b c ha hb hc ↦ ?_, fun hk52 a ha ↦ ?_⟩
    · obtain ⟨t, ht, hsrc, hcl⟩ := hkb hk52
      obtain ⟨p, hp, -, hkap⟩ := hplaced.2 k (by simpa [nStkBlocks, stackBlocks_length] using hk52)
      have hP : blockP layout k = p := by rw [blockP, hp]; rfl
      rw [loadHolds_unique ha hkap, loadHolds_mul_gen_pow, Nat.add_zero] at hb
      have hvc : p.variableCount = hgt layout t := by
        rw [← hP, (block_placed hbl hk52).2.1, blockKap, layout_kappa _ _ hcl hsrc]; rfl
      have hb' := hchic p.variableCount (by rw [hvc]; exact hchiT t ht) (by rw [hvc, hxl]; exact htL t ht)
      rw [loadHolds_unique hb hb', loadHolds_unique hc (hsel k hk52)]
      simp only [sentPure, hk52, ↓reduceIte, hP]
    · have hka := hkern' (k - 52) (by omega)
      rw [show k - 52 + 62 = k + 10 by omega] at hka
      rw [loadHolds_unique ha hka, h632, h631, h52]
      simp only [sentPure, show ¬ k < 52 by omega, ↓reduceIte]
  have h918 := sent_facts (sentPure layout x chi) sentList.reverse 633 629 hSent hW
  rw [sentAcc_eq, hlam, foldl_reverse_hornerT] at h918
  -- the basis
  rw [hring, hmem, h918, hlam, basisPure, tailPure, hornerL_append, h629, h618, h621, h611, h52, h53, h54,
    hpitake, hlam]
  simp only [hornerL, ← hxl, List.take_length, List.take_of_length_le (show z.length ≤ x.length by omega),
    List.take_of_length_le (show kOut.length ≤ hgt layout 5 + 6 by rw [hkoutl]; rfl)]
  ring_nf

end
end LeanVM.Guest.B1.VsC
