/-
  LeanVM.Guest.B1.Stack.TermSound

  `check_stack_terminal` is sound: the terminal's check against the stacked claims' basis.
-/

module

public import LeanVM.Guest.B1.Stack.TermFacts
public import LeanVM.Guest.B1.Eq.RingRows
public import LeanVM.Guest.B1.Eq.EqPrefix

/-!
# `check_stack_terminal`, sound

`check_stack_terminal_sound`: on a memory image of `2^κ` words, `6 ≤ κ ≤ 32`, a call of
`check_stack_terminal` gives `MeaningCheckStackTerminal`. From the template's segments
(`TermFacts`) and the callees' meanings, the guest's value is `basisPure` (`TermPure`), which is the
basis of the stacked claims `verifyExecution` makes (`stackedBasis_pure`):

* the selectors are the blocks' `eqAbove` (`stack_selectors_holds`), at the stack's size the
  dispatch reads;
* the prefix chains are `eq` of their points and `x` (`chain_val`), the ring rows `c_k` times `eq` of
  the row point's Frobenius powers (`ringRows_val`), a table's `ring_cols` the sum of its pointers'
  terms (`table_sum`);
* the sent columns' fold is Horner's (`foldl_reverse_hornerT`).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.B1.VerifySub LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## Padded points -/

/-- The opening point's words at `point1`: `1 + x`, then ones to `40`. -/
abbrev padX1 (x : List E) : List E := x.map (1 + ·) ++ List.replicate (40 - x.length) 1

theorem padX1_take (x : List E) {j : ℕ} (hj : j ≤ x.length) : (padX1 x).take j = (x.take j).map (1 + ·) := by
  rw [padX1, List.take_append_of_le_length (by simpa using hj), List.map_take]

theorem padX1_length (x : List E) (hx : x.length ≤ 40) : (padX1 x).length = 40 := by simp; omega

theorem readsAt_getD' {p : E} {xs : List E} (h : ReadsAt rd p xs) {i : ℕ} (hi : i < xs.length) :
    LoadHolds rd p i (xs.getD i 0) := by
  rw [List.getD_eq_getElem _ _ hi]
  exact h i hi

theorem readsAt_eq {p : E} {l1 l2 : List E} (h1 : ReadsAt rd p l1) (h2 : ReadsAt rd p l2)
    (hl : l1.length = l2.length) : l1 = l2 :=
  List.ext_getElem hl fun k hk1 hk2 ↦ loadHolds_unique (h1 k hk1) (h2 k hk2)

/-! ## The callees -/

/-- **A prefix chain from `1`**: entry `j` is `eq` of the read words and `x` over the first `j`. -/
theorem chain_val {chain a b1 : E} {n : ℕ} {as0 x : List E} (hx40 : x.length ≤ 40) (hn : n ≤ 40)
    (h : MeaningEqPrefixChain rd [chain, 1, a, b1, gen ^ n] []) (ha : ReadsAt rd a as0) (hlen : n ≤ as0.length)
    (hb : ReadsAt rd b1 (padX1 x)) :
    ∀ j ≤ n, j ≤ x.length → LoadHolds rd chain j (eqEval (as0.take j) (x.take j)) := by
  obtain ⟨-, -, n', hn', hcg, as, bs, hasl, hbsl, hra, hrb, hch⟩ := h
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

/-- **The ring rows**: row `h` is `c_k` times `eq` of the row point's first `h` coordinates' `2^k`-th
powers and `x`. -/
theorem ringRows_val {chain zA b1 ct : E} {chi x cs : List E} (hx40 : x.length ≤ 40) (hchi40 : chi.length ≤ 40)
    (h : MeaningRingRows rd [chain, zA, b1, ct, gen ^ chi.length] []) (hz : ReadsAt rd zA chi)
    (hb : ReadsAt rd b1 (padX1 x)) (hct : ReadsAt rd ct cs) (hcs : cs.length = 64) :
    ∀ hh ≤ chi.length, hh ≤ x.length → ∀ k < 64,
      LoadHolds rd chain (64 * hh + k) (cs.getD k 0 * eqEval ((chi.take hh).map (· ^ 2 ^ k)) (x.take hh)) := by
  obtain ⟨count, hc64, hcg, zs, ps, c, hzl, hpl, hcl, hrz, hrp, hrc, hrch, hrows, -⟩ := h
  have e : count = chi.length := gen_pow_inj (by omega) (by omega) hcg.symm
  subst e
  have hzs : zs = chi := readsAt_eq hrz hz hzl
  have hc : c = cs := readsAt_eq hrc hct (by rw [hcl, hcs])
  have hps : ps = (padX1 x).take zs.length := by
    rw [readsAt_prefix hrp hb (by rw [padX1_length x hx40]; omega), hpl, hzl]
  subst hzs hc
  intro hh hhc hhx k hk
  rcases Nat.eq_zero_or_pos hh with rfl | hpos
  · simpa [eqEval] using readsAt_getD' hrch (by omega : k < c.length)
  · have := hrows hh hpos hhc k hk
    rw [hps, List.take_take, min_eq_left hhc, padX1_take x hhx, ringRow_eq] at this
    exact this

/-- **A table's `ring_cols`**: `Σ_i m_i Σ_k r_k s_i^(2^k)` at the words it reads. -/
theorem table_sum {row scl msk ret : E} {n : ℕ} (h : MeaningRingCols n rd [row, scl, msk] [ret])
    (R S M : ℕ → E) (hR : ∀ k < 64, LoadHolds rd row k (R k)) (hS : ∀ i < n, LoadHolds rd scl i (S i))
    (hM : ∀ i < n, LoadHolds rd msk i (M i)) :
    ret = ∑ i ∈ Finset.range n, M i * ∑ k ∈ Finset.range 64, R k * S i ^ 2 ^ k := by
  obtain ⟨rs, ss, ms, hrl, hsl, hml, hrr, hrs, hrm, hret⟩ := h
  simp only [List.cons.injEq, and_true] at hret
  rw [hret]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := Finset.mem_range.1 hi
  rw [loadHolds_unique (readsAt_getD' hrm (by omega)) (hM i hi),
    loadHolds_unique (readsAt_getD' hrs (by omega)) (hS i hi), frobSum]
  refine congrArg (M i * ·) (Finset.sum_congr rfl fun k hk ↦ ?_)
  have hk : k < 64 := Finset.mem_range.1 hk
  rw [loadHolds_unique (readsAt_getD' hrr (by rw [hrl]; exact hk)) (hR k hk)]

/-! ## Horner -/

/-- Horner in `λ` onto a tail value. -/
def hornerT (lam : E) : List E → E → E
  | [], t => t
  | a :: l, t => a + lam * hornerT lam l t

theorem hornerL_append (lam : E) : ∀ A B : List E, hornerL lam (A ++ B) = hornerT lam A (hornerL lam B)
  | [], _ => rfl
  | a :: A, B => by rw [List.cons_append, hornerL, hornerL_append lam A B, hornerT]

theorem foldl_reverse_hornerT (lam : E) (W : ℕ → E) (a0 : E) : ∀ l : List ℕ,
    l.reverse.foldl (fun a k ↦ a * lam + W k) a0 = hornerT lam (l.map W) a0
  | [] => rfl
  | k :: l => by
    rw [List.reverse_cons, List.foldl_append, foldl_reverse_hornerT lam W a0 l, List.map_cons, hornerT]
    simp only [List.foldl_cons, List.foldl_nil]
    ring

/-! ## The theorem -/

set_option maxRecDepth 100000 in
theorem cstBodyA_flat : cstBodyA.all Stmt.flat = true := by decide +kernel

theorem cst_params : (fn% «check_stack_terminal»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7,
    .n 8, .n 9, .n 10, .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17, .n 18, .n 19, .n 20, .n 21, .n 22] := rfl

theorem sentList_facts : ∀ k ∈ sentList, k < 116 ∧ (k < 52 → ∃ t < 6,
    colSrc.getD (blockColumn k) (0, 0) = (2 + t, 0) ∧ blockColumn k < colSrc.length) := by decide +kernel

theorem sentAcc_eq : sentAcc 633 629 sentList.reverse = 918 := by decide

/-- **`check_stack_terminal` gives its meaning.** -/
theorem check_stack_terminal_sound {κ : ℕ} (hκ6 : 6 ≤ κ) (hκ : κ ≤ 32) (L : MemoryImage κ) (args rets : List E)
    (h : coreProgram.Rel L.read "check_stack_terminal" args rets) : MeaningCheckStackTerminal L.read args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem (coreProgram_find?_at (j := idx% «check_stack_terminal») rfl) args rets).mp h
  rw [cst_params] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [check_stack_terminal_body, cstBody, holdsList_flat_ret _ cstBodyA_flat] at hb
  obtain ⟨hA, hret⟩ := hb
  refine ⟨by simpa using hret.symm, ?_⟩
  intro layout link chi r qPoint kOut kIn f g x z rho lam rm outputs keccakSlices oodValue v0 v1 hctx
  obtain ⟨⟨bytecode, rows, hbl⟩, hexp, hkb, hplaced, hchiR, hgn, hchi24, hheights, hpieces, hcols, hqlen, heqq,
    hrR, hlmr, hglm, hmp, hgm1, hgm2, hrm, hzv, hkin, hout, hkoutl, hkinl, hf, hg, hct, hrho, hlam, hxl, hpt, hpt1,
    hzl, hoodz⟩ := hctx
  obtain ⟨claims, hclaims, hbasis⟩ := stackedBasis_pure (z := z) (rm := rm) (v0 := v0) (v1 := v1) (lam := lam)
    (oodValue := oodValue) (keccakSlices := keccakSlices) hbl link hpieces hcols hheights hmp hlmr hout hkoutl
    hf hg hxl
  refine ⟨claims, hclaims, ?_⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [hbasis]
  simp only [cstBodyA, allOk_append] at hA
  obtain ⟨⟨⟨⟨⟨⟨hH, hR⟩, hQ⟩, hRing⟩, hMem⟩, hSent⟩, hTail⟩ := hA
  rw [← tail_facts hTail]
  set rd := L.read with hrd
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
  have hL30 : layout.stackLog ≤ 30 := by omega
  have hx40 : x.length ≤ 40 := by omega
  obtain ⟨sel, hsel43, hselb⟩ := stack_selectors_holds hκ hκ6 L _ (cstArms_mem j hj) _ _ hselc layout
    (σ (.n 4)) x ⟨bytecode, rows, hbl⟩ hplaced hxl (by omega) hexp hpt hpt1
  simp only [List.cons.injEq, and_true] at hsel43
  subst hsel43
  have hsel : ∀ b < 52, LoadHolds rd (σ (.n 43)) b (selW layout x b) := fun b hb ↦ by
    obtain ⟨p, hp, hl⟩ := hselb b (by simpa [nStkBlocks, stackBlocks_length] using hb)
    rw [selW, blockP, hp, Option.getD_some]
    exact hl
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
  obtain ⟨count, hc64, hcg, chain, zs, ps, c, hzsl, hpsl, hcsl, hrz, hrp, hrc, hrch, hrows, hret59⟩ :=
    rs_eq_run_sound rd _ _ hrs
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
    rw [loadHolds_mul_gen_pow] at h1
    have h2 := hrows ((hgt layout 5 + 6 + 7) / 8) (by omega) le_rfl k hk
    have hmin : min (8 * ((hgt layout 5 + 6 + 7) / 8)) (hgt layout 5 + 6) = hgt layout 5 + 6 := by omega
    rw [hmin] at h2
    rw [hzs, hc, hps, List.take_take, min_self, padX1_take x (by omega)] at h2
    rw [List.take_of_length_le (by rw [hkinl, hkoutl]; rfl), ringRow_eq] at h2
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
  have hRRm := ring_rows_sound rd _ _ hrr
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
  have hrcL : ∀ p ∈ ringColsNames, ∀ args rets, coreProgram.Rel rd p.2 args rets → MeaningRingCols p.1 rd args rets :=
    fun p hp ↦ ring_cols_holds p hp rd
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
  have hc1' : coreProgram.Rel rd "ring_cols__L5" [σ (.n 31) * σ (.n 47) ^ 64, σ (.n 33) * word 32 0,
      σ (.n 32) * word 32 0] [σ (.n 488)] := hc1
  have h81' : σ (.n 485) = σ (.n 33) * word 32 0 := h81
  have h101' : σ (.n 487) = σ (.n 32) * word 32 0 := h101
  have hs1' : σ (.n 489) = σ (.n 471) + σ (.n 488) := hs1
  have hc2' : coreProgram.Rel rd "ring_cols__L3" [σ (.n 31) * σ (.n 48) ^ 64, σ (.n 485) * word 32 0,
      σ (.n 487) * word 32 0] [σ (.n 504)] := hc2
  have hs2' : σ (.n 505) = σ (.n 489) + σ (.n 504) := hs2
  have hc3' : coreProgram.Rel rd "ring_cols__L5" [σ (.n 31) * σ (.n 49) ^ 64, σ (.n 33) * word 8192 0,
      σ (.n 32) * word 8192 0] [σ (.n 522)] := hc3
  have h83' : σ (.n 519) = σ (.n 33) * word 8192 0 := h83
  have h103' : σ (.n 521) = σ (.n 32) * word 8192 0 := h103
  have hs3' : σ (.n 523) = σ (.n 505) + σ (.n 522) := hs3
  have hc4' : coreProgram.Rel rd "ring_cols__L5" [σ (.n 31) * σ (.n 50) ^ 64, σ (.n 519) * word 32 0,
      σ (.n 521) * word 32 0] [σ (.n 540)] := hc4
  have h84' : σ (.n 537) = σ (.n 519) * word 32 0 := h84
  have h104' : σ (.n 539) = σ (.n 521) * word 32 0 := h104
  have hs4' : σ (.n 541) = σ (.n 523) + σ (.n 540) := hs4
  have hc5' : coreProgram.Rel rd "ring_cols__L10" [σ (.n 31) * σ (.n 51) ^ 64, σ (.n 537) * word 32 0,
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
  have hmemc := chain_val hx40 (by omega) ((eq_prefix_chain_holds rd _ _).mp ch1) hrR hlmr hpt1
    _ le_rfl (by omega)
  have hpiR : ReadsAt rd (σ (.n 38)) (rm :: List.replicate 30 0) := fun k hk ↦ by
    rcases k with _ | k
    · simpa [hrm] using l9
    · have hk' : k < 30 := by rw [List.length_cons, List.length_replicate] at hk; omega
      rw [List.getElem_cons_succ, List.getElem_replicate]
      exact hz30 k hk'
  have hpic := chain_val hx40 (by omega) ((eq_prefix_chain_holds rd _ _).mp ch2) hpiR (by simp; omega) hpt1
    _ le_rfl (by omega)
  have houtc := chain_val hx40 (by omega) ((eq_prefix_chain_holds rd _ _).mp ch3) hzv
    (by rw [hkoutl]; exact le_refl _) hpt1 _ le_rfl (by omega)
  have hoodc := chain_val hx40 (by omega) ((eq_prefix_chain_holds rd _ _).mp ch4) hoodz
    (by rw [hzl]) hpt1 _ le_rfl (by omega)
  have hchic := chain_val hx40 (by omega) ((eq_prefix_chain_holds rd _ _).mp ch5) hchiR le_rfl hpt1
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
end LeanVM.Guest.B1.Stack
