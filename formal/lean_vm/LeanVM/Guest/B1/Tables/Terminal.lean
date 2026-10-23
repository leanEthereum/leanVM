/-
  LeanVM.Guest.B1.Tables.Terminal

  B1 for `check_opening_terminal`: soundness in `verify_sub`'s shape (`SoundTerm`).
-/

module

public import LeanVM.Guest.B1.Tables.TerminalBlocks

/-!
# `check_opening_terminal` (TRIAGE #42, #43)

`check_opening_terminal(…)` (G:2020-2075) evaluates the stacked opening's transparent weight
(V:1781-1785) at the opening point and checks the terminal `(inner + weight) · yr = target`
(V:1758-1760). The proof reads the body's segments: the prefix chains give each claim's own
coordinates, the 92 column selectors (dispatched on each column's log, `column_selector`) the
coordinates above them, the claims' blocks add `λ^(j+1)` times their weight (`weight_lo`,
`weight_q`), and the ring-switch rows sum to `ringWeight` (`ringWeight_eq`); `stackWeight_eq`
assembles the specification's weight.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The 29 arms of `column_selector` at once. -/
theorem column_selector_any {rd : Reader} {jj : ℕ} (hj : jj < csNames.length) {o p : E}
    {rets : List E} (h : coreProgram.Rel rd csNames[jj] [o, p] rets) :
    MeaningColumnSelector jj rd [o, p] rets := by
  have hj' : jj < 29 := hj
  interval_cases jj
  · exact (column_selector_L0_iff rd o p rets).mp h
  · exact (column_selector_L1_iff rd o p rets).mp h
  · exact (column_selector_L2_iff rd o p rets).mp h
  · exact (column_selector_L3_iff rd o p rets).mp h
  · exact (column_selector_L4_iff rd o p rets).mp h
  · exact (column_selector_L5_iff rd o p rets).mp h
  · exact (column_selector_L6_iff rd o p rets).mp h
  · exact (column_selector_L7_iff rd o p rets).mp h
  · exact (column_selector_L8_iff rd o p rets).mp h
  · exact (column_selector_L9_iff rd o p rets).mp h
  · exact (column_selector_L10_iff rd o p rets).mp h
  · exact (column_selector_L11_iff rd o p rets).mp h
  · exact (column_selector_L12_iff rd o p rets).mp h
  · exact (column_selector_L13_iff rd o p rets).mp h
  · exact (column_selector_L14_iff rd o p rets).mp h
  · exact (column_selector_L15_iff rd o p rets).mp h
  · exact (column_selector_L16_iff rd o p rets).mp h
  · exact (column_selector_L17_iff rd o p rets).mp h
  · exact (column_selector_L18_iff rd o p rets).mp h
  · exact (column_selector_L19_iff rd o p rets).mp h
  · exact (column_selector_L20_iff rd o p rets).mp h
  · exact (column_selector_L21_iff rd o p rets).mp h
  · exact (column_selector_L22_iff rd o p rets).mp h
  · exact (column_selector_L23_iff rd o p rets).mp h
  · exact (column_selector_L24_iff rd o p rets).mp h
  · exact (column_selector_L25_iff rd o p rets).mp h
  · exact (column_selector_L26_iff rd o p rets).mp h
  · exact (column_selector_L27_iff rd o p rets).mp h
  · exact (column_selector_L28_iff rd o p rets).mp h

/-! ## Offsets -/

/-- **Every offset ends inside the stack** (V:877-884). -/
theorem stackOffsets_bound (sizes : List ℕ) {c : ℕ} (hc : c < sizes.length) :
    (stackOffsets sizes).1.getD c 0 + 2 ^ sizes.getD c 0 ≤ (sizes.map (2 ^ ·)).sum := by
  set ord := (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0)) with hord
  have hperm : ord.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have hlen : ord.length = sizes.length := by rw [hperm.length_eq, List.length_range]
  obtain ⟨r, hr, hrc⟩ : ∃ r < ord.length, ord.getD r 0 = c := by
    obtain ⟨r, hr, he⟩ := List.getElem_of_mem (hperm.symm.subset (List.mem_range.mpr hc))
    exact ⟨r, hr, by rw [List.getD_eq_getElem _ _ hr, he]⟩
  have h1 := stackOffsets_fst sizes r (by omega)
  rw [← hord, hrc] at h1
  rw [h1, ← hrc, ← prefixSize_succ _ _ _ hr]
  have hfull := prefixSize_full (sizes.getD · 0) ord
  have hsum : (ord.map fun i => 2 ^ sizes.getD i 0).sum = (sizes.map (2 ^ ·)).sum := by
    rw [(hperm.map _).sum_eq, map_getD_range]
  rw [← hsum, ← hfull]
  unfold prefixSize
  rw [List.take_length]
  calc ((ord.take (r + 1)).map fun i => 2 ^ sizes.getD i 0).sum
      ≤ ((ord.take (r + 1)).map fun i => 2 ^ sizes.getD i 0).sum +
        ((ord.drop (r + 1)).map fun i => 2 ^ sizes.getD i 0).sum := Nat.le_add_right _ _
    _ = (ord.map fun i => 2 ^ sizes.getD i 0).sum := by
      rw [← List.sum_append, ← List.map_append, List.take_append_drop]

/-! ## Reading the point and the chains -/

/-- The opening point, padded with zeros (the buffer `open_stacked` writes). -/
theorem pt_reads {rd : Reader} {pt : E} {x : List E} (hx : x.length ≤ 42)
    (h : ReadsAt rd pt (x ++ List.replicate (pointCap - x.length) 0)) :
    ∀ k < 42, LoadHolds rd pt k (x.getD k 0) := by
  intro k hk
  have := (readsAt_iff_getD.mp h) k (by simp [pointCap]; omega)
  rw [getD_append'] at this
  split_ifs at this with h1
  · exact this
  · rw [getD_ge (by omega)]
    rwa [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_pos' (by simp [pointCap]; omega),
      Option.getD_some] at this

theorem readsAt_getD_eq {rd : Reader} {p : E} {A B : List E} (ha : ReadsAt rd p A)
    (hb : ReadsAt rd p B) {i : ℕ} (hi : i < A.length) (hi' : i < B.length) :
    A.getD i 0 = B.getD i 0 :=
  loadHolds_unique ((readsAt_iff_getD.mp ha) i hi) ((readsAt_iff_getD.mp hb) i hi')

/-- **A prefix chain** (`eq_prefix_chain`, G:800-808) from the seed 1 over `n < 33`
coordinates: entry `j` is the product of `1 + A[i] + Y i` below `j`, as far as `A` reaches. -/
theorem chain_prod {rd : Reader} {chain a b : E} {n : ℕ} (hn : n < 33) {A : List E} {Y : ℕ → E}
    (h : MeaningEqPrefixChain rd [chain, 1, a, b, gen ^ n] []) (ha : ReadsAt rd a A)
    (hb : ∀ k < n, LoadHolds rd b k (Y k)) :
    ∀ j ≤ n, j ≤ A.length →
      LoadHolds rd chain j (∏ i ∈ Finset.range j, (1 + A.getD i 0 + Y i)) := by
  obtain ⟨-, m, hm, hN, as, bs, hal, hbl, ra, rb, hc⟩ := h
  have hmn : m = n := (gen_pow_inj (by omega) hm hN).symm
  subst hmn
  intro j hj hjA
  have := hc j hj
  rw [one_mul, eqEval_take as bs j (by omega) (by omega)] at this
  convert this using 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [readsAt_getD_eq ha ra (by omega) (by omega),
    loadHolds_unique (hb i (by omega)) ((readsAt_iff_getD.mp rb) i (by omega))]

/-- **The public input's chain** (G:2027-2031): entry `j ∈ [1, n]` is entry 1 times the
products of `1 + Y i` over `1 ≤ i < j`. -/
theorem pi_chain {rd : Reader} {chain pt : E} {n : ℕ} (hn1 : 1 ≤ n) (hn : n < 33) {Y : ℕ → E}
    {v1 : E} (h1 : LoadHolds rd chain 1 v1)
    (hloop : gen + gen ^ n ≠ 0 → coreProgram.Rel rd "__loop83" [gen, gen ^ n, chain, pt] [])
    (hY : ∀ k < n, LoadHolds rd pt k (Y k)) :
    LoadHolds rd chain n (v1 * ∏ i ∈ Finset.Ico 1 n, (1 + Y i)) := by
  rcases Nat.eq_or_lt_of_le hn1 with rfl | hlt
  · simpa using h1
  have hrun := hloop (by
    have := gen_pow_ne_of_lt (a := 1) (b := n) hlt (by omega); rwa [pow_one] at this)
  have hrun' : coreProgram.Rel rd "__loop83" (gen ^ 1 :: [gen ^ n, chain, pt]) [] := by
    rw [pow_one]; exact hrun
  obtain ⟨m, hm1, hN, hfirst, hall⟩ := (loop_iff (loop83_step rd (gen ^ n) chain pt) 1).mp hrun'
  have hm : m = n := by
    rcases Nat.lt_or_ge n m with h | h
    · exact absurd rfl (hfirst n hlt h)
    · exact (gen_pow_inj' (by omega) (by omega) hN).symm
  subst hm
  have key : ∀ j, 1 ≤ j → j ≤ m → LoadHolds rd chain j (v1 * ∏ i ∈ Finset.Ico 1 j, (1 + Y i)) := by
    intro j hj1 hj
    induction j, hj1 using Nat.le_induction with
    | base => simpa using h1
    | succ j hj1 ih =>
      obtain ⟨c, p, lc, lp, ln⟩ := hall j hj1 (by omega)
      have ec := loadHolds_unique (lh_off0 lc) (ih (by omega))
      have ep := loadHolds_unique (lh_off0 lp) (hY j (by omega))
      rw [ec, ep] at ln
      rw [Finset.prod_Ico_succ_top (by omega), ← mul_assoc]
      exact lh_at ln rfl
  exact key m hn1 le_rfl

/-! ## The column selectors -/

/-- **Committed column `c`'s selector** (G:2034-2037, 2002-2017): with its offset `g^O` and its
log `g^K` in the placement's buffers, the dispatch reaches `column_selector__L{K}`, the offset is
aligned to `2^K`, and the selector is the product over the coordinates from `K` to 28. -/
theorem sel_fact {rd : Reader} {σ : Val} {kret : List E → Prop} {c : ℕ}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (selBlk c) True kret) {K O : ℕ} (hK : K ≤ 28)
    (hO : O < 2 ^ 28) (lo : LoadHolds rd (σ (.n 9)) c (gen ^ O))
    (lk : LoadHolds rd (σ (.n 10)) c (gen ^ K)) {X : ℕ → E}
    (hX : ∀ k < 28, LoadHolds rd (σ (.n 13)) k (X k)) :
    σ (.n (selV c)) = ∏ t ∈ Finset.range (28 - K), (1 + bitE (O.testBit (K + t)) + X (K + t)) ∧
      2 ^ K ∣ O := by
  simp only [selBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons,
    List.map_nil] at h
  obtain ⟨l1, l2, jj, hjj, hx, hrel⟩ := h
  rw [loadHolds_unique l1 lo] at hrel
  rw [loadHolds_unique l2 lk, ← gen_pow_eq_ofK] at hx
  have hj : jj < 29 := hjj
  obtain rfl : K = jj := gen_pow_inj' (by omega) (by omega) hx
  obtain ⟨off, zs, hoff, hdvd, hw, hzl, hzs, hret⟩ := column_selector_any hjj hrel
  obtain rfl : O = off := gen_pow_inj' (by omega) (by omega) hw
  simp only [List.cons.injEq, and_true] at hret
  refine ⟨?_, hdvd⟩
  rw [hret, eqAbove_eq_prod zs hzl]
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  rw [List.getD_eq_getElem _ _ (by omega),
    loadHolds_unique (hzs (K + t) (by omega) (by omega)) (hX (K + t) (by omega))]

/-! ## The prefix chains and the ring switch -/

/-- What `tPre` asks (G:2023-2032). -/
theorem t_pre {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ tPre True kret) :
    MeaningEqPrefixChain rd [σ (.n 17), 1, σ (.n 0), σ (.n 13), σ (.n 3)] [] ∧
      MeaningEqPrefixChain rd [σ (.n 19), 1, σ (.n 1), σ (.n 13), σ (.n 4)] [] ∧
      MeaningEqPrefixChain rd [σ (.n 21), 1, σ (.n 1), σ (.n 13) * gen ^ 8, σ (.n 6)] [] ∧
      LoadHolds rd (σ (.n 13)) 0 (σ (.n 29)) ∧
      LoadHolds rd (σ (.n 25)) 1 (1 + σ (.n 2) + σ (.n 29)) ∧
      (gen + σ (.n 5) ≠ 0 →
        coreProgram.Rel rd "__loop83" [gen, σ (.n 5), σ (.n 25), σ (.n 13)] []) ∧
      LoadHolds rd (σ (.n 25) * σ (.n 5)) 0 (σ (.n 35)) := by
  simp only [tPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true, word_one, word_gen, word_g8] at h
  obtain ⟨c18, e1, c20, e2, c22, c23, m24, e3, c26, -, c27, a28, l29, a30, l30, c31, a32, c33, -,
    hcall, m34, l35⟩ := h
  rw [eq_prefix_chain_iff, c18] at e1
  rw [eq_prefix_chain_iff, c20] at e2
  rw [eq_prefix_chain_iff, c22, m24, c23] at e3
  rw [a30, a28, c27] at l30
  rw [m34] at l35
  refine ⟨e1, e2, e3, l29, l30, fun hne => ?_, l35⟩
  have := hcall (by rwa [a32, c31])
  rwa [c33] at this

theorem ringRow_scale (c : E) (zs ps : List E) (k : ℕ) :
    ringRow c zs ps k = c * ringRow 1 zs ps k := by
  unfold ringRow
  generalize List.zip (zs.map (· ^ 2 ^ k)) ps = l
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    obtain ⟨v, ch⟩ := a
    simp only [List.foldl_cons]
    rw [ih, ih (1 * (1 + v + ch))]
    ring

/-- **The ring-switch rows** (G:2057-2065): with `q_flock`'s size `g^κ` (`κ < 29`), the chain's
rows telescope the products of `1 + z_n^(2^k) + point_n`, and the sum against `c_table` is
`ringWeight` (V:2011) at the point's first `κ` coordinates. -/
theorem rs_fact {rd : Reader} {σ : Val} {kret : List E → Prop} {κ : ℕ} (hκ : κ < 29) (hκ8 : 8 ≤ κ)
    (hq : σ (.n 6) * gen ^ 8 = gen ^ κ)
    (hinit : ∀ k < 64, Stmt.HoldsList (coreProgram.Rel rd) rd σ (rinitBlk k) True kret)
    (hB : Stmt.HoldsList (coreProgram.Rel rd) rd σ tPostB True kret)
    (hS : ∀ k < 64, Stmt.HoldsList (coreProgram.Rel rd) rd σ (rsBlk k) True kret)
    {fp cs x : List E} (hfp : fp.length = κ) (hcs : cs.length = 64) (hx : κ ≤ x.length)
    (rfp : ReadsAt rd (σ (.n 11)) fp) (rcs : ReadsAt rd (σ (.n 12)) cs)
    (rx : ∀ k < κ, LoadHolds rd (σ (.n 13)) k (x.getD k 0)) :
    σ (.n 2080) = ringWeight fp (x.take κ) cs := by
  simp only [tPostB, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true,
    word_g8] at hB
  obtain ⟨c15, m16, hrs, c17, m18, m19, m20, m21, m22, m23, m24, m25⟩ := hB
  rw [rs_eq_run_iff, m16, c15, hq] at hrs
  obtain ⟨-, m, hm, hN, zs, ps, hzl, hpl, rz, rp, c, hcl, hrow⟩ := hrs
  obtain rfl : κ = m := gen_pow_inj (by omega) hm hN
  have hzs : zs = fp := List.ext_getElem (by rw [hzl, hfp]) fun k h1 h2 =>
    loadHolds_unique (rz k h1) (rfp k h2)
  have hps : ps = x.take κ := by
    refine List.ext_getElem (by simp [hpl]; omega) fun k h1 h2 => ?_
    rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2, getD_take' _ (by omega)]
    exact loadHolds_unique ((readsAt_iff_getD.mp rp) k h1) (rx k (by omega))
  subst hzs hps
  have h1825 : σ (.n 1825) = σ (.n 1750) * gen ^ (64 * zs.length) := by
    rw [m25, m24, m23, m22, m21, m20, m19, m18, c17, hq, hzl]
    ring
  have hc1 : ∀ k < 64, c.getD k 0 = 1 := by
    intro k hk
    have hi := hinit k hk
    simp only [rinitBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at hi
    obtain ⟨e, l⟩ := hi
    rw [e] at l
    have := hrow (by omega) 0 (by omega) k hk
    simp only [List.take_zero, Nat.mul_zero, Nat.zero_add] at this
    exact (loadHolds_unique l this).symm
  have hr : ∀ k < 64, LoadHolds rd (σ (.n 1825)) k (ringRow 1 zs (x.take κ) k) := by
    intro k hk
    have := hrow (by omega) κ le_rfl k hk
    rw [hc1 k hk, List.take_of_length_le (show zs.length ≤ κ by omega), List.take_take,
      min_self] at this
    rw [h1825, hzl]
    exact (loadHolds_mul_gen_pow rd _ _ _ _).mpr this
  rw [rs_sum hS (c := fun k => cs.getD k 0) (fun k hk => (readsAt_iff_getD.mp rcs) k (by omega)) hr,
    ringWeight_eq, hcs]
  exact Finset.sum_congr rfl fun k _ => (ringRow_scale _ _ _ _).symm

/-! ## Soundness -/

theorem claimBlk_noRet (j : ℕ) : Stmt.noRetList (claimBlk j) = true := by
  unfold claimBlk
  split_ifs <;>
    first
    | rfl
    | simp [Stmt.noRetList, Stmt.noRet, noRetList_app, qFacs_noRet]

theorem args17 {P : List E → Prop} {args : List E} (hP : ∀ l, l.length ≠ 17 → ¬ P l) (h : P args) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16,
      args = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16] := by
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
      _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15,
      _ | ⟨a16, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    | exact absurd h (hP _ (by simp))

set_option maxHeartbeats 4000000 in
/-- **The terminal's value** (V:1781-1785): with the body's segments before the check holding,
the running sum plus the ring-switch term is the opening's inner value plus the stacked weight at
the opening point. -/
theorem terminal_val {rd : Reader} {layout : Layout} {bus : BusResult} {claims : List ColumnClaim}
    {lam : E} {fp cs : List E} {w : WhirEnd}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : E}
    (hpre : TermPre TCtx PCtx rd layout bus claims lam fp cs w
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16])
    {σ : Val} {kret : List E → Prop}
    (hp : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
        σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15),
        σ (.n 16)] = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16])
    (g0 : Stmt.HoldsList (coreProgram.Rel rd) rd σ tPre True kret)
    (g1 : ∀ c < 92, Stmt.HoldsList (coreProgram.Rel rd) rd σ (selBlk c) True kret)
    (g2 : ∀ j < 112, Stmt.HoldsList (coreProgram.Rel rd) rd σ (claimBlk j) True kret)
    (g4 : ∀ k < 64, Stmt.HoldsList (coreProgram.Rel rd) rd σ (rinitBlk k) True kret)
    (g5 : Stmt.HoldsList (coreProgram.Rel rd) rd σ tPostB True kret)
    (g6 : ∀ k < 64, Stmt.HoldsList (coreProgram.Rel rd) rd σ (rsBlk k) True kret) :
    σ (.n 1736) + σ (.n 2080) * σ (.n 53) = w.inner + stackWeight layout claims fp cs lam w.point := by
  obtain ⟨hT, hP, -, hglm, hgtau, hlp, hzv, hct, hpt, hin, hyr, hst, hpl, hsl, hμ28, hlm1, hbp,
    hxl, hfpl, hcsl⟩ := hpre
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := hp
  obtain ⟨chis, hzeta, hgmu, hchi, hgzcn, hchl, hcl, hcols, hpts⟩ := hT
  obtain ⟨hkl, hkap, hoff⟩ := hP
  -- the sizes, the offsets, the point
  generalize hkps : columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights = kps
    at hkl hkap hoff hpl hsl
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ, ∀ c, K c = (committedKappas kps).getD c 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : ℕ → ℕ, ∀ c, O c = offAt kps c := ⟨_, fun _ => rfl⟩
  have hcl92 : (committedKappas kps).length = 92 := committedKappas_length _ hkl
  have hlog : log2Ceil (stackTotal kps) ≤ layout.stackLog := by
    rw [hsl, placementsOf_snd]; exact le_max_right _ _
  have htot : stackTotal kps ≤ 2 ^ layout.stackLog :=
    le_trans (le_two_pow_log2Ceil _) (Nat.pow_le_pow_right (by norm_num) hlog)
  have hKμ : ∀ c < 92, K c ≤ layout.stackLog := fun c hc => by
    rw [hK]
    exact le_trans (le_log2Ceil_of_two_pow_le
      (stackTotal_eq kps ▸ single_le_sum_map _ c (by omega))) hlog
  have hOμ : ∀ c < 92, O c < 2 ^ layout.stackLog := fun c hc => by
    have h1 := stackOffsets_bound (committedKappas kps) (c := c) (by omega)
    have h2 := Nat.one_le_two_pow (n := (committedKappas kps).getD c 0)
    rw [← stackTotal_eq] at h1
    rw [hO, offAt]
    omega
  have hrO : ∀ c < 92, LoadHolds rd a9 c (gen ^ O c) := fun c hc => by
    rw [hO]; exact readsAt_map_iff.mp hoff c (by rw [stackOffsets_length, hcl92]; exact hc)
  have hrK : ∀ c < 92, LoadHolds rd a10 c (gen ^ K c) := fun c hc => by
    rw [hK]; exact readsAt_map_iff.mp hkap c (by rw [hcl92]; exact hc)
  have hX : ∀ k < 42, LoadHolds rd a13 k (w.point.getD k 0) := pt_reads (by omega) hpt
  have hsel : ∀ c < 92, σ (.n (selV c)) = ∏ t ∈ Finset.range (28 - K c),
      (1 + bitE ((O c).testBit (K c + t)) + w.point.getD (K c + t) 0) ∧ 2 ^ K c ∣ O c := by
    intro c hc
    have hK28 : K c ≤ 28 := le_trans (hKμ c hc) hμ28
    have hO28 : O c < 2 ^ 28 :=
      lt_of_lt_of_le (hOμ c hc) (Nat.pow_le_pow_right (by norm_num) hμ28)
    have l9 : LoadHolds rd (σ (.n 9)) c (gen ^ O c) := by rw [e9]; exact hrO c hc
    have l10 : LoadHolds rd (σ (.n 10)) c (gen ^ K c) := by rw [e10]; exact hrK c hc
    have l13 : ∀ k < 28, LoadHolds rd (σ (.n 13)) k (w.point.getD k 0) := fun k hk => by
      rw [e13]; exact hX k (by omega)
    exact sel_fact (X := fun k => w.point.getD k 0) (g1 c hc) hK28 hO28 l9 l10 l13
  -- the special sizes
  have hK0 : ∀ c < 3, K c = layout.logMemory := fun c hc => by
    rw [hK, committedKappas_getD _ hkl (by omega), blockCols_lo c (by omega), ← hkps,
      columnKappas_mem _ _ _ (by omega)]
  have hK5 : K 5 = layout.tableLogHeights.getD opBlake2s 0 + 8 := by
    rw [hK, committedKappas_getD _ hkl (by omega), qflock_col.2.2, ← hkps]
    exact columnKappas_qflock _ _ _
  have hlm28 : layout.logMemory ≤ 28 := by
    have := hKμ 0 (by omega); rw [hK0 0 (by omega)] at this; omega
  have hτ : layout.tableLogHeights.getD opBlake2s 0 + 8 ≤ layout.stackLog := by
    have := hKμ 5 (by omega); rwa [hK5] at this
  -- the prefix chains
  obtain ⟨cz, cr, cq, l29, l25, hc83, l35⟩ := t_pre g0
  rw [e0, e13, e3, hgmu] at cz
  rw [e1, e13, e4, hgzcn] at cr
  rw [e1, e13, e6, hgtau] at cq
  have hZ := chain_prod hbp cz hzeta (Y := fun k => w.point.getD k 0)
    (fun k hk => hX k (by omega))
  have hR := chain_prod (n := chis.length) (by omega) cr hchi (Y := fun k => w.point.getD k 0)
    (fun k hk => hX k (by omega))
  have hQ := chain_prod (n := layout.tableLogHeights.getD opBlake2s 0) (by omega) cq hchi
    (Y := fun k => w.point.getD (8 + k) 0)
    (fun k hk => (loadHolds_mul_gen_pow rd _ _ _ _).mpr (hX (8 + k) (by omega)))
  rw [e13] at l29
  rw [e2, loadHolds_unique l29 (hX 0 (by omega))] at l25
  rw [e5, hglm, e13] at hc83
  have hpi := pi_chain (n := layout.logMemory) hlm1 (by omega) l25 hc83
    (Y := fun k => w.point.getD k 0) (fun k hk => hX k (by omega))
  rw [e5, hglm] at l35
  have h35 := loadHolds_unique (lh_off0 l35) hpi
  -- the batching powers
  have hlam : ∀ j < 112, LoadHolds rd a8 j (lam ^ (j + 1)) := fun j hj => by
    have := (readsAt_iff_getD.mp hlp) j (by rw [length_powersFrom', hcl]; exact hj)
    rwa [powersFrom_getD _ _ _ _ (by rw [hcl]; exact hj), ← pow_succ'] at this
  -- the claims
  have hclaim : ∀ j < 112, σ (.n (claimAcc (j + 1))) = σ (.n (claimAcc j)) +
      lam ^ (j + 1) * (claims.map fun c => (c.onStack layout).1 w.point).getD j 0 := by
    intro j hj
    have hjl : j < claims.length := by rw [hcl]; exact hj
    have hW : (claims.map fun c => (c.onStack layout).1 w.point).getD j 0 =
        eqEval ((layout.placements.getD claims[j].column default).stackPoint claims[j].point
          layout.stackLog) w.point := by
      rw [List.getD_eq_getElem _ _ (by simpa using hjl), List.getElem_map]; rfl
    have hcolj : claims[j].column = claimColumns.getD j 0 := by
      rw [← hcols, List.getD_eq_getElem _ _ (by simpa using hjl), List.getElem_map]
    obtain ⟨hcpl, hpz, hpr, hpp⟩ := hpts j claims[j].point (by simp [hjl])
    obtain ⟨hc110, hlimb, hnon⟩ := claim_cols j hj
    obtain ⟨hs3, hs01, hs2⟩ := claimAcc_succ j hj
    rw [hW, hcolj, hpl, placementsOf_getD kps (by omega), hkl]
    have hkind : claimKind j = 0 ∨ claimKind j = 1 ∨ claimKind j = 2 ∨ claimKind j = 3 := by
      unfold claimKind; split_ifs <;> simp
    rcases hkind with hk0 | hk1 | hk2 | hk3
    · -- a claim on the bus point
      have hj5 : j < 5 := by unfold claimKind at hk0; split_ifs at hk0; omega
      obtain ⟨hls, hcc, hidx, hbc⟩ := hnon (by omega)
      simp only [hls, hidx]
      obtain ⟨cp, low, lam', l7, llow, lkap, l8, hacc⟩ := claim_lo (Or.inl hk0) (g2 j hj)
      simp only [hk0, ↓reduceIte] at llow
      rw [e7] at l7
      rw [e10] at lkap
      rw [e8] at l8
      have hplen : claims[j].point.length ≤ bus.point.length := by
        have := congrArg List.length (hpz hj5); rw [List.length_take] at this; omega
      have hcp : cp = gen ^ claims[j].point.length :=
        loadHolds_unique l7 (hcpl (by unfold nPooled nClaims; omega))
      have hκ : claims[j].point.length = K (claimCol j) :=
        gen_pow_inj' (by omega) (by have := hKμ _ hcc; omega)
          (hcp.symm.trans (loadHolds_unique lkap (hrK _ hcc)))
      rw [hcp] at llow
      have hlow := loadHolds_unique (lh_off0 llow) (hZ _ hplen hplen)
      have hkv : kps.getD (claimColumns.getD j 0) 0 = K (claimCol j) := by
        rw [hK, committedKappas_getD _ hkl hcc, hbc]
      rw [hkv, ← hO, weight_lo' w.point claims[j].point bus.point hxl (hpz hj5) hκ (hKμ _ hcc)
        hμ28 (hOμ _ hcc), hs01 (Or.inl hk0), hacc, (hsel _ hcc).1, hlow,
        loadHolds_unique l8 (hlam j hj), hκ]
      ring
    · -- a claim on the table point
      have hjr : 5 ≤ j ∧ j < 109 := by unfold claimKind at hk1; split_ifs at hk1 <;> omega
      obtain ⟨hls, hcc, hidx, hbc⟩ := hnon (by omega)
      simp only [hls, hidx]
      obtain ⟨cp, low, lam', l7, llow, lkap, l8, hacc⟩ := claim_lo (Or.inr hk1) (g2 j hj)
      simp only [hk1, show (1 : ℕ) ≠ 0 from by decide, ↓reduceIte] at llow
      rw [e7] at l7
      rw [e10] at lkap
      rw [e8] at l8
      have hpc := hpr hjr.1 (by unfold nPooled nClaims; omega)
      have hplen : claims[j].point.length ≤ chis.length := by
        have := congrArg List.length hpc; rw [List.length_take] at this; omega
      have hcp : cp = gen ^ claims[j].point.length :=
        loadHolds_unique l7 (hcpl (by unfold nPooled nClaims; omega))
      have hκ : claims[j].point.length = K (claimCol j) :=
        gen_pow_inj' (by omega) (by have := hKμ _ hcc; omega)
          (hcp.symm.trans (loadHolds_unique lkap (hrK _ hcc)))
      rw [hcp] at llow
      have hlow := loadHolds_unique (lh_off0 llow) (hR _ hplen hplen)
      have hkv : kps.getD (claimColumns.getD j 0) 0 = K (claimCol j) := by
        rw [hK, committedKappas_getD _ hkl hcc, hbc]
      rw [hkv, ← hO, weight_lo' w.point claims[j].point chis hxl hpc hκ (hKμ _ hcc)
        hμ28 (hOμ _ hcc), hs01 (Or.inr hk1), hacc, (hsel _ hcc).1, hlow,
        loadHolds_unique l8 (hlam j hj), hκ]
      ring
    · -- a limb's claim
      have hjr : 81 ≤ j ∧ j < 99 := by unfold claimKind at hk2; split_ifs at hk2 <;> omega
      obtain ⟨hls, hslot, h82, h100⟩ := hlimb hk2
      simp only [hls, qflock_col.2.1]
      have hqb : qflockSlotBits = 8 := by decide
      have hkc : kps.getD (claimColumns.getD j 0) 0 = layout.tableLogHeights.getD opBlake2s 0 := by
        rw [← hkps, show claimColumns.getD j 0 = 73 + (claimColumns.getD j 0 - 73) by omega,
          columnKappas_blake _ _ _ (by omega)]
        rfl
      rw [hkc, hqb, ← hO]
      obtain ⟨cp, low, lam', ys, l7, hys, llow, lkap5, l8, hacc⟩ := claim_q hk2 (g2 j hj)
      rw [e7] at l7
      rw [e10] at lkap5
      rw [e8] at l8
      have hpc := hpr (by omega) (by unfold nPooled nClaims; omega)
      have hplen : claims[j].point.length ≤ chis.length := by
        have := congrArg List.length hpc; rw [List.length_take] at this; omega
      have hcp : cp = gen ^ claims[j].point.length :=
        loadHolds_unique l7 (hcpl (by unfold nPooled nClaims; omega))
      have hτp : claims[j].point.length = layout.tableLogHeights.getD opBlake2s 0 := by
        have e := loadHolds_unique lkap5 (hrK 5 (by omega))
        rw [hcp, hK5, ← pow_add] at e
        have := gen_pow_inj' (by omega) (by omega) e
        omega
      rw [hcp] at llow
      have hlow := loadHolds_unique (lh_off0 llow) (hQ _ (by omega) hplen)
      have hal : 2 ^ (8 + layout.tableLogHeights.getD opBlake2s 0) ∣ O 5 := by
        have := (hsel 5 (by omega)).2; rwa [hK5, Nat.add_comm] at this
      rw [weight_q' w.point claims[j].point chis hxl hpc hτp (by omega) hμ28 hal hslot
        (hOμ 5 (by omega)), hs2 hk2, hacc, (hsel 5 (by omega)).1, hlow,
        loadHolds_unique l8 (hlam j hj), hK5, hτp]
      have hys' : ∏ t ∈ Finset.range 8, (1 + bitE ((claimSlot j).testBit t) + ys t) =
          ∏ t ∈ Finset.range 8, (1 + bitE ((claimSlot j).testBit t) + w.point.getD t 0) :=
        Finset.prod_congr rfl fun t ht => by
          rw [loadHolds_unique (hys t (Finset.mem_range.mp ht))
            (by rw [e13]; exact hX t (by have := Finset.mem_range.mp ht; omega))]
      rw [hys', show 8 + layout.tableLogHeights.getD opBlake2s 0 =
        layout.tableLogHeights.getD opBlake2s 0 + 8 from Nat.add_comm _ _]
      ring
    · -- a public-input claim
      have hjr : 109 ≤ j := by unfold claimKind at hk3; split_ifs at hk3 <;> omega
      obtain ⟨-, hcv, hcol⟩ := claimKind_pi hjr hj
      obtain ⟨hls, hcc, hidx, hbc⟩ := hnon (by omega)
      simp only [hls, hidx]
      obtain ⟨-, lam', l8, hacc⟩ := claim_pi hk3 (g2 j hj)
      rw [e8] at l8
      have hkv : kps.getD (claimColumns.getD j 0) 0 = layout.logMemory := by
        rw [← hK0 (claimCol j) (by omega), hK, committedKappas_getD _ hkl hcc, hbc]
      have hvars : (layout.placements.getD memory0 default).vars = layout.logMemory := by
        rw [hpl, placementsOf_getD kps (by rw [hkl]; decide), hkl]
        have h0 : limbSlot memory0 = none := by decide +kernel
        simp only [h0]
        rw [← hK0 0 (by omega), hK, committedKappas_getD _ hkl (by omega),
          blockCols_lo 0 (by omega)]
        rfl
      have hp := hpp (by unfold nPooled nClaims; omega)
      rw [hvars] at hp
      have hpl' : claims[j].point.length = layout.logMemory := by rw [hp]; simp; omega
      rw [hkv, ← hO, weight_lo w.point claims[j].point hxl hpl'
        (by rw [← hK0 (claimCol j) (by omega)]; exact hKμ _ hcc) hμ28 (hOμ _ hcc),
        hs3 hk3, hacc, h35, loadHolds_unique l8 (hlam j hj), (hsel _ hcc).1,
        hK0 (claimCol j) (by omega)]
      obtain ⟨n, hn⟩ : ∃ n, layout.logMemory = n + 1 := ⟨layout.logMemory - 1, by omega⟩
      rw [hn, Finset.prod_range_succ', Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, hp, hn]
      have hrep : ∀ i, (List.replicate n (0 : E)).getD i 0 = 0 := fun i => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
      simp only [Nat.add_sub_cancel, List.getD_cons_zero, List.getD_cons_succ, hrep, add_zero]
      simp only [show ∀ k, 1 + k = k + 1 from fun k => Nat.add_comm 1 k]
      ring
  -- the running sum
  have hsum : ∀ n ≤ 112, σ (.n (claimAcc n)) = σ (.n 14) + ∑ j ∈ Finset.range n,
      lam ^ (j + 1) * (claims.map fun c => (c.onStack layout).1 w.point).getD j 0 := by
    intro n hn
    induction n with
    | zero => simp [claimAcc]
    | succ n ih => rw [hclaim n (by omega), ih (by omega), Finset.sum_range_succ, add_assoc]
  have h1736 := hsum 112 le_rfl
  rw [show claimAcc 112 = 1736 by decide] at h1736
  -- the ring switch
  have hq : σ (.n 6) * gen ^ 8 = gen ^ (layout.tableLogHeights.getD opBlake2s 0 + 8) := by
    rw [e6, hgtau, ← pow_add]
  have hrw := rs_fact (κ := layout.tableLogHeights.getD opBlake2s 0 + 8) (fp := fp) (cs := cs)
    (x := w.point) (by omega) (by omega) hq
    g4 g5 g6 hfpl hcsl (by omega) (by rw [e11]; exact hzv) (by rw [e12]; exact hct)
    (fun k hk => by rw [e13]; exact hX k (by omega))
  -- the value
  have hqp : layout.placements.getD qflock default =
      ({ vars := K 5, index := O 5 } : Placement) := by
    rw [hpl, placementsOf_getD kps (by rw [hkl]; decide), hkl]
    simp only [qflock_col.1, qflock_col.2.1]
    rw [hK, committedKappas_getD _ hkl (by omega), qflock_col.2.2, hO]
  have hsel5 := (hsel 5 (by omega)).1
  rw [stackWeight_eq layout claims fp cs lam w.point (by rw [hcl]), ringSwitchClaim]
  simp only
  rw [hqp, eqAbove_lo w.point hxl (hKμ 5 (by omega)) hμ28 (hOμ 5 (by omega)), ← hsel5, hK5,
    ← hrw, ← hin, ← e14, h1736, show selV 5 = 53 from rfl]
  ring

/-- **`check_opening_terminal` is sound** (TRIAGE #42, #43): `SoundTerm`. -/
theorem check_opening_terminal_sound (rd : Reader) : SoundTerm TCtx PCtx rd := by
  intro layout bus claims lam fp cs w args hpre h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, rfl⟩ :=
    args17 (P := TermPre TCtx PCtx rd layout bus claims lam fp cs w)
    (fun l hl hP => by
      rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
          _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15,
          _ | ⟨a16, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals first | exact hP.elim | exact absurd rfl hl) hpre
  obtain ⟨σ, hp, hseg⟩ := check_opening_terminal_holds h
  simp only [tSegs, List.forall_mem_cons] at hseg
  obtain ⟨g0, g1, g2, -, g4, g5, g6, g7, -⟩ := hseg
  rw [holdsList_range_flatten 92 selBlk (fun _ => rfl), and_true] at g1
  rw [holdsList_range_flatten 112 claimBlk claimBlk_noRet, and_true] at g2
  rw [holdsList_range_flatten 64 rinitBlk (fun _ => rfl), and_true] at g4
  rw [holdsList_range_flatten 64 rsBlk (fun k => by unfold rsBlk; split <;> rfl), and_true] at g6
  have hv := terminal_val hpre hp g0 g1 g2 g4 g5 g6
  obtain ⟨-, -, -, -, -, -, -, -, -, hin, hyr, hst, -⟩ := hpre
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, e14, e15, e16⟩ := hp
  simp only [tEnd, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at g7
  obtain ⟨m81, a82, m83, hfin⟩ := g7
  unfold WhirEnd.Accepts
  rw [← hv, ← hyr, ← hst, ← e15, ← e16, ← e_add_eq_zero_iff.mp hfin, m83, a82, m81]

end
end LeanVM.Guest.B1
