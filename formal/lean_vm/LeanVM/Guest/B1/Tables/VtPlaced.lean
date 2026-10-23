/-
  LeanVM.Guest.B1.Tables.VtPlaced

  `verify_tables`' placed form's conditions on a valuation of its body (`VtPlacedOk`).
-/

module

public import LeanVM.Guest.B1.Tables.VtPlVals

/-!
# `verify_tables`, placed

On a valuation under which the body holds, with the arguments, the 205 hinted pointers and
`g^n`: the dispatches' selectors are the tables' `g^τ`, the hints' sizes are `vtSizes n` and their
pointers the allocator's, the frames match `vtKids`, and every load reads the caller's words or a
buffer (`vt_placed_loads`). Under the blocks' log-heights at most `|point|` (`logMem ≤ |point|`,
`18 ≤ |point|`), which a selector's chains need.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- Selector `i`'s callee. -/
noncomputable def vtSelKid (L : Main.Layout) (b n μ : ℕ) (ks : ℕ → ℕ) (zeta sq : E) (i : ℕ) : Kid :=
  ⟨selNames.getD i "", decide (μ - ks (selBlk.getD i 0) ≠ 0),
    [1, gen ^ (μ - ks (selBlk.getD i 0)), vtPtr b n (selBuf i) * gen ^ ks (selBlk.getD i 0),
      vtPtr b n (selBuf i + 1), zeta * gen ^ ks (selBlk.getD i 0), vtPtr b n (selBuf i + 2), sq,
      gen ^ ks (selBlk.getD i 0)], L, Returns []⟩

theorem vtKids_eq (Lin : Main.Layout) (b n μ logMem : ℕ) (ks τs nr : ℕ → ℕ) (point : List E)
    (zeta sq chiP : E) (own : List (List E)) :
    vtKids Lin b n μ logMem ks τs nr point zeta sq chiP own =
      (List.range 6).map (fun t => (⟨pwNames.getD (τs t) "", true, [eOfNat (nr t), zeta], Lin,
        Returns [paddingWeight (point.take (τs t)) (nr t), pwLead (τs t) (nr t), pwRest (τs t) (nr t)]⟩ : Kid)) ++
      ([vtSelKid (Lin ++ bufL b (vtSizes n) own) b n μ ks zeta sq 0,
        vtSelKid (Lin ++ bufL b (vtSizes n) own) b n μ ks zeta sq 1,
        ⟨"__loop14", decide (logMem ≠ 0), [1, gen ^ logMem, vtPtr b n 11, zeta, vtPtr b n 3],
          Lin ++ bufL b (vtSizes n) own, Returns []⟩,
        vtSelKid (Lin ++ bufL b (vtSizes n) own) b n μ ks zeta sq 2,
        ⟨"__loop16", true, [1, gen ^ 18, vtPtr b n 15, zeta, vtPtr b n 3], Lin ++ bufL b (vtSizes n) own,
          Returns []⟩] ++
      ((List.range 62).map (fun i => vtSelKid (Lin ++ bufL b (vtSizes n) own) b n μ ks zeta sq (i + 3)) ++
      [⟨"__loop79", decide (n ≠ 0), [1, gen ^ n, vtPtr b n 202, chiP, gen ^ n, vtPtr b n 203],
          Lin ++ bufL b (vtSizes n) own, Returns []⟩,
        ⟨"__loop80", decide (n ≠ 0), [1, gen ^ n, vtPtr b n 204, zeta, chiP], Lin ++ bufL b (vtSizes n) own,
          Returns []⟩])) := by
  simp only [vtKids, List.append_assoc]; rfl

theorem vtRestCalls_eq : vtRestCalls =
    [vtSelCall 0, vtSelCall 1, (some (.n 1928), "__loop14", [.n 1929, .n 1893, .n 1925, .n 5, .n 1817], []),
      vtSelCall 2, (some (.n 2032), "__loop16", [.n 2033, .n 1997, .n 2029, .n 5, .n 1817], [])] ++
    ((List.range 62).map (fun i => vtSelCall (i + 3)) ++
    [(some (.n 4644), "__loop79", [.n 4645, .n 4554, .n 4636, .n 15, .n 4554, .n 4639], []),
      (some (.n 4658), "__loop80", [.n 4659, .n 4554, .n 4655, .n 5, .n 15], [])]) := by
  simp only [vtRestCalls, List.append_assoc]

theorem vt_cm_cons {σ : Val} {c : Call} {k : Kid} {cs : List Call} {ks : List Kid} {o : List E × Main.Layout}
    {os : List (List E × Main.Layout)} (h1 : CallOk σ c k o) (h2 : CallsMatch σ cs ks os) :
    CallsMatch σ (c :: cs) (k :: ks) (o :: os) := ⟨h1.1, h1.2.1, h1.2.2, h2⟩

/-- **`VtPlacedOk`, with the blocks' log-heights at most `|point|`.** -/
def VtPlacedOk' : Prop :=
  ∀ (κ : ℕ), 7 ≤ κ → ∀ (rd : Reader) (σ : Val) (Lin : Main.Layout) (b : ℕ)
    (logMem n : ℕ) (rowsN : List ℕ) (point xs chis : List E) (claims cpw : List E)
    (cvr : ℕ → Digest) (cl ch : ℕ → E) (alphas : List E)
    (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (outs : List (List E × Main.Layout)),
    VtHolds rd σ → LowDef κ rd → MemL rd Lin →
    point.length < 33 → 16 ≤ logMem → logMem ≤ 32 → rowsN.length = 6 → (∀ m ∈ rowsN, log2Ceil m < 29) →
    alphas.length = 4 → n = ((List.range 6).map fun t => log2Ceil (rowsN.getD t 0)).foldl max 0 →
    n ≤ point.length → logMem ≤ point.length → 18 ≤ point.length →
    xs.length = 5 + 3 * n + 104 → claims.length = nClaims → chis.length = n →
    cpw.length = nPooled →
    σ (.n 2) = ofK (Parameters.gpow c) → σ (.n 5) = ofK (Parameters.gpow z) →
    σ (.n 6) = gen ^ point.length → σ (.n 7) = ofK (Parameters.gpow dims) →
    σ (.n 8) = ofK (Parameters.gpow rows) → σ (.n 9) = ofK (Parameters.gpow bk) →
    σ (.n 10) = ofK (Parameters.gpow sq) → σ (.n 11) = ofK (Parameters.gpow fpw) →
    σ (.n 13) = ofK (Parameters.gpow pool) → σ (.n 14) = ofK (Parameters.gpow cplen) →
    σ (.n 15) = ofK (Parameters.gpow chi) →
    (∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i) → σ (.n 4554) = gen ^ n →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun m ↦ gen ^ log2Ceil m) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun m ↦ gen ^ log2Ceil m)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) claims ∧
      ReadsAt rd (ofK (Parameters.gpow chi)) chis ∧
      ReadsAt rd (ofK (Parameters.gpow cplen)) cpw) →
    MemL rd (bufL b (vtSizes n) (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n
      cvr (ofK (Parameters.gpow c)) cl ch chis)) →
    OutsOk (vtKids Lin b n point.length logMem (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
      (fun t => log2Ceil (rowsN.getD t 0)) (fun t => rowsN.getD t 0) point (ofK (Parameters.gpow z))
      (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi))
      (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n cvr
        (ofK (Parameters.gpow c)) cl ch chis)) outs →
    (∀ s ∈ vtPre, DispOk σ s) ∧
      (vtPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = vtSizes n ∧
      ((vtPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b (vtSizes n)).map (fun b => ofK (Parameters.gpow b)) ∧
      CallsMatch σ ((vtPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (vtKids Lin b n point.length logMem (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          (fun t => log2Ceil (rowsN.getD t 0)) (fun t => rowsN.getD t 0) point (ofK (Parameters.gpow z))
          (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi))
          (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n cvr
            (ofK (Parameters.gpow c)) cl ch chis)) outs ∧
      ∀ q ∈ vtPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * Parameters.gpow q.2 = Parameters.gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL b (vtSizes n) (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          point logMem n cvr (ofK (Parameters.gpow c)) cl ch chis)) i)

section
variable {rd : Reader} {σ : Val}

set_option maxHeartbeats 4000000 in
/-- A selector's frame matches its callee. -/
theorem vt_sel_ok (h : VtHolds rd σ) {i : ℕ} (hi : i < 65) (L : Main.Layout) {b n μ bk : ℕ}
    {ks : ℕ → ℕ} {zeta sq : E} (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ μ)
    (h9 : σ (.n 9) = ofK (Parameters.gpow bk)) (h10 : σ (.n 10) = sq)
    (hptr : ∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i)
    (hbkR : ∀ b' < 102, LoadHolds rd (ofK (Parameters.gpow bk)) b' (gen ^ ks b'))
    (hks : ∀ b' < 102, ks b' ≤ μ) (hμ : μ < 33) (o : List E × Main.Layout)
    (hout : (vtSelKid L b n μ ks zeta sq i).taken = true → (vtSelKid L b n μ ks zeta sq i).Out o.1 o.2) :
    CallOk σ (Main.mkCall σ (vtSelCall i)) (vtSelKid L b n μ ks zeta sq i) o := by
  obtain ⟨sb2, -, -, av0, av1, av2, hblk⟩ := vt_selBuf i hi
  obtain ⟨l0, m6, -, -⟩ := vt_sel_facts h hi
  obtain ⟨m10, -, m14, a20, c21⟩ := vt_sel_facts2 h hi
  rw [h9] at l0
  have ev := loadHolds_unique l0 (hbkR _ hblk)
  have hkμ := hks _ hblk
  have e5 : σ (.n (selVal.getD i 0 + 5)) = gen ^ (μ - ks (selBlk.getD i 0)) := by
    rw [h6, ev] at m6
    refine mul_right_cancel₀ (b := gen ^ ks (selBlk.getD i 0)) (pow_ne_zero _ vt_gen_ne_zero) ?_
    rw [← m6, ← pow_add, Nat.sub_add_cancel hkμ]
  have p12 : σ (.n (selVal.getD i 0 + 12)) = vtPtr b n (selBuf i) := by rw [← av0, hptr _ (by omega)]
  have p15 : σ (.n (selVal.getD i 0 + 15)) = vtPtr b n (selBuf i + 1) := by rw [← av1, hptr _ (by omega)]
  have p16 : σ (.n (selVal.getD i 0 + 16)) = vtPtr b n (selBuf i + 2) := by rw [← av2, hptr _ (by omega)]
  simp only [CallOk, vtSelCall, vtSelKid, Main.mkCall, List.map_cons, List.map_nil]
  refine ⟨trivial, ?_, fun ht => ⟨?_, (hout ht).1.symm⟩⟩
  · rw [a20, e5]; exact one_add_gen_pow_dec' (by omega)
  · rw [c21, e5, m14, p12, p15, m10, h5, p16, h10, ev]

end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`verify_tables`' frames match its callees.** -/
theorem vt_calls_match {rd : Reader} {σ : Val} (h : VtHolds rd σ) {Lin : Main.Layout} {b n logMem bk : ℕ}
    {point : List E} {ks τs nr : ℕ → ℕ} {zeta sq chiP : E} {own : List (List E)}
    {outs : List (List E × Main.Layout)} (hk1 : ks 1 = logMem) (hk2 : ks 2 = 18)
    (hpad : ∀ t < 6, σ (.n (1733 + 14 * t)) = gen ^ τs t ∧ τs t < 29 ∧
      σ (.n (1733 + 14 * t + 5)) = eOfNat (nr t) ∧
      [σ (.n (1733 + 14 * t + 6)), σ (.n (1733 + 14 * t + 7)), σ (.n (1733 + 14 * t + 8))] =
        [paddingWeight (point.take (τs t)) (nr t), pwLead (τs t) (nr t), pwRest (τs t) (nr t)])
    (hbkR : ∀ b' < 102, LoadHolds rd (ofK (Parameters.gpow bk)) b' (gen ^ ks b'))
    (hks : ∀ b' < 102, ks b' ≤ point.length) (hμ : point.length < 33) (hlm32 : logMem ≤ 32)
    (hnμ : n ≤ point.length) (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length)
    (h9 : σ (.n 9) = ofK (Parameters.gpow bk)) (h10 : σ (.n 10) = sq) (h15 : σ (.n 15) = chiP)
    (hptr : ∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i) (h4554 : σ (.n 4554) = gen ^ n)
    (ho : OutsOk (vtKids Lin b n point.length logMem ks τs nr point zeta sq chiP own) outs) :
    CallsMatch σ ((vtPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
      (vtKids Lin b n point.length logMem ks τs nr point zeta sq chiP own) outs := by
  rw [vt_calls σ, vtRestCalls_eq, vtKids_eq]
  rw [vtKids_eq] at ho
  obtain ⟨o1, o2, rfl, ho1, ho2⟩ := vt_outsOk_append _ _ _ ho
  obtain ⟨o3, o4, rfl, ho3, ho4⟩ := vt_outsOk_append _ _ _ ho2
  obtain ⟨o5, o6, rfl, ho5, ho6⟩ := vt_outsOk_append _ _ _ ho4
  simp only [List.map_append, List.map_map]
  have selOK := fun i (hi : i < 65) o hout => vt_sel_ok h hi (Lin ++ bufL b (vtSizes n) own) h5 h6 h9 h10
    hptr hbkR hks hμ o hout
  refine vt_callsMatch_append _ _ _ _ _ _ (vt_callsMatch_map _ _ _ _ ho1 ?_)
    (vt_callsMatch_append _ _ _ _ _ _ ?_ (vt_callsMatch_append _ _ _ _ _ _
      (vt_callsMatch_map _ _ _ _ ho5 fun i hi o hout => selOK (i + 3) (by simp at hi; omega) o hout) ?_))
  · intro t ht o hout
    obtain ⟨e0, h29, e5', e6⟩ := hpad t (List.mem_range.mp ht)
    simp only [CallOk, Function.comp, vtPadCall, Main.mkCall, List.map_cons, List.map_nil]
    refine ⟨by rw [e0, logG_g _ (by omega)], trivial, fun _ => ⟨by rw [e5', h5], ?_⟩⟩
    rw [e6, (hout rfl).1]
  · -- the first five
    have e93 : σ (.n 1893) = gen ^ logMem := by
      have l93 := (vt_sel_facts h (i := 1) (by omega)).1
      rw [h9] at l93
      rw [← hk1]; exact loadHolds_unique l93 (hbkR 1 (by omega))
    have e97 : σ (.n 1997) = gen ^ 18 := by
      have l97 := (vt_sel_facts h (i := 2) (by omega)).1
      rw [h9] at l97
      rw [← hk2]; exact loadHolds_unique l97 (hbkR 2 (by omega))
    have a28 : σ (.n 1928) = σ (.n 1927) + σ (.n 1893) :=
      h.atom 1653 (.add (.n 1928) (.n 1927) (.n 1893)) (by decide +kernel)
    have c27 : σ (.n 1927) = word 1 0 0 := h.atom 1652 (.const (.n 1927) (word 1 0 0)) (by decide +kernel)
    have c29 : σ (.n 1929) = word 1 0 0 := h.atom 1654 (.const (.n 1929) (word 1 0 0)) (by decide +kernel)
    have a32 : σ (.n 2032) = σ (.n 2031) + σ (.n 1997) :=
      h.atom 1761 (.add (.n 2032) (.n 2031) (.n 1997)) (by decide +kernel)
    have c31 : σ (.n 2031) = word 1 0 0 := h.atom 1760 (.const (.n 2031) (word 1 0 0)) (by decide +kernel)
    have c33 : σ (.n 2033) = word 1 0 0 := h.atom 1762 (.const (.n 2033) (word 1 0 0)) (by decide +kernel)
    have av3 : vtAllocVar.getD 3 0 = 1817 := by decide
    obtain ⟨-, -, -, a11, a15, -, -, -, -, -, -, -, -⟩ := vt_allocVar_fixed
    have p1817 : σ (.n 1817) = vtPtr b n 3 := by rw [← av3, hptr 3 (by omega)]
    have p1925 : σ (.n 1925) = vtPtr b n 11 := by rw [← a11, hptr 11 (by omega)]
    have p2029 : σ (.n 2029) = vtPtr b n 15 := by rw [← a15, hptr 15 (by omega)]
    match o3, ho3 with
    | [q1, q2, q3, q4, q5], ⟨r1, r2, r3, r4, r5, _⟩ =>
      refine vt_cm_cons (selOK 0 (by omega) q1 r1) (vt_cm_cons (selOK 1 (by omega) q2 r2)
        (vt_cm_cons ?_ (vt_cm_cons (selOK 2 (by omega) q4 r4) (vt_cm_cons ?_ trivial))))
      · simp only [CallOk, Main.mkCall, List.map_cons, List.map_nil]
        refine ⟨trivial, ?_, fun ht => ⟨?_, (r3 ht).1.symm⟩⟩
        · rw [a28, c27, word_one, e93]; exact one_add_gen_pow_dec' (by omega)
        · rw [c29, word_one, e93, p1925, h5, p1817]
      · simp only [CallOk, Main.mkCall, List.map_cons, List.map_nil]
        refine ⟨trivial, ?_, fun _ => ⟨?_, (r5 rfl).1.symm⟩⟩
        · rw [a32, c31, word_one, e97]; exact one_add_gen_pow_dec' (by omega)
        · rw [c33, word_one, e97, p2029, h5, p1817]
  · -- the two sum-check loops
    have a44 : σ (.n 4644) = σ (.n 4643) + σ (.n 4554) :=
      h.atom 4355 (.add (.n 4644) (.n 4643) (.n 4554)) (by decide +kernel)
    have c43 : σ (.n 4643) = word 1 0 0 := h.atom 4354 (.const (.n 4643) (word 1 0 0)) (by decide +kernel)
    have c45 : σ (.n 4645) = word 1 0 0 := h.atom 4356 (.const (.n 4645) (word 1 0 0)) (by decide +kernel)
    have a58 : σ (.n 4658) = σ (.n 4657) + σ (.n 4554) :=
      h.atom 4371 (.add (.n 4658) (.n 4657) (.n 4554)) (by decide +kernel)
    have c57 : σ (.n 4657) = word 1 0 0 := h.atom 4370 (.const (.n 4657) (word 1 0 0)) (by decide +kernel)
    have c59 : σ (.n 4659) = word 1 0 0 := h.atom 4372 (.const (.n 4659) (word 1 0 0)) (by decide +kernel)
    obtain ⟨-, -, -, -, -, a202, a203, a204, -⟩ := vt_allocVar_fixed
    have p4636 : σ (.n 4636) = vtPtr b n 202 := by rw [← a202, hptr 202 (by omega)]
    have p4639 : σ (.n 4639) = vtPtr b n 203 := by rw [← a203, hptr 203 (by omega)]
    have p4655 : σ (.n 4655) = vtPtr b n 204 := by rw [← a204, hptr 204 (by omega)]
    match o6, ho6 with
    | [q1, q2], ⟨r1, r2, _⟩ =>
      refine vt_cm_cons ?_ (vt_cm_cons ?_ trivial)
      · simp only [CallOk, Main.mkCall, List.map_cons, List.map_nil]
        refine ⟨trivial, ?_, fun ht => ⟨?_, (r1 ht).1.symm⟩⟩
        · rw [a44, c43, word_one, h4554]; exact one_add_gen_pow_dec' (by omega)
        · rw [c45, word_one, h4554, p4636, h15, p4639]
      · simp only [CallOk, Main.mkCall, List.map_cons, List.map_nil]
        refine ⟨trivial, ?_, fun ht => ⟨?_, (r2 ht).1.symm⟩⟩
        · rw [a58, c57, word_one, h4554]; exact one_add_gen_pow_dec' (by omega)
        · rw [c59, word_one, h4554, p4655, h5, h15]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vt_placed_ok' : VtPlacedOk' := by
  intro κ hκ rd σ Lin b logMem n rowsN point xs chis claims cpw cvr cl ch alphas c z lp sq dims rows bk fpw
    pool cplen chi outs h hlow hLin hμ33 h16 hlm32 hrl hτ29 hal hn hnμ hlmμ h18 hxl hcl hchl hcpl h2 h5 h6
    h7 h8 h9 h10 h11 h13 h14 h15 hptr h4554 hpre hB ho
  obtain ⟨hxs, hz, hexp, hrows, hdims, hbk, hfpw, hpool, hchi, hcp⟩ := hpre rd hlow hLin
  have hτn : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ n := fun t ht => by
    rw [hn]; exact le_foldl_max _ 0 _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  have hτ29' : ∀ t < 6, log2Ceil (rowsN.getD t 0) < 29 := fun t ht =>
    hτ29 (rowsN.getD t 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hτμ : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length := fun t ht => le_trans (hτn t ht) hnμ
  have pad := fun t (ht : t < 6) => vt_pad_vals h hrl hτ29 hτμ h7 h8 h5 hdims hrows hz ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine dispOk_of fun p hp => ?_
    rw [vt_disps] at hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have ht6 := List.mem_range.mp ht
    exact ⟨log2Ceil (rowsN.getD t 0), by show _ < 29; exact hτ29' t ht6, by have := hτ29' t ht6; omega,
      by rw [(pad t ht6).1, gen_pow_eq_ofK]⟩
  · rw [show (vtPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) =
        ((vtPre.filterMap Main.Stmt.allocSz).map Prod.snd).map (fun y => y.elim id fun s => logG (σ s)) by
        rw [List.map_map]; rfl, vt_allocs, List.map_append, vtSizes_split]
    congr 1
    · rw [← vtSzSrcA_sizes]
      refine List.map_congr_left fun x hx => ?_
      have hc := List.all_eq_true.mp vtSzSrcA_cells x hx
      match x, hc with
      | .inl _, _ => rfl
      | .inr v, hc =>
        simp only [List.any_eq_true, beq_iff_eq, List.mem_range] at hc
        obtain ⟨i, hi, rfl⟩ := hc
        show logG (σ (.n (selVal.getD i 0 + 11))) = 34
        rw [(vt_sel_facts2 h hi).2.1, word_g34, logG_g _ (by norm_num)]
    · have c32 : σ (.n 4632) = word 2 0 0 := h.atom 4338 (.const (.n 4632) (word 2 0 0)) (by decide +kernel)
      have m33 : σ (.n 4633) = σ (.n 4554) * σ (.n 4632) :=
        h.atom 4339 (.mul (.n 4633) (.n 4554) (.n 4632)) (by decide +kernel)
      have m34 : σ (.n 4634) = σ (.n 4633) * σ (.n 4633) :=
        h.atom 4340 (.mul (.n 4634) (.n 4633) (.n 4633)) (by decide +kernel)
      have m35 : σ (.n 4635) = σ (.n 4634) * σ (.n 4634) :=
        h.atom 4341 (.mul (.n 4635) (.n 4634) (.n 4634)) (by decide +kernel)
      have c37 : σ (.n 4637) = word 2 0 0 := h.atom 4343 (.const (.n 4637) (word 2 0 0)) (by decide +kernel)
      have m38 : σ (.n 4638) = σ (.n 4554) * σ (.n 4637) :=
        h.atom 4344 (.mul (.n 4638) (.n 4554) (.n 4637)) (by decide +kernel)
      have c53 : σ (.n 4653) = word 2 0 0 := h.atom 4365 (.const (.n 4653) (word 2 0 0)) (by decide +kernel)
      have m54 : σ (.n 4654) = σ (.n 4554) * σ (.n 4653) :=
        h.atom 4366 (.mul (.n 4654) (.n 4554) (.n 4653)) (by decide +kernel)
      show [logG (σ (.n 4635)), logG (σ (.n 4638)), logG (σ (.n 4654))] = [4 * (n + 1), n + 1, n + 1]
      rw [m35, m34, m33, m38, m54, c32, c37, c53, word_gen, h4554, ← pow_succ, ← pow_add, ← pow_add,
        logG_g _ (by omega), logG_g _ (by omega)]
      simp only [List.cons.injEq, and_true]
      omega
  · rw [vt_allocs_fst, List.map_map]
    have hl : vtAllocVar.length = 205 := by decide
    apply List.ext_getElem (by simp [vt_length_bases, vtSizes_length, hl])
    intro i h1 h2
    have hi : i < 205 := by simpa [hl] using h1
    simp only [List.getElem_map, Function.comp]
    have := hptr i hi
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    rw [this, vtPtr, List.getD_eq_getElem _ _ (by simpa [vt_length_bases, vtSizes_length] using hi)]
  · exact vt_calls_match h (zeta := ofK (Parameters.gpow z)) (sq := ofK (Parameters.gpow sq))
      (chiP := ofK (Parameters.gpow chi)) (bk := bk) (by unfold vtKs; rfl) (by unfold vtKs; rfl)
      (fun t ht => ⟨(pad t ht).1, hτ29' t ht, (pad t ht).2.1, (pad t ht).2.2⟩)
      (fun b' hb' => by
        have := readsAt_getD0 hbk (k := b') (by simp [blockKappas]; exact hb')
        rwa [vt_bk_get hrl hb'] at this)
      (fun b' hb' => vtKs_le hlmμ h18 hnμ hτn hb') hμ33 hlm32 hnμ h5 h6 h9 h10 h15 hptr h4554 ho
  · exact vt_placed_loads (τ := fun t => log2Ceil (rowsN.getD t 0)) rfl rfl rfl h hlow hLin hlm32 hrl hτ29' hal
      hτn hnμ hxl hcl hcpl hlmμ h18 hμ33 h2 h6 h7 h8 h9 h10 h11 h13 h14 hptr h4554
      (fun rd a e => (hpre rd a e).1) (fun rd a e => (hpre rd a e).2.2.2.2.1)
      (fun rd a e => (hpre rd a e).2.2.2.1) (fun rd a e => (hpre rd a e).2.2.2.2.2.1)
      (fun rd a e => (hpre rd a e).2.2.2.2.2.2.1) (fun rd a e => (hpre rd a e).2.2.2.2.2.2.2.1)
      (fun rd a e => (hpre rd a e).2.2.2.2.2.2.2.2.2)
      (fun rd a e j hj => by
        simp only [List.length_map, List.length_range] at hj
        simp only [List.getElem_map, List.getElem_range]
        exact ((hpre rd a e).2.2.1 j hj).2) hB

/-- **`verify_tables`' placed conditions** (`VtPlacedOk`). -/
theorem vt_placed_ok : VtPlacedOk := vt_placed_ok'

end
end LeanVM.Guest.B1.VerifySub
