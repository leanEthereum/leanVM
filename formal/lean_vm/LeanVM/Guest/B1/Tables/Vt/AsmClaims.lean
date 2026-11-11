/-
  LeanVM.Guest.B1.Tables.Vt.AsmClaims

  `verify_tables`' column claims: the bus's five, the tables' `159` and the public input's three,
  the bus's and the public input's values in `claim_pool`, the tables' at `col_eval_words`, and what `TCtx` says of their columns and points.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.AsmRun
public import LeanVM.Guest.B1.Tables.Vt.Pi

/-!
# The column claims (G:2244-2278, 2391-2409, 2496-2510)

`vtAllClaims`: the claims `tablesSeg` returns on the layout of the announced sizes, with the
evaluations `vtEvsC σ` read table by table. `vt_tab_claims`: the tables' claims, through
`termsPure`, are evaluation `k`'s claim on column `vtColOf k` at the point's first `h_t`
coordinates. `vt_asm_claims`: there are `159`, their values are `claim_pool`'s (bus, public input) and
`col_eval_words`' (tables), and `TCtx` holds.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure termsPure_snd length_tableWeights)

@[expose] public section

/-- The tables' evaluations, table by table. -/
def vtEvsC (σ : Val) : List (List E) :=
  [(List.range 13).map fun c ↦ σ (.n (vtEvB (0 + c))),
    (List.range 13).map fun c ↦ σ (.n (vtEvB (13 + c))),
    (List.range 7).map fun c ↦ σ (.n (vtEvB (26 + c))),
    (List.range 14).map fun c ↦ σ (.n (vtEvB (33 + c))),
    (List.range 14).map fun c ↦ σ (.n (vtEvB (47 + c))),
    (List.range 92).map fun c ↦ σ (.n (vtEvB (61 + c)))]

/-- Evaluation `k`'s table. -/
def vtTabOf (k : ℕ) : ℕ :=
  if k < 13 then 0 else if k < 26 then 1 else if k < 33 then 2 else if k < 47 then 3
  else if k < 61 then 4 else 5

/-- Table `t`'s first evaluation. -/
def vtBaseOf (t : ℕ) : ℕ := [0, 13, 26, 33, 47, 61].getD t 0

/-- Evaluation `k`'s global column. -/
def vtColOf (k : ℕ) : ℕ := globalColumnBases.getD (vtTabOf k) 0 + (k - vtBaseOf (vtTabOf k))

/-- The tables' claims. -/
def vtTabClaims (rows : List ℕ) (chis : List E) (σ : Val) : List ColumnClaim :=
  (List.range 153).map fun k ↦ ⟨vtColOf k, chis.take (vtHt rows (vtTabOf k)), σ (.n (vtEvB k))⟩

/-- The public input's claims at `rm`. -/
def vtPubClaims (L : Layout) (pi : Digest) (rm : E) : List ColumnClaim :=
  List.zipWith (fun column value ↦ ⟨column, rm ::
    List.replicate ((L.placement memory0).variableCount - 1) 0, value⟩)
    [memory0, memory1] (([0, 1] : List (Fin 2)).map fun limb ↦
      multilinearEval [ofK ((digestHalves pi).1.limb limb),
        ofK ((digestHalves pi).2.limb limb)] [rm])

/-- **All the claims** `tablesSeg` returns. -/
def vtAllClaims (bc : List K) (lm : ℕ) (rows : List ℕ) (pi : Digest) (point pts cp fp : List E)
    (forms3 : List (List Form)) (σ : Val) : List ColumnClaim :=
  vtBusClaims (layoutOf bc lm rows) point [σ (.n 812), σ (.n 816)] (σ (.n 1302))
      (σ (.n 1316)) ++
    (termsPure cp fp pts.reverse (List.zip (vtRows (tableHeightsOf rows) forms3 point pts)
      (vtEvsC σ)) 0 0 []).2 ++
    vtPubClaims (layoutOf bc lm rows) pi (σ (.n 5961))

theorem vt_rows_length {rows : List ℕ} (hr : rows.length = 6) {forms3 : List (List Form)}
    (hf : forms3.length = 6) (e pts : List E) :
    (vtRows (tableHeightsOf rows) forms3 e pts).length = 6 := by
  simp [vtRows, vt_tableHeightsOf_length hr, hf, length_tableWeights, tables]

theorem vt_rows_getD {rows : List ℕ} (hr : rows.length = 6) {forms3 : List (List Form)}
    (hf : forms3.length = 6) (e pts : List E) {t : ℕ} (ht : t < 6) :
    ((vtRows (tableHeightsOf rows) forms3 e pts).getD t default).1 = tables.getD t default ∧
      ((vtRows (tableHeightsOf rows) forms3 e pts).getD t default).2.1 = vtHt rows t := by
  have hl := vt_rows_length hr hf e pts
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [vtRows, List.getElem_zip, vtHt]
  rw [List.getD_eq_getElem _ _ (by simp [tables]; omega),
    List.getD_eq_getElem _ _ (by rw [vt_tableHeightsOf_length hr]; omega)]
  exact ⟨rfl, rfl⟩

/-- A table's piece of the claims. -/
theorem vt_piece {w base : ℕ} (f : ℕ → E) (g : E × ℕ → ColumnClaim) (hh : ℕ → ColumnClaim)
    (hg : ∀ c < w, g (f (base + c), c) = hh (base + c)) :
    ((List.range w).map fun c ↦ f (base + c)).zipIdx.map g =
      (List.range w).map fun c ↦ hh (base + c) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, Nat.zero_add]
  exact hg i (by simpa using h2)

theorem vt_tabOf_piece : ∀ t < 6, ∀ c < [13, 13, 7, 14, 14, 92].getD t 0,
    vtTabOf (vtBaseOf t + c) = t := by
  intro t ht c hc
  interval_cases t <;>
    simp only [vtBaseOf, vtTabOf, List.getD_cons_succ, List.getD_cons_zero] at hc ⊢ <;>
    split_ifs <;> omega

theorem vt_opcode_lt : ∀ t < 6, (tables.getD t default).opcode = t := by decide

/-- **The tables' claims.** -/
theorem vt_tab_claims {rows : List ℕ} (hr : rows.length = 6) {forms3 : List (List Form)}
    (hf : forms3.length = 6) (cp fp e pts : List E) (σ : Val) :
    (termsPure cp fp pts.reverse (List.zip (vtRows (tableHeightsOf rows) forms3 e pts)
      (vtEvsC σ)) 0 0 []).2 = vtTabClaims rows pts.reverse σ := by
  rw [termsPure_snd, List.nil_append,
    vt_six _ (vt_rows_length hr hf e pts) default, vtEvsC]
  have hR := fun t (ht : t < 6) ↦ vt_rows_getD hr hf e pts ht
  simp only [List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  obtain ⟨r0, s0⟩ := hR 0 (by norm_num)
  obtain ⟨r1, s1⟩ := hR 1 (by norm_num)
  obtain ⟨r2, s2⟩ := hR 2 (by norm_num)
  obtain ⟨r3, s3⟩ := hR 3 (by norm_num)
  obtain ⟨r4, s4⟩ := hR 4 (by norm_num)
  obtain ⟨r5, s5⟩ := hR 5 (by norm_num)
  rw [r0, s0, r1, s1, r2, s2, r3, s3, r4, s4, r5, s5, vt_opcode_lt 0 (by norm_num),
    vt_opcode_lt 1 (by norm_num), vt_opcode_lt 2 (by norm_num), vt_opcode_lt 3 (by norm_num),
    vt_opcode_lt 4 (by norm_num), vt_opcode_lt 5 (by norm_num)]
  have hsplit : List.range 153 = List.range 13 ++ ((List.range 13).map (13 + ·) ++
      ((List.range 7).map (26 + ·) ++ ((List.range 14).map (33 + ·) ++
      ((List.range 14).map (47 + ·) ++ (List.range 92).map (61 + ·))))) := by
    rw [show 153 = 13 + (13 + (7 + (14 + (14 + 92)))) from rfl]
    simp only [List.range_add, List.map_append, List.map_map, Function.comp_def]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
  rw [vtTabClaims, hsplit]
  simp only [List.map_append, List.map_map, Function.comp_def]
  have P : ∀ t < 6, ∀ (g : E × ℕ → ColumnClaim),
      (∀ c v, g (v, c) = ⟨globalColumnBases.getD t 0 + c, pts.reverse.take (vtHt rows t), v⟩) →
      ((List.range ([13, 13, 7, 14, 14, 92].getD t 0)).map fun c ↦
          σ (.n (vtEvB (vtBaseOf t + c)))).zipIdx.map g =
        (List.range ([13, 13, 7, 14, 14, 92].getD t 0)).map fun c ↦
          (⟨vtColOf (vtBaseOf t + c), pts.reverse.take (vtHt rows (vtTabOf (vtBaseOf t + c))),
            σ (.n (vtEvB (vtBaseOf t + c)))⟩ : ColumnClaim) := by
    intro t ht g hg
    refine vt_piece (fun k ↦ σ (.n (vtEvB k))) g
      (fun k ↦ ⟨vtColOf k, pts.reverse.take (vtHt rows (vtTabOf k)), σ (.n (vtEvB k))⟩)
      fun c hc ↦ ?_
    rw [hg, vtColOf, vt_tabOf_piece t ht c hc, Nat.add_sub_cancel_left]
  have P0 := P 0 (by norm_num)
  have P1 := P 1 (by norm_num)
  have P2 := P 2 (by norm_num)
  have P3 := P 3 (by norm_num)
  have P4 := P 4 (by norm_num)
  have P5 := P 5 (by norm_num)
  simp only [vtBaseOf, List.getD_cons_succ, List.getD_cons_zero] at P0 P1 P2 P3 P4 P5
  rw [P0 _ ?_, P1 _ ?_, P2 _ ?_, P3 _ ?_, P4 _ ?_, P5 _ ?_]
  · simp only [Nat.zero_add]
  all_goals intro c v; rfl

theorem vt_claimColumns :
    [memory0, memory1, memoryFinalCounters, bytecodeFinalCounters] ++
      (List.range 153).map vtColOf ++ [memory0, memory1] = claimColumns := by
  decide +kernel

theorem vt_tabOf_lt' (k : ℕ) : vtTabOf k < 6 := by
  unfold vtTabOf; split_ifs <;> omega

/-- The tables' claims' kappa sources: claim `4 + k` is table `vtTabOf k`'s height. -/
theorem vt_claimKappa_tab : ∀ k < 153, claimKappaSrc.getD (4 + k) 0 = vtTabOf k + 2 ∧
    claimKappaAdj (4 + k) = 0 := by decide +kernel

theorem vt_claimLowDim_tab (lm : ℕ) (τ : ℕ → ℕ) {k : ℕ} (hk : k < 153) :
    claimLowDim lm (vtTauList τ) (4 + k) = τ (vtTabOf k) := by
  obtain ⟨e1, e2⟩ := vt_claimKappa_tab k hk
  have := vt_tau_getD lm τ (vt_tabOf_lt' k)
  simp only [List.cons_append, List.nil_append] at this
  rw [claimLowDim, e1, e2, Nat.add_zero, this]

theorem vt_tabOf_lt (k : ℕ) : vtTabOf k < 6 := by
  unfold vtTabOf; split_ifs <;> omega

theorem vt_readsAt_append' {rd : Reader} {p : E} {a b : List E} (ha : TbReadsAt rd p a)
    (hb : ∀ k (hk : k < b.length), LoadHolds rd p (a.length + k) b[k]) : TbReadsAt rd p (a ++ b) := by
  intro k hk
  rcases Nat.lt_or_ge k a.length with h1 | h1
  · rw [List.getElem_append_left h1]; exact ha k h1
  · rw [List.getElem_append_right h1]
    have := hb (k - a.length) (by simp at hk; omega)
    rwa [Nat.add_sub_cancel' h1] at this

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **The claims.** -/
theorem vt_asm_claims {σ : Val} (h : VtH Lm.read σ) {bc : List K} (hbc : bc.length = 2 ^ 23)
    {pi : Digest} (hpi : (σ (.n 6), σ (.n 7)) = digestHalves pi) {point : List E}
    (hz : TbReadsAt Lm.read (σ (.n 8)) point) (hmu : σ (.n 9) = gen ^ point.length)
    (hml : point.length < 33) (hE : ExpTablesAt Lm.read (σ (.n 12))) {lm : ℕ}
    (hlm : lm ≤ 32) {rows : List ℕ} (hr : rows.length = 6) (hτ : ∀ t < 6, vtHt rows t < 29)
    (hkb : ∀ i < 8, σ (.n (25 + i)) = gen ^ ([0, lm] ++ vtTauList (vtHt rows)).getD i 0)
    {n : ℕ} (hgn : σ (.n 2544) = gen ^ n) (hnm : n ≤ point.length)
    (hhn : ∀ t < 6, vtHt rows t ≤ n) {pts : List E} (hpl : pts.length = n)
    (hchi : ∀ i < n, LoadHolds Lm.read (σ (.n 16)) (n - 1 - i) (pts.getD i 0))
    (bus : BusResult) (hbp : bus.point = point) (cp fp : List E) (forms3 : List (List Form))
    (hf : forms3.length = 6) :
    (vtAllClaims bc lm rows pi point pts cp fp forms3 σ).length = nClaims ∧
      TbReadsAt Lm.read (σ (.n 15))
        (((vtAllClaims bc lm rows pi point pts cp fp forms3 σ).take nBusClaims).map (·.value)) ∧
      TbReadsAt Lm.read (σ (.n 2647))
        ((((vtAllClaims bc lm rows pi point pts cp fp forms3 σ).drop nBusClaims).take
          nColEvals).map (·.value)) ∧
      TbReadsAt Lm.read (σ (.n 15) * gen ^ nPooled)
        (((vtAllClaims bc lm rows pi point pts cp fp forms3 σ).drop nPooled).map (·.value)) ∧
      TCtx Lm.read (layoutOf bc lm rows) bus (vtAllClaims bc lm rows pi point pts cp fp forms3 σ)
        [σ (.n 8), σ (.n 16), σ (.n 5961), σ (.n 9), σ (.n 2544)] := by
  obtain ⟨hl1, hl2, -⟩ := vt_sels hμ Lm h hz hmu hml hE hlm hτ hkb
  have hk1 : σ (.n 26) = gen ^ lm := by simpa using hkb 1 (by norm_num)
  have hk2 : σ (.n 821) = gen ^ 19 := by
    have e0 : σ (.n 25) = 1 := by simpa using hkb 0 (by norm_num)
    rw [vt_fw2_kappa h, e0, one_mul]
  obtain ⟨-, -, -, -, -, -, p0, p1, p2, p3⟩ := vt_fw h hz hl1 (by omega) hl2 hk1 hk2
  obtain ⟨-, -, -, -, -, -, -, l157, l158⟩ := vt_pi h
  have hpi' : digestHalves pi = (σ (.n 6), σ (.n 7)) := hpi.symm
  -- the claims, explicitly
  have hB : vtBusClaims (layoutOf bc lm rows) point [σ (.n 812), σ (.n 816)]
      (σ (.n 1302)) (σ (.n 1316)) =
      [⟨memory0, point.take lm, σ (.n 812)⟩, ⟨memory1, point.take lm, σ (.n 816)⟩,
        ⟨memoryFinalCounters, point.take lm, σ (.n 1302)⟩,
        ⟨bytecodeFinalCounters, point.take 19, σ (.n 1316)⟩] := by
    simp only [vtBusClaims, vt_layout_logMemory, vt_layout_logBytecode bc lm rows hbc]
    rfl
  have hP : vtPubClaims (layoutOf bc lm rows) pi (σ (.n 5961)) =
      [⟨memory0, σ (.n 5961) :: List.replicate (((layoutOf bc lm rows).placement memory0).variableCount - 1) 0,
          multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [σ (.n 5961)]⟩,
        ⟨memory1, σ (.n 5961) :: List.replicate (((layoutOf bc lm rows).placement memory0).variableCount - 1) 0,
          multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [σ (.n 5961)]⟩] := by
    rw [vtPubClaims, hpi']
    simp only [List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left]
  have hT := vt_tab_claims hr hf cp fp point pts σ
  rw [vtAllClaims, hT, hB, hP]
  have hNB : nBusClaims = 4 := rfl
  have hNC : nColEvals = 153 := rfl
  have hNP : nPooled = 157 := rfl
  have hTl : (vtTabClaims rows pts.reverse σ).length = 153 := by simp [vtTabClaims]
  refine ⟨by simp [vtTabClaims], ?_, ?_, ?_, ?_⟩
  · -- the bus's values in the pool
    rw [hNB, List.append_assoc, List.take_append_of_le_length (by simp)]
    intro k hk
    simp only [List.take_of_length_le (show [_, _, _, _].length ≤ 4 by simp),
      List.length_map, List.length_cons, List.length_nil] at hk
    simp only [List.take_of_length_le (show [_, _, _, _].length ≤ 4 by simp)]
    interval_cases k
    · simpa using p0
    · simpa using p1
    · simpa using p2
    · simpa using p3
  · -- the tables' evaluations, read in place
    rw [hNB, hNC, List.append_assoc, List.drop_append_of_le_length (by simp),
      List.drop_of_length_le (by simp), List.nil_append, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
    intro k hk
    simp only [List.length_map, hTl] at hk
    simp only [vtTabClaims, List.getElem_map, List.getElem_range]
    exact (vt_eval h hk).1
  · -- the public input's values past the pool's 157
    rw [hNP, List.drop_left' (by simp [hTl])]
    intro k hk
    simp only [List.length_map, List.length_cons, List.length_nil] at hk
    rw [tb_loadHolds_mul_gen_pow]
    interval_cases k
    · simpa using l157
    · simpa using l158
  · -- the context
    unfold TCtx
    have hchiR : TbReadsAt Lm.read (σ (.n 16)) pts.reverse := by
      intro k hk
      simp only [List.length_reverse, hpl] at hk
      have := hchi (n - 1 - k) (by omega)
      rw [show n - 1 - (n - 1 - k) = k by omega] at this
      rw [List.getElem_reverse]
      rw [List.getD_eq_getElem _ _ (by omega)] at this
      convert this using 2
      omega
    have hTH : (layoutOf bc lm rows).tableLogHeights = vtTauList (vtHt rows) :=
      vt_tableHeights_eq hr
    refine ⟨pts.reverse, by rw [hbp]; exact hz, by rw [hbp]; exact hmu, hchiR,
      by rw [hgn, List.length_reverse, hpl], by rw [hbp, List.length_reverse, hpl]; exact hnm,
      by simp [vtTabClaims], ?_, ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil, vtTabClaims, List.map_map,
        Function.comp_def]
      exact vt_claimColumns
    · intro j p hp
      rw [vt_layout_logMemory, hTH]
      simp only [List.map_append, List.map_cons, List.map_nil, vtTabClaims, List.map_map,
        Function.comp_def] at hp
      rcases Nat.lt_or_ge j 4 with hj | hj
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
          at hp
        have hlm' : (point.take lm).length = lm := by simp; omega
        have h19' : (point.take 19).length = 19 := by simp; omega
        refine ⟨fun _ ↦ ?_, fun _ ↦ ?_, fun h5 ↦ absurd h5 (by omega), fun h5 ↦ absurd h5 (by omega)⟩
        · interval_cases j <;> simp at hp <;> subst hp
          · rw [hlm']; rfl
          · rw [hlm']; rfl
          · rw [hlm']; rfl
          · rw [h19']; rfl
        · interval_cases j <;> simp at hp <;> subst hp <;> rw [hbp] <;> simp
      rcases Nat.lt_or_ge j 157 with hj' | hj'
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
          at hp
        simp only [List.length_cons, List.length_nil, List.getElem?_map, List.getElem?_range
          (show j - 4 < 153 by omega), Option.map_some, Option.some.injEq] at hp
        subst hp
        have hk : j - 4 < 153 := by omega
        have hh := hhn _ (vt_tabOf_lt (j - 4))
        have hlen' : (pts.reverse.take (vtHt rows (vtTabOf (j - 4)))).length =
            vtHt rows (vtTabOf (j - 4)) := by simp; omega
        refine ⟨fun _ ↦ ?_, fun h5 ↦ absurd h5 (by omega), fun _ _ ↦ by simp, fun h5 ↦ absurd h5 (by omega)⟩
        rw [hlen', show j = 4 + (j - 4) by omega, vt_claimLowDim_tab lm (vtHt rows) hk,
          show 4 + (j - 4) - 4 = j - 4 by omega]
      · rw [List.getElem?_append_right (by simp; omega)] at hp
        have hj3 : j - (4 + 153) < 2 := by
          by_contra hc
          rw [List.getElem?_eq_none (by simp; omega)] at hp
          exact absurd hp (by simp)
        refine ⟨fun h5 ↦ absurd h5 (by omega), fun h5 ↦ absurd h5 (by omega),
          fun _ h5 ↦ absurd h5 (by omega), fun _ ↦ ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
          List.length_range] at hp
        interval_cases h3 : j - (4 + 153) <;> simp at hp <;> exact hp.symm

end

end
end LeanVM.Guest.B1.Tables
