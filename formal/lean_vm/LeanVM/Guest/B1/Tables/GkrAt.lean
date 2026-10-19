/-
  LeanVM.Guest.B1.Tables.GkrAt

  `verify_bus_gkr` complete in the uniform placed form (`CompleteGkrAt`).
-/

module

public import LeanVM.Guest.B1.Tables.GkrHolds
public import LeanVM.Guest.B1.Tables.FlockAt
public import LeanVM.Guest.B1.VerifySub.CompleteIface

/-!
# `verify_bus_gkr`, placed

The body is straight-line but for the odd layer's branch, taken when the depth is odd
(`completeAt_iteD`). Its five `HeapBuf`s hold the run's honest trace (`gkrOwn`), its two loops
are pure and complete on every memory agreeing with an honest one (`gkr_loop10`, `gkr_loop11`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The body's shape -/

/-- The statements before the branch. -/
def vbgPre : List Stmt := vbgP0 ++ (fsNextT (.n 17) (.n 18) (.n 2) 0 19 ++
  (fsNextT (.n 32) (.n 33) (.n 2) 1 34 ++ vbgP1))

/-- The odd layer's branch. -/
def vbgOdd : List Stmt := vbgO0 ++ (squeezeT (.n 128) (.n 129) 130 ++ (vbgO1 ++ (vbgOF ++ (vbgO2 ++
  (squeezeT (.n 248) (.n 249) 261 ++ vbgO3)))))

theorem vbg_body' : Fn.body Data.core10 = vbgPre ++ .ite (.n 127) [] vbgOdd ::
    (vbgQ ++ [.ret [.n 305, .n 306, .n 307, .n 308, .n 309, .n 310]]) := by
  rw [vbg_body]; simp only [vbgPre, vbgOdd, List.append_assoc]


set_option maxRecDepth 100000 in
theorem vbg_straight : vbgPre.all Main.Stmt.straight = true ∧ vbgOdd.all Main.Stmt.straight = true ∧
    vbgQ.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vbg_allocs (br : Bool) : (vbgPre ++ (if br then [] else vbgOdd) ++ vbgQ).filterMap Main.Stmt.allocSz =
    [(.n 10, .inr (.n 9)), (.n 11, .inl 3448), (.n 12, .inl 1640), (.n 56, .inl 33), (.n 57, .inl 33)] := by
  cases br <;> decide +kernel

set_option maxRecDepth 100000 in
theorem vbg_addrs (br : Bool) : (vbgPre ++ (if br then [] else vbgOdd) ++ vbgQ).filterMap Main.Stmt.addrS = [] := by
  cases br <;> decide +kernel

set_option maxRecDepth 100000 in
theorem vbg_calls (br : Bool) : (vbgPre ++ (if br then [] else vbgOdd) ++ vbgQ).filterMap Main.Stmt.callS =
    [(some (.n 290), "__loop10", [.n 291, .n 293, .n 57, .n 3, .n 10, .n 11], []),
      (some (.n 303), "__loop11", [.n 304, .n 3, .n 4, .n 301], [])] := by
  cases br <;> decide +kernel

/-- The body's loads: through which value, at which offsets. -/
def vbgLoadT (br : Bool) : List (ℕ × ℕ × ℕ) :=
  if br then [(2, 0, 2), (10, 0, 8), (56, 0, 33), (57, 0, 33), (124, 0, 1), (288, 0, 1), (292, 0, 1),
    (297, 0, 7)]
  else [(2, 0, 2), (10, 0, 16), (56, 0, 33), (57, 0, 33), (124, 0, 1), (144, 0, 6), (154, 0, 1),
    (288, 0, 1), (292, 0, 1), (297, 0, 7)]

def vbgLoadB (br : Bool) (q : V × ℕ) : Bool :=
  (vbgLoadT br).any fun t => q.1 == .n t.1 && decide (t.2.1 ≤ q.2) && decide (q.2 < t.2.2)

set_option maxRecDepth 100000 in
theorem vbg_loads (br : Bool) : ((vbgPre ++ (if br then [] else vbgOdd) ++ vbgQ).filterMap Stmt.loadS).all (vbgLoadB br) = true := by
  cases br <;> decide +kernel

set_option maxRecDepth 100000 in
theorem vbg_not_loop : coreProgram.loop "verify_bus_gkr" = false := by
  rw [Program.loop_of_find? find_verify_bus_gkr]; decide +kernel

set_option maxRecDepth 100000 in
theorem pure10 : coreProgram.PureIn ["__loop10", "__loop101", "sumcheck_round5"] := by
  intro g hg fn hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [find_loop10] at hfn; cases hfn; rw [core40_body]; decide +kernel
  · rw [find_loop101] at hfn; cases hfn; rw [core574_body]; decide +kernel
  · rw [find_sumcheck_round5] at hfn; cases hfn; decide +kernel

theorem pure11 : coreProgram.PureIn ["__loop11"] := by
  intro g hg fn hfn
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_loop11] at hfn; cases hfn; decide +kernel

/-! ## The buffers and the loops -/

/-- `gkr_pts`'s base, from the buffers' base `b`. -/
abbrev gP (μ b : ℕ) : ℕ := b + 8 * (μ + 2) + 3448

section
variable {T : GkrTrace} {μ : ℕ} {cv : Digest} {cur : E} {b : ℕ}

theorem mem_lay : (b, gLayW T μ cv cur (ofK (Parameters.gpow (gP μ b)))) ∈
    bufL b (gkrSizes μ) (gkrOwn T μ cv cur (ofK (Parameters.gpow (gP μ b)))) := by simp [bufL, gkrBases, gkrOwn]

theorem mem_pts : (gP μ b, gPtsW T μ) ∈ bufL b (gkrSizes μ) (gkrOwn T μ cv cur (ofK (Parameters.gpow (gP μ b)))) := by
  simp [bufL, gkrBases, gkrOwn]

theorem mem_pb : (gP μ b + 1640, vbgPb) ∈ bufL b (gkrSizes μ) (gkrOwn T μ cv cur (ofK (Parameters.gpow (gP μ b)))) := by
  simp [bufL, gkrBases, gkrOwn]

theorem mem_ds : (gP μ b + 1640 + 33, vbgDs) ∈
    bufL b (gkrSizes μ) (gkrOwn T μ cv cur (ofK (Parameters.gpow (gP μ b)))) := by simp [bufL, gkrBases, gkrOwn]

theorem gLayW_length : (gLayW T μ cv cur (ofK (Parameters.gpow (gP μ b)))).length = 8 * (μ + 2) := by
  have hl : ∀ i, (gLay T (μ % 2) cur (ofK (Parameters.gpow (gP μ b))) i ++ List.replicate 8 0).length = 16 := fun i => rfl
  rw [gLayW, List.length_append, length_flatMap_range_const hl]
  rcases Nat.mod_two_eq_zero_or_one μ with h | h
  · simp [h]; omega
  · simp [h, gLay0]; omega

theorem gPtsW_length : (gPtsW T μ).length = 40 * (μ % 2) + 40 * (μ / 2 + 1) := by
  have hr : ∀ i, (gRow (T.P i)).length = 40 := fun i => by simp [gRow]
  rw [gPtsW, List.length_append, length_flatMap_range_const hr, List.length_replicate]

/-- **The buffers' memory loads what `GkrMem` says.** -/
theorem gkrMem_at {rd : Reader} (h : MemL rd (bufL b (gkrSizes μ) (gkrOwn T μ cv cur (ofK (Parameters.gpow (gP μ b)))))) :
    GkrMem rd T μ cv cur (ofK (Parameters.gpow b)) (ofK (Parameters.gpow (b + 8 * (μ + 2)))) (ofK (Parameters.gpow (gP μ b)))
      (ofK (Parameters.gpow (gP μ b + 1640))) (ofK (Parameters.gpow (gP μ b + 1640 + 33))) :=
  gkrMem_of (h _ mem_lay) (h (b + 8 * (μ + 2), gRndW T μ cur) (by simp [bufL, gkrBases, gkrOwn]))
    (h _ mem_pts) (h _ mem_pb) (h _ mem_ds)

end

/-- The two loops' frames: on the caller's words and the buffers from `b`. -/
noncomputable def gkrKids (T : GkrTrace) (μ : ℕ) (cv : Digest) (c z : ℕ) (Lin : Main.Layout) (b : ℕ) : List Kid :=
  [⟨"__loop10", decide (μ / 2 ≠ 0), [word 1 0 0, gen ^ (μ / 2), ofK (Parameters.gpow (gP μ b + 1640 + 33)), gen ^ μ,
      ofK (Parameters.gpow b), ofK (Parameters.gpow (b + 8 * (μ + 2)))],
      Lin ++ bufL b (gkrSizes μ) (gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b)))), Returns []⟩,
    ⟨"__loop11", decide (μ ≠ 0), [word 1 0 0, gen ^ μ, ofK (Parameters.gpow z),
      ofK (Parameters.gpow (gP μ b)) * gen ^ (40 * (μ % 2 + μ / 2))],
      Lin ++ bufL b (gkrSizes μ) (gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b)))), Returns []⟩]

theorem gk_dec {a : ℕ} (ha : a < 33) : decide (word 1 0 0 + gen ^ a ≠ 0) = decide (a ≠ 0) := by
  rw [decide_eq_decide]
  constructor
  · intro h h0; exact absurd (gk_one_add_ne ha h) (by omega)
  · intro h; rw [word_one, ← pow_zero gen]; exact gen_pow_ne_of_lt (by omega) (by omega)

theorem gk_region {L : Main.Layout} {a : ℕ} {w : List E} (h : (a, w) ∈ L) {off : ℕ} (hoff : off < w.length) :
    ∃ i, Parameters.gpow (a + off) = Parameters.gpow i ∧ RegionL L i := ⟨a + off, rfl, region_buf h hoff⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_bus_gkr` is complete, placed** (TRIAGE #37): `CompleteGkrAt`, on memories defined
below `2^κ`, `κ ≥ 6`, for the range check of the depth. -/
theorem verify_bus_gkr_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 6 ≤ κ) :
    CompleteGkrAt fs cert κ := by
  intro cv μ xs r cv' c z Lin hμ hrun hpl hvl hLin
  obtain ⟨T, hT⟩ := exists_trace hrun
  obtain ⟨hs1, hs2, hs3⟩ := vbg_straight
  have h2k : 33 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have hxl : 2 + 6 * (μ % 2) ≤ xs.length := by
    rw [hT.xs_len, ← hT.ys_len _ le_rfl]; simp [gCur]
  refine completeAt_iteD find_vbg vbg_not_loop κ Lin _ _ vbg_body' hs1 (by decide) hs2 hs3
    (decide (μ % 2 = 0)) (vbg_addrs _) (gkrSizes μ)
    (fun fp => gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ (fp + fs "verify_bus_gkr")))))
    (fun fp => gkrOwn_fit T hμ _ _ _) (fun fp => gkrKids T μ cv c z Lin (fp + fs "verify_bus_gkr"))
    ?_ ?_ ?_ ?_
  · intro fp k hk ht
    simp only [gkrKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine completeAt_of_rel_lowD pure10 (by simp) κ fun rd hlow hL rd' hag => ?_
      obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
      have hM := gkrMem_at (memL_of_agree hL2 fun i hi => hag i (regionL_append.mpr (Or.inr hi)))
      have hx := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1
        fun i hi => hag i (regionL_append.mpr (Or.inl hi))
      have hm : 0 < μ / 2 := by simp only [decide_eq_true_eq] at ht; omega
      rw [word_one]; exact gkr_loop10 hT hμ hM hx hm
    · refine completeAt_of_rel_lowD pure11 (by simp) κ fun rd hlow hL rd' hag => ?_
      obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
      have hM := gkrMem_at (memL_of_agree hL2 fun i hi => hag i (regionL_append.mpr (Or.inr hi)))
      have hz := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2) hlow hL1
        fun i hi => hag i (regionL_append.mpr (Or.inl hi))
      have hm : 0 < μ := by simp only [decide_eq_true_eq] at ht; omega
      rw [word_one]; exact gkr_loop11 hT hM hz hμ hm
  · intro fp k hk _ i hi
    simp only [gkrKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact regionL_append.mp hi
  · intro fp rd hB hL k hk
    simp only [gkrKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact Main.memL_append.mpr ⟨hL, hB⟩
  · intro fp outs ho rd hlow hB hL
    set b := fp + fs "verify_bus_gkr" with hb
    have hM := gkrMem_at hB
    obtain ⟨hx, hz⟩ := hLin rd hlow hL
    obtain ⟨rc1, rck, rc2⟩ := rc_complete_low hlow (K := 33) (e := μ) h2k hμ
    refine ⟨vbgσ (ofK (Parameters.gpow z)) (digestScalars cv).1 (digestScalars cv).2 (ofK (Parameters.gpow c)) (gen ^ μ)
      (ofK (Parameters.gpow b)) (ofK (Parameters.gpow (b + 8 * (μ + 2)))) (ofK (Parameters.gpow (gP μ b))) (ofK (Parameters.gpow (gP μ b + 1640)))
      (ofK (Parameters.gpow (gP μ b + 1640 + 33))) (rcLow rd μ 33).1 (rcLow rd μ 33).2.1 (rcLow rd μ 33).2.2
      T.cnt⁻¹ T.x0 T.cnt (gen ^ (μ % 2)) (gen ^ (μ / 2)) (ofK (Parameters.gpow c) * gen ^ gCur (μ % 2) (μ / 2))
      (ofK (Parameters.gpow (gP μ b)) * gen ^ (40 * (μ % 2 + μ / 2)))
      ((T.P (μ / 2)).values.getD 0 0) ((T.P (μ / 2)).values.getD 1 0) ((T.P (μ / 2)).values.getD 2 0)
      cv (T.C (μ / 2)) T.oes, ?_, rfl,
      gkr_holds hT hμ hM hx hz (by rw [gen_pow_eq_ofK]; exact rc1) rc2
        (by rw [word_g32, gen_pow_eq_ofK, gen_pow_eq_ofK]; exact rck), ?_, ?_, ?_, ?_⟩
    · show gen ^ (μ % 2) + word 1 0 0 = 0 ↔ _
      rw [word_one]
      rcases Nat.mod_two_eq_zero_or_one μ with h | h
      · rw [h]; simp only [pow_zero, decide_true, iff_true]; exact e_add_self 1
      · rw [h]; simp only [pow_one, one_ne_zero, decide_false, Bool.false_eq_true, iff_false]
        intro h0
        exact gen_pow_ne_of_lt (a := 0) (b := 1) (by omega) (by omega) (by rw [pow_zero, pow_one, add_comm]; exact h0)
    · rw [vbg_allocs]
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id]
      have e9 : (((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0)) * ((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0))) *
          (((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0)) * ((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0))) =
          gen ^ (8 * (μ + 2)) := by
        rw [gk_word4, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      show [logG (((((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0)) * ((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0))) *
          (((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0)) * ((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0))))),
        3448, 1640, 33, 33] = _
      rw [e9, logG_g _ (by omega)]; rfl
    · rw [vbg_allocs]; rfl
    · rw [vbg_calls]
      obtain ⟨o1, o2, rfl⟩ : ∃ o1 o2, outs = [o1, o2] := by
        match outs, ho.length with
        | [o1, o2], _ => exact ⟨o1, o2, rfl⟩
      simp only [List.map_cons, List.map_nil, Main.mkCall, gkrKids]
      refine ⟨rfl, gk_dec (by omega), fun h => ⟨rfl, by rw [(ho.1 h).1]; rfl⟩, rfl, gk_dec hμ,
        fun h => ⟨rfl, by rw [(ho.2.1 h).1]; rfl⟩, trivial⟩
    · intro q hq
      have hbq := List.all_eq_true.mp (vbg_loads _) q hq
      obtain ⟨t, ht, htq⟩ := List.any_eq_true.mp hbq
      obtain ⟨p, off⟩ := q
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at htq
      obtain ⟨⟨hp, hlo⟩, hhi⟩ := htq
      have hlay := gLayW_length (T := T) (μ := μ) (cv := cv) (cur := ofK (Parameters.gpow c)) (b := b)
      have hpts := gPtsW_length (T := T) (μ := μ)
      have L2 : off < 2 → ∃ i, (ofK (Parameters.gpow c)).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ (RegionL Lin i ∨
          RegionL (bufL b (gkrSizes μ) (gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b))))) i) := fun h => by
        obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL (j := off) (by omega)
        exact ⟨i, hi, Or.inl hr⟩
      have L144 : μ % 2 = 1 → off < 6 → ∃ i, (ofK (Parameters.gpow c) * word 4 0 0).limb 0 * Parameters.gpow off = Parameters.gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL b (gkrSizes μ) (gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b))))) i) :=
        fun hs h => by
        obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL (j := 2 + off)
          (by omega)
        refine ⟨i, ?_, Or.inl hr⟩
        rw [gk_word4, addr_gen, ← hi, addr_k, Nat.add_assoc]
      have Lbuf : ∀ (a : ℕ) (w : List E) (m off' : ℕ),
          (a, w) ∈ bufL b (gkrSizes μ) (gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b)))) →
          m + off' < w.length → ∃ i, (ofK (Parameters.gpow a) * gen ^ m).limb 0 * Parameters.gpow off' = Parameters.gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL b (gkrSizes μ) (gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b))))) i) :=
        fun a w m off' hm ho' => by
        obtain ⟨i, hi, hr⟩ := gk_region hm ho'
        exact ⟨i, by rw [addr_gen, Nat.add_assoc, hi], Or.inr hr⟩
      have Lbuf0 : ∀ (a : ℕ) (w : List E) (off' : ℕ),
          (a, w) ∈ bufL b (gkrSizes μ) (gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b)))) →
          off' < w.length → ∃ i, (ofK (Parameters.gpow a)).limb 0 * Parameters.gpow off' = Parameters.gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL b (gkrSizes μ) (gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b))))) i) :=
        fun a w off' hm ho' => by
        obtain ⟨i, hi, hr⟩ := gk_region hm ho'
        exact ⟨i, by rw [addr_k, hi], Or.inr hr⟩
      have e297 : ofK (Parameters.gpow b) * (((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)) * ((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ))) =
          ofK (Parameters.gpow b) * gen ^ (8 * μ) := by
        simp only [← pow_add]; congr 2; ring
      rcases Nat.mod_two_eq_zero_or_one μ with hs | hs
      · simp only [vbgLoadT, hs, decide_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (dsimp only at hp hlo hhi ⊢; subst hp)
        · exact L2 hhi
        · exact Lbuf0 _ _ _ mem_lay (by rw [hlay]; omega)
        · exact Lbuf0 _ _ _ mem_pb (by simp [vbgPb]; omega)
        · exact Lbuf0 _ _ _ mem_ds (by simp [vbgDs]; omega)
        · exact Lbuf _ _ μ off mem_ds (by simp [vbgDs]; omega)
        · exact Lbuf _ _ μ off mem_pb (by simp [vbgPb]; omega)
        · exact Lbuf _ _ μ off mem_pb (by simp [vbgPb]; omega)
        · show ∃ i, (ofK (Parameters.gpow b) * (((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)) *
            ((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)))).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ _
          rw [e297]; exact Lbuf _ _ (8 * μ) off mem_lay (by rw [hlay]; omega)
      · simp only [vbgLoadT, hs, show ¬ (1 = 0) from by omega, decide_false, Bool.false_eq_true, ↓reduceIte,
          List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (dsimp only at hp hlo hhi ⊢; subst hp)
        · exact L2 hhi
        · exact Lbuf0 _ _ _ mem_lay (by rw [hlay]; omega)
        · exact Lbuf0 _ _ _ mem_pb (by simp [vbgPb]; omega)
        · exact Lbuf0 _ _ _ mem_ds (by simp [vbgDs]; omega)
        · exact Lbuf _ _ μ off mem_ds (by simp [vbgDs]; omega)
        · exact L144 hs hhi
        · show ∃ i, (ofK (Parameters.gpow (gP μ b)) * word 1099511627776 0 0).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ _
          rw [word_g40]; exact Lbuf _ _ 40 off mem_pts (by rw [hpts]; omega)
        · exact Lbuf _ _ μ off mem_pb (by simp [vbgPb]; omega)
        · exact Lbuf _ _ μ off mem_pb (by simp [vbgPb]; omega)
        · show ∃ i, (ofK (Parameters.gpow b) * (((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)) *
            ((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)))).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ _
          rw [e297]; exact Lbuf _ _ (8 * μ) off mem_lay (by rw [hlay]; omega)

end
end LeanVM.Guest.B1.VerifySub
