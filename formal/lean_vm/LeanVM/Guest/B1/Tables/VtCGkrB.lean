/-
  LeanVM.Guest.B1.Tables.VtCGkrB

  `verify_bus_gkr` complete in the bounded placed form (`CompleteGkrAtB`).
-/

module

public import LeanVM.Guest.B1.Tables.VtCGkrSize
public import LeanVM.Guest.B1.Tables.VtCStraightB

/-!
# `verify_bus_gkr`, placed, bounded

`verify_bus_gkr_completeAt`'s proof over `vtc_completeAt_iteB` and `vtc_completeAt_of_rel_lowB` with its two loops bounded
by their trees' sizes (`vtc_l10_total`, `vtc_l11_total`): the frame, the five `HeapBuf`s and the
loops, at most `vtcGkrBound fs` words at every depth below 33.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The bound -/

/-- The two loops' bounds: `__loop10` over at most 16 layers, `__loop11` over at most 32 words. -/
def vtcGkrBd (fs : String → ℕ) (k : Kid) : ℕ :=
  if k.f = "__loop10" then 16 * (fs "__loop10" + vtcK10 fs) + fs "__loop10"
  else 32 * (fs "__loop11" + 0) + fs "__loop11"

/-- The two loops together. -/
abbrev vtcGkrKB (fs : String → ℕ) : ℕ :=
  (16 * (fs "__loop10" + vtcK10 fs) + fs "__loop10") + (32 * (fs "__loop11" + 0) + fs "__loop11")

/-- **`verify_bus_gkr`'s bound**: its frame, its `HeapBuf`s at depth 32, its loops. -/
def vtcGkrBound (fs : String → ℕ) : ℕ :=
  fs "verify_bus_gkr" + (8 * 34 + 3448 + 1640 + 33 + 33) + vtcGkrKB fs

/-- `verify_bus_gkr`'s weight: its frame's and its loops'. -/
def vtcGkrBoundW (ω : String → ℕ) : ℕ := ω "verify_bus_gkr" + vtcGkrKB ω

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_bus_gkr` is complete, placed, by a tree of at most `vtcGkrBound fs` words weighing
at most `vtcGkrBoundW (w θ)`** (TRIAGE #37): `CompleteGkrAtW`, on memories defined below `2^κ`,
`κ ≥ 6`. -/
theorem verify_bus_gkr_completeAtW (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type}
    (w : Θ → String → ℕ) {κ : ℕ} (hκ : 6 ≤ κ) :
    CompleteGkrAtW fs cert κ w (vtcGkrBound fs) fun θ => vtcGkrBoundW (w θ) := by
  intro cv μ xs r cv' c z Lin hμ hrun hpl hvl hLin
  obtain ⟨T, hT⟩ := exists_trace hrun
  obtain ⟨hs1, hs2, hs3⟩ := vbg_straight
  have h2k : 33 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have hxl : 2 + 6 * (μ % 2) ≤ xs.length := by
    rw [hT.xs_len, ← hT.ys_len _ le_rfl]; simp [gCur]
  refine Main.CompleteAtW.bmono (vtc_completeAt_iteW find_vbg vbg_not_loop κ Lin _ _ vbg_body' hs1 (by decide) hs2
    hs3 (decide (μ % 2 = 0)) (vbg_addrs _) (gkrSizes μ)
    (fun fp => gkrOwn T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ (fp + fs "verify_bus_gkr")))))
    (fun fp => gkrOwn_fit T hμ _ _ _) (fun fp => gkrKids T μ cv c z Lin (fp + fs "verify_bus_gkr"))
    (vtcGkrBd fs) (fun k θ => vtcGkrBd (w θ) k) (vtcGkrKB fs) (fun θ => vtcGkrKB (w θ)) ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · intro fp k hk ht
    simp only [gkrKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine vtc_completeAt_of_rel_lowW (B := fun fs' => vtcGkrBd fs' _) pure10 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) (fun fs' rd hL t rets' hn hv hbo => ?_)
      swap
      · obtain ⟨-, hL2⟩ := Main.memL_append.mp hL
        have hM := gkrMem_at hL2
        have hds : LoadHolds rd (ofK (Parameters.gpow (gP μ (fp + fs "verify_bus_gkr") + 1640 + 33)) * gen ^ μ) 0
            (gen ^ (μ % 2)) := loadHolds_unshift (by rw [← vbgDs_get hμ]; exact hM.ds μ (by omega)) rfl
        have hm : 0 < μ / 2 := by simp only [decide_eq_true_eq] at ht; omega
        rw [word_one] at hv
        have := vtc_l10_total (fs := fs') hm (by omega) (Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))) hds hn hv hbo
        have hle : μ / 2 * (fs' "__loop10" + vtcK10 fs') ≤ 16 * (fs' "__loop10" + vtcK10 fs') :=
          Nat.mul_le_mul_right _ (by omega)
        simp (config := { decide := true }) only [vtcGkrBd, ↓reduceIte]
        omega
      obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
      have hM := gkrMem_at (memL_of_agree hL2 fun i hi => hag i (regionL_append.mpr (Or.inr hi)))
      have hx := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1
        fun i hi => hag i (regionL_append.mpr (Or.inl hi))
      have hm : 0 < μ / 2 := by simp only [decide_eq_true_eq] at ht; omega
      rw [word_one]; exact gkr_loop10 hT hμ hM hx hm
    · refine vtc_completeAt_of_rel_lowW (B := fun fs' => vtcGkrBd fs' _) pure11 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) (fun fs' rd hL t rets' hn hv hbo => ?_)
      swap
      · have hm : 0 < μ := by simp only [decide_eq_true_eq] at ht; omega
        rw [word_one] at hv
        have := vtc_l11_total (fs := fs') hm hn hv hbo
        have hle : μ * (fs' "__loop11" + 0) ≤ 32 * (fs' "__loop11" + 0) := Nat.mul_le_mul_right _ (by omega)
        simp (config := { decide := true }) only [vtcGkrBd, ↓reduceIte]
        omega
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
  · intro fp
    simp only [kidsBound, gkrKids, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vtcGkrKB]
    split_ifs <;> (try simp (config := { decide := true }) only [vtcGkrBd, ↓reduceIte]) <;> omega
  · intro fp θ
    simp only [Main.kidsBoundW, gkrKids, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vtcGkrKB]
    split_ifs <;> (try simp (config := { decide := true }) only [vtcGkrBd, ↓reduceIte]) <;> omega
  · simp only [gkrSizes, List.sum_cons, List.sum_nil, vtcGkrBound]
    omega

/-- **`verify_bus_gkr` is complete, placed, by a tree of at most `vtcGkrBound fs` words**
(TRIAGE #37): `CompleteGkrAtB`, on memories defined below `2^κ`, `κ ≥ 6`. -/
theorem verify_bus_gkr_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 6 ≤ κ) :
    CompleteGkrAtB fs cert κ (vtcGkrBound fs) :=
  (verify_bus_gkr_completeAtW fs cert (Θ := Empty) (fun e => e.elim) hκ).toB

end
end LeanVM.Guest.B1.VerifySub
