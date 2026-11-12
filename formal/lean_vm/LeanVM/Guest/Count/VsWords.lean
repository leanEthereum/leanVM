/-
  LeanVM.Guest.Count.VsWords

  `verify_sub`'s callees' words at the deployed frame sizes (`VsWords B2C.fs`), from the words
  certificates (`wSB`, `wSK`), B1-d's terminal words (`TermWordsFs`) and B1-c's
  `shared_selector_tables` bound (`ss_totalLeOn`); `verify_tables`' and the terminal's callees'
  weights from the `W` count certificates (`kuSB`, `kuSK`), `ss_weightLeOn` and the ratios of
  `__loop14` and `ring_switch_weight` (`Count/RatioV`).
-/

module

public import LeanVM.Guest.Count.StaticW
public import LeanVM.Guest.B1.VerifySub.WordsB
public import LeanVM.Guest.B1.Terminal.TermWordsFs
public import LeanVM.Guest.B1.Selectors.SharedWeight
public import LeanVM.Guest.Count.RatioV

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

theorem vtPairs_ok : (vtPairs.all fun p => wOkB p.2 p.1) = true := by decide +kernel

theorem vtPairs_names : B1.Tables.vtKidS.filter (fun g => g != "__loop9" && g != "shared_selector_tables" && g != "__loop8") =
    vtPairs.map Prod.fst := by decide +kernel

theorem vt_kids_totalLe : ∀ g ∈ B1.Tables.vtKidS, g ≠ "__loop9" → g ≠ "__loop8" →
    g ≠ "shared_selector_tables" → TotalLe coreProgram B2C.fs g (fun _ => wSB g) := by
  intro g hg h1 h3 h2
  have hm : g ∈ vtPairs.map Prod.fst := by
    rw [← vtPairs_names, List.mem_filter]
    exact ⟨hg, by simp [h1, h2, h3]⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  exact wSB_totalLe (List.all_eq_true.mp vtPairs_ok p hp)

/-- The four partial nibble selectors' words, at most. -/
noncomputable def kSp : ℕ :=
  max (max (wSB "sel_partial_nibble__L0") (wSB "sel_partial_nibble__L1"))
    (max (wSB "sel_partial_nibble__L2") (wSB "sel_partial_nibble__L3"))

theorem totalLe_mono {f : String} {B B' : ℕ} (h : TotalLe coreProgram B2C.fs f fun _ => B)
    (hB : B ≤ B') : TotalLe coreProgram B2C.fs f fun _ => B' :=
  fun rd t args rets hn hv hb => (h rd t args rets hn hv hb).trans hB

theorem sp_totalLe : ∀ j < 4,
    TotalLe coreProgram B2C.fs (B1.Tables.lName "sel_partial_nibble" j) (fun _ => kSp) := by
  intro j hj
  interval_cases j
  · rw [show B1.Tables.lName "sel_partial_nibble" 0 = "sel_partial_nibble__L0" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "sel_partial_nibble__L0") (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 1 = "sel_partial_nibble__L1" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "sel_partial_nibble__L1") (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 2 = "sel_partial_nibble__L2" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "sel_partial_nibble__L2") (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 3 = "sel_partial_nibble__L3" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "sel_partial_nibble__L3") (by decide +kernel)) (by unfold kSp; omega)

/-- The gkr rounds' words (`gkr_rounds__L{0,1,2,4,6}`), at most. -/
noncomputable def kGr : ℕ :=
  max (max (wSB "gkr_rounds__L0") (wSB "gkr_rounds__L1"))
    (max (max (wSB "gkr_rounds__L2") (wSB "gkr_rounds__L4")) (wSB "gkr_rounds__L6"))

theorem gr_totalLe : ∀ n ∈ [0, 1, 2, 4, 6],
    TotalLe coreProgram B2C.fs (B1.Tables.lName "gkr_rounds" n) (fun _ => kGr) := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · rw [show B1.Tables.lName "gkr_rounds" 0 = "gkr_rounds__L0" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "gkr_rounds__L0") (by decide +kernel)) (by unfold kGr; omega)
  · rw [show B1.Tables.lName "gkr_rounds" 1 = "gkr_rounds__L1" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "gkr_rounds__L1") (by decide +kernel)) (by unfold kGr; omega)
  · rw [show B1.Tables.lName "gkr_rounds" 2 = "gkr_rounds__L2" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "gkr_rounds__L2") (by decide +kernel)) (by unfold kGr; omega)
  · rw [show B1.Tables.lName "gkr_rounds" 4 = "gkr_rounds__L4" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "gkr_rounds__L4") (by decide +kernel)) (by unfold kGr; omega)
  · rw [show B1.Tables.lName "gkr_rounds" 6 = "gkr_rounds__L6" by decide]
    exact totalLe_mono (wSB_totalLe (j := wIdx "gkr_rounds__L6") (by decide +kernel)) (by unfold kGr; omega)

/-! ## The weights of `verify_tables`' and the terminal's callees -/

theorem vtPairs_okW (op : Opcode) : (vtPairs.all fun p => kuOkB op p.2 p.1) = true := by
  cases op <;> decide +kernel

theorem vt_kids_weightLe (op : Opcode) : ∀ g ∈ B1.Tables.vtKidS, g ≠ "__loop9" → g ≠ "__loop8" →
    g ≠ "shared_selector_tables" →
      WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) g (fun _ => kuSB op g) := by
  intro g hg h1 h3 h2
  have hm : g ∈ vtPairs.map Prod.fst := by
    rw [← vtPairs_names, List.mem_filter]
    exact ⟨hg, by simp [h1, h2, h3]⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  exact kuSB_weightLe (List.all_eq_true.mp (vtPairs_okW op) p hp)

/-- A loop's certificate per iteration, as `Budget.LoopW`. -/
theorem loopW_of {ω : String → ℕ} {f : String} {K : ℕ} (h : LoopWeightLe ω f K) :
    Budget.LoopW ω f K := fun rd t args rets a e hn hv hb ha he hae heo =>
  h rd t args rets a e hn hv hb ha he hae heo

/-- The four partial nibble selectors' weights, at most. -/
noncomputable def kSpW (op : Opcode) : ℕ :=
  max (max (kuSB op "sel_partial_nibble__L0") (kuSB op "sel_partial_nibble__L1"))
    (max (kuSB op "sel_partial_nibble__L2") (kuSB op "sel_partial_nibble__L3"))

theorem weightLe_mono {ω : String → ℕ} {f : String} {B B' : ℕ}
    (h : WeightLe coreProgram ω f fun _ => B) (hB : B ≤ B') : WeightLe coreProgram ω f fun _ => B' :=
  fun rd t args rets hn hv hb => (h rd t args rets hn hv hb).trans hB

set_option maxHeartbeats 800000 in
theorem sp_weightLe (op : Opcode) : ∀ j < 4, WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op)
    (B1.Tables.lName "sel_partial_nibble" j) (fun _ => kSpW op) := by
  intro j hj
  interval_cases j
  · rw [show B1.Tables.lName "sel_partial_nibble" 0 = "sel_partial_nibble__L0" by decide]
    exact weightLe_mono (kuSB_weightLe (j := wIdx "sel_partial_nibble__L0") (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 1 = "sel_partial_nibble__L1" by decide]
    exact weightLe_mono (kuSB_weightLe (j := wIdx "sel_partial_nibble__L1") (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 2 = "sel_partial_nibble__L2" by decide]
    exact weightLe_mono (kuSB_weightLe (j := wIdx "sel_partial_nibble__L2") (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 3 = "sel_partial_nibble__L3" by decide]
    exact weightLe_mono (kuSB_weightLe (j := wIdx "sel_partial_nibble__L3") (by cases op <;> decide +kernel)) (by unfold kSpW; omega)

/-- The column selectors' weights, at most. -/
noncomputable def kCsW (op : Opcode) : ℕ :=
  B1.VerifySub.lmax ((List.range 31).map fun κ => kuSB op (B1.Tables.lName "column_selector" κ))

theorem cs_okW (op : Opcode) : (List.range 31).all (fun κ =>
    kuOkB op (274 + κ) (B1.Tables.lName "column_selector" κ)) = true := by
  cases op <;> decide +kernel

theorem cs_weightLe (op : Opcode) : ∀ κ < 31, WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op)
    (B1.Tables.lName "column_selector" κ) (fun _ => kCsW op) := by
  intro κ hκ
  refine weightLe_mono (kuSB_weightLe (List.all_eq_true.mp (cs_okW op) κ (List.mem_range.mpr hκ))) ?_
  exact B1.VerifySub.le_lmax (List.mem_map.mpr ⟨κ, List.mem_range.mpr hκ, rfl⟩)

theorem ratio_le {w A t B : ℕ} (h : 1000 * w ≤ A * t) (ht : t ≤ B) : w ≤ A * B / 1000 :=
  (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
    have := Nat.mul_le_mul_left A ht; rw [Nat.mul_comm w]; omega)

/-- `verify_sub`'s statically bounded callees (`vsStaticS`), with their core indices. -/
def stPairs : List (String × ℕ) :=
  [("grind_check__L15", 307), ("opening_message__L1_L1", 319), ("grind_check__L13", 334),
    ("squeeze_point_from__L20", 308), ("squeeze_point_from__L21", 309),
    ("squeeze_point_from__L22", 310), ("squeeze_point_from__L23", 311),
    ("squeeze_point_from__L24", 312), ("squeeze_point_from__L25", 313),
    ("squeeze_point_from__L26", 314), ("squeeze_point_from__L27", 315),
    ("squeeze_point_from__L28", 316), ("squeeze_point_from__L29", 317),
    ("squeeze_point_from__L30", 318), ("bus_grind_check__L0", 320), ("bus_grind_check__L1", 321),
    ("bus_grind_check__L2", 322), ("bus_grind_check__L3", 323), ("bus_grind_check__L4", 324),
    ("bus_grind_check__L5", 325), ("bus_grind_check__L6", 326), ("bus_grind_check__L7", 327),
    ("bus_grind_check__L8", 328), ("bus_grind_check__L9", 329), ("bus_grind_check__L10", 330),
    ("bus_grind_check__L11", 331), ("bus_grind_check__L12", 332), ("bus_grind_check__L13", 333)]

theorem stPairs_ok : (stPairs.all fun p => wOkB p.2 p.1) = true := by decide +kernel

theorem stPairs_names : B1.VerifySub.vsStaticS = stPairs.map Prod.fst := by decide +kernel

theorem st_totalLe : ∀ g ∈ B1.VerifySub.vsStaticS, TotalLe coreProgram B2C.fs g (fun _ => wSB g) := by
  intro g hg
  rw [stPairs_names] at hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  exact wSB_totalLe (List.all_eq_true.mp stPairs_ok p hp)

/-- **`verify_sub`'s callees' words at `B2C.fs`.** -/
noncomputable def vsWords : B1.VerifySub.VsWords B2C.fs where
  Bg := wSB "g_power_of_word"
  hg := wSB_totalLe (j := wIdx "g_power_of_word") (by decide +kernel)
  Kst := wSB
  hst := st_totalLe
  K29 := wSK "__loop36" - B2C.fs "__loop36"
  R := kGr
  K8 := wSK "__loop7" - B2C.fs "__loop7"
  h29 := by simpa only [wSKt_eq] using wSKt_totalLeOn (j := wIdxL 36) (by decide +kernel)
  hR := gr_totalLe
  h8 := by simpa only [wSKt_eq] using wSKt_totalLeOn (j := wIdxL 7) (by decide +kernel)
  Kf := wSB
  Ksh := B2C.fs "shared_selector_tables" +
    (B2C.fs "__loop8" + 15 * (wSK "__loop8" - B2C.fs "__loop8")) + kSp
  K10 := wSK "__loop9" - B2C.fs "__loop9"
  hKf := vt_kids_totalLe
  hsh := B1.Tables.ss_totalLeOn (wSK "__loop8" - B2C.fs "__loop8") kSp
    (by simpa only [wSKt_eq] using wSKt_totalLeOn (j := wIdxL 8) (by decide +kernel)) sp_totalLe
  h10 := by simpa only [wSKt_eq] using wSKt_totalLeOn (j := wIdxL 9) (by decide +kernel)
  B14 := 3204
  hl14 := B1.VerifySub.l14_totalLeOn_fs
  Beqc := 184
  K15 := 19
  Bcs := 157
  Brs := 8142
  hEqc := B1.VerifySub.eqc_totalLe_fs
  hL15 := B1.VerifySub.l15_totalLeOn_fs
  hCsF := B1.VerifySub.cs_fs_le
  hrs := B1.VerifySub.rs_totalLeOn_fs
  ωv := fun op => B2C.ωArm B2C.xmssArmC op
  Kvw := kuSB
  Wss := fun op => B2C.ωArm B2C.xmssArmC op "shared_selector_tables" + 15 * kuSK op "__loop8" +
    kSpW op
  Kw10 := fun op => kuSK op "__loop9"
  hKvw := vt_kids_weightLe
  hssw := fun op => B1.Tables.ss_weightLeOn _ _ _
    (loopW_of (kuSK_loop (j := wIdxL 8) (by cases op <;> decide +kernel))) (sp_weightLe op)
  h10w := fun op => loopW_of (kuSK_loop (j := wIdxL 9) (by cases op <;> decide +kernel))
  Weqc := fun op => kuSB op "eq_prefix_chain"
  W15 := fun op => krVl15A op * max (B2C.fs "__loop14") (32 * 38) / 1000
  Wst := fun op => kuSB op "selector_tables"
  Wcs := kCsW
  Wrsw := fun op => krVrswA op * (B2C.fs "ring_switch_weight" + 2240 + 16433) / 1000
  hEqcW := fun op => kuSB_weightLe (j := wIdx "eq_prefix_chain") (by cases op <;> decide +kernel)
  hStW := fun op => kuSB_weightLe (j := wIdx "selector_tables") (by cases op <;> decide +kernel)
  hCsW := cs_weightLe
  h15W := fun op rd t args rets hn hv hb ht => ratio_le (krVl15_weight op rd t args rets hn hv hb)
    (ht.trans (by rw [B1.VerifySub.fs_l15]; decide))
  hrswW := fun op rd t args rets hn hv hb ht => ratio_le (krVrsw_weight op rd t args rets hn hv hb)
    (ht.trans (by omega))

end
end LeanVM.Guest.Count
