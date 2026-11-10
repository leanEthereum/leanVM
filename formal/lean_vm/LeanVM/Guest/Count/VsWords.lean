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

/-- `verify_tables`' callees but `__loop9` and `shared_selector_tables`, with their core
indices. -/
def vtPairs : List (String × ℕ) :=
  [("block_selector__L0", 160), ("block_selector__L1", 161), ("block_selector__L10", 170),
    ("block_selector__L11", 171), ("block_selector__L12", 172), ("block_selector__L13", 173),
    ("block_selector__L14", 174), ("block_selector__L15", 175), ("block_selector__L16", 176),
    ("block_selector__L17", 177), ("block_selector__L18", 178), ("block_selector__L19", 179),
    ("block_selector__L2", 162), ("block_selector__L20", 180), ("block_selector__L21", 181),
    ("block_selector__L22", 182), ("block_selector__L23", 183), ("block_selector__L24", 184),
    ("block_selector__L25", 185), ("block_selector__L26", 186), ("block_selector__L27", 187),
    ("block_selector__L28", 188), ("block_selector__L29", 189), ("block_selector__L3", 163),
    ("block_selector__L30", 190), ("block_selector__L31", 191), ("block_selector__L32", 192),
    ("block_selector__L33", 193), ("block_selector__L4", 164), ("block_selector__L5", 165),
    ("block_selector__L6", 166), ("block_selector__L7", 167), ("block_selector__L8", 168),
    ("block_selector__L9", 169), ("block_selector_tab__L0", 228), ("block_selector_tab__L1", 229),
    ("block_selector_tab__L10", 238), ("block_selector_tab__L11", 239),
    ("block_selector_tab__L12", 240), ("block_selector_tab__L13", 241),
    ("block_selector_tab__L14", 242), ("block_selector_tab__L15", 243),
    ("block_selector_tab__L16", 244), ("block_selector_tab__L17", 245),
    ("block_selector_tab__L18", 246), ("block_selector_tab__L19", 247),
    ("block_selector_tab__L2", 230), ("block_selector_tab__L20", 248),
    ("block_selector_tab__L21", 249), ("block_selector_tab__L22", 250),
    ("block_selector_tab__L23", 251), ("block_selector_tab__L24", 252),
    ("block_selector_tab__L25", 253), ("block_selector_tab__L26", 254),
    ("block_selector_tab__L27", 255), ("block_selector_tab__L28", 256),
    ("block_selector_tab__L29", 257), ("block_selector_tab__L3", 231),
    ("block_selector_tab__L30", 258), ("block_selector_tab__L31", 259),
    ("block_selector_tab__L32", 260), ("block_selector_tab__L33", 261),
    ("block_selector_tab__L4", 232), ("block_selector_tab__L5", 233),
    ("block_selector_tab__L6", 234), ("block_selector_tab__L7", 235),
    ("block_selector_tab__L8", 236), ("block_selector_tab__L9", 237), ("eq_prefix_chain", 4),
    ("eq_prefix_run__L0", 39), ("eq_prefix_run__L1", 40), ("eq_prefix_run__L10", 49),
    ("eq_prefix_run__L11", 50), ("eq_prefix_run__L12", 51), ("eq_prefix_run__L13", 52),
    ("eq_prefix_run__L14", 53), ("eq_prefix_run__L15", 54), ("eq_prefix_run__L16", 55),
    ("eq_prefix_run__L17", 56), ("eq_prefix_run__L18", 57), ("eq_prefix_run__L19", 58),
    ("eq_prefix_run__L2", 41), ("eq_prefix_run__L20", 59), ("eq_prefix_run__L21", 60),
    ("eq_prefix_run__L22", 61), ("eq_prefix_run__L23", 62), ("eq_prefix_run__L24", 63),
    ("eq_prefix_run__L25", 64), ("eq_prefix_run__L26", 65), ("eq_prefix_run__L27", 66),
    ("eq_prefix_run__L28", 67), ("eq_prefix_run__L29", 68), ("eq_prefix_run__L3", 42),
    ("eq_prefix_run__L30", 69), ("eq_prefix_run__L31", 70), ("eq_prefix_run__L32", 71),
    ("eq_prefix_run__L33", 72), ("eq_prefix_run__L34", 73), ("eq_prefix_run__L35", 74),
    ("eq_prefix_run__L36", 75), ("eq_prefix_run__L37", 76), ("eq_prefix_run__L38", 77),
    ("eq_prefix_run__L39", 78), ("eq_prefix_run__L4", 43), ("eq_prefix_run__L40", 79),
    ("eq_prefix_run__L5", 44), ("eq_prefix_run__L6", 45), ("eq_prefix_run__L7", 46),
    ("eq_prefix_run__L8", 47), ("eq_prefix_run__L9", 48), ("index_mle__L0", 194),
    ("index_mle__L1", 195), ("index_mle__L10", 204), ("index_mle__L11", 205),
    ("index_mle__L12", 206), ("index_mle__L13", 207), ("index_mle__L14", 208),
    ("index_mle__L15", 209), ("index_mle__L16", 210), ("index_mle__L17", 211),
    ("index_mle__L18", 212), ("index_mle__L19", 213), ("index_mle__L2", 196),
    ("index_mle__L20", 214), ("index_mle__L21", 215), ("index_mle__L22", 216),
    ("index_mle__L23", 217), ("index_mle__L24", 218), ("index_mle__L25", 219),
    ("index_mle__L26", 220), ("index_mle__L27", 221), ("index_mle__L28", 222),
    ("index_mle__L29", 223), ("index_mle__L3", 197), ("index_mle__L30", 224),
    ("index_mle__L31", 225), ("index_mle__L32", 226), ("index_mle__L33", 227),
    ("index_mle__L4", 198), ("index_mle__L5", 199), ("index_mle__L6", 200), ("index_mle__L7", 201),
    ("index_mle__L8", 202), ("index_mle__L9", 203), ("opening_tail_round", 8),
    ("padding_weight__L0", 97), ("padding_weight__L1", 98), ("padding_weight__L10", 107),
    ("padding_weight__L11", 108), ("padding_weight__L12", 109), ("padding_weight__L13", 110),
    ("padding_weight__L14", 111), ("padding_weight__L15", 112), ("padding_weight__L16", 113),
    ("padding_weight__L17", 114), ("padding_weight__L18", 115), ("padding_weight__L19", 116),
    ("padding_weight__L2", 99), ("padding_weight__L20", 117), ("padding_weight__L21", 118),
    ("padding_weight__L22", 119), ("padding_weight__L23", 120), ("padding_weight__L24", 121),
    ("padding_weight__L25", 122), ("padding_weight__L26", 123), ("padding_weight__L27", 124),
    ("padding_weight__L28", 125), ("padding_weight__L3", 100), ("padding_weight__L4", 101),
    ("padding_weight__L5", 102), ("padding_weight__L6", 103), ("padding_weight__L7", 104),
    ("padding_weight__L8", 105), ("padding_weight__L9", 106), ("plus_one_run__L0", 126),
    ("plus_one_run__L1", 127), ("plus_one_run__L10", 136), ("plus_one_run__L11", 137),
    ("plus_one_run__L12", 138), ("plus_one_run__L13", 139), ("plus_one_run__L14", 140),
    ("plus_one_run__L15", 141), ("plus_one_run__L16", 142), ("plus_one_run__L17", 143),
    ("plus_one_run__L18", 144), ("plus_one_run__L19", 145), ("plus_one_run__L2", 128),
    ("plus_one_run__L20", 146), ("plus_one_run__L21", 147), ("plus_one_run__L22", 148),
    ("plus_one_run__L23", 149), ("plus_one_run__L24", 150), ("plus_one_run__L25", 151),
    ("plus_one_run__L26", 152), ("plus_one_run__L27", 153), ("plus_one_run__L28", 154),
    ("plus_one_run__L29", 155), ("plus_one_run__L3", 129), ("plus_one_run__L30", 156),
    ("plus_one_run__L31", 157), ("plus_one_run__L32", 158), ("plus_one_run__L33", 159),
    ("plus_one_run__L4", 130), ("plus_one_run__L5", 131), ("plus_one_run__L6", 132),
    ("plus_one_run__L7", 133), ("plus_one_run__L8", 134), ("plus_one_run__L9", 135),
    ("sel_partial_nibble__L0", 93), ("sel_partial_nibble__L1", 94), ("sel_partial_nibble__L2", 95),
    ("sel_partial_nibble__L3", 96), ("sumcheck_round4", 6)]

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
    exact totalLe_mono (wSB_totalLe (j := 93) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 1 = "sel_partial_nibble__L1" by decide]
    exact totalLe_mono (wSB_totalLe (j := 94) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 2 = "sel_partial_nibble__L2" by decide]
    exact totalLe_mono (wSB_totalLe (j := 95) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 3 = "sel_partial_nibble__L3" by decide]
    exact totalLe_mono (wSB_totalLe (j := 96) (by decide +kernel)) (by unfold kSp; omega)

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
    exact totalLe_mono (wSB_totalLe (j := 450) (by decide +kernel)) (by unfold kGr; omega)
  · rw [show B1.Tables.lName "gkr_rounds" 1 = "gkr_rounds__L1" by decide]
    exact totalLe_mono (wSB_totalLe (j := 454) (by decide +kernel)) (by unfold kGr; omega)
  · rw [show B1.Tables.lName "gkr_rounds" 2 = "gkr_rounds__L2" by decide]
    exact totalLe_mono (wSB_totalLe (j := 451) (by decide +kernel)) (by unfold kGr; omega)
  · rw [show B1.Tables.lName "gkr_rounds" 4 = "gkr_rounds__L4" by decide]
    exact totalLe_mono (wSB_totalLe (j := 452) (by decide +kernel)) (by unfold kGr; omega)
  · rw [show B1.Tables.lName "gkr_rounds" 6 = "gkr_rounds__L6" by decide]
    exact totalLe_mono (wSB_totalLe (j := 453) (by decide +kernel)) (by unfold kGr; omega)

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

theorem sp_weightLe (op : Opcode) : ∀ j < 4, WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op)
    (B1.Tables.lName "sel_partial_nibble" j) (fun _ => kSpW op) := by
  intro j hj
  interval_cases j
  · rw [show B1.Tables.lName "sel_partial_nibble" 0 = "sel_partial_nibble__L0" by decide]
    exact weightLe_mono (kuSB_weightLe (j := 93) (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 1 = "sel_partial_nibble__L1" by decide]
    exact weightLe_mono (kuSB_weightLe (j := 94) (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 2 = "sel_partial_nibble__L2" by decide]
    exact weightLe_mono (kuSB_weightLe (j := 95) (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 3 = "sel_partial_nibble__L3" by decide]
    exact weightLe_mono (kuSB_weightLe (j := 96) (by cases op <;> decide +kernel)) (by unfold kSpW; omega)

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- The column selectors' weights, at most. -/
noncomputable def kCsW (op : Opcode) : ℕ :=
  ((List.range 29).map fun κ => kuSB op (B1.Tables.lName "column_selector" κ)).foldr max 0

theorem cs_okW (op : Opcode) : (List.range 29).all (fun κ =>
    kuOkB op (272 + κ) (B1.Tables.lName "column_selector" κ)) = true := by
  cases op <;> decide +kernel

theorem cs_weightLe (op : Opcode) : ∀ κ < 29, WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op)
    (B1.Tables.lName "column_selector" κ) (fun _ => kCsW op) := by
  intro κ hκ
  refine weightLe_mono (kuSB_weightLe (List.all_eq_true.mp (cs_okW op) κ (List.mem_range.mpr hκ))) ?_
  exact le_foldr_max (List.mem_map.mpr ⟨κ, List.mem_range.mpr hκ, rfl⟩)

theorem ratio_le {w A t B : ℕ} (h : 1000 * w ≤ A * t) (ht : t ≤ B) : w ≤ A * B / 1000 :=
  (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
    have := Nat.mul_le_mul_left A ht; rw [Nat.mul_comm w]; omega)

/-- `verify_sub`'s statically bounded callees (`vsStaticS`), with their core indices. -/
def stPairs : List (String × ℕ) :=
  [("grind_check__L15", 303), ("opening_message__L1_L1", 311), ("grind_check__L14", 330),
    ("squeeze_point_from__L22", 304), ("squeeze_point_from__L23", 305),
    ("squeeze_point_from__L24", 306), ("squeeze_point_from__L25", 307),
    ("squeeze_point_from__L26", 308), ("squeeze_point_from__L27", 309),
    ("squeeze_point_from__L28", 310), ("bus_grind_check__L0", 312), ("bus_grind_check__L1", 313),
    ("bus_grind_check__L2", 314), ("bus_grind_check__L3", 315), ("bus_grind_check__L4", 316),
    ("bus_grind_check__L5", 317), ("bus_grind_check__L6", 318), ("bus_grind_check__L7", 319),
    ("bus_grind_check__L8", 320), ("bus_grind_check__L9", 321), ("bus_grind_check__L10", 322),
    ("bus_grind_check__L11", 323), ("bus_grind_check__L12", 324), ("bus_grind_check__L13", 325),
    ("bus_grind_check__L14", 326), ("bus_grind_check__L15", 327), ("bus_grind_check__L16", 328),
    ("bus_grind_check__L17", 329)]

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
  hg := wSB_totalLe (j := 2) (by decide +kernel)
  Kst := wSB
  hst := st_totalLe
  K29 := wSK "__loop36" - B2C.fs "__loop36"
  R := kGr
  K8 := wSK "__loop7" - B2C.fs "__loop7"
  h29 := by simpa only [wSKt_eq] using wSKt_totalLeOn (j := 449) (by decide +kernel)
  hR := gr_totalLe
  h8 := by simpa only [wSKt_eq] using wSKt_totalLeOn (j := 91) (by decide +kernel)
  Kf := wSB
  Ksh := B2C.fs "shared_selector_tables" +
    (B2C.fs "__loop8" + 15 * (wSK "__loop8" - B2C.fs "__loop8")) + kSp
  K10 := wSK "__loop9" - B2C.fs "__loop9"
  hKf := vt_kids_totalLe
  hsh := B1.Tables.ss_totalLeOn (wSK "__loop8" - B2C.fs "__loop8") kSp
    (by simpa only [wSKt_eq] using wSKt_totalLeOn (j := 92) (by decide +kernel)) sp_totalLe
  h10 := by simpa only [wSKt_eq] using wSKt_totalLeOn (j := 262) (by decide +kernel)
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
    (loopW_of (kuSK_loop (j := 92) (by cases op <;> decide +kernel))) (sp_weightLe op)
  h10w := fun op => loopW_of (kuSK_loop (j := 262) (by cases op <;> decide +kernel))
  Weqc := fun op => kuSB op "eq_prefix_chain"
  W15 := fun op => krVl15A op * max (B2C.fs "__loop14") (32 * 38) / 1000
  Wst := fun op => kuSB op "selector_tables"
  Wcs := kCsW
  Wrsw := fun op => krVrswA op * (B2C.fs "ring_switch_weight" + 2240 + 16433) / 1000
  hEqcW := fun op => kuSB_weightLe (j := 4) (by cases op <;> decide +kernel)
  hStW := fun op => kuSB_weightLe (j := 16) (by cases op <;> decide +kernel)
  hCsW := cs_weightLe
  h15W := fun op rd t args rets hn hv hb ht => ratio_le (krVl15_weight op rd t args rets hn hv hb)
    (ht.trans (by rw [B1.VerifySub.fs_l15]; decide))
  hrswW := fun op rd t args rets hn hv hb ht => ratio_le (krVrsw_weight op rd t args rets hn hv hb)
    (ht.trans (by omega))

end
end LeanVM.Guest.Count
