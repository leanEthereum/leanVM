/-
  LeanVM.Guest.Budget.VsCount

  `verify_sub`'s instructions on a child, per opcode, by its callees at the child's candidate:
  the static callees' and its opening arm's counts (`Count/VsCountData`), `verify_tables`' and the
  terminal's by their trees' shapes (`kcVtW`, `kcTermW`), and its two callees with no static bound
  within ratios of their words.
-/

module

public import LeanVM.Guest.Count.VsCountChkX
public import LeanVM.Guest.Count.VsCountChkM
public import LeanVM.Guest.Count.VsCountChkS
public import LeanVM.Guest.Count.VsCountChkD
public import LeanVM.Guest.Count.VsCountChkJ
public import LeanVM.Guest.Count.VsCountChkK
public import LeanVM.Guest.Count.RatioV
public import LeanVM.Guest.Budget.FlatShape
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.VerifySub.BoundsB
public import LeanVM.Guest.Count.VsWB
public import LeanVM.Guest.Count.VsWordsOs

/-!
# `verify_sub`'s instructions per candidate

`B1.VerifySub.vsNames μ r d`: `verify_sub`'s sixteen callees in call order, the squeeze's arm at the
stack log `μ` seventh, the bus grind's at the depth `d` ninth, its opening arm `openName μ r`
fifteenth. `vsWs op c Bs`: a bound on each callee's instructions of `op`, the static ones' and the
arm's (candidate `c`) from the `V` certificates, the two dispatches' the largest of their arms'
(`vsSqMax`, `vsBgMax`), `verify_tables`' and the terminal's from the `W` certificates (`kcVtW`,
`kcTermW`: their trees within B1's `vtWB`, `termWB`), `verify_bus_gkr`'s and `verify_keccak`'s
within their ratios of their words `Bs[9]`, `Bs[11]`. `vs_weight_le`: a `verify_sub` node of
B1-d's shape (`vsTs` at `Count.vsWordsOs`) weighs at most its frame's weight and `vsWs`.
`vs_weight_le_vsTs`: with `verify_bus_gkr` and `verify_keccak` within `46339` and `56391` words,
at most `vsCountT op c`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Count

@[expose] public section

/-- `squeeze_point_from`'s arms' instructions of `op`, the largest (`vsStNames` `8 .. 14`). -/
def vsSqMax (op : Opcode) : ℕ :=
  B1.VerifySub.lmax ((List.range 7).map fun j ↦ (kcVsStT op).getD (8 + j) 0)

/-- `bus_grind_check`'s arms' instructions of `op`, the largest (`vsStNames` `15 .. 32`). -/
def vsBgMax (op : Opcode) : ℕ :=
  B1.VerifySub.lmax ((List.range 18).map fun j ↦ (kcVsStT op).getD (15 + j) 0)

/-- **The callees' instructions of `op`** at the candidate `c`, the two ratio-bounded ones within
the words `Bs`. -/
def vsWs (op : Opcode) (c : ℕ) (Bs : List ℕ) : List ℕ :=
  [(kcVsStT op).getD 0 0, (kcVsStT op).getD 0 0, (kcVsStT op).getD 1 0, (kcVsStT op).getD 2 0,
    (kcVsStT op).getD 3 0, (kcVsStT op).getD 4 0, vsSqMax op, (kcVsStT op).getD 5 0, vsBgMax op,
    krVbgA op * Bs.getD 9 0 / 1000, kcVtW op, krVkA op * Bs.getD 11 0 / 1000,
    (kcVsStT op).getD 6 0, (kcVsStT op).getD 7 0, (kcOsT op).getD c 0, kcTermW op]

theorem vsTab_ok (op : Opcode) : vsTabOk op = true := by
  cases op
  · exact vsTab_ok_x
  · exact vsTab_ok_m
  · exact vsTab_ok_s
  · exact vsTab_ok_d
  · exact vsTab_ok_j
  · exact vsTab_ok_k

/-- A table's entry is a `WeightLe` bound. -/
theorem weightLe_tab {op : Opcode} {j n : ℕ} {f : String}
    (h : (kvOkB op j f && kvSBJ op j == n) = true) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) f fun _ => n := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hok, hv⟩ := h
  have hw := kvSB_weightLe hok
  have hn : (coreProgram[j]?).map Fn.name = some f := by
    simp only [kvOkB, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  rw [kvSB_idx hn, hv] at hw
  exact hw

/-- A table's entry is a `LoopWeightLe` bound. -/
theorem loopWeightLe_tab {op : Opcode} {j n : ℕ} {f : String}
    (h : (kvOkK op j f && kvSKJ op j == n) = true) :
    LoopWeightLe (B2C.ωArm B2C.xmssArmC op) f n := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hok, hv⟩ := h
  have hw := kvSK_loop hok
  have hn : (coreProgram[j]?).map Fn.name = some f := by
    simp only [kvOkK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  rw [kvSK_idx hn, hv] at hw
  exact hw

theorem vsTab_parts (op : Opcode) :
    (∀ c < 28, (kvOkB op (osJ.getD c 0) ("open_stacked__L" ++ B1.Whir.natStr c) &&
      kvSBJ op (osJ.getD c 0) == (kcOsT op).getD c 0) = true) ∧
    (∀ i < 33, (kvOkB op (vsStJ.getD i 0) (vsStNames.getD i "") &&
      kvSBJ op (vsStJ.getD i 0) == (kcVsStT op).getD i 0) = true) ∧
    (∀ k < 17, (kvOkB op (cclJ.getD k 0) ("child_claim_list_last__L" ++ B1.Whir.natStr k) &&
      kvSBJ op (cclJ.getD k 0) == (kcCclT op).getD k 0) = true) ∧
    (kvOkB op lsJ "list_split" && kvSBJ op lsJ == kcLs op) = true ∧
    (∀ i < 4, (kvOkK op (ccLpJ.getD i 0) (ccLpNames.getD i "") &&
      kvSKJ op (ccLpJ.getD i 0) == (kcCcLpT op).getD i 0) = true) ∧
    (∀ i < 5, decide ((coreProgram[omJ.getD i 0]?).map Fn.name = some (omNames.getD i "")) = true ∧
      (B2C.plumbOf (omJ.getD i 0 + 1)).pmax.getD (B2C.opIdx op) 0 = (omT op).getD i 0) := by
  have h := vsTab_ok op
  simp only [vsTabOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h4a⟩, h4b⟩, h5⟩, h6⟩ := h
  refine ⟨fun c hc => ?_, fun i hi => ?_, fun k hk => ?_, ?_, fun i hi => ?_, fun i hi => h6 i hi⟩
  · have := h1 c hc; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h2 i hi; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h3 k hk; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h4a, h4b⟩
  · have := h5 i hi; simp only [Bool.and_eq_true, beq_iff_eq]; exact this

/-- **The opening arm of candidate `c`.** -/
theorem kcOs_weightLe (op : Opcode) {c : ℕ} (hc : c < 28) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) ("open_stacked__L" ++ B1.Whir.natStr c)
      fun _ => (kcOsT op).getD c 0 :=
  weightLe_tab ((vsTab_parts op).1 c hc)

/-- **`verify_sub`'s static callees.** -/
theorem vsSt_weightLe (op : Opcode) {i : ℕ} (hi : i < 33) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) (vsStNames.getD i "")
      fun _ => (kcVsStT op).getD i 0 :=
  weightLe_tab ((vsTab_parts op).2.1 i hi)

/-- **`child_claim_list_last__L{k}`.** -/
theorem ccl_weightLe (op : Opcode) {k : ℕ} (hk : k < 17) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) ("child_claim_list_last__L" ++ B1.Whir.natStr k)
      fun _ => (kcCclT op).getD k 0 :=
  weightLe_tab ((vsTab_parts op).2.2.1 k hk)

/-- **`list_split`.** -/
theorem ls_weightLe (op : Opcode) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) "list_split" fun _ => kcLs op :=
  weightLe_tab (vsTab_parts op).2.2.2.1

/-- `child_claim_list_any`'s loops' instructions per iteration: `__loop17` per `136` claims,
`__loop18` per `17`. -/
def kcL17 (op : Opcode) : ℕ := (kcCcLpT op).getD 0 0

/-- See `kcL17`. -/
def kcL18 (op : Opcode) : ℕ := (kcCcLpT op).getD 1 0

/-- **`__loop17`, per iteration.** -/
theorem l17_loop (op : Opcode) : LoopWeightLe (B2C.ωArm B2C.xmssArmC op) "__loop17" (kcL17 op) :=
  loopWeightLe_tab (by simpa [ccLpNames, kcL17] using (vsTab_parts op).2.2.2.2.1 0 (by norm_num))

/-- **`__loop18`, per iteration.** -/
theorem l18_loop (op : Opcode) : LoopWeightLe (B2C.ωArm B2C.xmssArmC op) "__loop18" (kcL18 op) :=
  loopWeightLe_tab (by simpa [ccLpNames, kcL18] using (vsTab_parts op).2.2.2.2.1 1 (by norm_num))

/-- **The frame weights** of `verify_sub`, `child_claim_list_digest`, `__loop4`,
`child_claim_list_any`, `child_claim_list_mono`. -/
theorem om_eq (op : Opcode) {i : ℕ} (hi : i < 5) :
    B2C.ωArm B2C.xmssArmC op (omNames.getD i "") = (omT op).getD i 0 := by
  obtain ⟨hn, hv⟩ := (vsTab_parts op).2.2.2.2.2 i hi
  rw [ωArm_idx (decide_eq_true_eq.mp hn) (by interval_cases i <;> decide), hv]

theorem openName_eq {μ r : ℕ} (h : B1.Whir.candidate μ r < 28) :
    B1.Whir.openName μ r = "open_stacked__L" ++ B1.Whir.natStr (B1.Whir.candidate μ r) := by
  unfold B1.Whir.openName B1.Whir.openNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some, B1.Whir.natStr_eq]

theorem div_of_ratio {w A t B : ℕ} (h : 1000 * w ≤ A * t) (ht : t ≤ B) : w ≤ A * B / 1000 :=
  (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
    have := Nat.mul_le_mul_left A ht; rw [Nat.mul_comm w]; omega)

theorem squeezeName_eq {j : ℕ} (hj : j < 7) :
    B1.VerifySub.squeezeNames.getD j "" = vsStNames.getD (8 + j) "" := by
  interval_cases j <;> rfl

theorem busGrindName_eq {j : ℕ} (hj : j < 18) :
    B1.VerifySub.busGrindNames.getD j "" = vsStNames.getD (15 + j) "" := by
  interval_cases j <;> rfl

theorem le_vsSqMax (op : Opcode) {j : ℕ} (hj : j < 7) : (kcVsStT op).getD (8 + j) 0 ≤ vsSqMax op :=
  B1.VerifySub.le_lmax (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

theorem le_vsBgMax (op : Opcode) {j : ℕ} (hj : j < 18) :
    (kcVsStT op).getD (15 + j) 0 ≤ vsBgMax op :=
  B1.VerifySub.le_lmax (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

/-- **`verify_sub`'s instructions of `op`**: a node of B1-d's shape at `Count.vsWordsOs` (`vsTs`)
weighs at most its frame's weight and `vsWs op (candidate μ r) (vsBsAt vsWordsOs Bvk μ r)`. -/
theorem vs_weight_le (op : Opcode) {μ r d : ℕ} (hc : B1.Whir.candidate μ r < 28) (hμ : μ - 22 < 7)
    (hd : d < 18) {Bvk : ℕ} {rd : Reader} {t : Tree} {args rets : List E}
    (h : FlatShape coreProgram "verify_sub" (B1.VerifySub.vsTs B2C.fs vsWordsOs Bvk μ r d) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ B2C.ωArm B2C.xmssArmC op "verify_sub" +
      (vsWs op (B1.Whir.candidate μ r) (B1.VerifySub.vsBsAt vsWordsOs Bvk μ r)).sum := by
  refine FlatShape.weight_le _ _ h hv hb
    (by simp [B1.VerifySub.vsTs, B1.namedP, B1.VerifySub.vsNames, B1.VerifySub.vsBsAt,
      B1.VerifySub.vsBsWith, B1.VerifySub.vsPs, vsWs]) ?_
  intro i hT hW rd' t' args' rets' hv' hb' hTi
  have hi : i < 16 := by simpa [vsWs] using hW
  have st := fun (k : ℕ) (hk : k < 33) (hnk : t'.name = vsStNames.getD k "") =>
    vsSt_weightLe op hk rd' t' args' rets' hnk hv' hb'
  interval_cases i <;>
    simp only [B1.VerifySub.vsTs, B1.VerifySub.vsNames, B1.VerifySub.vsBsAt,
      B1.VerifySub.vsBsWith, B1.VerifySub.vsPs, vsWs, List.getElem_cons_zero,
      List.getElem_cons_succ] at hTi ⊢
  · exact st 0 (by norm_num) hTi.1.1
  · exact st 0 (by norm_num) hTi.1.1
  · exact st 1 (by norm_num) hTi.1.1
  · exact st 2 (by norm_num) hTi.1.1
  · exact st 3 (by norm_num) hTi.1.1
  · exact st 4 (by norm_num) hTi.1.1
  · exact (st (8 + (μ - 22)) (by omega) (hTi.1.1.trans (squeezeName_eq hμ))).trans
      (le_vsSqMax op hμ)
  · exact st 5 (by norm_num) hTi.1.1
  · exact (st (15 + d) (by omega) (hTi.1.1.trans (busGrindName_eq hd))).trans (le_vsBgMax op hd)
  · exact div_of_ratio (krVbg_weight op rd' t' args' rets' hTi.1.1 hv' hb') hTi.1.2
  · exact (hTi.2 op rd' args' rets' hv' hb').trans (vtWB_eq op).le
  · exact div_of_ratio (krVk_weight op rd' t' args' rets' hTi.1.1 hv' hb') hTi.1.2
  · exact st 6 (by norm_num) hTi.1.1
  · exact st 7 (by norm_num) hTi.1.1
  · rw [openName_eq hc] at hTi
    exact kcOs_weightLe op hc rd' t' args' rets' hTi.1.1 hv' hb'
  · exact (hTi.2 op rd' args' rets' hv' hb').trans (termWB_eq op).le

/-- The ratio-bounded callees' words at their deployed bounds, `46339` and `56391`. -/
def vsBs0 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 46339, 0, 56391, 0, 0, 0, 0]

/-- `vsCountT` is the frame's weight and `vsWs` at the two ratio-bounded callees' words. -/
theorem vsCountT_eq (op : Opcode) : ∀ c < 28, (omT op).getD 0 0 +
    (vsWs op c vsBs0).sum = (vsCountT op).getD c 0 := by
  cases op <;> decide +kernel

theorem vsWs_mono (op : Opcode) (c : ℕ) {Bs Bs' : List ℕ} (h9 : Bs.getD 9 0 ≤ Bs'.getD 9 0)
    (h11 : Bs.getD 11 0 ≤ Bs'.getD 11 0) : (vsWs op c Bs).sum ≤ (vsWs op c Bs').sum := by
  have m := fun (A x y : ℕ) (h : x ≤ y) => Nat.div_le_div_right (c := 1000) (Nat.mul_le_mul_left A h)
  have := m (krVbgA op) _ _ h9; have := m (krVkA op) _ _ h11
  simp only [vsWs, List.sum_cons, List.sum_nil]
  omega

/-- **`verify_sub`'s instructions of `op` on a tree of B1-d's shape** (`vsTs` at
`Count.vsWordsOs`), `verify_bus_gkr`'s and `verify_keccak`'s bounds within `46339` and `56391`
words: at most `vsCountT op` at the candidate. -/
theorem vs_weight_le_vsTs (op : Opcode) {Bvk μ r d : ℕ} (hc : B1.Whir.candidate μ r < 28)
    (hμ : μ - 22 < 7) (hd : d < 18)
    (h5 : B1.VerifySub.vbgMax B2C.fs vsWords.K29 vsWords.R vsWords.K8 ≤ 46339) (h7 : Bvk ≤ 56391)
    {rd : Reader} {t : Tree} {args rets : List E}
    (h : FlatShape coreProgram "verify_sub" (B1.VerifySub.vsTs B2C.fs vsWordsOs Bvk μ r d) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ (vsCountT op).getD (B1.Whir.candidate μ r) 0 := by
  have h1 := vs_weight_le op hc hμ hd h hv hb
  have h2 := vsWs_mono op (B1.Whir.candidate μ r) (Bs := B1.VerifySub.vsBsAt vsWordsOs Bvk μ r)
    (Bs' := vsBs0) h5 h7
  have h3 := vsCountT_eq op _ hc
  have h4 := om_eq op (i := 0) (by norm_num)
  simp only [omNames, List.getD_cons_zero] at h4
  omega

end
end LeanVM.Guest.Budget
