/-
  LeanVM.Guest.Budget.VsCount

  `verify_sub`'s instructions on a child, per opcode, by its callees at the child's opening arm:
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
public import LeanVM.Guest.B1.VerifySub.CompleteBT
public import LeanVM.Guest.Count.VsWB

/-!
# `verify_sub`'s instructions per opening arm

`B1.VerifySub.vsNames μ r`: `verify_sub`'s thirteen callees in call order, its opening arm `openName μ`
twelfth. `vsWs op c Bs`: a bound on each callee's instructions of `op`, the static ones' and the
arm's (arm `c`, stack log `20 + c`) from the `V` certificates, `verify_tables`' and the terminal's from the `W`
certificates (`kcVtW`, `kcTermW`: their trees within B1's `vtWB`, `termWB`), `verify_bus_gkr`'s and
`verify_keccak`'s within their ratios of their words `Bs[5]`, `Bs[7]`. `vs_weight_le`: a
`verify_sub` node of B1-d's shape (`vsTs` at `Count.vsWords`) weighs at most its frame's weight and
`vsWs`. `vs_weight_le_vsTs`: with `verify_bus_gkr` and `verify_keccak` within `50050` and `65770`
words, at most `vsCountT op c`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Count

@[expose] public section

/-- **The callees' instructions of `op`** at the arm `c`, the two ratio-bounded ones within
the words `Bs`. -/
def vsWs (op : Opcode) (c : ℕ) (Bs : List ℕ) : List ℕ :=
  [(kcVsStT op).getD 0 0, (kcVsStT op).getD 0 0, (kcVsStT op).getD 1 0, (kcVsStT op).getD 2 0,
    (kcVsStT op).getD 2 0, krVbgA op * Bs.getD 5 0 / 1000, kcVtW op,
    krVkA op * Bs.getD 7 0 / 1000, (kcVsStT op).getD 3 0, (kcVsStT op).getD 4 0,
    (kcVsStT op).getD 5 0, (kcOsT op).getD c 0, kcTermW op]

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
    (∀ c < 11, (kvOkB op (osJ.getD c 0) ("open_stacked__L" ++ B1.Whir.natStr c) &&
      kvSBJ op (osJ.getD c 0) == (kcOsT op).getD c 0) = true) ∧
    (∀ i < 6, (kvOkB op (vsStJ.getD i 0) (vsStNames.getD i "") &&
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

/-- **The opening arm `c`.** -/
theorem kcOs_weightLe (op : Opcode) {c : ℕ} (hc : c < 11) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) ("open_stacked__L" ++ B1.Whir.natStr c)
      fun _ => (kcOsT op).getD c 0 :=
  weightLe_tab ((vsTab_parts op).1 c hc)

/-- **`verify_sub`'s static callees.** -/
theorem vsSt_weightLe (op : Opcode) {i : ℕ} (hi : i < 6) :
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

theorem openName_eq {μ : ℕ} (h1 : 20 ≤ μ) (h2 : μ ≤ 30) :
    B1.Whir.openName μ = "open_stacked__L" ++ B1.Whir.natStr (μ - 20) := by
  have h : μ - B1.Whir.minOpenLog < 11 := by simp only [B1.Whir.minOpenLog]; omega
  unfold B1.Whir.openName B1.Whir.openNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some, B1.Whir.natStr_eq]

theorem div_of_ratio {w A t B : ℕ} (h : 1000 * w ≤ A * t) (ht : t ≤ B) : w ≤ A * B / 1000 :=
  (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
    have := Nat.mul_le_mul_left A ht; rw [Nat.mul_comm w]; omega)

/-- **`verify_sub`'s instructions of `op`**: a node of B1-d's shape at `Count.vsWords` (`vsTs`)
weighs at most its frame's weight and `vsWs op (μ - 20) (vsBsAt vsWords Bvk μ r)`. -/
theorem vs_weight_le (op : Opcode) {μ r : ℕ} (hμ1 : 20 ≤ μ) (hμ2 : μ ≤ 30) {Bvk : ℕ}
    {rd : Reader} {t : Tree} {args rets : List E}
    (h : FlatShape coreProgram "verify_sub" (B1.VerifySub.vsTs B2C.fs vsWords Bvk μ r) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ B2C.ωArm B2C.xmssArmC op "verify_sub" +
      (vsWs op (μ - 20) (B1.VerifySub.vsBsAt vsWords Bvk μ r)).sum := by
  refine FlatShape.weight_le _ _ h hv hb
    (by simp [B1.VerifySub.vsTs, B1.namedP, B1.VerifySub.vsNames, B1.VerifySub.vsBsAt,
      B1.VerifySub.vsPs, vsWs]) ?_
  intro i hT hW rd' t' args' rets' hv' hb' hTi
  have hi : i < 13 := by simpa [vsWs] using hW
  have st := fun (k : ℕ) (hk : k < 6) (hnk : t'.name = vsStNames.getD k "") =>
    vsSt_weightLe op hk rd' t' args' rets' hnk hv' hb'
  interval_cases i <;>
    simp only [B1.VerifySub.vsTs, B1.namedP, B1.VerifySub.vsNames, B1.VerifySub.vsBsAt,
      B1.VerifySub.vsPs, vsWs, List.getElem_cons_zero, List.getElem_cons_succ,
      Budget.NamedWithin] at hTi ⊢
  · exact st 0 (by norm_num) hTi.1.1
  · exact st 0 (by norm_num) hTi.1.1
  · exact st 1 (by norm_num) hTi.1.1
  · exact st 2 (by norm_num) hTi.1.1
  · exact st 2 (by norm_num) hTi.1.1
  · exact div_of_ratio (krVbg_weight op rd' t' args' rets' hTi.1.1 hv' hb') hTi.1.2
  · exact (hTi.2 op rd' args' rets' hv' hb').trans (vtWB_eq op).le
  · exact div_of_ratio (krVk_weight op rd' t' args' rets' hTi.1.1 hv' hb') hTi.1.2
  · exact st 3 (by norm_num) hTi.1.1
  · exact st 4 (by norm_num) hTi.1.1
  · exact st 5 (by norm_num) hTi.1.1
  · rw [openName_eq hμ1 hμ2] at hTi
    exact kcOs_weightLe op (by omega) rd' t' args' rets' hTi.1.1 hv' hb'
  · exact (hTi.2 op rd' args' rets' hv' hb').trans (termWB_eq op).le

/-- `vsCountT` is the frame's weight and `vsWs` at the two ratio-bounded callees' words. -/
theorem vsCountT_eq (op : Opcode) : ∀ c < 11, (omT op).getD 0 0 +
    (vsWs op c [0, 0, 0, 0, 0, 50050, 0, 65770, 0, 0, 0, 0, 0]).sum = (vsCountT op).getD c 0 := by
  cases op <;> decide +kernel

theorem vsWs_mono (op : Opcode) (c : ℕ) {Bs Bs' : List ℕ} (h5 : Bs.getD 5 0 ≤ Bs'.getD 5 0)
    (h7 : Bs.getD 7 0 ≤ Bs'.getD 7 0) : (vsWs op c Bs).sum ≤ (vsWs op c Bs').sum := by
  have m := fun (A x y : ℕ) (h : x ≤ y) => Nat.div_le_div_right (c := 1000) (Nat.mul_le_mul_left A h)
  have := m (krVbgA op) _ _ h5; have := m (krVkA op) _ _ h7
  simp only [vsWs, List.sum_cons, List.sum_nil]
  omega

/-- **`verify_sub`'s instructions of `op` on a tree of B1-d's shape** (`vsTs` at `Count.vsWords`),
`verify_bus_gkr`'s and `verify_keccak`'s bounds within `50050` and `65770` words: at most
`vsCountT op` at the arm `μ - 20`. -/
theorem vs_weight_le_vsTs (op : Opcode) {Bvk μ r : ℕ} (hμ1 : 20 ≤ μ) (hμ2 : μ ≤ 30)
    (h5 : B1.VerifySub.vbgMax B2C.fs vsWords.K29 vsWords.R vsWords.K8 ≤ 50050) (h7 : Bvk ≤ 65770)
    {rd : Reader} {t : Tree} {args rets : List E}
    (h : FlatShape coreProgram "verify_sub" (B1.VerifySub.vsTs B2C.fs vsWords Bvk μ r) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ (vsCountT op).getD (μ - 20) 0 := by
  have h1 := vs_weight_le op hμ1 hμ2 h hv hb
  have h2 := vsWs_mono op (μ - 20) (Bs := B1.VerifySub.vsBsAt vsWords Bvk μ r)
    (Bs' := [0, 0, 0, 0, 0, 50050, 0, 65770, 0, 0, 0, 0, 0]) h5 h7
  have h3 := vsCountT_eq op _ (by omega : μ - 20 < 11)
  have h4 := om_eq op (i := 0) (by norm_num)
  simp only [omNames, List.getD_cons_zero] at h4
  omega

end
end LeanVM.Guest.Budget
