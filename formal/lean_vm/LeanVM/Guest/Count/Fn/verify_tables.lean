/-
  LeanVM.Guest.Count.Fn.verify_tables

  `verify_tables`' words interface at the deployed frame sizes and weights (`vtWords`, `vtWeights`), from the words
  certificates (`wSB`, `wSK`), the `W` count certificates (`kuSB`, `kuSK`) and B1-c's `shared_selector_tables`
  bounds (`ss_totalLeOn`, `ss_weightLeOn`), its bound written out by the kernel (`vtMaxV`) and its weight bound
  as one closed form (`vtWForm`, `vtWeightB_form`).
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Count.StaticW
public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.B1.Tables.VtWords
public import LeanVM.Guest.B1.Selectors.SharedWeight
public import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

theorem vtPairs_ok : (vtPairs.all fun p => wOkB p.2 p.1) = true := by decide +kernel

theorem vtPairs_names : B1.Tables.vtKidS.filter (fun g => g != (name% verify_tables_loop0) &&
    g != "shared_selector_tables" &&
    g != (name% shared_selector_tables_loop0)) =
    vtPairs.map Prod.fst := by decide +kernel

theorem vt_kids_totalLe : ∀ g ∈ B1.Tables.vtKidS, g ≠ (name% verify_tables_loop0) →
    g ≠ (name% shared_selector_tables_loop0) →
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

theorem vtPairs_okW (op : Opcode) : (vtPairs.all fun p => kuOkB op p.2 p.1) = true := by
  cases op <;> decide +kernel

theorem vt_kids_weightLe (op : Opcode) : ∀ g ∈ B1.Tables.vtKidS, g ≠ (name% verify_tables_loop0) →
    g ≠ (name% shared_selector_tables_loop0) →
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

/-- **`verify_tables`' words facts at `B2C.fs`.** -/
noncomputable def vtWords : B1.Tables.VtWords B2C.fs where
  Kf := wSB
  Ksh := B2C.fs "shared_selector_tables" +
    (B2C.fs (name% shared_selector_tables_loop0) + 15 * (wSK (name% shared_selector_tables_loop0) - B2C.fs (name% shared_selector_tables_loop0))) + kSp
  K10 := wSK (name% verify_tables_loop0) - B2C.fs (name% verify_tables_loop0)
  hKf := vt_kids_totalLe
  hsh := B1.Tables.ss_totalLeOn (wSK (name% shared_selector_tables_loop0) - B2C.fs (name% shared_selector_tables_loop0)) kSp
    (by simpa only [wSKt_eq] using wSKt_totalLeOn (j := idx% shared_selector_tables_loop0) (by decide +kernel)) sp_totalLe
  h10 := by simpa only [wSKt_eq] using wSKt_totalLeOn (j := idx% verify_tables_loop0) (by decide +kernel)

/-- **`verify_tables`' weights facts at the xmss arm's weights.** -/
noncomputable def vtWeights : B1.Tables.VtWeights fun op => B2C.ωArm B2C.xmssArmC op where
  Kvw := kuSB
  Wss := fun op => B2C.ωArm B2C.xmssArmC op "shared_selector_tables" + 15 * kuSK op (name% shared_selector_tables_loop0) +
    kSpW op
  Kw10 := fun op => kuSK op (name% verify_tables_loop0)
  hKvw := vt_kids_weightLe
  hssw := fun op => B1.Tables.ss_weightLeOn _ _ _
    (loopW_of (kuSK_loop (j := idx% shared_selector_tables_loop0) (by cases op <;> decide +kernel))) (sp_weightLe op)
  h10w := fun op => loopW_of (kuSK_loop (j := idx% verify_tables_loop0) (by cases op <;> decide +kernel))

/-- **`verify_tables`' weight bound as one closed form** in an opcode's frame weights `ω` and the `W`
certificates' bounds `KB`, `KK` (`kuSB`, `kuSK` at the opcode): what `Count/VsWB` instantiates. -/
noncomputable def vtWForm (ω KB KK : String → ℕ) : ℕ :=
  ω "verify_tables" + (B1.Tables.vtBs KB
    (ω "shared_selector_tables" + 15 * KK (name% shared_selector_tables_loop0) +
      max (max (KB "sel_partial_nibble__L0") (KB "sel_partial_nibble__L1"))
        (max (KB "sel_partial_nibble__L2") (KB "sel_partial_nibble__L3")))
    (32 * KK (name% verify_tables_loop0))).sum

theorem vtWeightB_form (op : Opcode) :
    B1.Tables.vtWeightB vtWeights op = vtWForm (B2C.ωArm B2C.xmssArmC op) (kuSB op) (kuSK op) := by
  unfold B1.Tables.vtWeightB vtWForm
  dsimp only [vtWeights, kSpW]

/-- `verify_tables`' largest bound, at the search tree's lookups. -/
kernel_lit vtMaxV : ℕ := B1.Tables.vtMaxOf fsFast wSBFast
  (fsFast "shared_selector_tables" + (fsFast (name% shared_selector_tables_loop0) +
    15 * (wSKFast (name% shared_selector_tables_loop0) - fsFast (name% shared_selector_tables_loop0))) +
    max (max (wSBFast "sel_partial_nibble__L0") (wSBFast "sel_partial_nibble__L1"))
      (max (wSBFast "sel_partial_nibble__L2") (wSBFast "sel_partial_nibble__L3")))
  (wSKFast (name% verify_tables_loop0) - fsFast (name% verify_tables_loop0))

theorem vtWordsMax_eq : B1.Tables.vtMax B2C.fs vtWords = vtMaxV := by
  unfold B1.Tables.vtMax
  rw [← vtMaxV_eq, fsFast_eq, wSBFast_eq, wSKFast_eq]; dsimp only [vtWords, kSp]

end
end LeanVM.Guest.Count
