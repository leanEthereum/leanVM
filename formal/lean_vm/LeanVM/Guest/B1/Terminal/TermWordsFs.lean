/-
  LeanVM.Guest.B1.Terminal.TermWordsFs

  The terminal's callees' words at the frame sizes `B2C.fs`, from the words certificates (and
  `rs_eq_run`'s by hand).
-/

module

public import LeanVM.Guest.B1.Terminal.TermCompleteB
public import LeanVM.Guest.B1.Eq.RsWords
public import LeanVM.Guest.Memory.GuestWords

/-!
# The terminal's words at `B2C.fs`

The hypotheses of `check_opening_terminal_completeAtB`, `rst_completeAtB` and `rsw_completeAtB` at
`B2C.fs`:

* `eqc_totalLe_fs`: `eq_prefix_chain` within `184` (its certificate);
* `l15_totalLeOn_fs`, `l6_totalLeOn_fs`: `__loop14`, `__loop5` within `19`, `1644` words per
  iteration and their runs' one phantom frame, `19`, `27` (their certificates);
* `rsRows_totalLe_fs`: each `rs_eq_rows__L{r}`, `r < 8`, within `1489` words (their certificates);
* `l14_totalLeOn_fs`: `__loop13` from `1` (to its constant end `g^8`) within `8 · 661 + 661`;
* `cs_totalLe_fs`, `cs_fs_le`: each `column_selector__L{κ}`, `κ < 33`, within `157` words, its frame
  at most `157` (its certificate is its frame);
* `rs_totalLeOn_fs`: `rs_eq_run` on `c ≤ 34` coordinates within `8142` (`rs_totalLeOn34`:
  `50 + (27 + 4 · 1644) + 1489`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The frame sizes -/

/-- `B2C.fs` by core index. -/
theorem fsB_idx {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) :
    B2C.fs f = wfsJ j := by
  rcases hj : coreProgram[j]? with _ | fn
  · rw [hj] at h; cases h
  · rw [hj] at h
    obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h, ← hfn]
    exact wfs_eq hlt

theorem fs_rs : B2C.fs "rs_eq_run" = 50 := by
  rw [fsB_idx (j := 6) (by decide +kernel)]; decide +kernel

theorem fs_l6 : B2C.fs "__loop5" = 27 := by
  rw [fsB_idx (j := 80) (by decide +kernel)]; decide +kernel

theorem fs_l15 : B2C.fs "__loop14" = 19 := by
  rw [fsB_idx (j := 274) (by decide +kernel)]; decide +kernel

theorem fs_l14 : B2C.fs "__loop13" = 661 := by
  rw [fsB_idx (j := 273) (by decide +kernel)]; decide +kernel

/-! ## The callees' words -/

/-- `eq_prefix_chain` within `184` words. -/
theorem eqc_totalLe_fs : TotalLe coreProgram B2C.fs "eq_prefix_chain" fun _ => 184 :=
  fs_totalLe (by rw [wcertOf_of_idx (j := 5) (by decide +kernel)]; rfl :
    wcertOf "eq_prefix_chain" = .stat [] ⟨184, []⟩ [])

/-- A loop helper ending at its argument `1`, `K` words per iteration by its certificate: its run
from a start below its end within `K` per unit of its end's exponent and its one phantom frame,
`B2C.fs f`. -/
theorem loopTotalLeOn_fs {f : String} {K : ℕ} {ks : List (V × ℕ)}
    (hcf : wcertOf f = .loop none [] ⟨K, []⟩ ks) :
    TotalLeOn coreProgram B2C.fs f LoopPre fun a => logG (a.getD 1 0) * K + B2C.fs f := by
  intro rd t args rets hn ⟨a, e, ha, he, hae, heo⟩ hv hb
  have := fs_total_le_of_loop hcf hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  show _ ≤ logG (args.getD 1 0) * K + B2C.fs f
  rw [he, logG_spec heo]
  simp only [Aff.eval, List.map_nil, List.sum_nil, add_zero] at this
  have h2 : (e - a) * K ≤ e * K := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  omega

/-- `__loop14` within `19` words per iteration and its run's phantom frame, `19`. -/
theorem l15_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs "__loop14" LoopPre
      fun a => logG (a.getD 1 0) * 19 + B2C.fs "__loop14" :=
  loopTotalLeOn_fs (by rw [wcertOf_of_idx (j := 274) (by decide +kernel)]; rfl :
    wcertOf "__loop14" = .loop none [] ⟨19, []⟩ [])

/-- `__loop5` within `1644` words per iteration and its run's phantom frame, `27`. -/
theorem l6_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs "__loop5" LoopPre
      fun a => logG (a.getD 1 0) * 1644 + B2C.fs "__loop5" :=
  loopTotalLeOn_fs (by rw [wcertOf_of_idx (j := 80) (by decide +kernel)]; rfl :
    wcertOf "__loop5" = .loop none [] ⟨1644, []⟩ [])

/-- `__loop13` from `1` (to its constant end `g^8`) within `8 · 661 + 661` words (`8 · 661` and its
run's phantom frame, `661`). -/
theorem l14_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs "__loop13" (fun a => a.getD 0 0 = 1) fun _ => 5949 := by
  intro rd t args rets hn ha hv hb
  have := fs_total_le_of_loop (by rw [wcertOf_of_idx (j := 273) (by decide +kernel)]; rfl :
      wcertOf "__loop13" = .loop (some 8) [] ⟨661, []⟩ []) hn hv hb (a := 0) (e := 8)
    (by rw [ha]; simp [Parameters.addressOfIndex]) rfl (by decide) (by decide)
    (fun _ h => (List.not_mem_nil h).elim)
  rw [fs_l14] at this
  show t.total B2C.fs ≤ 5949
  simp only [Aff.eval, List.map_nil, List.sum_nil, add_zero] at this
  omega

/-- A constant words certificate within `B`. -/
def certLe (B : ℕ) : Cert → Bool
  | .stat [] ⟨b, []⟩ _ => decide (b ≤ B)
  | _ => false

theorem certLe_spec {B : ℕ} {c : Cert} (h : certLe B c = true) :
    ∃ b ks, c = .stat [] ⟨b, []⟩ ks ∧ b ≤ B := by
  unfold certLe at h
  split at h
  · exact ⟨_, _, rfl, of_decide_eq_true h⟩
  · cases h

/-- The column selectors: core functions `275 + κ`, constant words certificates within `157`, frames
within `157`. -/
theorem cs_ok : (List.range 33).all (fun κ =>
    decide ((coreProgram[275 + κ]?).map Fn.name = some (Tables.lName "column_selector" κ)) &&
      certLe 157 (Data.wcertJ (275 + κ)) && decide (wfsJ (275 + κ) ≤ 157)) = true := by
  decide +kernel

theorem cs_facts {κ : ℕ} (hκ : κ < 33) :
    (coreProgram[275 + κ]?).map Fn.name = some (Tables.lName "column_selector" κ) ∧
      certLe 157 (Data.wcertJ (275 + κ)) = true ∧ wfsJ (275 + κ) ≤ 157 := by
  have h := List.all_eq_true.mp cs_ok κ (List.mem_range.mpr hκ)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Each `column_selector__L{κ}` within `157` words.** -/
theorem cs_totalLe_fs : ∀ κ < 33,
    TotalLe coreProgram B2C.fs (Tables.lName "column_selector" κ) fun _ => 157 := by
  intro κ hκ rd t args rets hn hv hb
  obtain ⟨hname, hc, -⟩ := cs_facts hκ
  obtain ⟨b, ks, hcb, hb157⟩ := certLe_spec hc
  exact (fs_totalLe ((wcertOf_of_idx hname).trans hcb) rd t args rets hn hv hb).trans hb157

/-- **Each `column_selector__L{κ}`'s frame at most `157` words.** -/
theorem cs_fs_le : ∀ κ < 33, B2C.fs (Tables.lName "column_selector" κ) ≤ 157 := by
  intro κ hκ
  obtain ⟨hname, -, hF⟩ := cs_facts hκ
  rw [fsB_idx hname]
  exact hF

/-- The rows' specializations: core functions `81 + r`, constant words certificates within
`1489`. -/
theorem rsRows_ok : (List.range 8).all (fun r =>
    decide ((coreProgram[81 + r]?).map Fn.name = some (rsEqRowsNames.getD r "")) &&
      certLe 1489 (Data.wcertJ (81 + r))) = true := by
  decide +kernel

/-- **Each `rs_eq_rows__L{r}`, `r < 8`, within `1489` words.** -/
theorem rsRows_totalLe_fs : ∀ r < 8,
    TotalLe coreProgram B2C.fs (rsEqRowsNames.getD r "") fun _ => 1489 := by
  intro r hr rd t args rets hn hv hb
  have h := List.all_eq_true.mp rsRows_ok r (List.mem_range.mpr hr)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨b, ks, hcb, hbB⟩ := certLe_spec h.2
  exact (fs_totalLe ((wcertOf_of_idx h.1).trans hcb) rd t args rets hn hv hb).trans hbB

/-- **`rs_eq_run` on at most `34` coordinates within `8142` words** (`rs_totalLeOn34`:
`50 + (27 + 4 · 1644) + 1489`). -/
theorem rs_totalLeOn_fs : ∀ c ≤ 34,
    TotalLeOn coreProgram B2C.fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c) fun _ => 8142 := by
  intro c hc rd t args rets hn hp hv hb
  refine (rs_totalLeOn34 l6_totalLeOn_fs rsRows_totalLe_fs c hc rd t args rets hn hp hv hb).trans ?_
  show B2C.fs "rs_eq_run" + (B2C.fs "__loop5" + 4 * 1644) + 1489 ≤ 8142
  rw [fs_rs, fs_l6]

/-! ## At `B2C.fs` -/

end
end LeanVM.Guest.B1.VerifySub
