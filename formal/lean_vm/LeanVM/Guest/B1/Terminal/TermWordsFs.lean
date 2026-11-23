/-
  LeanVM.Guest.B1.Terminal.TermWordsFs

  The terminal's callees' words at the frame sizes `B2C.fs`, from the words certificates (and
  `rs_eq_run`'s by hand).
-/

module

public import LeanVM.Guest.B1.Terminal.TermCompleteB
public import LeanVM.Guest.B1.Eq.RsWords
public import LeanVM.Guest.Memory.GuestWords
public import LeanVM.Guest.Data.NameStrings

/-!
# The terminal's words at `B2C.fs`

The hypotheses of `check_opening_terminal_completeAtB`, `rst_completeAtB` and `rsw_completeAtB` at
`B2C.fs`:

* `eqc_totalLe_fs`: `eq_prefix_chain` within `184` (its certificate);
* `l15_totalLeOn_fs`, `l6_totalLeOn_fs`: `check_opening_terminal_loop0`, `rs_eq_run_loop0` within
  `19` (their certificate: `17`), `1641` words per iteration and their runs' one phantom frame,
  `17`, `25`;
* `rsRows_totalLe_fs`: each `rs_eq_rows__L{r}`, `r < 8`, within `1489` words (their certificates);
* `l14_totalLeOn_fs`: `ring_switch_target_loop0` from `1` (to its constant end `g^8`) within `3204`
  (`8 · 354 + 354`);
* `cs_totalLe_fs`, `cs_fs_le`: each `column_selector__L{κ}`, `κ < 31`, within `157` words, its frame
  at most `157` (its certificate is its frame);
* `rs_totalLeOn_fs`: `rs_eq_run` on `c ≤ 34` coordinates within `8526` (`rs_totalLeOn34`:
  `57 + (25 + 4 · 1641) + 1489 + 384`); `rs_bound_fs`: the same bounds as `RsBound`, what
  `rsw_completeAtB` takes.
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

theorem fs_rs : B2C.fs "rs_eq_run" = 57 := by
  rw [fsB_idx (j := idx% «rs_eq_run») (by decide +kernel)]; decide +kernel

theorem fs_l6 : B2C.fs name% «rs_eq_run_loop0» = 25 := by
  rw [fsB_idx (j := idx% «rs_eq_run_loop0») (by decide +kernel)]; decide +kernel

theorem fs_l15 : B2C.fs name% «check_opening_terminal_loop0» = 17 := by
  rw [fsB_idx (j := idx% «check_opening_terminal_loop0») (by decide +kernel)]; decide +kernel

theorem fs_l14 : B2C.fs name% «ring_switch_target_loop0» = 354 := by
  rw [fsB_idx (j := idx% «ring_switch_target_loop0») (by decide +kernel)]; decide +kernel

/-! ## The callees' words -/

/-- `eq_prefix_chain` within `184` words. -/
theorem eqc_totalLe_fs : TotalLe coreProgram B2C.fs "eq_prefix_chain" fun _ => 184 :=
  fs_totalLe (by rw [wcertOf_of_idx (j := idx% «eq_prefix_chain») (by decide +kernel)]; rfl :
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

/-- `check_opening_terminal_loop0` within `19` words per iteration (its certificate: `17`) and its
run's phantom frame, `17`. -/
theorem l15_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs name% «check_opening_terminal_loop0» LoopPre
      fun a => logG (a.getD 1 0) * 19 + B2C.fs name% «check_opening_terminal_loop0» := by
  intro rd t args rets hn hp hv hb
  have h := loopTotalLeOn_fs (by rw [wcertOf_of_idx (j := idx% «check_opening_terminal_loop0»)
                         (by decide +kernel)]; rfl :
    wcertOf name% «check_opening_terminal_loop0» = .loop none [] ⟨17, []⟩ []) rd t args rets hn hp hv hb
  have := Nat.mul_le_mul_left (logG (args.getD 1 0)) (show 17 ≤ 19 by decide)
  dsimp only at h ⊢
  omega

/-- `rs_eq_run_loop0` within `1641` words per iteration and its run's phantom frame, `25`. -/
theorem l6_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs name% «rs_eq_run_loop0» LoopPre
      fun a => logG (a.getD 1 0) * 1641 + B2C.fs name% «rs_eq_run_loop0» :=
  loopTotalLeOn_fs (by rw [wcertOf_of_idx (j := idx% «rs_eq_run_loop0») (by decide +kernel)]; rfl :
    wcertOf name% «rs_eq_run_loop0» = .loop none [] ⟨1641, []⟩ [])

/-- `ring_switch_target_loop0` from `1` (to its constant end `g^8`) within `3204` words (`8 · 354`
and its run's phantom frame, `354`). -/
theorem l14_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs name% «ring_switch_target_loop0» (fun a => a.getD 0 0 = 1) fun _
        => 3204 := by
  intro rd t args rets hn ha hv hb
  have := fs_total_le_of_loop (by rw [wcertOf_of_idx (j := idx% «ring_switch_target_loop0»)
                                    (by decide +kernel)]; rfl :
      wcertOf name% «ring_switch_target_loop0» = .loop (some 8) [] ⟨354,
          []⟩ []) hn hv hb (a := 0) (e := 8)
    (by rw [ha]; simp [Parameters.addressOfIndex]) rfl (by decide) (by decide)
    (fun _ h => (List.not_mem_nil h).elim)
  rw [fs_l14] at this
  show t.total B2C.fs ≤ 3204
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

/-- The column selectors: core functions `idx% «column_selector__L0» + κ`, constant words
certificates within `157`, frames within `157`. -/
theorem cs_ok : (List.range 31).all (fun κ =>
    decide ((coreProgram[idx% «column_selector__L0» + κ]?).map Fn.name = some (Tables.lName "column_selector" κ)) &&
      certLe 157 (Data.wcertJ (idx% «column_selector__L0» + κ)) &&
      decide (wfsJ (idx% «column_selector__L0» + κ) ≤ 157)) = true := by
  decide +kernel

theorem cs_facts {κ : ℕ} (hκ : κ < 31) :
    (coreProgram[idx% «column_selector__L0» + κ]?).map Fn.name = some (Tables.lName "column_selector" κ) ∧
      certLe 157 (Data.wcertJ (idx% «column_selector__L0» + κ)) = true ∧
      wfsJ (idx% «column_selector__L0» + κ) ≤ 157 := by
  have h := List.all_eq_true.mp cs_ok κ (List.mem_range.mpr hκ)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Each `column_selector__L{κ}` within `157` words.** -/
theorem cs_totalLe_fs : ∀ κ < 31,
    TotalLe coreProgram B2C.fs (Tables.lName "column_selector" κ) fun _ => 157 := by
  intro κ hκ rd t args rets hn hv hb
  obtain ⟨hname, hc, -⟩ := cs_facts hκ
  obtain ⟨b, ks, hcb, hb157⟩ := certLe_spec hc
  exact (fs_totalLe ((wcertOf_of_idx hname).trans hcb) rd t args rets hn hv hb).trans hb157

/-- **Each `column_selector__L{κ}`'s frame at most `157` words.** -/
theorem cs_fs_le : ∀ κ < 31, B2C.fs (Tables.lName "column_selector" κ) ≤ 157 := by
  intro κ hκ
  obtain ⟨hname, -, hF⟩ := cs_facts hκ
  rw [fsB_idx hname]
  exact hF

/-- The rows' specializations: core functions `idx% «rs_eq_rows__L0» + r`, constant words certificates within
`1489`. -/
theorem rsRows_ok : (List.range 8).all (fun r =>
    decide ((coreProgram[idx% «rs_eq_rows__L0» + r]?).map Fn.name = some (rsEqRowsNames.getD r "")) &&
      certLe 1489 (Data.wcertJ (idx% «rs_eq_rows__L0» + r))) = true := by
  decide +kernel

/-- **Each `rs_eq_rows__L{r}`, `r < 8`, within `1489` words.** -/
theorem rsRows_totalLe_fs : ∀ r < 8,
    TotalLe coreProgram B2C.fs (rsEqRowsNames.getD r "") fun _ => 1489 := by
  intro r hr rd t args rets hn hv hb
  have h := List.all_eq_true.mp rsRows_ok r (List.mem_range.mpr hr)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨b, ks, hcb, hbB⟩ := certLe_spec h.2
  exact (fs_totalLe ((wcertOf_of_idx h.1).trans hcb) rd t args rets hn hv hb).trans hbB

/-- **`rs_eq_run` on at most `34` coordinates within `8526` words** (`rs_totalLeOn34`:
`57 + (25 + 4 · 1641) + 1489 + 384 ≤ 8526`). -/
theorem rs_totalLeOn_fs : ∀ c ≤ 34,
    TotalLeOn coreProgram B2C.fs "rs_eq_run" (fun a => a.getD 2 0 = gen ^ c) fun _ => 8526 := by
  intro c hc rd t args rets hn hp hv hb
  refine (rs_totalLeOn34 B2C.fs_tailKey_le l6_totalLeOn_fs rsRows_totalLe_fs c hc rd t args rets hn hp hv
    hb).trans ?_
  show B2C.fs "rs_eq_run" + (B2C.fs name% «rs_eq_run_loop0» + 4 * 1641) + 1489 + 384 ≤ 8526
  rw [fs_rs, fs_l6]; decide

/-- **`rs_eq_run`'s callees' words at `B2C.fs`, its own on at most `34` coordinates within `8526`**
(`RsBound`: `57 + (25 + 4 · 1641) + 1489 + 384 ≤ 8526`). -/
theorem rs_bound_fs : RsBound B2C.fs 8526 :=
  ⟨B2C.fs_tailKey_le, 1641, 1489, l6_totalLeOn_fs, rsRows_totalLe_fs, by rw [fs_rs, fs_l6]; decide⟩

/-! ## At `B2C.fs` -/

end
end LeanVM.Guest.B1.VerifySub
