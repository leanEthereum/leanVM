/-
  LeanVM.Guest.Sound

  B2's soundness for the deployed bytecode: every compiled function's contract from its checks,
  and `main`'s relation from a halting run of it.
-/

module

public import LeanVM.Guest.CheckSound
public import LeanVM.Guest.Checked
public import LeanVM.Guest.End
public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.CoreNames
public import LeanVM.Guest.JumpTable

/-!
# B2 soundness

The contracts are checker K's over `glob`: function `j`'s entry, `Check.Pre glob L j` and
`Check.Post coreProgram glob L j`.

* `b2_step`: a function's contract for runs shorter than `n + 1`, given every contract for runs
  shorter than `n` (`checkWins_run` on its checked windows, `Checked.all_ok`). Each window after
  the first takes its memory bounds and semantic pairs from the statements before it: none but in
  `verify_sub`, whose second window, before `check_opening_terminal`, takes the column selectors'
  bound from `VsKnown` (B1's, over the exponent tables its precondition carries).
* `b2_main`: `main`'s relation from a halting run from its entry at `fp = 1`, the jump table
  written. Its second window starts after `exponent_tables`, whose returns it knows to be the
  tables (`exponent_tables_iff`).

Names are unique in `coreProgram` (`coreProgram_find_getElem`), and the jump table the checks
read is the one `__jump_tables` writes (`JumpTable.jt_of_jumpTables`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec

@[expose] public section

theorem certOf_pows (j : ℕ) : (certOf j).facts.pows = Data.powTree := by
  unfold certOf
  split
  rfl

theorem certOf_pows_ok (j : ℕ) : (certOf j).facts.pows.Ok := by
  rw [certOf_pows]
  exact PowTree.ok_of_okW Checked.powTree_ok

theorem functions_length : Data.functions.length = nFns := by decide +kernel

theorem coreProgram_length' : coreProgram.length + 1 = nFns := by
  rw [coreProgram_length]; rfl

theorem fnOf_mem {j : ℕ} (h : j < nFns) : fnOf j ∈ Data.functions := by
  unfold fnOf
  rw [nth_eq (functions_length ▸ h)]
  exact List.getElem_mem _

theorem coreOf_find {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    coreProgram.find? (coreOf j).name = some (coreOf j) := by
  have h : j - 1 < coreProgram.length := by have := coreProgram_length'; omega
  unfold coreOf
  rw [nth_eq h]
  exact coreProgram_find_getElem h

theorem winOk_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    ∀ i ≤ (certOf j).cuts.length, checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true :=
  Checked.all_ok j h1 h2

theorem jtHolds_of {κ : ℕ} {L : MemImage κ} (h : JumpTables L) : JTHolds glob L :=
  JumpTable.jt_of_jumpTables h (PowTree.ok_of_okW Checked.powTree_ok)

theorem known_plain {j : ℕ} (h0j : 1 ≤ j) (hj : j < nFns) (h1 : j ≠ 1) (h16 : j ≠ 16) {κ : ℕ}
    {L : MemImage κ} {fp : K} {i : ℕ} (hi : i ≤ (certOf j).cuts.length) (h0 : 0 < i) :
    MemKnown L fp ((certOf j).cutAt i).known ∧ SemHolds glob L fp ((certOf j).cutAt i).sems := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hall := List.all_eq_true.mp (Checked.all_plain j h0j hj h1 h16)
    ((certOf j).cuts[i]'(by omega))
    (List.getElem_mem _)
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hall
  have hc : (certOf j).cutAt (i + 1) = (certOf j).cuts[i]'(by omega) := by
    simp only [Cert.cutAt]
    exact nth_eq _
  rw [hc, hall.1, hall.2]
  exact ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩

/-! ## `verify_sub`'s obligation -/

theorem vs_cuts : (certOf 16).cuts.length = 1 := by decide +kernel

theorem vs_cut : ((certOf 16).cutAt 1).start = 1927 ∧ ((certOf 16).cutAt 1).known = [(1106, 92, 29)] ∧
    ((certOf 16).cutAt 1).sems = [] := by decide +kernel

theorem vs_cells : (certOf 16).locs.getD 4 0 = 6 ∧ (certOf 16).locs.getD 5 0 = 7 ∧
    (certOf 16).locs.getD 1631 0 = 1106 := by
  decide +kernel

theorem vs_sem : (certOf 16).sem = [(6, 7)] := by decide +kernel

theorem coreOf_16 : coreOf 16 = Data.core15 := rfl

theorem known_vs (hvs : B1.VerifySub.VsKnown) {κ : ℕ} {L : MemImage κ} (h16 : minLogMem ≤ κ)
    (h32 : κ ≤ maxLogMem) {fp : K} (hsem : SemHolds glob L fp (certOf 16).sem) {i : ℕ}
    (hi : i ≤ (certOf 16).cuts.length) (h0 : 0 < i)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf 16))
      ((coreOf 16).body.take ((certOf 16).cutAt i).start) True (fun _ ↦ True)) :
    MemKnown L fp ((certOf 16).cutAt i).known ∧ SemHolds glob L fp ((certOf 16).cutAt i).sems := by
  obtain rfl : i = 1 := by rw [vs_cuts] at hi; omega
  obtain ⟨hst, hkn, hsm⟩ := vs_cut
  obtain ⟨c4, c5, c1631⟩ := vs_cells
  rw [hkn, hsm]
  refine ⟨fun m hm c hc ↦ ?_, fun _ h ↦ by simp at h⟩
  simp only [List.mem_singleton] at hm
  subst hm
  rw [hst, coreOf_16] at hl
  have ht : B1.ExpTables L.read (valG L fp (certOf 16) (.n 4)) (valG L fp (certOf 16) (.n 5)) := by
    have := hsem (6, 7) (by rw [vs_sem]; exact List.mem_singleton_self _)
    simp only [valG, c4, c5]
    exact this
  have := hvs L.read ⟨κ, h16, h32, L, rfl⟩ _ ht hl c hc
  simpa only [valG, Core.V.idx, c1631] using this

/-! ## `main`'s obligation -/

theorem main_cut : (certOf 1).cuts.length = 1 ∧ ((certOf 1).cutAt 1).known = [] ∧
    ((certOf 1).cutAt 1).sems = [((certOf 1).locs.getD 65 0, (certOf 1).locs.getD 66 0)] := by
  decide +kernel

theorem main_call : ((coreOf 1).body.take ((certOf 1).cutAt 1).start) =
    (coreOf 1).body.take (((certOf 1).cutAt 1).start - 1) ++
      [.call "exponent_tables" [] [.n 65, .n 66]] := by
  have h : ((coreOf 1).body[((certOf 1).cutAt 1).start - 1]?) =
      some (.call "exponent_tables" [] [.n 65, .n 66]) := rfl
  obtain ⟨m, hm⟩ : ∃ m, ((certOf 1).cutAt 1).start = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by decide +kernel)).symm⟩
  rw [hm, Nat.add_sub_cancel] at h ⊢
  rw [List.take_add_one, h]
  rfl

theorem known_main {κ : ℕ} {L : MemImage κ} {fp : K} {i : ℕ} (hi : i ≤ (certOf 1).cuts.length)
    (h0 : 0 < i)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf 1))
      ((coreOf 1).body.take ((certOf 1).cutAt i).start) True (fun _ ↦ True)) :
    MemKnown L fp ((certOf 1).cutAt i).known ∧ SemHolds glob L fp ((certOf 1).cutAt i).sems := by
  obtain ⟨hlen, hkn, hsm⟩ := main_cut
  obtain rfl : i = 1 := by rw [hlen] at hi; omega
  rw [hkn, hsm]
  refine ⟨fun _ h ↦ by simp at h, fun p hp ↦ ?_⟩
  simp only [List.mem_singleton] at hp
  subst hp
  have hnr : Stmt.noRetList ((coreOf 1).body.take (((certOf 1).cutAt 1).start - 1)) = true := by
    decide +kernel
  rw [main_call, holdsList_append] at hl
  have hcall := ((holdsList_noRet _ hnr _ _).mp hl).2
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hcall
  have := (B1.exponent_tables_iff L.read [] _).mp hcall.1
  exact this

/-! ## The contracts -/

/-- **B2's step**: each contract for runs shorter than `n + 1`, given all of them for runs
shorter than `n`. -/
theorem b2_step (hvs : B1.VerifySub.VsKnown) :
    ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ n,
      (∀ j, FunSpecLt guest L n (glob.sig j).entry (Check.Pre glob L j)
        (Check.Post coreProgram glob L j)) →
      ∀ i, FunSpecLt guest L (n + 1) (glob.sig i).entry (Check.Pre glob L i)
        (Check.Post coreProgram glob L i) := by
  intro κ L h16 h32 n hlt j fp k hk hpre hsafe
  obtain ⟨hgood, hjt, henv, hbnd, hmem, hsem⟩ := hpre
  have hj : 2 ≤ j ∧ j < nFns := by simpa [glob, good] using hgood
  have hc := winOk_of (j := j) (by omega) hj.2
  have h1 : (j == 1) = false := by simp; omega
  rw [h1] at hc
  have hfp := checkWin_fpOne (hc 0 (Nat.zero_le _))
  obtain ⟨hrel, hpost, hret⟩ := checkWins_run (Prog := coreProgram) hc (fnOf_mem hj.2)
    (coreOf_find (by omega) hj.2) (certOf_pows_ok j) h32 (fun h ↦ by rw [← hfp] at h; cases h)
    (fun i ↦ (hlt i).mono (by omega)) hjt henv hbnd hmem hsem
    (fun i hi h0 hl ↦ by
      by_cases h16 : j = 16
      · subst h16
        exact known_vs hvs h16 h32 hsem hi h0 hl
      · exact known_plain (by omega) hj.2 (by omega) h16 hi h0)
    hsafe
  obtain ⟨k', hk', r, hr, hs⟩ := hret rfl
  exact ⟨k', hk', r, hr, ⟨hrel, hpost⟩, hs⟩

theorem main_facts : (certOf 1).facts.env = [] ∧ (certOf 1).pre = [] ∧ (certOf 1).mem = [] ∧
    (certOf 1).sem = [] ∧ (certOf 1).nret = 0 ∧ (coreOf 1).params = [] ∧ (coreOf 1).name = "main" := by
  decide +kernel

theorem fnOf_1 : (fnOf 1).entry = mainEntry := rfl

/-- **B2 at `main`**: a halting run from `main`'s entry at `fp = 1`, the jump table written and
every contract holding for runs shorter than it, gives `main`'s relation. -/
theorem b2_main :
    ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → JumpTables L → ∀ k,
      (∀ j, FunSpecLt guest L k (glob.sig j).entry (Check.Pre glob L j)
        (Check.Post coreProgram glob L j)) →
      Safe guest L k ⟨gpow mainEntry, 1⟩ → coreProgram.Rel L.read "main" [] [] := by
  intro κ L _ h32 hjtab k hlt hsafe
  have hc := winOk_of (j := 1) le_rfl (by decide)
  obtain ⟨henv, hpre, hmem, hsem, hnret, hparams, hname⟩ := main_facts
  obtain ⟨hrel, -, -⟩ := checkWins_run (Prog := coreProgram) (fp := 1) hc (fnOf_mem (by decide))
    (coreOf_find le_rfl (by decide)) (certOf_pows_ok 1) h32 (fun _ ↦ rfl) hlt
    (jtHolds_of hjtab) (by rw [Facts.entryEnv, henv]; exact EnvHolds.nil)
    (by rw [hpre]; intro _ h; simp at h) (by rw [hmem]; intro _ h; simp at h)
    (by rw [hsem]; intro _ h; simp at h) (fun i hi h0 hl ↦ known_main hi h0 hl)
    (by rw [fnOf_1]; exact hsafe)
  rw [hname, hparams, hnret] at hrel
  exact hrel

end
end LeanVM.Guest.End
