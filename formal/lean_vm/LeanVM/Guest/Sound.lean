/-
  LeanVM.Guest.Sound

  B2's soundness for the deployed bytecode: every compiled function's contract from its checks,
  and `main`'s relation from a halting run of it.
-/

module

public import LeanVM.Guest.SoundFacts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# B2 soundness

The contracts are checker K's over `glob`: function `j`'s entry, `Check.Pre glob L j` and
`Check.Post coreProgram glob L certByName (Check.EnteredAt glob L) j`, on the run from `(g^0, 1)`
(`FunSpecLtReached`): each callee's body holds at its frame, its calls located at frames entered
on that run (`Check.EnteredAt`).

* `b2_step`: a function's contract for runs shorter than `n + 1`, given every contract for runs
  shorter than `n` (`checkWins_run` on its checked windows, `Checked.all_ok`). Each window after
  the first takes its memory bounds and semantic tuples from the statements before it, the
  function's cut obligations (`CutsKnown`, `cutsKnown_of`): none for a `Plain` function; in
  `verify_sub`, the window table `tabs` it hands `open_stacked` (`VsTabsKnown`, proved here from
  the window section of the exponent table its precondition carries, `vsTabsKnown_proved`) and,
  from its call of `check_stack_terminal` on, the bounds of the `52` kappas `kaps` it hands it
  (`VsKapsKnown`), which `stack_selectors` dispatches on; in the windowed Merkle walks,
  `WalkKnown`.
* `b2_mainL`: `main`'s relation from a halting run from its entry at `fp = 1`, the jump table
  written. Its second window starts after `exponent_tables`, whose return it knows to be the
  table (`ExpTablesSound`).

`VsKapsKnown` and `ExpTablesSound` are statements about the core IR alone (`coreProgram.Rel`),
B1's to prove (`certify_stack` and the range check of the stack's log in `verify_sub`, and
`exponent_tables`); `WalkKnown` is stated at the certificates' cuts, B1's core IR facts on the
walks read through the certificates' cells. The theorems here take them as hypotheses.

Names are unique in `coreProgram` (`coreProgram_find_getElem`), and the jump table the checks
read is the one `__jump_tables` writes (`JumpTable.jt_of_jumpTables`). The certificates' facts
are `SoundFacts.lean`'s.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec

@[expose] public section

/-! ## B1's obligations -/

/-- **`verify_sub`'s obligation at its call of `check_stack_terminal`** (B1's): on every memory
image, over the exponent table at `verify_sub`'s argument `4` (`g_squares`), its first `vsKapsAt`
statements, up to the call, put each of the `52` entries of `kaps` (the value `vsKaps`, the kappas
`certify_stack` returns, each at most the stack's log, which `verify_sub` range checks below
`g^31`) among the powers `g^e`, `e < 31`, which `stack_selectors` dispatches on. -/
def VsKapsKnown : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ σ : Val,
    B1.ExpTables L.read (σ (.n (val% «verify_sub» "g_squares"))) →
    B1.ExpWinTab L.read (σ (.n (val% «verify_sub» "g_squares"))) →
    Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf (fn_idx% «verify_sub»)).body.take vsKapsAt) True (fun _ ↦ True) →
      ∀ b < vsKapsBlocks, ∃ e < vsKapsBound, LoadHolds L.read (σ (.n vsKaps)) b (ofK (addressOfIndex e))

/-- **`verify_sub`'s obligation on the stack's log at its call of `check_stack_terminal`** (B1's): on
every memory image, its first `vsKapsAt` statements, up to the call, put the stack's log it hands
it (the value `vsGmv`, `certify_stack`'s `gmv`) at `g^(16 + e)`, `e < 15`, which `verify_sub`
range checks (`size_sel = gmv·g^-16`) and `check_stack_terminal` dispatches on, shifted. -/
def VsGmvKnown : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ σ : Val,
    Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf (fn_idx% «verify_sub»)).body.take vsKapsAt) True (fun _ ↦ True) →
      ∃ e < vsGmvN, σ (.n vsGmv) = ofK (addressOfIndex (vsGmvD + e))

/-- **`verify_sub`'s window table** at `tabs` (the value `vsTabs`, `g_squares·g^178`), from the
window section of the exponent table at its argument `4`, once its statements up to `tabs`' hold;
`open_stacked` assumes it (`tagTabs`). Proved (`vsTabsKnown_proved`). -/
def VsTabsKnown : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), ∀ σ : Val,
    B1.ExpWinTab L.read (σ (.n (val% «verify_sub» "g_squares"))) →
    Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf (fn_idx% «verify_sub»)).body.take (vsTabsAt + 2)) True (fun _ ↦ True) →
      B1.WinTabs L.read (σ (.n vsTabs))

/-- **`exponent_tables`' relation** (B1's): its returned pointer holds the exponent table and its
window section. -/
def ExpTablesSound : Prop :=
  ∀ (rd : Reader) (q : E), coreProgram.Rel rd "exponent_tables" [] [q] →
    B1.ExpTables rd q ∧ B1.ExpWinTab rd q

/-- **B1's obligations at function `j`'s cuts**: on every memory image, from the semantic tuples
and memory bounds of `j`'s entry and the statements before each cut `i > 0` of `j`'s certificate,
under its frame's valuation, the cut's memory bounds, conditional memory bounds and semantic
tuples. They are `VsTabsKnown` and `VsKapsKnown` for `verify_sub`, the walks' (`WalkKnown`) for the windowed Merkle
walks, and nothing (`known_of_plain`) for a function whose cuts hand nothing on. -/
def CutsKnown (j : ℕ) : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ fp : K,
    MemPre L fp (certOf j).mem → SemHolds glob L fp (certOf j).sem →
    ∀ i ≤ (certOf j).cuts.length, 0 < i →
      Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf j))
        ((coreOf j).body.take ((certOf j).cutAt i).start) True (fun _ ↦ True) →
      MemKnown L fp ((certOf j).cutAt i).known ∧ MemIf L fp ((certOf j).cutAt i).knownIf ∧
        SemHolds glob L fp ((certOf j).cutAt i).sems

/-! ## `verify_sub`'s obligation -/

/-- `verify_sub`'s first `m` statements hold under any longer prefix of its body. -/
theorem vs_take {κ : ℕ} {L : MemoryImage κ} {σ : Val} {m n : ℕ} (hn : m ≤ n)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf (fn_idx% «verify_sub»)).body.take n) True
      (fun _ ↦ True)) :
    Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf (fn_idx% «verify_sub»)).body.take m) True
      (fun _ ↦ True) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [List.take_add, holdsList_append] at hl
  exact holdsList_mono (fun _ _ _ h ↦ h) _ (fun _ ↦ trivial) (fun _ h ↦ h) hl

theorem known_vs (hkaps : VsKapsKnown) (hgmv : VsGmvKnown) (htabs : VsTabsKnown) {κ : ℕ}
    {L : MemoryImage κ} (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem) {fp : K}
    (hsem : SemHolds glob L fp (certOf (fn_idx% «verify_sub»)).sem) {i : ℕ}
    (hi : i ≤ (certOf (fn_idx% «verify_sub»)).cuts.length) (h0 : 0 < i)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf (fn_idx% «verify_sub»)))
      ((coreOf (fn_idx% «verify_sub»)).body.take ((certOf (fn_idx% «verify_sub»)).cutAt i).start) True (fun _ ↦ True)) :
    MemKnown L fp ((certOf (fn_idx% «verify_sub»)).cutAt i).known ∧ MemIf L fp ((certOf (fn_idx% «verify_sub»)).cutAt i).knownIf ∧
      SemHolds glob L fp ((certOf (fn_idx% «verify_sub»)).cutAt i).sems := by
  have ht : B1.ExpTables L.read (valG L fp (certOf (fn_idx% «verify_sub»)) (.n (val% «verify_sub» "g_squares"))) ∧
      B1.ExpWinTab L.read (valG L fp (certOf (fn_idx% «verify_sub»)) (.n (val% «verify_sub» "g_squares"))) := by
    have := (semRel_exp _ _).mp (hsem (0, [6]) (by rw [vs_sem]; exact List.mem_singleton_self _))
    simp only [valG, vs_cells]
    exact this
  obtain ⟨hif, hkn, hkat, hsm⟩ := vs_cutOk hi h0
  refine ⟨fun m hm ↦ ?_, by rw [hif]; intro _ h; simp at h, fun t ht' ↦ ?_⟩
  · have hat := hkat ⟨_, hm⟩
    have hm' := hkn m hm
    simp only [vsKapsKnown, List.mem_map, List.mem_range] at hm'
    obtain ⟨b, hb, hmb⟩ := hm'
    have hk3 := hkaps L h16 h32 (valG L fp (certOf (fn_idx% «verify_sub»))) ht.1 ht.2 (vs_take hat hl) b hb
    rw [← hmb]
    obtain ⟨e, he, hl3⟩ := hk3
    refine ⟨e, he, ?_⟩
    unfold valG at hl3
    exact hl3
  · rcases hsm t ht' with ⟨rfl, hat⟩ | ⟨rfl, hat⟩
    · rw [semRel_tabs]
      exact htabs L (valG L fp (certOf (fn_idx% «verify_sub»))) ht.2 (vs_take hat hl)
    · obtain ⟨e, he, hg⟩ := hgmv L h16 h32 (valG L fp (certOf (fn_idx% «verify_sub»))) (vs_take hat hl)
      exact (semRel_shift vsGmvD vsGmvN (by decide) (by decide) _ _).mpr ⟨e, he, hg⟩

/-! ## The walks' obligations -/

/-- **The walks' obligations** (B1's: whir's `opening_queries*` and their loops, `level_queries`,
ostack's `open_stacked`): the cut obligations (`CutsKnown`) of every function the certificates hand
something on at its cuts (`Checked.oblFns`) but `main` and `verify_sub`. Checker K hands on there the
window bounds of the windowed Merkle walk (`knownIf`: a query's dispatch selector `L[w·g^i]` below
`g^(2^width)`, from the walk along `opening_queries`' loop of the windows `decode_query_windows`'
range checks in `open_stacked` give, read twice through the window pointers for a level-0
specialization's odd first query) and the tuples at the calls (`sems`: the walk along the loop,
keyed by the path depth); B1 proves them on the core IR, read off the
certificates' cells (`WalkKnown.lean`'s `loop0_cutsKnown`, `loop1_cutsKnown`, `main_cutsKnown`,
`WalkLq.lean`, `WalkOs.lean`, and the generated `WalkKnownAll.lean`'s `walkKnown_proved`). -/
def WalkKnown : Prop :=
  ∀ j ∈ Checked.oblFns, j ≠ 1 → j ≠ fn_idx% «verify_sub» → CutsKnown j

/-- **Every callee's cut obligations**: `verify_sub`'s from `VsKapsKnown`, `VsGmvKnown` and `VsTabsKnown`, the
walks' from `WalkKnown`, and nothing for the others (`Plain`, `Checked.all_plain`). -/
theorem cutsKnown_of (hkaps : VsKapsKnown) (hgmv : VsGmvKnown) (htabs : VsTabsKnown) (hwalk : WalkKnown) {j : ℕ} (h2 : 2 ≤ j)
    (hj : j < nFns) : CutsKnown j := by
  intro κ L h16 h32 fp hmem hsem i hi h0 hl
  by_cases h19 : j = fn_idx% «verify_sub»
  · subst h19
    exact known_vs hkaps hgmv htabs h16 h32 hsem hi h0 hl
  · by_cases ho : j ∈ Checked.oblFns
    · exact hwalk j ho (by omega) h19 L h16 h32 fp hmem hsem i hi h0 hl
    · exact known_of_plain (Checked.all_plain j (by omega) hj ho) hi h0

/-! ## `main`'s obligation -/

theorem known_main (hexp : ExpTablesSound) {κ : ℕ} {L : MemoryImage κ} {fp : K} {i : ℕ}
    (hi : i ≤ (certOf 1).cuts.length)
    (h0 : 0 < i)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf 1))
      ((coreOf 1).body.take ((certOf 1).cutAt i).start) True (fun _ ↦ True)) :
    MemKnown L fp ((certOf 1).cutAt i).known ∧ MemIf L fp ((certOf 1).cutAt i).knownIf ∧
      SemHolds glob L fp ((certOf 1).cutAt i).sems := by
  obtain ⟨hlen, hkn, hki, hsm⟩ := main_cut
  obtain rfl : i = 1 := by rw [hlen] at hi; omega
  rw [hkn, hki, hsm]
  refine ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h, fun p hp ↦ ?_⟩
  simp only [List.mem_singleton] at hp
  subst hp
  rw [main_call, holdsList_append] at hl
  have hcall := ((holdsList_noRet _ main_exp_noRet _ _).mp hl).2
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hcall
  exact (semRel_exp _ _).mpr (hexp L.read _ hcall.1)

/-! ## The contracts -/

/-- **B2's step**: each contract for runs shorter than `n + 1`, given all of them for runs
shorter than `n`. -/
theorem b2_step (hcuts : ∀ j, 2 ≤ j → j < nFns → CutsKnown j) :
    ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ n,
      (∀ j, FunSpecLtReached guestProgram L n (glob.sig j).entry (Check.Pre glob L j)
        (Check.Post coreProgram glob L certByName (EnteredAt glob L) j)) →
      ∀ i, FunSpecLtReached guestProgram L (n + 1) (glob.sig i).entry (Check.Pre glob L i)
        (Check.Post coreProgram glob L certByName (EnteredAt glob L) i) := by
  intro κ L h16 h32 n hlt j fp k hk hpre hsafe
  have hpre' := hpre
  obtain ⟨hgood, hjt, henv, hbnd, hmem, hsem⟩ := hpre
  have hj : 2 ≤ j ∧ j < nFns := by simpa [glob, good] using hgood
  have hc := winOk_of (j := j) (by omega) hj.2
  have h1 : (j == 1) = false := by simp; omega
  rw [h1] at hc
  have hfp := checkWin_fpOne (hc 0 (Nat.zero_le _))
  obtain ⟨hbody, hpost, hret, hin, -⟩ := checkWins_run (Prog := coreProgram) hc (fnOf_mem hj.2)
    (coreOf_find (by omega) hj.2) (certOf_pows_ok j) (h32.trans (by decide))
    (fun h ↦ by rw [← hfp] at h; cases h)
    (certByName_coreOf (by omega) hj.2)
    (fun i ↦ (hlt i).mono (by omega)) hjt henv hbnd hmem hsem
    (fun i hi h0 hl ↦ hcuts j hj.1 hj.2 L h16 h32 fp hmem hsem i hi h0
      (holdsList_mono (relL_le_rel _) _ id (fun _ h ↦ h) hl))
    hsafe
  obtain ⟨k', hk', r, hr, hs⟩ := hret rfl
  exact ⟨k', hk', r, hr, ⟨hbody, ⟨hin, j, rfl, hpre', hsafe.2, rfl, rfl⟩, hpost⟩, hs⟩

/-- **B2 at `main`, located**: a halting run from `main`'s entry at `fp = 1`, the jump table
written and every contract holding for runs shorter than it, gives `main`'s body under its frame's
valuation, its calls located. -/
theorem b2_mainL (hexp : ExpTablesSound) :
    ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → JumpTables L → ∀ k,
      (∀ j, FunSpecLtReached guestProgram L k (glob.sig j).entry (Check.Pre glob L j)
        (Check.Post coreProgram glob L certByName (EnteredAt glob L) j)) →
      SafeReached guestProgram L k ⟨addressOfIndex mainEntry, 1⟩ →
        Stmt.HoldsList (RL coreProgram L certByName (EnteredAt glob L)) L.read (valG L 1 (certOf 1)) (coreOf 1).body
          False (fun rs ↦ rs = []) := by
  intro κ L _ h32 hjtab k hlt hsafe
  have hc := winOk_of (j := 1) le_rfl (by decide)
  obtain ⟨henv, hpre, hmem, hsem, hnret, hparams, hname⟩ := main_facts
  obtain ⟨-, -, -, -, -, hbody⟩ := checkWins_run (Prog := coreProgram) (fp := 1) hc
    (fnOf_mem (by decide)) (coreOf_find le_rfl (by decide)) (certOf_pows_ok 1)
    (h32.trans (by decide)) (fun _ ↦ rfl)
    (certByName_coreOf le_rfl (by decide)) hlt
    (jtHolds_of hjtab) (by rw [Facts.entryEnv, henv]; exact EnvHolds.nil)
    (by rw [hpre]; intro _ h; simp at h) (by rw [hmem]; intro _ h; simp at h)
    (by rw [hsem]; intro _ h; simp at h)
    (fun i hi h0 hl ↦ known_main hexp hi h0 (holdsList_mono (relL_le_rel _) _ id (fun _ h ↦ h) hl))
    (by rw [fnOf_1]; exact hsafe)
  rw [hnret] at hbody
  exact hbody

end
end LeanVM.Guest.End
