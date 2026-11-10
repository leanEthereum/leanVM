/-
  LeanVM.Guest.Sound

  B2's soundness for the deployed bytecode: every compiled function's contract from its checks,
  and `main`'s relation from a halting run of it.
-/

module

public import LeanVM.Guest.SoundFacts

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
  `verify_sub` (function `19`), whose second window starts at its call of `verify_tables`, the
  bound of entry `0` of `dims_g` from `VsDimsKnown`, and whose third starts at its call of
  `check_opening_terminal`, those and the bounds of the `8` entries of `kappa_base` from
  `VsKnown`, over the exponent table its precondition carries; in the windowed Merkle walks and
  `verify_bus_gkr`'s layer loop, `WalkKnown`.
* `b2_main`: `main`'s relation from a halting run from its entry at `fp = 1`, the jump table
  written. Its second window starts after `exponent_tables`, whose return it knows to be the
  table (`ExpTablesSound`).

`VsDimsKnown`, `VsKnown` and `ExpTablesSound` are statements about the core IR alone
(`coreProgram.Rel`), B1's to prove (`verify_sub`'s callees `verify_tables` and
`certify_placement`, and `exponent_tables`);
`WalkKnown` is stated at the certificates' cuts, B1's core IR facts on the walks read through
the certificates' cells. The theorems here take them as hypotheses.

Names are unique in `coreProgram` (`coreProgram_find_getElem`), and the jump table the checks
read is the one `__jump_tables` writes (`JumpTable.jt_of_jumpTables`). The certificates' facts
are `SoundFacts.lean`'s.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec

@[expose] public section

/-! ## B1's obligations -/

/-- **`verify_sub`'s obligation** (B1's): on every memory image, over the exponent table at
`verify_sub`'s argument `4` (`g_squares`), its first `1600` statements, which include its call of
`check_opening_terminal`, put entry `c < 8` of `kappa_base` (the value `139`) among the powers
`g^e`, `e < vsKbBound c`, which `check_opening_terminal` dispatches on. -/
def VsKnown : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ σ : Val,
    B1.ExpTables L.read (σ (.n 4)) →
    Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf 19).body.take 1600) True (fun _ ↦ True) →
      ∀ c < 8, ∃ e < vsKbBound c, LoadHolds L.read (σ (.n 139)) c (ofK (addressOfIndex e))

/-- **`verify_sub`'s obligation at its call of `verify_tables`** (B1's; REC-GUEST-IFACE 'tool:
dims_g known', 'verifysub#7'): on every memory image, its first `552` statements, up to its call
of `verify_tables`, put entry `0` of `dims_g` (the value `127`, `g^logMem`) among the powers
`g^e`, `e < 34`, which `verify_tables` dispatches on. -/
def VsDimsKnown : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ σ : Val,
    Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf 19).body.take 552) True (fun _ ↦ True) →
      ∃ e < 34, LoadHolds L.read (σ (.n 127)) 0 (ofK (addressOfIndex e))

/-- **`exponent_tables`' relation** (B1's): its returned pointer holds the exponent table. -/
def ExpTablesSound : Prop :=
  ∀ (rd : Reader) (q : E), coreProgram.Rel rd "exponent_tables" [] [q] → B1.ExpTables rd q

/-- **B1's obligations at function `j`'s cuts**: on every memory image, from the semantic tuples
and memory bounds of `j`'s entry and the statements before each cut `i > 0` of `j`'s certificate,
under its frame's valuation, the cut's memory bounds, conditional memory bounds and semantic
tuples. They are `VsKnown` for `verify_sub`, the walks' (`WalkKnown`) for the windowed Merkle
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

/-- `verify_sub`'s first `552` statements hold under any longer prefix of its body. -/
theorem vs_take552 {κ : ℕ} {L : MemoryImage κ} {σ : Val} {n : ℕ} (hn : 552 ≤ n)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf 19).body.take n) True
      (fun _ ↦ True)) :
    Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf 19).body.take 552) True
      (fun _ ↦ True) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [List.take_add, holdsList_append] at hl
  exact holdsList_mono (fun _ _ _ h ↦ h) _ (fun _ ↦ trivial) (fun _ h ↦ h) hl

theorem known_vs (hvd : VsDimsKnown) (hvs : VsKnown) {κ : ℕ} {L : MemoryImage κ}
    (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem) {fp : K}
    (hsem : SemHolds glob L fp (certOf 19).sem) {i : ℕ}
    (hi : i ≤ (certOf 19).cuts.length) (h0 : 0 < i)
    (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf 19))
      ((coreOf 19).body.take ((certOf 19).cutAt i).start) True (fun _ ↦ True)) :
    MemKnown L fp ((certOf 19).cutAt i).known ∧ MemIf L fp ((certOf 19).cutAt i).knownIf ∧
      SemHolds glob L fp ((certOf 19).cutAt i).sems := by
  have ht : B1.ExpTables L.read (valG L fp (certOf 19) (.n 4)) := by
    have := (semRel_exp _ _).mp (hsem (0, [6]) (by rw [vs_sem]; exact List.mem_singleton_self _))
    simp only [valG, vs_cells]
    exact this
  have hdims (n : ℕ) (hn : 552 ≤ n)
      (hl : Stmt.HoldsList (coreProgram.Rel L.read) L.read (valG L fp (certOf 19))
        ((coreOf 19).body.take n) True (fun _ ↦ True)) :
      MemKnown L fp (vsDimsKnown ((certOf 19).locs.getD 127 0)) := by
    intro m hm
    rw [vsDimsKnown, List.mem_singleton] at hm
    subst hm
    exact hvd L h16 h32 _ (vs_take552 hn hl)
  rw [vs_cuts] at hi
  obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
  · obtain ⟨hst, hkn, hki, hsm⟩ := vs_cut1
    rw [hkn, hki, hsm]
    rw [hst] at hl
    exact ⟨hdims 552 le_rfl hl, fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩
  · obtain ⟨hst, hkn, hki, hsm⟩ := vs_cut
    rw [hkn, hki, hsm]
    rw [hst] at hl
    refine ⟨fun m hm ↦ ?_, fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact hdims 1600 (by omega) hl m hm
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
    exact hvs L h16 h32 _ ht hl c (List.mem_range.mp hc)

/-! ## The walks' obligations -/

/-- **The walks' obligations** (B1's: whir's `opening_queries*` and their loops, `walk_path`'s
specializations, ostack's `open_stacked`, gkr's `verify_bus_gkr` and its layer loop `__loop6`;
REC-GUEST-IFACE 'tool: walk obligations — IMPLEMENTED', 'tool: gkr obligations', PR661-IFACE
'walk-K'): the cut obligations (`CutsKnown`) of every function the certificates hand something on
at its cuts (`Checked.oblFns`) but `main` and `verify_sub`. Checker K hands on there the window
bounds of the windowed Merkle walk (`knownIf`, in `walk_path`: the dispatch selector `L[w·g^i]`
below `g^(2^width)`, from its precondition `WinsAt`, which `decode_query_windows`' range checks in
`open_stacked` give), the parity of a GKR layer (`L[layer·g^12]` below `g^4`) and the tuples at the
calls (`sems`: the walk along `opening_queries`' loop, `WinsAt` of the window pointer before each
`walk_path` call); B1 proves them on the core IR, as `VsKnown` for `verify_sub`, read off the
certificates' cells (`WalkKnown.lean`'s `loop0_cutsKnown`, `loop1_cutsKnown`, `main_cutsKnown`,
`wp_cutsKnown`; `walkKnown_proved`). -/
def WalkKnown : Prop :=
  ∀ j ∈ Checked.oblFns, j ≠ 1 → j ≠ 19 → CutsKnown j

/-- **Every callee's cut obligations**: `verify_sub`'s from `VsDimsKnown` and `VsKnown`, the
walks' from `WalkKnown`, and nothing for the others (`Plain`, `Checked.all_plain`). -/
theorem cutsKnown_of (hvd : VsDimsKnown) (hvs : VsKnown) (hwalk : WalkKnown) {j : ℕ} (h2 : 2 ≤ j)
    (hj : j < nFns) : CutsKnown j := by
  intro κ L h16 h32 fp hmem hsem i hi h0 hl
  by_cases h19 : j = 19
  · subst h19
    exact known_vs hvd hvs h16 h32 hsem hi h0 hl
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
    (coreOf_find (by omega) hj.2) (certOf_pows_ok j) h32 (fun h ↦ by rw [← hfp] at h; cases h)
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
    (fnOf_mem (by decide)) (coreOf_find le_rfl (by decide)) (certOf_pows_ok 1) h32 (fun _ ↦ rfl)
    (certByName_coreOf le_rfl (by decide)) hlt
    (jtHolds_of hjtab) (by rw [Facts.entryEnv, henv]; exact EnvHolds.nil)
    (by rw [hpre]; intro _ h; simp at h) (by rw [hmem]; intro _ h; simp at h)
    (by rw [hsem]; intro _ h; simp at h)
    (fun i hi h0 hl ↦ known_main hexp hi h0 (holdsList_mono (relL_le_rel _) _ id (fun _ h ↦ h) hl))
    (by rw [fnOf_1]; exact hsafe)
  rw [hnret] at hbody
  exact hbody

/-- The GKR parity tag is a 32-bit tag (`WalkGkr`, `WalkKnown`). -/
theorem tagGkr_lt : tagGkr < 2 ^ 32 := by unfold tagGkr; norm_num

end
end LeanVM.Guest.End
