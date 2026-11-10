/-
  LeanVM.Guest.WalkOs

  `open_stacked`'s cut obligations (`CutsKnown`): at each level's `opening_queries` call, the
  callee's walk precondition `OqMainWins` on the call's cells, from the body's prefix.
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOsPre
public import LeanVM.Guest.B1.Whir.DataAll
public import LeanVM.Guest.B1.Bits.QueryWindowsAll

/-!
# `open_stacked`'s walk obligations

Checker K cuts `open_stacked__L{m}` before each level's `opening_queries` call; the cut hands on
`impTag (walkTag (2 + base) odd depth cd) 1 l` on the cells of `query_win_ptrs` and `n_iters_g`
(REC-GUEST-IFACE 'tool: walk obligations' (b)): `OqMainWins`, if `n_iters_g`'s cell holds the
one-limb word `l` the call's setup sets. `osOk` (`WalkOsDefs`) checks the function assumes the
window table at `tabs` (`tagTabs`) and each tuple is one level's, on its window pointers' cell,
past them; `osPre_oqMainWins` (`WalkOsPre`) proves it on the prefix.

`os_cutsKnown`: `CutsKnown j` for `open_stacked__L{m}` from its body's template, the candidate's
numbers (`osLvB`) and the certificate's check (`osOk`). The instances are `WalkOsN.lean`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- A conditional tag on the immediate `l` at position `1`: the relation holds if the second
word is `l`'s. -/
theorem semRel_impL {t : ℕ} (ht : t < 2 ^ 32) (l : ℕ) (rd : Reader) (ws : List E) :
    SemRel glob (impTag t 1 l) rd ws ↔
      (ws.getD 1 0 = OffsetInstruction.immediateWord l 0 → SemRel0 glob t rd ws) := by
  have e0 : impTag t 1 l / 2 ^ 32 = 1 + 1 + 8 * l := by
    unfold impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht, Nat.zero_add]
  have e1 : impPos (impTag t 1 l) = 1 := by unfold impPos; rw [e0]; omega
  have e2 : impImm (impTag t 1 l) = l := by unfold impImm; rw [e0]; omega
  have e3 : impBase (impTag t 1 l) = t := by
    unfold impBase impTag
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  unfold SemRel
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by unfold impTag; omega)), e1, e2, e3]

theorem osCfg_getD {m ℓ : ℕ} (h : ℓ < (osCfg m).levels.length) :
    (osCfg m).levels.getD ℓ default = osLv m ℓ := by
  rw [List.getD_eq_getElem _ _ h]
  simp [osCfg]

/-- **A candidate's levels' facts** (`OsWalkLv`), from its template's data and its numbers. -/
theorem osWalkLv_of {m : ℕ} (hm : m < 28) (hlv : osLvB (osCfg m) = true) {κ : ℕ} (hκ : κ ≤ 32)
    (L : MemoryImage κ) {ℓ : ℕ} (hℓ : ℓ < (osCfg m).levels.length) :
    OsWalkLv L.read (osCfg m) ℓ := by
  have hall : ∀ i < (osCfg m).levels.length, _ := fun i hi ↦
    List.all_eq_true.mp hlv i (List.mem_range.mpr hi)
  have hi := hall ℓ hℓ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  obtain ⟨⟨⟨⟨⟨⟨⟨hpw, hper⟩, hq⟩, hs1⟩, hso⟩, hs5⟩, -⟩, hdec⟩ := hi
  have hloop := (osData_all m hm).2.1 ℓ hℓ
  rw [← osCfg_getD hℓ] at hloop
  refine ⟨hloop, hpw, hper, hq, hs1, hso, hs5, fun i _ hi' ↦ ?_,
    fun args rets hw h ↦ decode_query_windows_all_holds _ hdec hκ L args rets hw h⟩
  have := hall i hi'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.2

/-- `open_stacked__L{m}`'s body is its template. -/
theorem os_body {m j : ℕ} (hm : m < 28) (h1 : 1 ≤ j) (hj : j < nFns)
    (hname : (coreOf j).name = "open_stacked__L" ++ natStr m) :
    (coreOf j).body = osBody (osCfg m) := by
  obtain ⟨fn, hf, -, hb⟩ := (osData_all m hm).1
  have h := coreOf_find h1 hj
  rw [hname, hf] at h
  cases h
  exact hb

/-- **`open_stacked`'s cut obligations**, from its template, the candidate's numbers and its
certificate's check. -/
theorem os_cutsKnown {j m : ℕ} (hm : m < 28) (hb : (coreOf j).body = osBody (osCfg m))
    (hlv : osLvB (osCfg m) = true) (hok : osOk j (osCfg m) = true) : CutsKnown j := by
  intro κ L _ h32 fp _ hsem i hi h0 hl
  simp only [osOk, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hs, hcuts⟩ := hok
  have hwt : WinTabs L.read (valG L fp (certOf j) (.n osTabs)) := by
    rw [hs] at hsem
    exact (semRel_tabs _ _).mp (hsem _ (List.mem_singleton_self _))
  have hc := List.all_eq_true.mp hcuts _ (cutAt_mem hi h0)
  simp only [osCutOk, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hc
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hc
  refine ⟨by rw [hkn]; intro _ h; simp at h, by rw [hki]; intro _ h; simp at h, fun t ht ↦ ?_⟩
  have h1 := hsm t ht
  simp only [osSemOk, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Nat.ble_eq] at h1
  obtain ⟨ℓ, hℓ, ⟨⟨⟨⟨⟨⟨⟨ht1, htW⟩, hcd⟩, hN⟩, hl0⟩, hlen⟩, hbp⟩, hpre⟩⟩ := h1
  have hF := osWalkLv_of hm hlv (κ := κ) (by unfold maxLogMem at h32; omega) L hℓ
  rw [hb] at hl
  have hW := osPre_oqMainWins hℓ hF hwt hpre hl
  have ho : ((osCfg m).levels.getD ℓ default).queries % 2 * (if ℓ = 0 then 1 else 0) < 2 := by
    split_ifs <;> omega
  have hbase : (if ℓ = 0 then 1 else 0) < 2 := by split_ifs <;> omega
  have htW' := htW.trans tagGkr_lt
  rw [ht1, semRel_impL htW', ← semRel_lt htW', semRel_main ho hcd hbase htW]
  intro hx
  rw [getD_map_lt (by omega)] at hx
  rw [getD_map_lt (by omega), getD_map_lt (by omega), hx, hbp, Exec.imm_of_ofBits hl0,
    gpowK_eq hN, ← Value.gen_pow_eq_ofK]
  exact hW

end
end LeanVM.Guest.End
