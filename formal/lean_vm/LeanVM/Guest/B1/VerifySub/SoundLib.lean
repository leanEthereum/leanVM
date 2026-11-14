/-
  LeanVM.Guest.B1.VerifySub.SoundLib

  The facts `verify_sub`'s soundness assembles its sections with: the body cut into sections, the
  exponent tables as `verify_tables` reads them, the heights and the bus depth.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.VerifySub.Split
public import LeanVM.Guest.B1.Tables.InterfaceP

/-!
# The assembly's library

* `vsT_split` and the sections' `noRet` facts: every section but the tail returns nothing, so a
  run of the body holds each section on its own (`holdsList_noRet`).
* `expTablesAt_of`, `winTabs_of`: `verify_sub`'s precondition as `verify_tables`, the grinds and
  `open_stacked` read it.
* `tau_ge`, `tau_lt`, `depth_ge`: the `KECCAK` table's height lies in `[9, 28]`, and the bus depth
  is at least `20`.
* `bytecodeAt_claimed`: the deferring check accepts the claim it is handed.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The body's sections -/

theorem vsT_split : vsT = vsHeadT ++ (vsReadsT ++ (vsSizesT ++ (vsPushT ++ (vsRootsT ++ (vsPlaceT ++
    (vsOodT ++ (vsBusGrindT ++ (vsFpwT ++ (vsCallsT ++ (vsMapsT ++ (vsCtabT ++
      (vsLamT ++ vsTailT)))))))))))) := by
  simp only [vsT, List.append_assoc]

theorem vsSizesT_noRet : Stmt.noRetList vsSizesT = true := by decide +kernel
theorem vsPlaceT_noRet : Stmt.noRetList vsPlaceT = true := by decide +kernel
theorem vsOodT_noRet : Stmt.noRetList vsOodT = true := by decide +kernel
theorem vsBusGrindT_noRet : Stmt.noRetList vsBusGrindT = true := by decide +kernel
theorem vsFpwT_noRet : Stmt.noRetList vsFpwT = true := by decide +kernel
theorem vsCallsT_noRet : Stmt.noRetList vsCallsT = true := by decide +kernel
theorem vsMapsT_noRet : Stmt.noRetList vsMapsT = true := by decide +kernel
theorem vsCtabT_noRet : Stmt.noRetList vsCtabT = true := by decide +kernel
theorem vsLamT_noRet : Stmt.noRetList vsLamT = true := by decide +kernel

/-! ## The exponent tables -/

theorem gSquares_of_exp {rd : Reader} {sq : E} (h : ExpTables rd sq) :
    ReadsAt rd sq Tables.gSquaresList := by
  intro k hk
  simp only [Tables.gSquaresList, List.length_map, List.length_range] at hk
  simpa [Tables.gSquaresList] using h.1 k hk

/-- The window table at `g_squares·g^236`. -/
theorem winTabs_of {rd : Reader} {sq : E} (h : ExpWinTab rd sq) : WinTabs rd (sq * gen ^ winTabAt) :=
  fun n hn ↦ by rw [loadHolds_mul_gen_pow]; exact h n hn

/-- What `verify_tables` reads of the exponent table: the squares, the rank keys, the sides, the
window table. -/
theorem expTablesAt_of {rd : Reader} {sq : E} (h : ExpTables rd sq) (hw : ExpWinTab rd sq) :
    Tables.ExpTablesAt rd sq := by
  refine ⟨gSquares_of_exp h, fun k hk ↦ ?_, fun gi hgi ↦ ?_, winTabs_of hw⟩
  · simp only [Tables.rankKeysList, List.length_map, List.length_range] at hk
    rw [loadHolds_mul_gen_pow]
    simpa [Tables.rankKeysList] using h.2.2.1 k hk
  · simp only [Tables.sideTabList, List.length_map, List.length_range] at hgi
    rw [loadHolds_mul_gen_pow]
    simp only [Tables.sideTabList, List.getElem_map, List.getElem_range]
    have h0 := fun gi (h1 : gi < 9) ↦ h.2.2.2 0 (by decide) gi (by simp [sideGroupStart]) (by
      simpa [sideGroupStart] using h1)
    have h1 := fun gi (h1 : 9 ≤ gi) (h2 : gi < 18) ↦ h.2.2.2 1 (by decide) gi (by
      simpa [sideGroupStart] using h1) (by simpa [sideGroupStart] using h2)
    have h2 := fun gi (h1 : 18 ≤ gi) (h2 : gi < 24) ↦ h.2.2.2 2 (by decide) gi (by
      simpa [sideGroupStart] using h1) (by simpa [sideGroupStart] using h2)
    interval_cases gi
    all_goals first
      | exact h0 _ (by decide)
      | exact h1 _ (by decide) (by decide)
      | exact h2 _ (by decide) (by decide)

/-! ## The heights -/

theorem getD_mem' {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem tableHeights_length (rowsN : List ℕ) (h : rowsN.length = 6) :
    (Tables.tableHeightsOf rowsN).length = 6 := by
  simp [Tables.tableHeightsOf, h, tableLogFloors]

theorem tau_ge {rowsN : List ℕ} (h : rowsN.length = 6) :
    9 ≤ (Tables.tableHeightsOf rowsN).getD 5 0 := by
  match rowsN, h with
  | [_, _, _, _, _, _], _ =>
    simp [Tables.tableHeightsOf, tableLogFloors, keccakMinStepsLog]

theorem tau_lt {rowsN : List ℕ} (h : rowsN.length = 6)
    (hh : ∀ x ∈ Tables.tableHeightsOf rowsN, x < 33) : (Tables.tableHeightsOf rowsN).getD 5 0 < 33 :=
  hh _ (getD_mem' (by rw [tableHeights_length rowsN h]; omega))

/-- The Keccak table's height is at most `24` once every committed column's log is below `31`:
its column `q_keccak` has the log `τ + 6`. -/
theorem tau_le_of_kappasBelow {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6)
    (hKB : Tables.KappasBelow (columnKappas logMem 19 hs)) : hs.getD 5 0 ≤ 24 := by
  have hck := Tables.committedKappas_columnKappas logMem hs hl
  have k4 := hKB 4 (by decide)
  simp only [Tables.guestLogBytecode] at hck
  rw [hck, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; decide),
    List.getElem_map, List.getElem_range,
    show Tables.colKappaSrc 4 = 7 from rfl, show Tables.colKappaAdj 4 = 6 from rfl] at k4
  clear * - k4 hl
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero] at k4 ⊢
  omega

theorem layoutOf_heights (bytecode : List K) (m : ℕ) (rowsN : List ℕ) :
    (Tables.layoutOf bytecode m rowsN).tableLogHeights = Tables.tableHeightsOf rowsN := rfl

/-! ## The bus depth -/

/-- The push total of the memory's log `m` and the heights `hs`. -/
def pushTotal (m : ℕ) (hs : List ℕ) : ℕ := ((List.range 54).map fun b ↦ 2 ^ pushKappa m hs b).sum

theorem pushTotal_ge2 {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) :
    2 ^ logMem + 2 ^ 19 ≤ pushTotal logMem hs := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    unfold pushTotal
    rw [show (List.range 54).map (fun b ↦ 2 ^ pushKappa logMem [h0, h1, h2, h3, h4, h5] b) =
      ((List.range 54).map (pushKappa logMem [h0, h1, h2, h3, h4, h5])).map (2 ^ ·) from
      (List.map_map ..).symm, pushKappas_eq]
    simp only [List.cons_append, List.map_cons, List.sum_cons]
    omega

theorem depth_ge {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) :
    20 ≤ log2Ceil (pushTotal logMem hs) := by
  have h := pushTotal_ge2 (logMem := logMem) hl
  have : 2 ^ 19 < pushTotal logMem hs := by
    have := Nat.one_le_two_pow (n := logMem)
    omega
  exact lt_log2Ceil_iff.2 this

/-- `g^n ≠ 1` below the order. -/
theorem vs_gen_pow_ne_one {n : ℕ} (h0 : 0 < n) (h : n < 2 ^ 64 - 1) : gen ^ n ≠ 1 := by
  intro e
  have := gen_pow_inj h (by norm_num) (e.trans (pow_zero gen).symm)
  omega

/-! ## The claimed bytecode -/

theorem bytecodeAt_claimed (bytecode : List K) (pt : List E) (v : E) :
    Tables.BytecodeAt (claimedBytecodeValue ⟨pt, v⟩) bytecode pt v := by
  intro s
  simp [claimedBytecodeValue, Tables.tbRun, VerifierProgram.require, Compile.runWithHash]
  rfl

end
end LeanVM.Guest.B1.VerifySub
