/-
  LeanVM.Guest.B1.VerifySub.Known

  `kappa_base` is in range after `verify_sub`'s placement and the stack's log check
  (G:3487-3493): the tail of `VsKnown`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Mid
public import LeanVM.Guest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.Placement.Interface
public import LeanVM.Guest.B1.Placement.Kappas
public import LeanVM.Guest.B1.VerifySub.Body

/-!
# The columns' logs, from the placement and the stack's log

`vsKnown_tail`: from `kappa_base = [1, g^logMem, g^h…]` (`logMem ≤ 32`, the six heights below
`29`) and the exponent table, the first statements of `vsTailT` — `certify_placement`,
`m = max 15 (log2Ceil total)` in the exponent, and `g^(m - 22)` range-checked below `g^6` — give
`m ≤ 28`, so every committed column's log is below `29` (`hypKappa_holds`): the memory's
`logMem ≤ 28` (columns `0 .. 3`) and the Keccak table's `τ_5 + 6 ≤ 28` (`q_keccak`, column `5`).
`kappa_base`'s entries are then below `kbBound`: what `check_opening_terminal`'s dispatches on
`kb[i]`, `kb[0]·g^19` and `kb[7]·g^6` need.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- `LIG_MIN_SHIFT_INV = g^-22`. -/
theorem kn_word_ginv22_mul : word 8198552432976855044 0 0 * gen ^ 22 = 1 := by
  rw [show gen ^ 22 = ofK (K.ofBits (2 ^ 22)) by
      rw [← word_two_pow (a := 22) (by decide)]; exact word_eOfNat _,
    show word 8198552432976855044 0 0 = ofK (K.ofBits 8198552432976855044) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 8198552432976855044 * K.ofBits (2 ^ 22) = 1 by decide +kernel, ofK_one]

theorem kn_hs_getD_le {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (i : ℕ) : hs.getD i 0 ≤ 28 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : hs[i]? with _ | x
  · simp
  · have := hh x (List.mem_of_getElem? hx)
    simp only [Option.getD_some]; omega

theorem kn_columnKappas_le {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32) :
    ∀ x ∈ columnKappas logMem Tables.guestLogBytecode hs, x ≤ 34 := by
  intro x hx
  unfold columnKappas at hx
  rw [List.mem_append] at hx
  have hq : qkeccakSlotBits = 6 := by decide
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · omega
    · show 19 ≤ 34; omega
    · have := kn_hs_getD_le hh opKeccak; omega
  · rw [List.mem_flatMap] at hx
    obtain ⟨t, -, ht⟩ := hx
    rw [(List.mem_replicate.1 ht).2]
    have := kn_hs_getD_le hh t.opcode; omega

theorem kn_stackTotal_lt {kappas : List ℕ} (hl : kappas.length = 165) (hk : ∀ x ∈ kappas, x ≤ 34) :
    Tables.stackTotal kappas < 2 ^ 60 := by
  have hle := List.sum_le_length_nsmul ((Tables.committedKappas kappas).map (2 ^ ·)) (2 ^ 34) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    refine Nat.pow_le_pow_right (by norm_num) ?_
    simp only [Tables.committedKappas, List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    rw [List.getD_eq_getElem?_getD]
    rcases hc : kappas[c]? with _ | z
    · simp
    · simp only [Option.getD_some]; exact hk z (List.mem_of_getElem? hc))
  have hlen : (Tables.committedKappas kappas).length ≤ 165 := by
    simp only [Tables.committedKappas, Tables.committedCols, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp [hl])
  simp only [List.length_map, smul_eq_mul] at hle
  unfold Tables.stackTotal
  calc _ ≤ _ := hle
    _ ≤ 165 * 2 ^ 34 := Nat.mul_le_mul_right _ hlen
    _ < 2 ^ 60 := by norm_num

/-- The bound `check_opening_terminal`'s dispatches need of `kappa_base`'s entry `i`: `kb[0] = g^0`
(dispatched as `kb[0]·g^19`), the memory's and the tables' logs below `29`, and the Keccak table's
below `23` (dispatched as `kb[7]·g^6`). -/
def kbBound (i : ℕ) : ℕ := [1, 29, 29, 29, 29, 29, 29, 23].getD i 0

/-- **The tail of `VsKnown`**: the placement and the stack's log check put every committed
column's log below `29`, so the memory's log is at most `28` and the Keccak table's height at most
`22`. -/
theorem vsKnown_tail {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hcp : Tables.certify_placement_Spec L.read)
    (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hm : logMem ≤ 32) (hl : hs.length = 6) (hh : ∀ x ∈ hs, x < 29)
    (hkb : ReadsAt L.read (σ (.n 139)) (1 :: gen ^ logMem :: hs.map (gen ^ ·)))
    (h : Stmt.HoldsList C L.read σ (vsTailT.take 6) next kret) :
    logMem ≤ 28 ∧ hs.getD 5 0 ≤ 22 := by
  simp only [vsTailT, List.cons_append, List.take_succ_cons, List.take_zero, Stmt.HoldsList,
    Stmt.Holds, vsCall, vsConst, vsMul, vsRange, List.map_cons, List.map_nil, Atom.Holds] at h
  obtain ⟨c1, c2, e1677, m1678, e1679, r1678, -⟩ := h
  -- the placement
  obtain ⟨hsq, hrk, -⟩ := expTablesAt_of hexp
  have e178 : Tables.rankKeysAt = 178 := rfl
  rw [e178] at hrk
  obtain ⟨off, hr, hP⟩ := hcp logMem hs _ _ _ hm hl hh hkb hsq hrk (hC _ _ _ c1)
  simp only [List.cons.injEq, and_true] at hr
  obtain ⟨h1674, -⟩ := hr
  -- the stack's log
  have hST0 := kn_stackTotal_lt (Tables.columnKappas_length logMem Tables.guestLogBytecode hs)
    (kn_columnKappas_le hh hm)
  have hr2 := (log2_holds.2 hκ hκ6 L _ _ hexp _).1 (hC _ _ _ c2)
  rw [h1674, meaningLog2CeilExp_pow (by norm_num) hST0] at hr2
  simp only [List.cons.injEq, and_true] at hr2
  obtain ⟨hlt34, hr2⟩ := hr2
  obtain ⟨e, he, h1678⟩ := rc_pow hκ hκ6 L (a := 6) (by norm_num)
    (by rw [e1679, show (64 : ℕ) = 2 ^ 6 from rfl, word_pow2 (by norm_num)]) r1678
  have hm28 : max 15 (log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)))
      = e + 22 := by
    have := congrArg (· * gen ^ 22) (m1678.symm.trans h1678)
    simp only [hr2, e1677, mul_assoc, kn_word_ginv22_mul, mul_one, ← pow_add] at this
    exact gen_pow_inj (by omega) (by omega) this
  have h28 : log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)) ≤ 28 := by
    omega
  have hK := Tables.hypKappa_holds _ (Tables.columnKappas_length _ _ _) h28
  have hck := Tables.committedKappas_columnKappas logMem hs hl
  have k0 := hK 0 (by decide)
  have k5 := hK 5 (by decide)
  rw [hck, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; decide), List.getElem_map, List.getElem_range,
    show Tables.colKappaSrc 0 = 1 from rfl, show Tables.colKappaAdj 0 = 0 from rfl] at k0
  rw [hck, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; decide), List.getElem_map, List.getElem_range,
    show Tables.colKappaSrc 5 = 7 from rfl, show Tables.colKappaAdj 5 = 6 from rfl] at k5
  clear * - k0 k5 hl
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero] at k0 k5 ⊢
  omega

/-- `kappa_base`'s entries below `kbBound`, from the memory's log at most `28`, the heights below
`29` and the Keccak table's at most `22`. -/
theorem kb_bounds {rd : Reader} {p : E} {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6)
    (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 28) (h5 : hs.getD 5 0 ≤ 22)
    (hkb : ReadsAt rd p (1 :: gen ^ logMem :: hs.map (gen ^ ·))) :
    ∀ i < 8, ∃ e < kbBound i, LoadHolds rd p i (ofK (addressOfIndex e)) := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5'], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hh
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h5
    intro i hi
    have hr := hkb i (by simp; omega)
    simp only [← gen_pow_eq_ofK]
    interval_cases i
    · exact ⟨0, by decide, by simpa using hr⟩
    · exact ⟨logMem, by show logMem < 29; omega, by simpa using hr⟩
    · exact ⟨h0, by show h0 < 29; omega, by simpa using hr⟩
    · exact ⟨h1, by show h1 < 29; omega, by simpa using hr⟩
    · exact ⟨h2, by show h2 < 29; omega, by simpa using hr⟩
    · exact ⟨h3, by show h3 < 29; omega, by simpa using hr⟩
    · exact ⟨h4, by show h4 < 29; omega, by simpa using hr⟩
    · exact ⟨h5', by show h5' < 23; omega, by simpa using hr⟩

/-- The sections before the tail. -/
def vsPre : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsAlphasT ++ vsFpwT ++
    vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT

theorem vsPre_length : vsPre.length = 1586 := by decide +kernel

theorem vsT_take : vsT.take 1600 = vsPre ++ vsTailT.take 14 := by
  rw [show vsT = vsPre ++ vsTailT from rfl, List.take_append, List.take_of_length_le
    (by rw [vsPre_length]; omega), vsPre_length]

theorem noRet_mid : Stmt.noRetList (vsMapsT ++ vsCtabT ++ vsLamT) = true := by decide +kernel

theorem vsTailT_take14 : vsTailT.take 14 = vsTailT.take 6 ++ (vsTailT.take 14).drop 6 := by
  have := List.take_append_drop 6 (vsTailT.take 14)
  rw [List.take_take, show min 6 14 = 6 from rfl] at this
  exact this.symm

/-- **`VsKnown`** from the callees' specifications: `kappa_base`'s entries below `kbBound`. -/
theorem vsKnown_of {κ : ℕ} (L : MemoryImage κ) (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (hgkr : Tables.verify_bus_gkr_SpecC L.read (coreProgram.Rel L.read))
    (htab : Tables.verify_tables_SpecC (List.replicate (2 ^ 23) 0) L.read (coreProgram.Rel L.read))
    (hcp : Tables.certify_placement_Spec L.read)
    (σ : Val) (hexp : B1.ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 1600) True
      (fun _ ↦ True)) :
    ∀ i < 8, ∃ e < kbBound i, LoadHolds L.read (σ (.n 139)) i (ofK (addressOfIndex e)) := by
  have hκ : κ ≤ 32 := h32
  have hκ6 : 6 ≤ κ := by have : 16 ≤ κ := h16; omega
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  rw [show Fn.body Data.core18 = vsT from vs_body, vsT_take, vsPre] at h
  rw [holdsList_append, holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨⟨F⟩, h⟩ := vs_front hκ hκ6 L hle (List.replicate (2 ^ 23) 0) hgkr htab hexp h
  rw [← holdsList_append, ← holdsList_append] at h
  have h' := ((holdsList_noRet _ noRet_mid _ _).1 h).2
  rw [vsTailT_take14, holdsList_append] at h'
  have hsL := tableHeights_length F.rowsN F.hrowsL
  obtain ⟨hm28, h5⟩ := vsKnown_tail hκ hκ6 L hle hcp hexp F.hm32 hsL F.hh29 F.hkb h'
  exact kb_bounds hsL F.hh29 hm28 h5 F.hkb

end
end LeanVM.Guest.B1.VerifySub
