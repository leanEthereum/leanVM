/-
  LeanVM.Guest.B1.VerifySub.Known

  `kappa_base` is in range after `verify_sub`'s placement and the stack's log check
  (G:3534-3539): the tail of `VsKnown`.
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
`33`) and the exponent table, the first statements of `vsTailT` (`certify_placement`,
`m = max 16 (log2Ceil total)` in the exponent, and `g^(m - 20)` range-checked below `g^11`) give
`m ≤ 30`, so every committed column's log is below `31` (`hypKappa_holds`): the Keccak table's
`τ_5 + 6 ≤ 30` (`q_keccak`, column `5`).
`kappa_base`'s entries are then below `kbBound`: what `check_opening_terminal`'s dispatches on
`kb[i]`, `kb[0]·g^19` and `kb[7]·g^6` need.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- `LIG_MIN_SHIFT_INV = g^-20`. -/
theorem kn_word_ginv20_mul : word 14347465658197868555 0 0 * gen ^ 20 = 1 := by
  rw [show gen ^ 20 = ofK (K.ofBits (2 ^ 20)) by
      rw [← word_two_pow (a := 20) (by decide)]; exact word_eOfNat _,
    show word 14347465658197868555 0 0 = ofK (K.ofBits 14347465658197868555) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 14347465658197868555 * K.ofBits (2 ^ 20) = 1 by decide +kernel, ofK_one]

theorem kn_hs_getD_le {hs : List ℕ} (hh : ∀ x ∈ hs, x < 33) (i : ℕ) : hs.getD i 0 ≤ 32 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : hs[i]? with _ | x
  · simp
  · have := hh x (List.mem_of_getElem? hx)
    simp only [Option.getD_some]; omega

theorem kn_columnKappas_le {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 33) (hm : logMem ≤ 32) :
    ∀ x ∈ columnKappas logMem Tables.guestLogBytecode hs, x ≤ 38 := by
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
    · show 19 ≤ 38; omega
    · have := kn_hs_getD_le hh opKeccak; omega
  · rw [List.mem_flatMap] at hx
    obtain ⟨t, -, ht⟩ := hx
    rw [(List.mem_replicate.1 ht).2]
    have := kn_hs_getD_le hh t.opcode; omega

theorem kn_stackTotal_lt {kappas : List ℕ} (hl : kappas.length = 165) (hk : ∀ x ∈ kappas, x ≤ 38) :
    Tables.stackTotal kappas < 2 ^ 60 := by
  have hle := List.sum_le_length_nsmul ((Tables.committedKappas kappas).map (2 ^ ·)) (2 ^ 38) (by
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
    _ ≤ 165 * 2 ^ 38 := Nat.mul_le_mul_right _ hlen
    _ < 2 ^ 60 := by norm_num

/-- The bound `check_opening_terminal`'s dispatches need of `kappa_base`'s entry `i`: `kb[0] = g^0`
(dispatched as `kb[0]·g^19`), the memory's and the tables' logs below `33`, and the Keccak table's
below `27` (dispatched as `kb[7]·g^6`). -/
def kbBound (i : ℕ) : ℕ := [1, 31, 31, 31, 31, 31, 31, 25].getD i 0

/-- **The tail of `VsKnown`**: the placement and the stack's log check put every committed
column's log below `31`, so the Keccak table's height is at most `24`. -/
theorem vsKnown_tail {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hcp : Tables.certify_placement_Spec L.read)
    (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hm : logMem ≤ 32) (hl : hs.length = 6) (hh : ∀ x ∈ hs, x < 33)
    (hkb : ReadsAt L.read (σ (.n 139)) (1 :: gen ^ logMem :: hs.map (gen ^ ·)))
    (h : Stmt.HoldsList C L.read σ (vsTailT.take 6) next kret) :
    hs.getD 5 0 ≤ 24 := by
  simp only [vsTailT, List.cons_append, List.take_succ_cons, List.take_zero, Stmt.HoldsList,
    Stmt.Holds, vsCall, vsConst, vsMul, vsRange, List.map_cons, List.map_nil, Atom.Holds] at h
  obtain ⟨c1, c2, e1685, m1686, e1687, r1686, -⟩ := h
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
  obtain ⟨e, he, h1686⟩ := rc_pow hκ L (a := 10) (by norm_num)
    (by rw [e1687, show (1024 : ℕ) = 2 ^ 10 from rfl, word_pow2 (by norm_num)]) r1686
  have hm32 : max 16 (log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)))
      = e + 20 := by
    have := congrArg (· * gen ^ 20) (m1686.symm.trans h1686)
    simp only [hr2, e1685, mul_assoc, kn_word_ginv20_mul, mul_one, ← pow_add] at this
    exact gen_pow_inj (by omega) (by omega) this
  have h30 : log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)) ≤ 30 := by
    omega
  have hK := Tables.hypKappa_holds _ (Tables.columnKappas_length _ _ _) h30
  have hck := Tables.committedKappas_columnKappas logMem hs hl
  have k5 := hK 5 (by decide)
  rw [hck, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; decide), List.getElem_map, List.getElem_range,
    show Tables.colKappaSrc 5 = 7 from rfl, show Tables.colKappaAdj 5 = 6 from rfl] at k5
  clear * - k5 hl
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero] at k5 ⊢
  omega

/-- `kappa_base`'s entries below `kbBound`, from the memory's log at most `30`, the heights below
`31` and the Keccak table's at most `24`. -/
theorem kb_bounds {rd : Reader} {p : E} {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6)
    (hh : ∀ x ∈ hs, x < 31) (hm : logMem ≤ 30) (h5 : hs.getD 5 0 ≤ 24)
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
    · exact ⟨logMem, by show logMem < 31; omega, by simpa using hr⟩
    · exact ⟨h0, by show h0 < 31; omega, by simpa using hr⟩
    · exact ⟨h1, by show h1 < 31; omega, by simpa using hr⟩
    · exact ⟨h2, by show h2 < 31; omega, by simpa using hr⟩
    · exact ⟨h3, by show h3 < 31; omega, by simpa using hr⟩
    · exact ⟨h4, by show h4 < 31; omega, by simpa using hr⟩
    · exact ⟨h5', by show h5' < 25; omega, by simpa using hr⟩

/-- The sections before the tail. -/
def vsPre : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsAlphasT ++ vsFpwT ++
    vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT

theorem vsPre_length : vsPre.length = 1586 := by decide +kernel

theorem vsT_take : vsT.take 1593 = vsPre ++ vsTailT.take 7 := by
  rw [show vsT = vsPre ++ vsTailT from rfl, List.take_append, List.take_of_length_le
    (by rw [vsPre_length]; omega), vsPre_length]

theorem noRet_mid : Stmt.noRetList (vsMapsT ++ vsCtabT ++ vsLamT) = true := by decide +kernel

theorem vsTailT_take7 : vsTailT.take 7 = vsTailT.take 6 ++ (vsTailT.take 7).drop 6 := by
  have := List.take_append_drop 6 (vsTailT.take 7)
  rw [List.take_take, show min 6 7 = 6 from rfl] at this
  exact this.symm

/-- **`VsKnown`** from the callees' specifications: `kappa_base`'s entries below `kbBound`. -/
theorem vsKnown_of {κ : ℕ} (L : MemoryImage κ) (_hmin : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (hgkr : Tables.verify_bus_gkr_SpecC L.read (coreProgram.Rel L.read))
    (htab : Tables.verify_tables_SpecC (List.replicate (2 ^ 23) 0) L.read (coreProgram.Rel L.read))
    (hcp : Tables.certify_placement_Spec L.read)
    (σ : Val) (hexp : B1.ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 1593) True
      (fun _ ↦ True)) :
    ∀ i < 8, ∃ e < kbBound i, LoadHolds L.read (σ (.n 139)) i (ofK (addressOfIndex e)) := by
  have hκ : κ ≤ 32 := h32.trans (by decide)
  have hκ6 : 6 ≤ κ := by
    obtain ⟨hsq, -, -⟩ := expTablesAt_of hexp
    have hm := mem_size hκ L (n := 34) (by norm_num) fun j hj ↦
      ⟨_, hsq j (by simp [Tables.gSquaresList]; omega)⟩
    by_contra hlt
    have : 2 ^ κ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  rw [show Fn.body Data.core18 = vsT from vs_body, vsT_take, vsPre] at h
  rw [holdsList_append, holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨⟨F⟩, h⟩ := vs_front hκ hκ6 L hle (List.replicate (2 ^ 23) 0) hgkr htab hexp h
  rw [← holdsList_append, ← holdsList_append] at h
  have h' := ((holdsList_noRet _ noRet_mid _ _).1 h).2
  rw [vsTailT_take7, holdsList_append] at h'
  have hsL := tableHeights_length F.rowsN F.hrowsL
  have h5 := vsKnown_tail hκ hκ6 L hle hcp hexp F.hm32 hsL F.hh33 F.hkb h'
  exact kb_bounds hsL F.hh31 F.hm30 h5 F.hkb

end
end LeanVM.Guest.B1.VerifySub
