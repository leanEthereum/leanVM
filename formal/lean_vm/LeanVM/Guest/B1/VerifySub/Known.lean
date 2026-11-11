/-
  LeanVM.Guest.B1.VerifySub.Known

  `kappa_base` is in range after `verify_sub`'s placement and the stack's log check
  (G:3632-3635): the facts of `VsKnown`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Mid
public import LeanVM.Guest.B1.VerifySub.Body
public import LeanVM.Guest.B1.Placement.Interface
public import LeanVM.Guest.B1.Placement.Kappas

/-!
# The columns' logs, from the placement and the stack's log

`vsPlaceT_known`: from `kappa_base = [1, g^logMem, d_0, …, d_5]` (`logMem ≤ 32`, the `d_t` hinted
words) and the exponent table, `vsPlaceT`'s statements — `certify_placement` (its range checks make
the `d_t` powers `g^τ_t`, `τ_t < 34`), `m = max 15 (log2Ceil total)` in the exponent, and
`g^(m - 22)` range-checked below `g^7` — give `m ≤ 28`, so every committed column's log is below
`29` (`hypKappa_holds`): the memory's `logMem ≤ 28`, each table's `τ_t ≤ 28` and the Keccak
table's `τ_5 + 6 ≤ 28` (`q_keccak`). `kb_bounds`: `kappa_base`'s entries are then below `kbBound`,
what `check_opening_terminal`'s dispatches on `kb[i]`, `kb[0]·g^19` and `kb[7]·g^6` need.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {σ : Val} {next : Prop} {kret : List E → Prop}

theorem kn_ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

/-- `LIG_MIN_SHIFT_INV = g^-22`. -/
theorem vsGinv22_mul : vsGinv22 * gen ^ 22 = 1 := by
  rw [show vsGinv22 = ofK (K.ofBits 8198552432976855044) by rw [vsGinv22, word_eOfNat]; rfl,
    gen_pow_eq_ofK, ← kn_ofK_mul,
    show K.ofBits 8198552432976855044 * Parameters.addressOfIndex 22 = 1 by decide +kernel]
  exact map_one (algebraMap K E)

theorem kn_hs_lt {hs : List ℕ} (hh : ∀ x ∈ hs, x < 34) (i : ℕ) : hs.getD i 0 < 34 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : hs[i]? with _ | x
  · simp
  · exact hh x (List.mem_of_getElem? hx)

theorem kn_columnKappas_le {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 34) (hm : logMem ≤ 32) :
    ∀ x ∈ columnKappas logMem Tables.guestLogBytecode hs, x ≤ 40 := by
  intro x hx
  unfold columnKappas at hx
  rw [List.mem_append] at hx
  have hq : qkeccakSlotBits = 6 := by decide
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · decide
    · have := kn_hs_lt hh opKeccak; rw [hq]; omega
  · rw [List.mem_flatMap] at hx
    obtain ⟨t, -, ht⟩ := hx
    rw [(List.mem_replicate.1 ht).2]
    have := kn_hs_lt hh t.opcode; omega

theorem kn_stackTotal_lt {kappas : List ℕ} (hl : kappas.length = 158) (hk : ∀ x ∈ kappas, x ≤ 40) :
    Tables.stackTotal kappas < 2 ^ 60 := by
  have hle := List.sum_le_length_nsmul ((Tables.committedKappas kappas).map (2 ^ ·)) (2 ^ 40) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    refine Nat.pow_le_pow_right (by norm_num) ?_
    simp only [Tables.committedKappas, List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    rw [List.getD_eq_getElem?_getD]
    rcases hc : kappas[c]? with _ | z
    · simp
    · simp only [Option.getD_some]; exact hk z (List.mem_of_getElem? hc))
  have hlen : (Tables.committedKappas kappas).length ≤ 158 := by
    simp only [Tables.committedKappas, Tables.committedCols, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp [hl])
  simp only [List.length_map, smul_eq_mul] at hle
  unfold Tables.stackTotal
  calc _ ≤ _ := hle
    _ ≤ 158 * 2 ^ 40 := Nat.mul_le_mul_right _ hlen
    _ < 2 ^ 60 := by norm_num

/-- The bound `check_opening_terminal`'s dispatches need of `kappa_base`'s entry `i`: `kb[0] = g^0`
(dispatched as `kb[0]·g^19`), the memory's and the tables' logs below `29`, and the Keccak table's
below `23` (dispatched as `kb[7]·g^6`). -/
def kbBound (i : ℕ) : ℕ := [1, 29, 29, 29, 29, 29, 29, 23].getD i 0

/-- What the placement and the size check give of the base: the table logs `hs`, the memory's log
at most `28`, every table's below `29` and the Keccak table's at most `22`. -/
def PlaceKnown (rd : Reader) (σ : Val) (logMem : ℕ) (ds : List E) : Prop :=
  ∃ hs : List ℕ, hs.length = 6 ∧ ds = hs.map (gen ^ ·) ∧ logMem ≤ 28 ∧ (∀ x ∈ hs, x < 29) ∧
    hs.getD 5 0 ≤ 22 ∧
    ∃ off, σ (.n 274) = gen ^ Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs) ∧
      σ (.n 275) = off ∧ Tables.PCtx rd (columnKappas logMem Tables.guestLogBytecode hs) off ∧
      σ (.n 276) = gen ^ max 15 (log2Ceil
        (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs))) ∧
      max 15 (log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs))) ≤ 28

/-- **The placement and the stack's log** (G:3632-3635): the base's table entries are powers
`g^τ_t`, and the stack at most `2^28` puts every committed column's log below `29`. -/
theorem vsPlaceT_known {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hcp : Tables.certify_placement_Spec L.read)
    (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {ds : List E} (hm : logMem ≤ 32) (hl : ds.length = 6)
    (hkb : ReadsAt L.read (σ (.n 83)) (1 :: gen ^ logMem :: ds))
    (h : Stmt.HoldsList C L.read σ vsPlaceT next kret) :
    PlaceKnown L.read σ logMem ds ∧ next := by
  simp only [vsPlaceT, Stmt.HoldsList, Stmt.Holds, vsCall, vsConst, vsMul, vsRange,
    List.map_cons, List.map_nil, Atom.Holds] at h
  obtain ⟨c1, c2, e277, m278, e279, r278, hn⟩ := h
  refine ⟨?_, hn⟩
  -- the placement
  have hsq : Tables.TbReadsAt L.read (σ (.n 4)) Tables.gSquaresList := fun k hk ↦ by
    simp only [Tables.gSquaresList, List.length_map, List.length_range] at hk
    simpa [Tables.gSquaresList] using hexp.1 k hk
  have hrk : Tables.TbReadsAt L.read (σ (.n 4) * gen ^ 178) Tables.rankKeysList := fun k hk ↦ by
    simp only [Tables.rankKeysList, List.length_map, List.length_range] at hk
    rw [loadHolds_mul_gen_pow]
    simpa [Tables.rankKeysList] using hexp.2.2.1 k hk
  obtain ⟨hs, hsl, hds, hh34, off, hr, hP⟩ := hcp logMem ds _ _ _ hm hl hkb hsq hrk (hC _ _ _ c1)
  simp only [List.cons.injEq, and_true] at hr
  obtain ⟨h274, h275⟩ := hr
  -- the stack's log
  have hST0 := kn_stackTotal_lt (Tables.columnKappas_length logMem Tables.guestLogBytecode hs)
    (kn_columnKappas_le hh34 hm)
  have hr2 := (log2_holds.2 hκ hκ6 L _ _ hexp _).1 (hC _ _ _ c2)
  rw [h274, meaningLog2CeilExp_pow (by norm_num) hST0] at hr2
  simp only [List.cons.injEq, and_true] at hr2
  obtain ⟨hlt34, hr2⟩ := hr2
  obtain ⟨e, he, h278⟩ := rc_pow hκ hκ6 L (a := 6) (by norm_num)
    (by rw [e279, show (64 : ℕ) = 2 ^ 6 from rfl, word_pow2 (by norm_num)]) r278
  have hm28 : max 15 (log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)))
      = e + 22 := by
    have := congrArg (· * gen ^ 22) (m278.symm.trans h278)
    simp only [hr2, e277, mul_assoc, vsGinv22_mul, mul_one, ← pow_add] at this
    exact gen_pow_inj (by omega) (by omega) this
  have h28 : log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)) ≤ 28 := by
    omega
  have hK := Tables.hypKappa_holds _ (Tables.columnKappas_length _ _ _) h28
  have hck := Tables.committedKappas_columnKappas logMem hs hsl
  have kc : ∀ c < 94, ((0 :: logMem :: hs).getD (Tables.colKappaSrc c) 0 + Tables.colKappaAdj c) < 29 :=
    fun c hc ↦ by
      have := hK c hc
      rwa [hck, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
        List.getElem_map, List.getElem_range] at this
  refine ⟨hs, hsl, hds, ?_, ?_, ?_, off, h274, h275, hP, hr2, by omega⟩
  · have := kc 0 (by decide)
    simp [Tables.colKappaSrc, Tables.colKappaAdj] at this
    omega
  · obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
      match hs, hsl with
      | [h0, h1, h2, h3, h4, h5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
    have k5 := kc 5 (by decide)
    have k18 := kc 18 (by decide)
    have k31 := kc 31 (by decide)
    have k38 := kc 38 (by decide)
    have k52 := kc 52 (by decide)
    have k66 := kc 66 (by decide)
    simp [Tables.colKappaSrc, Tables.colKappaAdj] at k5 k18 k31 k38 k52 k66
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  · obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
      match hs, hsl with
      | [h0, h1, h2, h3, h4, h5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
    have k4 := kc 4 (by decide)
    simp [Tables.colKappaSrc, Tables.colKappaAdj] at k4
    simp only [List.getD_cons_succ, List.getD_cons_zero]
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

theorem vsHeadT_noRet : Stmt.noRetList vsHeadT = true := by decide +kernel

theorem vsReadsT_noRet : Stmt.noRetList vsReadsT = true := by decide +kernel

theorem vsPushT_noRet : Stmt.noRetList vsPushT = true := by decide +kernel

theorem vsRootsT_noRet : Stmt.noRetList vsRootsT = true := by decide +kernel

theorem vsPre249_length : (vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsPlaceT).length =
    249 := by decide +kernel

theorem vsT_pre249 : vsT = (vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++ vsRootsT ++ vsPlaceT) ++
    (vsOodT ++ vsBusGrindT ++ vsFpwT ++ vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++ vsTailT) := by
  simp only [vsT, List.append_assoc]

/-- **`VsKnown`** from `certify_placement`'s specification: `kappa_base`'s entries below
`kbBound`, from the body's first `1552` statements (only its first `249` are read). -/
theorem vsKnown_of {κ : ℕ} (L : MemoryImage κ) (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (hcp : Tables.certify_placement_Spec L.read)
    (σ : Val) (hexp : B1.ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 1552) True
      (fun _ ↦ True)) :
    ∀ i < 8, ∃ e < kbBound i, LoadHolds L.read (σ (.n 83)) i (ofK (addressOfIndex e)) := by
  have hκ : κ ≤ 32 := h32
  have hκ6 : 6 ≤ κ := by have : 16 ≤ κ := h16; omega
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  rw [show Fn.body Data.core18 = vsT from vs_body, vsT_pre249, List.take_append,
    List.take_of_length_le (by rw [vsPre249_length]; omega)] at h
  simp only [holdsList_append] at h
  have h := ((holdsList_noRet _ vsHeadT_noRet _ _).1 h).2
  have h := ((holdsList_noRet _ vsReadsT_noRet _ _).1 h).2
  obtain ⟨-, logMem, -, -, -, -, -, hm32, -, -, ds, hdl, -, hkb, -, h⟩ := vsSizesT_holds hκ hκ6 L hle h
  have h := ((holdsList_noRet _ vsPushT_noRet _ _).1 h).2
  have h := ((holdsList_noRet _ vsRootsT_noRet _ _).1 h).2
  obtain ⟨⟨hs, hsl, rfl, hm28, hh, h5, -⟩, -⟩ := vsPlaceT_known hκ hκ6 L hle hcp hexp hm32 hdl hkb h
  exact kb_bounds hsl hh hm28 h5 hkb

end
end LeanVM.Guest.B1.VerifySub
